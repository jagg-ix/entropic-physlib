/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.SpacetimePositiveMass
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.JacobsonUnruhRindlerClock
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Gauss–Codazzi thermodynamics on the timelike screen (Piazza, arXiv:1005.5151)

An extension of `SpacetimePositiveMass` (the Gauss–Codazzi / spacetime-PMT arc) to the **thermodynamic** reading
of the same geometry, following F. Piazza, *"Gauss–Codazzi thermodynamics on the timelike screen"*,
arXiv:1005.5151v2 (2010). Piazza extends Jacobson's horizon result — the matter-energy flux through a local
Rindler horizon obeys the first law `dE = T dS` (Eq. 1.1) — to a **timelike screen** `ℋ` of observers with
finite acceleration `A`, using the Gauss–Codazzi equation (Eq. 3.2) `(R_{dabc} n^d)_{\|ℋ} = (K_{ab;c} −
K_{ac;b})_{\|ℋ}`.

Where `SpacetimePositiveMass` reads the Gauss–Codazzi/constraint geometry as the *gravitational mass*, this
module reads it as *heat* `dE = T dS`: the same Einstein/Gauss–Codazzi structure, the thermodynamic face.

* **§A — Einstein flux, Unruh temperature, Bekenstein–Hawking entropy.** the Einstein-equation step
  `R_{ab}V^a n^b = 8πG\,T_{ab}V^a n^b` (the metric term drops since `V ⟂ n`, Eq. 3.3); `T = A/2π`;
  `S = 𝒜/4G`.
* **§B — the Clausius first law `dE = T dS` (Eq. 3.7).** the flat-screen energy flux `dE = A\,d𝒜/(8πG)` equals
  `T dS = (A/2π)·d(𝒜/4G)` — Jacobson's first law for the finite-acceleration screen (`screen_first_law`).
* **§C — the expansion is the log-derivative of area.** `θ̃ = d ln(Δ𝒜)/ds`, i.e. `d𝒜/ds = θ̃·𝒜`, which feeds
  the flux `dE = (1/8πG)·A·θ̃·𝒜·ds`.
* **§D — the cone condition (Eq. 3.10/3.11).** for the cone profile `k̃ = 1/R`, `Θ = R'/R`, the extrinsic
  curvature evolves as `dk̃/ds = −Θ k̃` — the geometric requirement that lets a curved screen still satisfy the
  first law.

All statements are exact `ring`/algebra identities. The geometric derivation (the tensor Gauss–Codazzi
calculation Eqs. 2.1–3.6) is Piazza's; formalized here is the thermodynamic algebra it produces.

## References

* F. Piazza, arXiv:1005.5151v2 — Eqs. (1.1), (3.2), (3.3), (3.7), (3.10), (3.11); T. Jacobson, PRL 75 (1995)
  1260. `Physlib` (`SpacetimePositiveMass` — Gauss–Codazzi constraints; `AdSCFT.PenroseHolographicMassEntropyBound`,
  `HorizonCell.CellThreeFacesAssembly` — `S = A/4`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics


/-- **[The Einstein-equation flux step (Eq. 3.3)]** for `V ⟂ n` (the screen velocity is orthogonal to the
normal, `g_{ab}V^a n^b = 0`), the Einstein equation `R_{ab} − ½R g_{ab} = 8πG T_{ab}` contracted with `V^a n^b`
gives `R_{ab}V^a n^b = 8πG T_{ab}V^a n^b` — the metric/cosmological term drops out. -/
lemma ricci_flux_eq_matter_flux (ricciFlux R gFlux matterFlux G : ℝ) (hg : gFlux = 0)
    (heinstein : ricciFlux - (1 / 2) * R * gFlux = 8 * Real.pi * G * matterFlux) :
    ricciFlux = 8 * Real.pi * G * matterFlux := by
  rw [hg] at heinstein; simpa using heinstein

-- The Unruh temperature `T = A/2π` of a screen observer with acceleration scalar `A` is the
-- geometric-convention carrier `Lorentz.JacobsonUnruhRindlerClock.unruhTemperature` (the local
-- duplicate this file used to define is consolidated onto it).
open Physlib.QuantumMechanics.ComplexAction.Lorentz.JacobsonUnruhRindlerClock in
section
open Physlib.QuantumMechanics.ComplexAction.Lorentz.JacobsonUnruhRindlerClock

/-- The **Bekenstein–Hawking entropy** `S = 𝒜/4G` of the screen area `𝒜`. -/
noncomputable def bekensteinHawkingEntropy (area G : ℝ) : ℝ := area / (4 * G)

/-- The **entropy differential** `dS = d𝒜/4G`. -/
noncomputable def entropyDifferential (dArea G : ℝ) : ℝ := dArea / (4 * G)


/-- The **flat-screen energy flux** `dE = A·d𝒜/(8πG)` (Eq. 3.7) — the matter-energy through the screen element
in proper time `ds`, after using the Gauss–Codazzi relation `R_{ab}V^a n^b = A θ̃` for a flat (`K̃ = 0`)
screen. -/
noncomputable def screenEnergyFlux (A dArea G : ℝ) : ℝ := A * dArea / (8 * Real.pi * G)

/-- **[Jacobson's first law on the timelike screen] `dE = T dS`** — the flat-screen energy flux equals the
Unruh temperature times the Bekenstein–Hawking entropy change: `A·d𝒜/(8πG) = (A/2π)·(d𝒜/4G)`. This is Eq.
(3.7) `=` Eq. (1.1), the central result of Piazza's extension of Jacobson to finite acceleration. -/
lemma screen_first_law (A dArea G : ℝ) :
    screenEnergyFlux A dArea G = unruhTemperature A * entropyDifferential dArea G := by
  unfold screenEnergyFlux unruhTemperature entropyDifferential; ring


/-- The **area rate** `d𝒜/ds = θ̃·𝒜` — from `θ̃ = d ln(Δ𝒜)/ds` (Eq. 3.5/3.7), the proper-time derivative of
the screen area element is the two-dimensional expansion times the area. -/
noncomputable def areaRate (expansion area : ℝ) : ℝ := expansion * area

/-- **[The expansion is the logarithmic derivative of the area]** `θ̃ = (d𝒜/ds)/𝒜` (`= d ln 𝒜/ds`). -/
lemma expansion_eq_log_deriv_area (expansion area : ℝ) (h : area ≠ 0) :
    areaRate expansion area / area = expansion := by
  unfold areaRate; rw [mul_div_assoc, div_self h, mul_one]

/-- **[Energy flux from the expansion]** `dE = (1/8πG)·A·θ̃·𝒜·ds` — substituting `d𝒜 = θ̃·𝒜·ds` into the
screen flux. -/
lemma screenEnergyFlux_from_expansion (A expansion area G : ℝ) :
    screenEnergyFlux A (areaRate expansion area) G = A * expansion * area / (8 * Real.pi * G) := by
  unfold screenEnergyFlux areaRate; ring


/-- The cone-section **extrinsic curvature** `k̃ = 1/R` (a circle of radius `R(s)` at distance `s` from the
cone vertex). -/
noncomputable def coneExtrinsicCurvature (R : ℝ) : ℝ := 1 / R
/-- The cone **expansion** `Θ = R'/R` of the straight generators through the vertex. -/
noncomputable def coneExpansion (R Rprime : ℝ) : ℝ := Rprime / R
/-- The **rate of extrinsic curvature** `dk̃/ds = −R'/R²`. -/
noncomputable def coneCurvatureRate (R Rprime : ℝ) : ℝ := -Rprime / R ^ 2

/-- **[The cone condition `dk̃/ds = −Θ k̃` (Eq. 3.10/3.11)]** the extrinsic curvature of the screen rescales in
proper time proportionally to the expansion — the weakened flatness requirement (`K̃` evolves "like on a cone")
under which the finite-acceleration screen still obeys the first law. -/
lemma cone_condition (R Rprime : ℝ) :
    coneCurvatureRate R Rprime = -(coneExpansion R Rprime) * coneExtrinsicCurvature R := by
  unfold coneCurvatureRate coneExpansion coneExtrinsicCurvature; ring


/-- **[Acceleration scalar (Eq. 2.2)]** `A² = V̇·V̇` — with `V̇_a = A n_a` and a unit normal `n` (`n·n = 1`),
the squared acceleration vector equals the acceleration scalar squared (`A²` defines the screen temperature
`T = A/2π`). -/
lemma acceleration_scalar_sq (A nDotn : ℝ) (hn : nDotn = 1) : A ^ 2 * nDotn = A ^ 2 := by
  rw [hn, mul_one]

/-- **[Expansion decomposition (Eq. 2.11)]** `θ = θ̃ + θ₃` — the full expansion splits into the two-dimensional
screen expansion `θ̃` (which feeds the entropy / area change) and the normal-direction expansion `θ₃` (which is
irrelevant to the first law). -/
noncomputable def totalExpansion (expansion2D expansion3 : ℝ) : ℝ := expansion2D + expansion3

/-- **[Extrinsic curvature trace (Eq. 3.1)]** `K = A + tr K̃` — from the decomposition `K_ab = −A V_a V_b +
K̃_ab` and the timelike normalization `V·V = −1`, the trace of the screen's extrinsic curvature is the
acceleration `A` plus the two-dimensional trace `tr K̃`. -/
lemma extrinsicCurvature_trace (A KtildeTrace : ℝ) :
    -A * (-1) + KtildeTrace = A + KtildeTrace := by ring

/-- The Gauss–Codazzi contraction `q^{ab} V^c K_{ac;b} = A θ̃ − θ̃^c_b K̃_{ac}` (Eq. 3.5). -/
noncomputable def gaussCodazziContraction (A expansion2D KtildeTerm : ℝ) : ℝ :=
  A * expansion2D - KtildeTerm

/-- **[Flat-screen Ricci flux (Eqs. 3.4, 3.5, 3.8)]** when the projected extrinsic curvature vanishes
(`K̃ = 0`, condition iv-a), the Gauss–Codazzi scalar collapses to `R_{ab}V^a n^b = A θ̃` — the geometric input
that turns the matter flux into `(1/8πG) A θ̃ Δ𝒜 ds`. -/
lemma flat_screen_ricci_flux (A expansion2D : ℝ) :
    gaussCodazziContraction A expansion2D 0 = A * expansion2D := by
  unfold gaussCodazziContraction; ring

/-- **[The complete Jacobson derivation on the flat timelike screen]** combining the flat-screen Gauss–Codazzi
relation `R_{ab}V^a n^b = A θ̃` (`hflat`) with Einstein's equation `T_{ab}V^a n^b = R_{ab}V^a n^b/(8πG)`
(`hein`), the matter energy flux per unit area is the Unruh temperature times the entropy change:
`dE = T dS`. This assembles Eqs. (3.3)–(3.8) into the first law Eq. (1.1) for the finite-acceleration screen. -/
lemma flat_screen_full_first_law (A expansion2D area G ricciFlux matterFlux : ℝ)
    (hflat : ricciFlux = A * expansion2D)
    (hein : matterFlux = ricciFlux / (8 * Real.pi * G)) :
    matterFlux * area = unruhTemperature A * entropyDifferential (areaRate expansion2D area) G := by
  rw [hein, hflat]
  unfold unruhTemperature entropyDifferential areaRate
  ring

end

end Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics

end
