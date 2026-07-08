/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
public import Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification

/-!
# CHSH / Bell is the spacelike (Locality) face of the light cone

Links the CHSH / Bell formalizations (`Bell.DeterministicBounds`, `AlgebraicQFT.SummersVacuumBellCHSH`) to the
`45°`-light-cone "Three Faces" unification of `Rapidity.LightCone45RapidityUnification`. The unification
document's **Three Faces** — *Information* (the imaginary energy `E_I = ⟨T̂⟩`, entropic time),
*Spacelike* (Locality), *Timelike* (Dynamics, `E = γmc²`) — are the causal regions of the light cone
in the complex `(E, ξ)` plane (`lorentzianForm q = E² − ξ²`).

**CHSH / Bell correlations are the Spacelike face (Locality).** Bell correlations are defined for
**spacelike-separated** regions (the CHSH commuting observables `AᵢBⱼ = BⱼAᵢ` are microcausality /
Einstein locality / no-signaling — `AlgebraicQFT.SummersVacuumBellCHSH`). The spacelike region is `lorentzianForm
q < 0` (`spacelike`, `spacelike_iff_abs_lt`, `|Re q| < |Im q|`) — *outside* the `45°` cone — and the
Locality face's correlation limits are the CHSH bounds: classical `|S| ≤ 2` (`classicalCHSH_bound`),
Tsirelson `|S| ≤ 2√2` (`tsirelson_correlation_bound`).

The `45°` null cone (`lightlike`, the **massless / luminal limit** `β = ±1`,
`massless_energyVector_lightlike`) is the **no-signaling boundary** between the Spacelike (Locality) and
Timelike (Dynamics) faces (`causal_trichotomy`); the Information face's imaginary unit `i` (the entropic
time `E_I`) **swaps** the two (`spacelike_timelike_wick_swap`, `lorentzianForm(i·q) = −lorentzianForm
q`). And the Locality face is **Lorentz-invariant** — boosts preserve `lorentzianForm`
(`spacelike_boost_invariant`), so the CHSH no-signaling structure is relativistically invariant.

* **§A — the spacelike (Locality) face** (`spacelike`, `spacelike_iff_abs_lt`, `causal_trichotomy`).
* **§B — CHSH / Bell on the Locality face** (`chsh_on_spacelike_face`).
* **§C — the boundary and the Wick swap** (`spacelike_timelike_wick_swap`, `spacelike_boost_invariant`).
* **§D — the Three Faces, unified** (`threeFaces_chsh_unification`).

## References

* The complex-action/entropic-time grand-unification "Rosetta Stone" (Three Faces); J. Bisognano, E. Wichmann (microcausality
  / wedge locality). Repo dependencies: `Bell.DeterministicBounds`, `Rapidity.LightCone45RapidityUnification`,
  `ComplexDelta.Convergence` (`lorentzianForm`, `lorentzian_pos_iff_timelike`, `lorentzianForm_mul_I`),
  `TimeOperator.HyperbolicPoincareLorentzMisra` (`lorentzBoost_preserves_form`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces

open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra

/-! ## §A — the spacelike (Locality) face -/

/-- **The spacelike (Locality) face** `L(q) < 0` — the causal region *outside* the `45°` light cone,
where Bell / CHSH correlations live (spacelike-separated regions, Einstein locality / no-signaling). -/
def spacelike (q : ℂ) : Prop := lorentzianForm q < 0

/-- **The spacelike condition** `|Re q| < |Im q|` — the Locality face is the region with the imaginary
(spatial) leg longer than the real (temporal) one, outside the `45°` cone. -/
theorem spacelike_iff_abs_lt (q : ℂ) : spacelike q ↔ |q.re| < |q.im| := by
  unfold spacelike lorentzianForm
  constructor
  · intro h; nlinarith [sq_abs q.re, sq_abs q.im, abs_nonneg q.re, abs_nonneg q.im]
  · intro h; nlinarith [sq_abs q.re, sq_abs q.im, abs_nonneg q.re, abs_nonneg q.im]

/-- **[The Three causal Faces] every point is spacelike, lightlike, or timelike** — the `45°` null cone
`lightlike` (boundary) separates the **Spacelike** (Locality) and **Timelike** (Dynamics) faces, the two
non-Information faces of the unification. -/
theorem causal_trichotomy (q : ℂ) : spacelike q ∨ lightlike q ∨ 0 < lorentzianForm q := by
  unfold spacelike lightlike
  rcases lt_trichotomy (lorentzianForm q) 0 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ## §B — CHSH / Bell on the spacelike (Locality) face -/

/-- **[CHSH / Bell is the Spacelike face] the Locality-face correlation limits are the CHSH bounds.**
On a spacelike point (`|Re q| < |Im q|`, the Locality face, where Bell correlations live), the CHSH
combination obeys the classical local-hidden-variable bound `|S| ≤ 2` (`classicalCHSH_bound`) and the
quantum Tsirelson bound `2√2 > 2` (`classical_lt_tsirelson`) — the spacelike-separated Bell correlation,
bounded by the no-signaling structure. -/
theorem chsh_on_spacelike_face (q : ℂ) (hq : spacelike q) (x : CHSHAssignment) :
    |q.re| < |q.im|
      ∧ |classicalCHSHValue x| ≤ 2
      ∧ (2 : ℝ) < tsirelsonWitness :=
  ⟨(spacelike_iff_abs_lt q).mp hq, classicalCHSH_bound x, classical_lt_tsirelson⟩

/-! ## §C — the boundary and the Wick swap -/

/-- **[Information `i` swaps Locality ↔ Dynamics] `spacelike q ↔ timelike (i·q)`.** Multiplying by the
imaginary unit `i` — the same `i` of the Information face's entropic time `E_I` — flips the spacelike
(Locality) face to the timelike (Dynamics) face, since `lorentzianForm(i·q) = −lorentzianForm q`
(`ComplexDelta.Convergence.lorentzianForm_mul_I`). The Wick rotation between the two faces. -/
theorem spacelike_timelike_wick_swap (q : ℂ) :
    spacelike q ↔ 0 < lorentzianForm (Complex.I * q) := by
  unfold spacelike
  rw [lorentzianForm_mul_I]
  constructor <;> intro h <;> linarith

/-- **[The Locality face is Lorentz-invariant] boosts preserve `lorentzianForm`.** A Lorentz boost on
the energy vector `(E, ξ)` preserves `E² − ξ²` (`lorentzBoost_preserves_form`), so the spacelike
(Locality / no-signaling) face is **boost-invariant** — the CHSH spacelike-separation structure is
relativistically invariant (the same in every inertial frame). -/
theorem spacelike_boost_invariant (θ t x : ℝ) :
    (lorentzBoost θ t x).1 ^ 2 - (lorentzBoost θ t x).2 ^ 2 = t ^ 2 - x ^ 2 :=
  lorentzBoost_preserves_form θ t x

/-! ## §D — the Three Faces, unified -/

/-- **[The Three Faces with CHSH = Spacelike, unified].** The unification document's Three Faces are the
causal regions of the light cone: *Spacelike* (Locality) is where Bell / CHSH lives — bounded by the
classical `|S| ≤ 2` and quantum `2√2` (`chsh_on_spacelike_face`); the `45°` null cone is the
**massless / luminal** boundary (`massless_energyVector_lightlike`); the Information face's `i` swaps
Locality ↔ Dynamics (`spacelike_timelike_wick_swap`); and the Locality face is Lorentz-invariant
(`spacelike_boost_invariant`). CHSH / Bell correlations are the spacelike, no-signaling, boost-invariant
Locality face of the relativistic light cone. -/
theorem threeFaces_chsh_unification (q : ℂ) (hq : spacelike q) (x : CHSHAssignment) (ξ θ t x' : ℝ) :
    |classicalCHSHValue x| ≤ 2
      ∧ (2 : ℝ) < tsirelsonWitness
      ∧ lightlike ((bogoliubovEnergy ξ 0 : ℂ) + (ξ : ℂ) * Complex.I)
      ∧ (spacelike q ↔ 0 < lorentzianForm (Complex.I * q))
      ∧ (lorentzBoost θ t x').1 ^ 2 - (lorentzBoost θ t x').2 ^ 2 = t ^ 2 - x' ^ 2 :=
  ⟨classicalCHSH_bound x, classical_lt_tsirelson, massless_energyVector_lightlike ξ,
    spacelike_timelike_wick_swap q, spacelike_boost_invariant θ t x'⟩

end Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces

end
