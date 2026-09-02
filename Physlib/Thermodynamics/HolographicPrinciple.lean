/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
public import Physlib.Relativity.SemiClassical.HawkingTemperature
public import Physlib.Thermodynamics.BekensteinJacobsonEntropicBits
public import Physlib.Thermodynamics.NewtonGIsolation
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

meta import Zil

/- Consolidated from Physlib/Thermodynamics/HolographicScreenEntropy.lean -/

/-!
# The Verlinde screen carries Bekenstein–Hawking entropy

Welds the two information-count carriers of the repository that were consistent but never
connected: the **Verlinde screen cells** `holographicBits A G ℏ c = A·c³/(Gℏ) = A/ℓ_P²`
(`Thermodynamics.VerlindeNewtonGravity`, the count that `newtonG_isolated` proved is
forced by Newton's form) and the **quarter-nat horizon cells**
`microstateEntropy N = N·log k` with `cellBondDimension k = e^{1/4}`
(`HorizonCell.CellBondDimension`, the per-cell quantum that
`logBondDimension_fixed_by_areaLaw` proved is forced by the area law).  Composed, they
give Bousso's dictionary (*The holographic principle*, Rev. Mod. Phys. **74** (2002) 825)
as theorems:

* `holographicBits_eq_planckCells` — the screen count is the Planck-cell count `A/ℓ_P²`
  under the Planck-length identification `ℓ_P² = Gℏ/c³`;
* `screenEntropy_bekensteinHawking` — `S(screen) = A·c³/(4Gℏ)`: Bousso **Eq. (2.2)**,
  the Bekenstein–Hawking entropy in full units (nats, `k_B ≡ 1`);
* `screenEntropy_area_quarter` — `S(screen) = A/(4ℓ_P²)`: Bousso **Eqs. (3.4)/(3.6)** —
  the degrees of freedom in a region bounded by area `A` are `A/4` in Planck units; pure
  composition with the existing `bekensteinHawking_recovery`;
* `screen_hilbert_dimension` — `k^N = e^{A c³/(4Gℏ)}`: Bousso **Eq. (3.7)**
  `𝒩 = e^{A/4}`, the Hilbert-space dimension of the fundamental system;
* `schwarzschild_screen_entropy` and `..._planckMass` — the horizon screen saturates the
  count: `S = 4πGM²/(ℏc) = 4π·M²/m_P²`: Bousso **Eq. (2.26)** `S = 4πM²` in Planck
  masses — the black hole as the most entropic object of given size (§II.C.3);
* `newton_form_forces_bekensteinHawking` — the system closure: if the entropic force
  takes Newton's form `F = GMm/R²`, the screen's microstate entropy **is**
  Bekenstein–Hawking at the same `G` — extending
  `newtonG_establishes_gravitationalSystem` to Bousso's entropy sector.

**Honest layering.**  Exact identities at the saturating configuration — the dictionary
sector of Bousso's review.  His actual subject, the entropy *bounds*, is inequality
content: the covariant bound of §V now lives in `BoussoCovariantEntropyBound`
(`LightSheet.bousso_covariant_bound`, on a local Flanagan-Marolf-Wald flux hypothesis), and
this module's exact identities are its saturating configuration -- the caustic limit of
`LightSheet.entropyFlux_eq_bekenstein_deficit`.  The Bekenstein Eq. (2.9) and spherical
Eq. (2.22) bounds are derived from the generalized second law in
`HolographicEntropyBounds`.  The `c = 1` face of Eq. (2.2) on
the entropic-time carrier is the existing
`CausalDiamondThermodynamics.bekensteinTauEnt_eq_over_hbarG`; this module states the
full-units face on the statistical carrier `microstateEntropy`.

## References

* R. Bousso, *The holographic principle*, Rev. Mod. Phys. **74** (2002) 825,
  arXiv:hep-th/0203101.  Eqs. (2.2), (2.26), (3.1), (3.4), (3.6), (3.7).
* Carrier reuse: `Thermodynamics.VerlindeNewtonGravity` (`holographicBits`,
  `sphereArea`), `Thermodynamics.NewtonGIsolation` (`newtonG_isolated`,
  `bitScreenTemperature`), `HorizonCell.CellBondDimension` (`microstateEntropy`,
  `cellBondDimension`, `bekensteinHawking_recovery`),
  `Relativity.SemiClassical.SchwarzschildVerlinde` (`schwarzschildRadius`),
  `ComptonClock.EntanglementScreenArea` (`planckMassSq`).
-/

set_option autoImplicit false

open Physlib.Thermodynamics
open Physlib.Thermodynamics.NewtonGIsolation
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea
open Physlib.Relativity.SemiClassical

@[expose] public section

namespace Physlib.Thermodynamics.HolographicScreenEntropy

/-! ## §A — the dictionary: screen cells are Planck cells, their entropy is `A/4` -/

/-- **The screen count is the Planck-cell count**: under the Planck-length identification
`ℓ_P² = Gℏ/c³`, the Verlinde bit count is exactly `A/ℓ_P²` — the raw cell count consumed
by `bekensteinHawking_recovery`. -/
theorem holographicBits_eq_planckCells (A G ℏ c ℓP : ℝ)
    (hℓ : ℓP ^ 2 = G * ℏ / c ^ 3) :
    holographicBits A G ℏ c = A / ℓP ^ 2 := by
  rw [hℓ, div_div_eq_mul_div]
  rfl

/-- **The Verlinde screen carries Bekenstein–Hawking entropy** — Bousso Eq. (2.2),
`S_BH = A·c³/(4Gℏ)` in nats (`k_B ≡ 1`): the microstate entropy of the screen's
`N = A·c³/(Gℏ)` cells, each at the quarter-nat bond dimension `k = e^{1/4}`. -/
theorem screenEntropy_bekensteinHawking (A G ℏ c : ℝ) :
    microstateEntropy (holographicBits A G ℏ c) = A * c ^ 3 / (4 * (G * ℏ)) := by
  rw [microstateEntropy_eq_quarter, holographicBits_def, div_div, mul_comm (G * ℏ) 4]

/-- **The screen's degrees of freedom are a quarter of its area in Planck units** —
Bousso Eqs. (3.4)/(3.6), `N_dof = A/4` — by pure composition of the two existing welds:
`holographicBits = A/ℓ_P²` cells (above) and `bekensteinHawking_recovery`. -/
theorem screenEntropy_area_quarter (A G ℏ c ℓP : ℝ)
    (hℓ2 : ℓP ^ 2 = G * ℏ / c ^ 3) (hℓ : ℓP ≠ 0) :
    microstateEntropy (holographicBits A G ℏ c) = A / (4 * ℓP ^ 2) := by
  rw [holographicBits_eq_planckCells A G ℏ c ℓP hℓ2, bekensteinHawking_recovery A ℓP hℓ]

/-! ## §B — the Hilbert-space dimension of the fundamental system -/

/-- **The number of states of the screen is `e^{A/4}`** — Bousso Eq. (3.7),
`𝒩 = e^{A/4}` in Planck units: the bond dimension `k = e^{1/4}` raised to the cell
count is the exponential of the Bekenstein–Hawking entropy. -/
theorem screen_hilbert_dimension (A G ℏ c : ℝ) :
    cellBondDimension ^ holographicBits A G ℏ c =
      Real.exp (A * c ^ 3 / (4 * (G * ℏ))) := by
  unfold cellBondDimension
  rw [← Real.exp_mul, holographicBits_def]
  congr 1
  ring

/-! ## §C — black holes saturate the count -/

/-- **The horizon screen's entropy is `4πGM²/(ℏc)`** — Bousso Eq. (2.26), `S = 4πM²` in
Planck units: the screen at the Schwarzschild radius of mass `M` carries exactly the
black-hole entropy, the saturating configuration of the spherical bound (§II.C.3: "the
most entropic object one can put inside a given spherical surface"). -/
theorem schwarzschild_screen_entropy (M G ℏ c : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) :
    microstateEntropy
        (holographicBits (sphereArea (schwarzschildRadius M G c)) G ℏ c) =
      4 * Real.pi * G * M ^ 2 / (ℏ * c) := by
  rw [microstateEntropy_eq_quarter, holographicBits_def]
  unfold sphereArea schwarzschildRadius
  field_simp
  ring

/-- **The horizon entropy in Planck masses**: `S = 4π·M²/m_P²` — the same saturation with
the mass ratio explicit, on the existing `planckMassSq = ℏc/G`. -/
theorem schwarzschild_screen_entropy_planckMass (M G ℏ c : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) :
    microstateEntropy
        (holographicBits (sphereArea (schwarzschildRadius M G c)) G ℏ c) =
      4 * Real.pi * M ^ 2 / planckMassSq G ℏ c := by
  rw [schwarzschild_screen_entropy M G ℏ c hℏ hc hG]
  unfold planckMassSq
  rw [div_div_eq_mul_div]
  ring

/-! ## §D — the system closure: Newton's form forces the entropy -/

/-- **Newton's form forces Bekenstein–Hawking entropy at the same `G`** — the missing
clause of the one-`G` system: if the `G`-free entropic force takes Newton's form
`F = GMm/R²`, then (`newtonG_isolated`) the bit count is the holographic count, and the
screen's microstate entropy **is** the Bekenstein–Hawking entropy of the screen area with
the *same* constant — Bousso's Eq. (2.2) joins Newton, Poisson, the Einstein coupling,
and Schwarzschild in `newtonG_establishes_gravitationalSystem`'s hierarchy. -/
theorem newton_form_forces_bekensteinHawking (M c N kB m ℏ Δx G R : ℝ)
    (hN : N ≠ 0) (hkB : kB ≠ 0) (hΔx : Δx ≠ 0) (hm : m ≠ 0) (hM : M ≠ 0)
    (hc : c ≠ 0) (hℏ : ℏ ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (h : verlindeEntropicForce (bitScreenTemperature M c N kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx) Δx = G * M * m / R ^ 2) :
    microstateEntropy N = sphereArea R * c ^ 3 / (4 * (G * ℏ)) := by
  rw [(newtonG_isolated M c N kB m ℏ Δx G R hN hkB hΔx hm hM hc hℏ hG hR).mp h]
  exact screenEntropy_bekensteinHawking (sphereArea R) G ℏ c

end Physlib.Thermodynamics.HolographicScreenEntropy

end

/- Consolidated from Physlib/Thermodynamics/HolographicEntropyBounds.lean -/

/-!
# The holographic entropy bounds from the generalized second law

The bound sector of Bousso, *The holographic principle* (Rev. Mod. Phys. **74** (2002)
825), §II — the part `HolographicScreenEntropy` deliberately left open.  The generalized
second law (GSL, Bousso Eqs. (2.3)/(2.5)) is the physical input; it enters every theorem
as an **explicit hypothesis**, never as an axiom, and the bounds are its exact
consequences on the repository's welded carriers:

* `susskind_process_spherical_bound` — the **Susskind process** (§II.C.1, Eqs.
  (2.22)–(2.24)): if collapsing a shell converts the system to a black hole whose final
  entropy is the screen's `microstateEntropy`, the GSL forces the **spherical entropy
  bound** `S_matter ≤ A·c³/(4Gℏ)`;
* `blackhole_saturates` — the bound is tight: `4πGM²/(ℏc)` *equals*
  `A(r_s)·c³/(4Gℏ)` — 't Hooft's "most entropic object" (§II.C.3), by composing the two
  saturation faces of `HolographicScreenEntropy`;
* `multi_blackhole_spherical_bound` — Eqs. (2.26)–(2.27): several black holes inside a
  circumscribing sphere satisfy the bound *with room to spare*, by
  `Finset.sum_sq_le_sq_sum_of_nonneg` (the cross terms are the slack);
* `blackHoleEntropy_hasDerivAt`, `schwarzschild_first_law` — the differential face:
  `dS_BH/dM = 8πGM/(ℏc)`, and the Hawking temperature at the Schwarzschild surface
  gravity `κ = c⁴/(4GM)` satisfies `T·k_B·(dS/dM) = c²` — the first law `dE = T dS`
  (Eqs. (2.6)–(2.8)) with `E = Mc²`;
* `geroch_entropy_gain_bound`, `geroch_process_bekenstein_bound` — the **Geroch
  process** (§II.B.1, Eqs. (2.18)–(2.20)): lowering the system to the horizon redshifts
  the added mass to `δM ≤ ER/(4GM)`; the entropy gained by the hole is then at most
  `2πER/(ℏc)` — `G` and `M` cancel — and the GSL forces the **Bekenstein bound**
  `S_matter ≤ 2πER/(ℏc)` (Eq. (2.9)), in which "Newton's constant does not enter": the
  cancellation is the proof, not an observation.

**Honest layering.**  Entropies in nats (`k_B ≡ 1`) except where `k_B` is explicit; the
Geroch redshift factor `χ(R) = R/(2b)` is the leading near-horizon order (Eqs.
(2.15)–(2.17)), taken as the hypothesis `hδ`, and the Unruh–Wald quantum-buoyancy
corrections (§II.B.2) are outside scope; the GSL itself is not derived — it is the
conditional's antecedent, exactly as in the review.  The covariant (light-sheet) bound
of §V is `BoussoCovariantEntropyBound`, whose ceiling is welded to §A's by
`covariantBound_ceiling_eq_sphericalBound`.

## References

* R. Bousso, *The holographic principle*, Rev. Mod. Phys. **74** (2002) 825,
  arXiv:hep-th/0203101.  Eqs. (2.3), (2.6)–(2.9), (2.15)–(2.20), (2.22)–(2.27).
* Carrier reuse: `Thermodynamics.HolographicScreenEntropy` (the dictionary),
  `HorizonCell.CellBondDimension` (`microstateEntropy`),
  `Relativity.SemiClassical.HawkingTemperature`, `SchwarzschildVerlinde`
  (`schwarzschildRadius`), `VerlindeNewtonGravity` (`sphereArea`, `holographicBits`).
-/

set_option autoImplicit false

open Physlib.Thermodynamics
open Physlib.Thermodynamics.HolographicScreenEntropy
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
open Physlib.Relativity.SemiClassical

@[expose] public section

namespace Physlib.Thermodynamics.HolographicEntropyBounds

/-! ## §A — the Susskind process: GSL ⟹ spherical entropy bound -/

/-- **The spherical entropy bound from the GSL** — Bousso Eqs. (2.22)–(2.24): the
Susskind process converts a matter system (entropy `S_matter`) plus a collapsing shell
(entropy `S_shell ≥ 0`) into a black hole that just fills the circumscribing sphere of
area `A`, whose entropy is the screen's `microstateEntropy`.  The GSL —
`S_initial ≤ S_final`, the hypothesis `hGSL` — then forces `S_matter ≤ A·c³/(4Gℏ)`. -/
theorem susskind_process_spherical_bound (S_matter S_shell A G ℏ c : ℝ)
    (hshell : 0 ≤ S_shell)
    (hGSL : S_matter + S_shell ≤ microstateEntropy (holographicBits A G ℏ c)) :
    S_matter ≤ A * c ^ 3 / (4 * (G * ℏ)) := by
  rw [screenEntropy_bekensteinHawking] at hGSL
  linarith

/-- **Black holes saturate the spherical bound** — 't Hooft (§II.C.3): the closed-form
horizon entropy `4πGM²/(ℏc)` *equals* the bound value at the horizon area, by composing
the two saturation faces of `HolographicScreenEntropy`. -/
theorem blackhole_saturates (M G ℏ c : ℝ) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) :
    4 * Real.pi * G * M ^ 2 / (ℏ * c) =
      sphereArea (schwarzschildRadius M G c) * c ^ 3 / (4 * (G * ℏ)) :=
  (schwarzschild_screen_entropy M G ℏ c hℏ hc hG).symm.trans
    (screenEntropy_bekensteinHawking (sphereArea (schwarzschildRadius M G c)) G ℏ c)

/-! ## §B — several black holes: the bound with room to spare -/

/-- **The multi-black-hole bound** — Bousso Eqs. (2.26)–(2.27): black holes of masses
`Mᵢ ≥ 0` have total entropy `Σ 4πGMᵢ²/(ℏc)`; a circumscribing sphere must at least hold
the Schwarzschild area of the total mass (`hA`), and then the spherical bound holds
*with room to spare* — the slack is exactly the cross terms of
`Finset.sum_sq_le_sq_sum_of_nonneg`. -/
theorem multi_blackhole_spherical_bound {ι : Type*} (s : Finset ι) (M : ι → ℝ)
    (A G ℏ c : ℝ) (hM : ∀ i ∈ s, 0 ≤ M i)
    (hG : 0 < G) (hℏ : 0 < ℏ) (hc : 0 < c)
    (hA : 16 * Real.pi * G ^ 2 * (∑ i ∈ s, M i) ^ 2 / c ^ 4 ≤ A) :
    ∑ i ∈ s, 4 * Real.pi * G * M i ^ 2 / (ℏ * c) ≤ A * c ^ 3 / (4 * (G * ℏ)) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsum : ∑ i ∈ s, M i ^ 2 ≤ (∑ i ∈ s, M i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg hM
  calc ∑ i ∈ s, 4 * Real.pi * G * M i ^ 2 / (ℏ * c)
      = 4 * Real.pi * G * (∑ i ∈ s, M i ^ 2) / (ℏ * c) := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
    _ ≤ 4 * Real.pi * G * (∑ i ∈ s, M i) ^ 2 / (ℏ * c) := by gcongr
    _ ≤ A * c ^ 3 / (4 * (G * ℏ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hA' : 16 * Real.pi * G ^ 2 * (∑ i ∈ s, M i) ^ 2 ≤ A * c ^ 4 := by
          rw [div_le_iff₀ (by positivity)] at hA
          linarith
        nlinarith [mul_le_mul_of_nonneg_right hA' hℏ.le, pow_pos hc 4]

/-! ## §C — the differential face: `dS/dM` and the first law -/

/-- **The horizon entropy grows as `dS_BH/dM = 8πGM/(ℏc)`** — the derivative Bousso's
Eq. (2.19) consumes, on the closed form `S_BH(M) = 4πGM²/(ℏc)` of
`schwarzschild_screen_entropy`. -/
theorem blackHoleEntropy_hasDerivAt (G ℏ c M : ℝ) :
    HasDerivAt (fun m : ℝ => 4 * Real.pi * G * m ^ 2 / (ℏ * c))
      (8 * Real.pi * G * M / (ℏ * c)) M := by
  have h8 : (8 : ℝ) * Real.pi * G * M / (ℏ * c) = 4 * Real.pi * G * (2 * M) / (ℏ * c) := by
    ring
  rw [h8]
  simpa using ((hasDerivAt_pow 2 M).const_mul (4 * Real.pi * G)).div_const (ℏ * c)

/-- **The first law of the horizon** — Bousso Eqs. (2.6)–(2.8): at the Schwarzschild
surface gravity `κ = c⁴/(4GM)`, the Hawking temperature times `k_B` times `dS_BH/dM`
is exactly `c²` — that is, `d(Mc²) = T·dS_thermo`: the entropy of
`HolographicScreenEntropy` is the one whose Clausius conjugate is the Hawking
temperature, with the same `G`. -/
theorem schwarzschild_first_law (M G ℏ c kB : ℝ)
    (hM : M ≠ 0) (hG : G ≠ 0) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hkB : kB ≠ 0) :
    hawkingTemperature ℏ (c ^ 4 / (4 * G * M)) c kB
        * (kB * (8 * Real.pi * G * M / (ℏ * c))) = c ^ 2 := by
  unfold hawkingTemperature
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ## §D — the Geroch process: GSL ⟹ Bekenstein bound, `G` cancels -/

/-- **The Geroch entropy gain is `G`-free** — Bousso Eqs. (2.18)–(2.19): lowering the
system to proper distance `R` from the horizon redshifts the added mass to
`δM ≤ E·R/(4GM)` (the leading near-horizon redshift `χ = R/(2b)` at `b = 2GM/c²`, in
mass units — hypothesis `hδ`).  The horizon entropy gain `(dS/dM)·δM` is then at most
`2πER/(ℏc)`: **`G` and `M` cancel** — the mechanism behind Bousso's remark on Eq. (2.9)
that "Newton's constant does not enter". -/
theorem geroch_entropy_gain_bound (M G ℏ c E R δM : ℝ)
    (hM : 0 < M) (hG : 0 < G) (hℏ : 0 < ℏ) (hc : 0 < c)
    (hδ : δM ≤ E * R / (4 * G * M)) :
    8 * Real.pi * G * M / (ℏ * c) * δM ≤ 2 * Real.pi * E * R / (ℏ * c) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  calc 8 * Real.pi * G * M / (ℏ * c) * δM
      ≤ 8 * Real.pi * G * M / (ℏ * c) * (E * R / (4 * G * M)) := by
        apply mul_le_mul_of_nonneg_left hδ
        positivity
    _ = 2 * Real.pi * E * R / (ℏ * c) := by
        field_simp
        ring

/-- **The Bekenstein bound from the GSL** — Bousso Eq. (2.20): if the GSL holds for the
Geroch process — the matter entropy lost is at most the horizon entropy gained
(`hGSL`) — then `S_matter ≤ 2πER/(ℏc)`: Eq. (2.9), with no `G` on the right-hand
side. -/
theorem geroch_process_bekenstein_bound (M G ℏ c E R δM S_matter : ℝ)
    (hM : 0 < M) (hG : 0 < G) (hℏ : 0 < ℏ) (hc : 0 < c)
    (hδ : δM ≤ E * R / (4 * G * M))
    (hGSL : S_matter ≤ 8 * Real.pi * G * M / (ℏ * c) * δM) :
    S_matter ≤ 2 * Real.pi * E * R / (ℏ * c) :=
  hGSL.trans (geroch_entropy_gain_bound M G ℏ c E R δM hM hG hℏ hc hδ)

end Physlib.Thermodynamics.HolographicEntropyBounds

end

/- Consolidated from Physlib/Thermodynamics/BoussoCovariantEntropyBound.lean -/

/-!
# The covariant entropy bound on a light-sheet

`HolographicScreenEntropy` carries the *dictionary* sector of Bousso's review — the exact
identities at the saturating configuration, `S = A c³/(4Gℏ)`.  Its docstring names what was
missing: the **inequality** content, the bound itself.  This module supplies it.

A **light-sheet** off a spatial cross-section is the null hypersurface generated by an
orthogonal null congruence along which the expansion is **non-positive**, `θ ≤ 0`
(*The holographic principle*, Rev. Mod. Phys. **74** (2002) 825, §V).  That sign condition is
the whole content of "covariant": of the four null directions off a surface, it selects the
ones along which the cross-section is not growing, and it is what makes the bound survive in
strong gravity where the spherical bound fails.

* `LightSheet` — the kinematical carrier: cross-section area `A(λ) > 0` transported by
  `A' = θA`, with `θ ≤ 0` on the sheet.  Deliberately **not** an extension of
  `FutureRegularNullRaychaudhuri`: that structure's global regularity *forces* `θ ≥ 0`
  (`expansion_nonneg`), so a light-sheet built on it would collapse to `θ ≡ 0`.  Light-sheets
  are the opposite sign class — they end at caustics, which is exactly what future-regularity
  excludes.
* `area_antitoneOn`, `area_le_initial` — focusing: the cross-section never grows.
* `bekensteinRate_nonpos` — the Bekenstein–Hawking entropy of the cross-section is
  non-increasing along the sheet.  On a light-sheet the area law runs *backwards*: the
  horizon-area theorem's monotonicity (`FutureRegularHorizonAreaEvolution.area_monotone`) is
  the `θ ≥ 0` face of the same transport equation.
* `bousso_covariant_bound` — **the bound**: `S[L] ≤ A(0)·c³/(4Gℏ)` in the `ℓ_P` form
  `bekensteinEntropy (A 0) ℓP`.
* `entropyFlux_eq_bekenstein_deficit` — the exact identity behind it: when the flux
  saturates, the entropy crossing the sheet is precisely the *deficit* of cross-section
  entropy, `S_BH(A(0)) − S_BH(A(λ_f))`.  The bound is therefore saturated exactly in the
  caustic limit `A(λ_f) → 0`, which is where the `HolographicScreenEntropy` dictionary's
  `S = A/4` lives: **the exact identity is the saturation case of this inequality**.

## The hypothesis, stated plainly

Bousso's bound is a conjecture about general spacetimes; it is not derivable from
Raychaudhuri focusing alone, because nothing in the geometry knows what entropy is.  What
*is* derivable — the Flanagan–Marolf–Wald route (Phys. Rev. D **62** (2000) 084035) — is the
global bound from a **local** hypothesis on the entropy flux.  Here that hypothesis is
`hflux`: the entropy flux density crossing the sheet is bounded by the rate at which the
cross-section's Bekenstein–Hawking entropy is being destroyed by focusing,

  `s(λ) ≤ −S_BH'(λ) = −k_B θ(λ) A(λ) / (4 ℓ_P²)`.

Given that, the bound is a one-line consequence of the fundamental theorem of calculus, and
that is what is proved below.  The physical content sits in the hypothesis; the theorem
records exactly what the hypothesis buys, and the `caveat` edges say so.  The flux bound
itself, and the conditions under which a matter model satisfies it, are not formalized here.

## Where this sits among the repository's other bounds

`HolographicEntropyBounds` already derives the §II bounds from the generalized second law
taken as an explicit hypothesis: the **spherical** bound by the Susskind process
(`susskind_process_spherical_bound`), the **Bekenstein** bound `S ≤ 2πER/(ℏc)` by the Geroch
process (`geroch_process_bekenstein_bound`, where `G` cancels), black-hole saturation, and
the first law.  The GSL itself is carried by `BekensteinJacobsonEntropicBits`
(`generalizedEntropy_monotone`) and, on other carriers, by
`ElectronExclusionEntropyProduction.electron_boundary_generalized_second_law` and
`ConfinementAreaLawEntropicWeight.confinement_obeys_gsl`.  This module supplies the §V
covariant bound, which `HolographicEntropyBounds` recorded as needing Raychaudhuri
machinery, and `covariantBound_ceiling_eq_sphericalBound` welds the two: **the two bounds
have the same ceiling, reached by different physics** — light-sheet focusing here, shell
collapse plus the GSL there.
-/

@[expose] public section

namespace Physlib.Thermodynamics

open MeasureTheory

/-- A **light-sheet** in Bousso's sense: a null congruence off a spatial cross-section,
carrying a positive cross-sectional area `A(λ)` transported by the expansion (`A' = θA`),
along which the expansion is **non-positive** on the sheet's affine range.

`expansion_nonpos` is the light-sheet condition — the selection rule that makes the entropy
bound covariant.  No Raychaudhuri equation is imposed: Bousso's definition is kinematical,
and the focusing dynamics is carried separately by `FutureRegularNullRaychaudhuri`. -/
structure LightSheet where
  /-- Affine length of the sheet. -/
  affineLength : ℝ
  /-- The sheet has positive affine extent. -/
  affineLength_pos : 0 < affineLength
  /-- Null expansion scalar `θ(λ)`. -/
  expansion : ℝ → ℝ
  /-- The expansion varies continuously. -/
  expansion_continuous : Continuous expansion
  /-- Cross-section area `A(λ)`. -/
  area : ℝ → ℝ
  /-- Cross-sections have positive area. -/
  area_pos : ∀ lam, 0 < area lam
  /-- Expansion transports area: `A' = θA`. -/
  area_hasDerivAt : ∀ lam, HasDerivAt area (expansion lam * area lam) lam
  /-- **The light-sheet condition**: the congruence is nowhere expanding on the sheet. -/
  expansion_nonpos : ∀ lam ∈ Set.Icc 0 affineLength, expansion lam ≤ 0

namespace LightSheet

variable (L : LightSheet)

/-! ### §A — kinematics -/

lemma area_differentiable : Differentiable ℝ L.area :=
  fun lam => (L.area_hasDerivAt lam).differentiableAt

lemma area_continuous : Continuous L.area :=
  L.area_differentiable.continuous

/-- **Focusing**: on a light-sheet the cross-section area is non-increasing — the direct
content of `A' = θA` with `θ ≤ 0`. -/
theorem area_antitoneOn : AntitoneOn L.area (Set.Icc 0 L.affineLength) := by
  intro a ha b hb hab
  have htransport : (∫ u in a..b, L.expansion u * L.area u) = L.area b - L.area a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => L.area_hasDerivAt x)
      ((L.expansion_continuous.mul L.area_continuous).intervalIntegrable _ _)
  have hnonpos : (∫ u in a..b, L.expansion u * L.area u) ≤ ∫ _u in a..b, (0 : ℝ) := by
    refine intervalIntegral.integral_mono_on hab
      ((L.expansion_continuous.mul L.area_continuous).intervalIntegrable _ _)
      intervalIntegrable_const ?_
    intro x hx
    have hxI : x ∈ Set.Icc 0 L.affineLength :=
      ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩
    have hθ := L.expansion_nonpos x hxI
    have hA := (L.area_pos x).le
    nlinarith
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at hnonpos
  rw [htransport] at hnonpos
  linarith

/-- No cross-section of the sheet exceeds the initial one. -/
theorem area_le_initial {lam : ℝ} (hlam : lam ∈ Set.Icc 0 L.affineLength) :
    L.area lam ≤ L.area 0 :=
  L.area_antitoneOn ⟨le_refl 0, L.affineLength_pos.le⟩ hlam hlam.1

/-! ### §B — the Bekenstein–Hawking entropy of the cross-sections -/

/-- The rate of change of the cross-section's Bekenstein–Hawking entropy along the sheet,
`S_BH' = k_B θ A/(4ℓ_P²)`. -/
noncomputable def bekensteinRate (ℓP lam : ℝ) : ℝ :=
  Constants.kB * (L.expansion lam * L.area lam) / (4 * ℓP ^ 2)

lemma bekensteinRate_continuous (ℓP : ℝ) : Continuous (L.bekensteinRate ℓP) := by
  unfold bekensteinRate
  exact (continuous_const.mul (L.expansion_continuous.mul L.area_continuous)).div_const _

/-- The cross-section entropy is differentiable along the sheet with derivative the rate. -/
lemma bekensteinEntropy_hasDerivAt (ℓP lam : ℝ) :
    HasDerivAt (fun u => bekensteinEntropy (L.area u) ℓP) (L.bekensteinRate ℓP lam) lam := by
  have h := ((L.area_hasDerivAt lam).const_mul Constants.kB).div_const (4 * ℓP ^ 2)
  simpa [bekensteinEntropy, bekensteinRate] using h

/-- **On a light-sheet the area law runs backwards**: cross-section entropy is
non-increasing.  The `θ ≥ 0` face of the same transport equation is the horizon-area
theorem (`FutureRegularHorizonAreaEvolution.area_monotone`). -/
lemma bekensteinRate_nonpos (ℓP : ℝ) (hℓP : ℓP ≠ 0) {lam : ℝ}
    (hlam : lam ∈ Set.Icc 0 L.affineLength) :
    L.bekensteinRate ℓP lam ≤ 0 := by
  have hsquare : 0 < ℓP ^ 2 := sq_pos_of_ne_zero hℓP
  have hcoef : 0 < Constants.kB / (4 * ℓP ^ 2) :=
    div_pos Constants.kB_pos (mul_pos (by norm_num) hsquare)
  have hθA : L.expansion lam * L.area lam ≤ 0 := by
    have hθ := L.expansion_nonpos lam hlam
    have hA := (L.area_pos lam).le
    nlinarith
  have hrw : L.bekensteinRate ℓP lam
      = (Constants.kB / (4 * ℓP ^ 2)) * (L.expansion lam * L.area lam) := by
    unfold bekensteinRate; ring
  rw [hrw]
  nlinarith

/-- The cross-section entropy is nonnegative (positive area, positive `k_B`). -/
lemma bekensteinEntropy_area_nonneg (ℓP : ℝ) (hℓP : ℓP ≠ 0) (lam : ℝ) :
    0 ≤ bekensteinEntropy (L.area lam) ℓP := by
  have hsquare : 0 < ℓP ^ 2 := sq_pos_of_ne_zero hℓP
  unfold bekensteinEntropy
  apply div_nonneg
  · exact mul_nonneg Constants.kB_pos.le (L.area_pos lam).le
  · positivity

/-! ### §C — the covariant bound -/

/-- **The covariant entropy bound** (Bousso, Rev. Mod. Phys. **74** (2002) 825, §V), on the
Flanagan–Marolf–Wald route: if the entropy flux density `s` crossing the light-sheet is
bounded at each point by the rate at which focusing destroys the cross-section's
Bekenstein–Hawking entropy (`hflux`), then the total entropy crossing the sheet is at most
the Bekenstein–Hawking entropy of the **initial** cross-section,

  `S[L] ≤ k_B A(0)/(4ℓ_P²)`.

The proof is the fundamental theorem of calculus applied to `hflux`: the pointwise bound
integrates to the area deficit, and the deficit is at most the initial entropy because the
terminal cross-section still has nonnegative entropy.  The physical content is the
hypothesis, not the calculus — see the module docstring. -/
theorem bousso_covariant_bound (ℓP : ℝ) (hℓP : ℓP ≠ 0) (s : ℝ → ℝ)
    (hs : IntervalIntegrable s volume 0 L.affineLength)
    (hflux : ∀ lam ∈ Set.Icc 0 L.affineLength, s lam ≤ -(L.bekensteinRate ℓP lam)) :
    (∫ lam in (0 : ℝ)..L.affineLength, s lam) ≤ bekensteinEntropy (L.area 0) ℓP := by
  have hrate : IntervalIntegrable (fun lam => -(L.bekensteinRate ℓP lam)) volume 0 L.affineLength :=
    ((L.bekensteinRate_continuous ℓP).neg).intervalIntegrable _ _
  have hmono : (∫ lam in (0 : ℝ)..L.affineLength, s lam)
      ≤ ∫ lam in (0 : ℝ)..L.affineLength, -(L.bekensteinRate ℓP lam) :=
    intervalIntegral.integral_mono_on L.affineLength_pos.le hs hrate hflux
  have hftc : (∫ lam in (0 : ℝ)..L.affineLength, L.bekensteinRate ℓP lam)
      = bekensteinEntropy (L.area L.affineLength) ℓP - bekensteinEntropy (L.area 0) ℓP :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => L.bekensteinEntropy_hasDerivAt ℓP x)
      ((L.bekensteinRate_continuous ℓP).intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg, hftc] at hmono
  have hterm := L.bekensteinEntropy_area_nonneg ℓP hℓP L.affineLength
  linarith

/-- **The exact identity behind the bound**: when the flux saturates the local hypothesis,
the entropy crossing the sheet is precisely the *deficit* of cross-section entropy between
the initial and final cross-sections.  The bound `S ≤ S_BH(A(0))` is therefore saturated
exactly in the caustic limit `A(λ_f) → 0` — which is the configuration where the
`HolographicScreenEntropy` dictionary's exact `S = A c³/(4Gℏ)` lives.  The identity and the
inequality are one statement read at two configurations. -/
theorem entropyFlux_eq_bekenstein_deficit (ℓP : ℝ) (s : ℝ → ℝ)
    (hsat : Set.EqOn s (fun lam => -(L.bekensteinRate ℓP lam)) (Set.uIcc 0 L.affineLength)) :
    (∫ lam in (0 : ℝ)..L.affineLength, s lam)
      = bekensteinEntropy (L.area 0) ℓP - bekensteinEntropy (L.area L.affineLength) ℓP := by
  rw [intervalIntegral.integral_congr hsat, intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => L.bekensteinEntropy_hasDerivAt ℓP x)
      ((L.bekensteinRate_continuous ℓP).intervalIntegrable _ _)]
  ring

/-! ### §D — the carrier is inhabited: a concrete light-sheet -/

/-- **A uniformly focusing light-sheet**: `θ ≡ −1`, `A(λ) = e^{−λ}`.  The transport equation
`A' = θA` holds exactly, the area stays positive, and the expansion is everywhere negative —
so the light-sheet condition is satisfiable and the bound above is not vacuous. -/
noncomputable def uniformlyFocusing : LightSheet where
  affineLength := 1
  affineLength_pos := one_pos
  expansion := fun _ => -1
  expansion_continuous := continuous_const
  area := fun lam => Real.exp (-lam)
  area_pos := fun lam => Real.exp_pos _
  area_hasDerivAt := by
    intro lam
    have h := ((hasDerivAt_id lam).neg).exp
    simpa [mul_comm] using h
  expansion_nonpos := fun _ _ => by norm_num

/-- **The bound is attained with room to spare on the witness.**  Saturating the local flux
hypothesis on the uniformly focusing sheet sends `k_B(1 − e^{−1})/(4ℓ_P²)` across it — the
initial cross-section entropy `k_B/(4ℓ_P²)` minus exactly the entropy of the cross-section
that survives at the end of the sheet.  Pushing the sheet to a caustic (`A → 0`) is what
closes the gap, which is the `HolographicScreenEntropy` saturating configuration. -/
theorem uniformlyFocusing_saturating_flux (ℓP : ℝ) :
    (∫ lam in (0 : ℝ)..uniformlyFocusing.affineLength,
        -(uniformlyFocusing.bekensteinRate ℓP lam))
      = Constants.kB * (1 - Real.exp (-1)) / (4 * ℓP ^ 2) := by
  rw [uniformlyFocusing.entropyFlux_eq_bekenstein_deficit ℓP _ (fun x _ => rfl)]
  show Constants.kB * Real.exp (-(0 : ℝ)) / (4 * ℓP ^ 2)
      - Constants.kB * Real.exp (-(1 : ℝ)) / (4 * ℓP ^ 2) = _
  rw [neg_zero, Real.exp_zero]
  ring

end LightSheet

/-! ### §E — the weld: the covariant ceiling is the spherical ceiling -/

/-- **The covariant bound and the spherical bound have the same ceiling.**  Under the Planck
length identification `ℓ_P² = Gℏ/c³`, the ceiling of `bousso_covariant_bound` is exactly the
right-hand side of `HolographicEntropyBounds.susskind_process_spherical_bound`, in `k_B`
units.  The two bounds are one bound reached by different physics: focusing along a
light-sheet here, shell collapse plus the generalized second law there.

**Under the holographic Newton constant** (`[G] = L³M⁻¹T⁻²I⁻¹`, `G` as area per bit) this
identity is where the information charge becomes visible.  Typing `ℓ_P` as a plain length
makes it break by exactly one nat — the same defect the bit-form bridges carry.  But the
hypothesis `hℓP` forbids that reading: `Gℏ/c³` then carries `I⁻¹`, so `ℓ_P` carries
`I^{-1/2}` and the identity is homogeneous again.  The one-nat fault line is anchored at the
Planck *area*: `ℓ_P²` is area-per-nat, which is the holographic principle `N = A/ℓ_P²`
itself.  Both readings are build-enforced in `Meta.EntropicWepDepthGate` §20. -/
theorem covariantBound_ceiling_eq_sphericalBound (A G ℏ c ℓP : ℝ)
    (hℓP : ℓP ^ 2 = G * ℏ / c ^ 3) (hG : G ≠ 0) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) :
    bekensteinEntropy A ℓP = Constants.kB * (A * c ^ 3 / (4 * (G * ℏ))) := by
  unfold bekensteinEntropy
  rw [hℓP]
  field_simp

/-- **The covariant bound in the spherical bound's units**: composing
`bousso_covariant_bound` with the ceiling identity states the light-sheet bound with the
same right-hand side the Susskind process produces. -/
theorem bousso_covariant_bound_spherical_form (L : LightSheet) (G ℏ c ℓP : ℝ)
    (hℓP : ℓP ^ 2 = G * ℏ / c ^ 3) (hG : G ≠ 0) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hℓPne : ℓP ≠ 0)
    (s : ℝ → ℝ) (hs : IntervalIntegrable s volume 0 L.affineLength)
    (hflux : ∀ lam ∈ Set.Icc 0 L.affineLength, s lam ≤ -(L.bekensteinRate ℓP lam)) :
    (∫ lam in (0 : ℝ)..L.affineLength, s lam)
      ≤ Constants.kB * (L.area 0 * c ^ 3 / (4 * (G * ℏ))) := by
  have h := L.bousso_covariant_bound ℓP hℓPne s hs hflux
  rwa [covariantBound_ceiling_eq_sphericalBound (L.area 0) G ℏ c ℓP hℓP hG hℏ hc] at h

/- ZIL-BEGIN -/

zil attach Physlib.Thermodynamics.LightSheet.area_antitoneOn where
  formalizes @ "claim:on-a-light-sheet-the-cross-section-area-is-nonincreasing-because-the-transport-equation-carries-a-nonpositive-expansion",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:bousso-2002-the-holographic-principle-rev-mod-phys-74-825"

zil attach Physlib.Thermodynamics.LightSheet.bekensteinRate_nonpos where
  caveat @ "claim:rests-on-future-regular-focusing-and-area-monotonicity-inputs-labeled-conditional-model",
  discloses @ "lean:Physlib.Thermodynamics.FutureRegularHorizonAreaEvolution.area_monotone",
  discloses @ "lean:Physlib.Thermodynamics.FutureRegularNullRaychaudhuri.expansion_nonneg",
  discloses @ "lean:Physlib.Thermodynamics.FutureRegularNullRaychaudhuri.focusing_contradiction",
  formalizes @ "claim:on-a-light-sheet-the-bekenstein-hawking-entropy-of-the-cross-section-is-nonincreasing-the-horizon-area-theorem-read-at-the-opposite-expansion-sign",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.FutureRegularHorizonAreaEvolution.area_monotone"

zil attach Physlib.Thermodynamics.LightSheet.bousso_covariant_bound where
  formalizes @ "claim:the-covariant-entropy-bound-the-entropy-crossing-a-light-sheet-is-at-most-the-bekenstein-hawking-entropy-of-its-initial-cross-section",
  derives @ "claim:boussos-covariant-entropy-bound-follows-from-a-local-flanagan-marolf-wald-flux-hypothesis-by-the-fundamental-theorem-of-calculus",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "paper:bousso-2002-the-holographic-principle-rev-mod-phys-74-825",
  supported_by @ "paper:flanagan-marolf-wald-2000-proof-of-classical-versions-of-the-bousso-entropy-bound-phys-rev-d-62-084035",
  supported_by @ "lean:Physlib.Thermodynamics.LightSheet.entropyFlux_eq_bekenstein_deficit",
  requires @ "assumption:the-entropy-flux-density-crossing-the-light-sheet-is-bounded-by-the-rate-at-which-focusing-destroys-cross-section-bekenstein-hawking-entropy",
  caveat @ "claim:the-physical-content-is-the-local-flux-hypothesis-the-theorem-supplies-only-the-integration-and-no-matter-model-is-shown-to-satisfy-the-hypothesis",
  caveat @ "claim:boussos-bound-in-full-generality-is-a-conjecture-about-arbitrary-spacetimes-and-is-not-established-here",
  supported_by @ "lean:Physlib.Thermodynamics.HolographicEntropyBounds.susskind_process_spherical_bound",
  supported_by @ "lean:Physlib.Thermodynamics.HolographicEntropyBounds.geroch_process_bekenstein_bound",
  supported_by @ "lean:Physlib.Thermodynamics.FutureRegularHorizonAreaEvolution.generalizedEntropy_monotone"

zil attach Physlib.Thermodynamics.LightSheet.entropyFlux_eq_bekenstein_deficit where
  caveat @ "claim:rests-on-future-regular-focusing-and-area-monotonicity-inputs-labeled-conditional-model",
  discloses @ "lean:Physlib.Thermodynamics.FutureRegularHorizonAreaEvolution.generalizedEntropy_monotone",
  discloses @ "lean:Physlib.Thermodynamics.LightSheet.bousso_covariant_bound",
  formalizes @ "claim:with-saturating-flux-the-entropy-crossing-a-light-sheet-equals-the-deficit-of-cross-section-bekenstein-hawking-entropy-so-the-bound-saturates-exactly-in-the-caustic-limit",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.HolographicScreenEntropy.screenEntropy_bekensteinHawking"

zil attach Physlib.Thermodynamics.LightSheet.uniformlyFocusing_saturating_flux where
  caveat @ "claim:the-saturating-flux-reading-rests-on-the-bousso-covariant-bound-whose-local-flux-hypothesis-is-ansatz-loaded",
  discloses @ "lean:Physlib.Thermodynamics.LightSheet.bousso_covariant_bound",
  supported_by @ "lean:Physlib.Thermodynamics.LightSheet.entropyFlux_eq_bekenstein_deficit",
  formalizes @ "claim:a-uniformly-focusing-light-sheet-with-saturating-flux-carries-kb-one-minus-one-over-e-over-four-planck-areas-strictly-below-its-initial-cross-section-entropy",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:an-explicit-inhabitant-of-the-light-sheet-carrier-showing-the-bound-is-not-vacuous-not-a-physical-spacetime-construction"

/- ZIL-END -/

end Physlib.Thermodynamics

end

