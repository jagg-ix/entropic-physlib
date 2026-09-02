/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.ComptonClockSorkinJohnstonState
public import Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum
meta import Zil

/-!
# The Compton clock on Malament proper time: zitterbewegung, entanglement, horizon, causal state

The Compton–de Broglie clock reading Malament's proper time
(`ComptonClockMalamentProperTime`) links to the wider clock arc.

* **Zitterbewegung.**  The Dirac zitterbewegung frequency is twice Compton
  (`zitterbewegung_rest_eq_two_compton`), so its phase over a proper-time interval is twice
  the de Broglie phase (`zitterbewegungPhase_eq_two_comptonPhase`); its phase ratios are the
  same exact causal invariants (`zitterbewegungPhase_ratio_causalAutomorphism`).

* **Entanglement reparametrization.**  A Schmidt/two-mode state of rapidity `η` and a
  kinematic momentum boost `θ` multiply the clock by `cosh θ·cosh η`
  (`EntanglementReparametrization.doubly_boosted_compton_clock`), keeping the identical form
  `ω = E/ℏ`.  Over proper time this gives `entangledComptonPhase = cosh θ·cosh η · φ`
  (`entangledComptonPhase_eq`), whose ratios remain exact causal invariants
  (`entangledComptonPhase_ratio_causalAutomorphism`) — the entanglement/kinematic boosts, like
  the Malament dilation, cancel in a ratio.

* **Verlinde horizon (no explicit `G`).**  At the three-origin mass the clock rate is the
  Verlinde horizon-entropy rate `ω₀ = c³Ȧ/(4Għ)` — Newton's constant appearing only through
  the horizon area rate `Ȧ` — with the Compton mass simultaneously the Yukawa, horizon, and
  Witten Chern–Simons topological mass
  (`EntropicClockComptonAnchor.comptonAnchored_entropicTime_threeOriginMass`).

* **Sorkin–Johnston causal state.**  The clock's two-point kernel `e^{-iω(t-t')}` is a
  Sorkin–Johnston vacuum (`ComptonClockSorkinJohnstonState.clockKernel_isSJState`), so the
  proper-time evolution is a causal QFT state; and its reversible (real-`ω`) generator sits on
  the unitary edge of the three-clock reversibility spectrum
  (`ThreeClockReversibilitySpectrum.reversible_generator_flow_unitary`), separated from the
  entropic (contracting) clocks.

* **Operational uniqueness.**  For nonzero mass, light speed, and Planck constant the Compton
  phase is injective in proper time (`comptonPhase_injective`).  Consequently one preserved
  nonzero timelike clock reading fixes Malament's residual conformal factor to exactly one and
  makes every proper-time interval invariant (`comptonCalibration_fixes_malamentScale`).  At
  fixed kinematic boost and nonzero clock interval, the nonnegative Schmidt rapidity is likewise
  uniquely recovered from the entanglement-reparametrized phase
  (`entanglementRapidity_unique_of_phase`) and explicitly reconstructed by `arcosh`
  (`entanglementRapidity_eq_arcosh_phaseRatio`).  The calibrated causal map is consequently
  a genuine Poincaré transformation with no dilation (`comptonCalibration_is_poincare`), and
  one nonzero phase interval also determines the Compton mass uniquely
  (`comptonMass_unique_of_phase`).  Conversely the calibrated proper time is reconstructed by
  an explicit inverse phase formula (`properTime_reconstruct_from_comptonPhase`), and global
  phase preservation is equivalent to global proper-time preservation
  (`globalComptonCalibration_iff_properTimeInvariant`).  Globally calibrated maps contain the
  identity and are closed under composition and inverse
  (`isGloballyComptonCalibrated_refl`, `IsGloballyComptonCalibrated.trans`,
  `IsGloballyComptonCalibrated.symm`); among affine causal automorphisms they are exactly the
  Poincaré transformations (`isGloballyComptonCalibrated_iff_poincare`).

* **Causal-QFT/gravity closure.**  The conditional holographic coupling `G = ħc/m²` is
  reconstructed directly from a nonzero Compton phase (`derivedNewtonG_eq_from_comptonPhase`).
  Once a causal automorphism is clock-calibrated, it preserves the Sorkin–Johnston Compton
  kernel on every interval (`comptonClockKernel_invariant_of_calibration`), the full two-interval
  kernel (`comptonClockKernel_pair_invariant_of_calibration`), and its Hadamard/Pauli–Jordan
  decomposition (`comptonClockSJ_parts_invariant_of_calibration`).  The final capstone
  assembles the Poincaré reduction, clock-frequency form of the coupling, causal state, and
  reversible unitary flow (`calibratedComptonClock_poincare_sj_unitary_holographic`).  The
  coupling formula is an exact inversion/identifiability result, not an independently calibrated
  numerical prediction.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.ComptonClockSorkinJohnstonState
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition
open Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum
open Lorentz Lorentz.Vector SpaceTime

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTimeLinks

/-! ## Zitterbewegung phase on proper time -/

/-- **The zitterbewegung phase** over a proper-time interval: `φ_Z = ω_Z·τ`. -/
def zitterbewegungPhase (m c ħ τ : ℝ) : ℝ := zitterbewegungFrequency 0 m c ħ * τ

/-- **Zitterbewegung phase is twice the Compton phase** (`ω_Z = 2ω_C`). -/
@[zil_level physical_theorem]
theorem zitterbewegungPhase_eq_two_comptonPhase (m c ħ τ : ℝ) (hm : 0 ≤ m) :
    zitterbewegungPhase m c ħ τ = 2 * comptonPhase m c ħ τ := by
  unfold zitterbewegungPhase comptonPhase
  rw [zitterbewegung_rest_eq_two_compton m c ħ hm]; ring

/-- **Zitterbewegung phase ratios are exact causal invariants.** -/
@[zil_level bridge_theorem]
theorem zitterbewegungPhase_ratio_causalAutomorphism (e : Vector 3 ≃ᵃ[ℝ] Vector 3)
    (hcausal : IsCausalAutomorphism e) (m c ħ : ℝ) (hm : 0 ≤ m) (q p q' p' : SpaceTime 3) :
    zitterbewegungPhase m c ħ (properTime (e q) (e p)) * properTime q' p'
      = zitterbewegungPhase m c ħ (properTime q p) * properTime (e q') (e p') := by
  rw [zitterbewegungPhase_eq_two_comptonPhase m c ħ (properTime (e q) (e p)) hm,
    zitterbewegungPhase_eq_two_comptonPhase m c ħ (properTime q p) hm]
  linear_combination 2 * comptonPhase_ratio_causalAutomorphism e hcausal m c ħ q p q' p'

/-! ## Entanglement-reparametrized (doubly-boosted) Compton phase on proper time -/

/-- **The entanglement-reparametrized Compton phase** over a proper-time interval: the de
Broglie phase at the doubly-boosted energy `cosh η · E(mc·sinh θ)`, carrying a Schmidt
entanglement boost `cosh η` and a kinematic momentum boost `cosh θ`. -/
def entangledComptonPhase (m c ħ θ η τ : ℝ) : ℝ :=
  deBroglieFrequency (Real.cosh η * einsteinEnergy m c (m * c * Real.sinh θ)) ħ * τ

/-- **The entanglement/kinematic boost multiplies the Compton phase by `cosh θ·cosh η`.** -/
@[zil_level bridge_theorem]
theorem entangledComptonPhase_eq (m c ħ θ η τ : ℝ) (hm : 0 ≤ m) :
    entangledComptonPhase m c ħ θ η τ = (Real.cosh θ * Real.cosh η) * comptonPhase m c ħ τ := by
  unfold entangledComptonPhase comptonPhase
  rw [doubly_boosted_compton_clock m c ħ θ η hm]; ring

/-- **Entanglement-reparametrized phase ratios are exact causal invariants** — the
entanglement boost `cosh η` and kinematic boost `cosh θ`, like the Malament dilation, cancel
in a ratio. -/
@[zil_level bridge_theorem]
theorem entangledComptonPhase_ratio_causalAutomorphism (e : Vector 3 ≃ᵃ[ℝ] Vector 3)
    (hcausal : IsCausalAutomorphism e) (m c ħ θ η : ℝ) (hm : 0 ≤ m) (q p q' p' : SpaceTime 3) :
    entangledComptonPhase m c ħ θ η (properTime (e q) (e p)) * properTime q' p'
      = entangledComptonPhase m c ħ θ η (properTime q p) * properTime (e q') (e p') := by
  rw [entangledComptonPhase_eq m c ħ θ η (properTime (e q) (e p)) hm,
    entangledComptonPhase_eq m c ħ θ η (properTime q p) hm]
  linear_combination (Real.cosh θ * Real.cosh η) *
    comptonPhase_ratio_causalAutomorphism e hcausal m c ħ q p q' p'

/-! ## Operational uniqueness and removal of the conformal clock scale -/

/-- **A physical Compton phase is an injective proper-time reading.**  Once `m`, `c`, and
`ħ` are nonzero, the clock frequency `mc²/ħ` is nonzero; hence two intervals carrying the
same accumulated phase are the same proper-time interval. -/
@[zil_level bridge_theorem]
theorem comptonPhase_injective (m c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    Function.Injective (comptonPhase m c ħ) := by
  intro τ₁ τ₂ hphase
  unfold comptonPhase at hphase
  apply mul_left_cancel₀ (show comptonFrequency m c ħ ≠ 0 by
    unfold comptonFrequency
    exact div_ne_zero (mul_ne_zero hm (pow_ne_zero 2 hc)) hħ)
  exact hphase

/-- **One nonzero Compton-clock calibration fixes Malament's conformal scale uniquely.**
If an affine causal automorphism preserves the Compton phase on one timelike interval, phase
injectivity fixes that interval's proper time.  The causal-order ratio theorem then fixes every
proper-time interval, and the positive Malament dilation supplied by
`properTime_causalAutomorphism` is exactly `1`. -/
@[zil_level bridge_theorem]
theorem comptonCalibration_fixes_malamentScale
    (e : Vector 3 ≃ᵃ[ℝ] Vector 3) (hcausal : IsCausalAutomorphism e)
    (m c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (q p : SpaceTime 3) (htime : causalCharacter (p - q) = .timeLike)
    (hphase : comptonPhase m c ħ (properTime (e q) (e p)) =
      comptonPhase m c ħ (properTime q p)) :
    ∃ a : ℝ, 0 < a ∧ a = 1 ∧ ∀ q' p' : SpaceTime 3,
      properTime (e q') (e p') = properTime q' p' := by
  have hcal : properTime (e q) (e p) = properTime q p :=
    comptonPhase_injective m c ħ hm hc hħ hphase
  have hτ : properTime q p ≠ 0 := ne_of_gt (properTime_pos_ofTimeLike q p htime)
  have hglobal : ∀ q' p' : SpaceTime 3,
      properTime (e q') (e p') = properTime q' p' := by
    intro q' p'
    have hratio := properTime_ratio_causalAutomorphism e hcausal q p q' p'
    rw [hcal] at hratio
    exact (mul_left_cancel₀ hτ hratio).symm
  obtain ⟨a, ha, hscale⟩ := properTime_causalAutomorphism e hcausal
  have hsqrt : Real.sqrt a = 1 := by
    apply mul_right_cancel₀ hτ
    rw [← hscale q p, hglobal q p, one_mul]
  exact ⟨a, ha, Real.sqrt_eq_one.mp hsqrt, hglobal⟩

/-- **The nonnegative entanglement rapidity is uniquely read by the boosted clock.**
At fixed kinematic rapidity `θ`, a nondegenerate clock interval cannot have the same
entanglement-reparametrized phase at two different nonnegative Schmidt rapidities: after
cancelling the positive `cosh θ` and nonzero Compton phase, injectivity of `cosh` on
`[0,∞)` gives `η₁ = η₂`. -/
@[zil_level bridge_theorem]
theorem entanglementRapidity_unique_of_phase
    (m c ħ θ η₁ η₂ τ : ℝ) (hm0 : 0 ≤ m) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hτ : τ ≠ 0) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (hphase : entangledComptonPhase m c ħ θ η₁ τ =
      entangledComptonPhase m c ħ θ η₂ τ) :
    η₁ = η₂ := by
  rw [entangledComptonPhase_eq m c ħ θ η₁ τ hm0,
    entangledComptonPhase_eq m c ħ θ η₂ τ hm0] at hphase
  have hclock : comptonPhase m c ħ τ ≠ 0 := by
    unfold comptonPhase comptonFrequency
    exact mul_ne_zero (div_ne_zero (mul_ne_zero hm (pow_ne_zero 2 hc)) hħ) hτ
  have hθ : Real.cosh θ ≠ 0 := ne_of_gt (Real.cosh_pos θ)
  have hcosh : Real.cosh η₁ = Real.cosh η₂ := by
    apply mul_left_cancel₀ hθ
    apply mul_right_cancel₀ hclock
    exact hphase
  exact Real.cosh_injOn hη₁ hη₂ hcosh

/-- **A calibrated affine causal automorphism is a Poincaré transformation.**  The shared
Malament decomposition/proper-time witness lets one preserved nonzero timelike Compton phase
cancel the dilation exactly.  What remains is a Lorentz map followed by translation. -/
@[zil_level bridge_theorem]
theorem comptonCalibration_is_poincare
    (e : Vector 3 ≃ᵃ[ℝ] Vector 3) (hcausal : IsCausalAutomorphism e)
    (m c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (q p : SpaceTime 3) (htime : causalCharacter (p - q) = .timeLike)
    (hphase : comptonPhase m c ħ (properTime (e q) (e p)) =
      comptonPhase m c ħ (properTime q p)) :
    ∃ g : Vector 3 →ₗ[ℝ] Vector 3, IsLorentz g ∧ ∀ x, e x = g x + e 0 := by
  obtain ⟨a, _, g, hg, he, hscale⟩ :=
    causalAutomorphism_decomposition_with_properTime e hcausal
  have hproper : properTime (e q) (e p) = properTime q p :=
    comptonPhase_injective m c ħ hm hc hħ hphase
  have hτ : properTime q p ≠ 0 := ne_of_gt (properTime_pos_ofTimeLike q p htime)
  have hsqrt : Real.sqrt a = 1 := by
    apply mul_right_cancel₀ hτ
    rw [← hscale q p, hproper, one_mul]
  exact ⟨g, hg, fun x => by rw [he x, hsqrt, one_smul]⟩

/-- **Constructive reconstruction of the nonnegative Schmidt rapidity.**  Dividing the
entanglement-reparametrized phase by the fixed kinematic factor and the nonzero Compton phase
leaves `cosh η`; applying `arcosh` recovers `η` exactly on the physical nonnegative branch. -/
@[zil_level bridge_theorem]
theorem entanglementRapidity_eq_arcosh_phaseRatio
    (m c ħ θ η τ : ℝ) (hm0 : 0 ≤ m) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hτ : τ ≠ 0) (hη : 0 ≤ η) :
    Real.arcosh
        (entangledComptonPhase m c ħ θ η τ /
          (Real.cosh θ * comptonPhase m c ħ τ)) = η := by
  rw [entangledComptonPhase_eq m c ħ θ η τ hm0]
  have hclock : comptonPhase m c ħ τ ≠ 0 := by
    unfold comptonPhase comptonFrequency
    exact mul_ne_zero (div_ne_zero (mul_ne_zero hm (pow_ne_zero 2 hc)) hħ) hτ
  have hden : Real.cosh θ * comptonPhase m c ħ τ ≠ 0 :=
    mul_ne_zero (ne_of_gt (Real.cosh_pos θ)) hclock
  have hratio :
      (Real.cosh θ * Real.cosh η) * comptonPhase m c ħ τ /
          (Real.cosh θ * comptonPhase m c ħ τ) = Real.cosh η := by
    apply (div_eq_iff hden).2
    ring
  rw [hratio, Real.arcosh_cosh hη]

/-- **One nonzero Compton phase interval determines the mass uniquely.**  For fixed nonzero
`c`, `ħ`, and proper-time interval, equality of the internal phases forces equality of the
two mass parameters. -/
@[zil_level bridge_theorem]
theorem comptonMass_unique_of_phase
    (m₁ m₂ c ħ τ : ℝ) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hτ : τ ≠ 0)
    (hphase : comptonPhase m₁ c ħ τ = comptonPhase m₂ c ħ τ) :
    m₁ = m₂ := by
  have hphase' := hphase
  unfold comptonPhase comptonFrequency at hphase'
  have hdiv : m₁ * c ^ 2 / ħ = m₂ * c ^ 2 / ħ := by
    apply mul_right_cancel₀ hτ
    exact hphase'
  have hmul : m₁ * c ^ 2 = m₂ * c ^ 2 := by
    apply (div_left_inj' hħ).mp
    exact hdiv
  exact mul_right_cancel₀ (pow_ne_zero 2 hc) hmul

/-- **Proper time is constructively reconstructed from the Compton phase.**  For nonzero
physical clock parameters, multiplying `φ = (mc²/ħ)τ` by `ħ/(mc²)` returns the original
interval exactly.  This is the explicit left inverse complementing `comptonPhase_injective`. -/
@[zil_level bridge_theorem]
theorem properTime_reconstruct_from_comptonPhase
    (m c ħ τ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    ħ * comptonPhase m c ħ τ / (m * c ^ 2) = τ := by
  unfold comptonPhase comptonFrequency
  field_simp [hm, hc, hħ]

/-- **Global Compton calibration.**  An affine map is calibrated when it preserves the
accumulated Compton reading on every pair of events.  With nonzero physical parameters this
will be equivalent to preserving proper time itself. -/
def IsGloballyComptonCalibrated (e : Vector 3 ≃ᵃ[ℝ] Vector 3) (m c ħ : ℝ) : Prop :=
  ∀ q p : SpaceTime 3,
    comptonPhase m c ħ (properTime (e q) (e p)) = comptonPhase m c ħ (properTime q p)

/-- **Global Compton calibration is exactly global proper-time invariance.**  Nonzero clock
parameters make the phase map injective, so phase preservation and proper-time preservation
are equivalent pointwise for every pair of events. -/
@[zil_level bridge_theorem]
theorem globalComptonCalibration_iff_properTimeInvariant
    (e : Vector 3 ≃ᵃ[ℝ] Vector 3) (m c ħ : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    IsGloballyComptonCalibrated e m c ħ ↔
    (∀ q p : SpaceTime 3, properTime (e q) (e p) = properTime q p) := by
  constructor
  · intro hphase q p
    exact comptonPhase_injective m c ħ hm hc hħ (hphase q p)
  · intro hproper q p
    rw [hproper q p]

/-- **The identity affine map is globally Compton-calibrated.** -/
@[zil_level bridge_theorem]
theorem isGloballyComptonCalibrated_refl (m c ħ : ℝ) :
    IsGloballyComptonCalibrated (AffineEquiv.refl ℝ (Vector 3)) m c ħ := by
  intro q p
  rfl

/-- **Global Compton calibrations compose.**  This is the exact clock-level counterpart of
composition in the Poincaré group. -/
@[zil_level bridge_theorem]
theorem IsGloballyComptonCalibrated.trans
    {e f : Vector 3 ≃ᵃ[ℝ] Vector 3} {m c ħ : ℝ}
    (he : IsGloballyComptonCalibrated e m c ħ)
    (hf : IsGloballyComptonCalibrated f m c ħ) :
    IsGloballyComptonCalibrated (e.trans f) m c ħ := by
  intro q p
  change comptonPhase m c ħ (properTime (f (e q)) (f (e p))) =
    comptonPhase m c ħ (properTime q p)
  rw [hf (e q) (e p), he q p]

/-- **The inverse of a global Compton calibration is calibrated.** -/
@[zil_level bridge_theorem]
theorem IsGloballyComptonCalibrated.symm
    {e : Vector 3 ≃ᵃ[ℝ] Vector 3} {m c ħ : ℝ}
    (he : IsGloballyComptonCalibrated e m c ħ) :
    IsGloballyComptonCalibrated e.symm m c ħ := by
  intro q p
  have h := he (e.symm q) (e.symm p)
  simpa using h.symm

/-- **For affine causal automorphisms, global Compton calibration is exactly Poincaré
kinematics.**  Calibration removes the unique Malament dilation.  Conversely a Lorentz map
followed by translation preserves the Minkowski interval, hence proper time and its clock
phase. -/
@[zil_level bridge_theorem]
theorem isGloballyComptonCalibrated_iff_poincare
    (e : Vector 3 ≃ᵃ[ℝ] Vector 3) (hcausal : IsCausalAutomorphism e)
    (m c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    IsGloballyComptonCalibrated e m c ħ ↔
      ∃ g : Vector 3 →ₗ[ℝ] Vector 3, IsLorentz g ∧ ∀ x, e x = g x + e 0 := by
  constructor
  · intro hcal
    apply comptonCalibration_is_poincare e hcausal m c ħ hm hc hħ 0 temporalBasis3
    · rw [timeLike_iff_norm_sq_pos]
      simp [temporalBasis3]
    · exact hcal 0 temporalBasis3
  · rintro ⟨g, hg, he⟩ q p
    apply congrArg (comptonPhase m c ħ)
    unfold properTime
    have hsub : e p - e q = g (p - q) := by
      rw [he p, he q, map_sub]
      abel
    rw [hsub, hg]

/-- **The conditional holographic coupling is reconstructible directly from one nonzero
Compton phase interval.**  Substituting `φ = (mc²/ħ)·τ` into `ħc/m²` gives the displayed
phase-only expression.  This is an exact inversion identity, not a numerical prediction of
Newton's constant. -/
@[zil_level bridge_theorem]
theorem derivedNewtonG_eq_from_comptonPhase
    (m c ħ τ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hτ : τ ≠ 0) :
    ħ * c / m ^ 2 =
      c ^ 5 * τ ^ 2 / (ħ * comptonPhase m c ħ τ ^ 2) := by
  unfold comptonPhase comptonFrequency
  field_simp [hm, hc, hħ, hτ]

/-- **Clock calibration makes the Compton Sorkin–Johnston kernel invariant on every
interval.**  Preserving one nonzero timelike Compton reading eliminates Malament's scale;
the resulting global proper-time equality then transports the two-point kernel. -/
@[zil_level bridge_theorem]
theorem comptonClockKernel_invariant_of_calibration
    (e : Vector 3 ≃ᵃ[ℝ] Vector 3) (hcausal : IsCausalAutomorphism e)
    (m c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (q p : SpaceTime 3) (htime : causalCharacter (p - q) = .timeLike)
    (hphase : comptonPhase m c ħ (properTime (e q) (e p)) =
      comptonPhase m c ħ (properTime q p))
    (q' p' : SpaceTime 3) :
    clockKernel (comptonFrequency m c ħ) (properTime (e q') (e p')) 0 =
      clockKernel (comptonFrequency m c ħ) (properTime q' p') 0 := by
  obtain ⟨_, _, _, hglobal⟩ :=
    comptonCalibration_fixes_malamentScale e hcausal m c ħ hm hc hħ q p htime hphase
  rw [hglobal q' p']

/-- **A single clock calibration preserves the full two-interval SJ kernel.**  Both arguments
of `W(t,t') = exp(-iω(t-t'))` may be independently reconstructed proper-time intervals; the
one-reading uniqueness theorem transports each and therefore the complete two-point value. -/
@[zil_level bridge_theorem]
theorem comptonClockKernel_pair_invariant_of_calibration
    (e : Vector 3 ≃ᵃ[ℝ] Vector 3) (hcausal : IsCausalAutomorphism e)
    (m c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (q p : SpaceTime 3) (htime : causalCharacter (p - q) = .timeLike)
    (hphase : comptonPhase m c ħ (properTime (e q) (e p)) =
      comptonPhase m c ħ (properTime q p))
    (q₁ p₁ q₂ p₂ : SpaceTime 3) :
    clockKernel (comptonFrequency m c ħ)
        (properTime (e q₁) (e p₁)) (properTime (e q₂) (e p₂)) =
      clockKernel (comptonFrequency m c ħ)
        (properTime q₁ p₁) (properTime q₂ p₂) := by
  obtain ⟨_, _, _, hglobal⟩ :=
    comptonCalibration_fixes_malamentScale e hcausal m c ħ hm hc hħ q p htime hphase
  rw [hglobal q₁ p₁, hglobal q₂ p₂]

/-- **The calibrated clock preserves both parts of the SJ decomposition.**  Full kernel
invariance descends functorially to its real Hadamard part and doubled-imaginary Pauli–Jordan
part, so neither the symmetric correlation nor the commutator sector depends on the calibrated
causal representative. -/
@[zil_level bridge_theorem]
theorem comptonClockSJ_parts_invariant_of_calibration
    (e : Vector 3 ≃ᵃ[ℝ] Vector 3) (hcausal : IsCausalAutomorphism e)
    (m c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (q p : SpaceTime 3) (htime : causalCharacter (p - q) = .timeLike)
    (hphase : comptonPhase m c ħ (properTime (e q) (e p)) =
      comptonPhase m c ħ (properTime q p))
    (q₁ p₁ q₂ p₂ : SpaceTime 3) :
    hadamardPart (clockKernel (comptonFrequency m c ħ))
        (properTime (e q₁) (e p₁)) (properTime (e q₂) (e p₂)) =
      hadamardPart (clockKernel (comptonFrequency m c ħ))
        (properTime q₁ p₁) (properTime q₂ p₂) ∧
    pauliJordanPart (clockKernel (comptonFrequency m c ħ))
        (properTime (e q₁) (e p₁)) (properTime (e q₂) (e p₂)) =
      pauliJordanPart (clockKernel (comptonFrequency m c ħ))
        (properTime q₁ p₁) (properTime q₂ p₂) := by
  have hW := comptonClockKernel_pair_invariant_of_calibration e hcausal m c ħ
    hm hc hħ q p htime hphase q₁ p₁ q₂ p₂
  constructor
  · simpa only [hadamardPart] using congrArg Complex.re hW
  · simpa only [pauliJordanPart] using congrArg (fun z : ℂ => 2 * z.im) hW

/-- **Calibrated Compton-clock closure.**  A single nonzero timelike phase calibration
simultaneously removes the causal dilation, puts the map in the Poincaré group, retains the
clock-frequency form of the conditional holographic coupling, supplies the Compton
Sorkin–Johnston state, and keeps the real-frequency evolution unitary. -/
@[zil_level bridge_theorem]
theorem calibratedComptonClock_poincare_sj_unitary_holographic
    (e : Vector 3 ≃ᵃ[ℝ] Vector 3) (hcausal : IsCausalAutomorphism e)
    (m c ħ : ℝ) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ)
    (q p : SpaceTime 3) (htime : causalCharacter (p - q) = .timeLike)
    (hphase : comptonPhase m c ħ (properTime (e q) (e p)) =
      comptonPhase m c ħ (properTime q p)) :
    (∃ g : Vector 3 →ₗ[ℝ] Vector 3, IsLorentz g ∧ ∀ x, e x = g x + e 0) ∧
      ħ * c / m ^ 2 = c ^ 5 / (ħ * (comptonAnchoredClock m c ħ hm hc hħ).omega0 ^ 2) ∧
      IsSJState (clockKernel (comptonFrequency m c ħ))
        (pauliJordanPart (clockKernel (comptonFrequency m c ħ))) ∧
      ∀ t : ℝ, ‖Complex.exp (-Complex.I * (comptonFrequency m c ħ : ℂ) * (t : ℂ))‖ = 1 := by
  refine ⟨comptonCalibration_is_poincare e hcausal m c ħ hm.ne' hc.ne' hħ.ne'
      q p htime hphase, ?_, clockKernel_isSJState _, ?_⟩
  · exact comptonAnchored_newtonG_eq_from_clockFrequency m c ħ hm hc hħ
  · exact fun t => reversible_generator_flow_unitary (comptonFrequency m c ħ) t

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTimeLinks

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTimeLinks

zil attach zitterbewegungPhase_ratio_causalAutomorphism where
  formalizes @ "claim:the-dirac-zitterbewegung-phase-is-twice-the-compton-phase-over-proper-time-and-its-phase-ratios-are-the-same-exact-causal-invariants",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegung_rest_eq_two_compton"

zil attach entangledComptonPhase_ratio_causalAutomorphism where
  formalizes @ "claim:the-entanglement-reparametrized-compton-phase-multiplies-by-cosh-theta-cosh-eta-the-kinematic-and-schmidt-entanglement-boosts-and-its-ratios-remain-exact-causal-invariants-since-the-boosts-cancel-like-the-malament-dilation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization.doubly_boosted_compton_clock",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MassOrigin.ComptonClockSorkinJohnstonState.clockKernel_isSJState"

zil attach comptonPhase_injective where
  formalizes @ "claim:for-nonzero-mass-light-speed-and-planck-constant-the-compton-phase-is-an-injective-reading-and-therefore-uniquely-determines-the-proper-time-interval",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency"

zil attach comptonCalibration_fixes_malamentScale where
  formalizes @ "claim:one-preserved-nonzero-timelike-compton-clock-reading-fixes-the-positive-malament-conformal-factor-uniquely-to-one-and-therefore-fixes-every-proper-time-interval",
  supported_by @ "lean:Lorentz.Vector.properTime_ratio_causalAutomorphism",
  supported_by @ "lean:Lorentz.Vector.properTime_causalAutomorphism",
  caveat @ "claim:this-calibrates-the-affine-causal-automorphism-classified-by-the-repository-and-does-not-supply-the-still-separate-general-nonlinear-collineation-to-affine-step"

zil attach entanglementRapidity_unique_of_phase where
  formalizes @ "claim:at-fixed-kinematic-boost-and-a-nondegenerate-compton-clock-interval-the-nonnegative-schmidt-entanglement-rapidity-is-uniquely-determined-by-the-entanglement-reparametrized-phase",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization.doubly_boosted_compton_clock",
  caveat @ "claim:this-is-parameter-identifiability-on-the-nonnegative-rapidity-branch-not-an-independent-derivation-that-entanglement-physically-boosts-rest-energy"

zil attach comptonCalibration_is_poincare where
  formalizes @ "claim:an-affine-causal-automorphism-preserving-one-nonzero-timelike-compton-clock-reading-has-no-dilation-and-is-exactly-a-lorentz-transformation-followed-by-translation",
  supported_by @ "lean:Lorentz.Vector.causalAutomorphism_decomposition_with_properTime",
  caveat @ "claim:this-is-the-calibrated-affine-stage-and-does-not-supply-the-separate-general-nonlinear-light-ray-collineation-to-affine-theorem"

zil attach entanglementRapidity_eq_arcosh_phaseRatio where
  formalizes @ "claim:the-nonnegative-schmidt-rapidity-is-constructively-recovered-as-arcosh-of-the-entangled-phase-divided-by-the-fixed-kinematic-factor-and-compton-phase",
  supported_by @ "lean:Real.arcosh_cosh",
  caveat @ "claim:the-inverse-is-on-the-nonnegative-rapidity-branch-and-requires-a-nondegenerate-clock-phase"

zil attach comptonMass_unique_of_phase where
  supported_by @ "lean:comptonPhase_injective",
  formalizes @ "claim:at-fixed-nonzero-light-speed-planck-constant-and-proper-time-interval-one-compton-phase-reading-determines-the-mass-parameter-uniquely",
  caveat @ "claim:this-is-identifiability-with-calibrated-c-hbar-and-proper-time-not-a-prediction-of-an-observed-particle-mass"

zil attach properTime_reconstruct_from_comptonPhase where
  formalizes @ "claim:for-nonzero-clock-parameters-proper-time-is-constructively-recovered-from-the-compton-phase-by-multiplication-with-hbar-over-m-c-squared",
  epistemic_status @ "inversion",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime.comptonPhase"

zil attach globalComptonCalibration_iff_properTimeInvariant where
  formalizes @ "claim:with-nonzero-clock-parameters-global-compton-phase-preservation-is-equivalent-to-global-proper-time-preservation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTimeLinks.comptonPhase_injective",
  caveat @ "claim:this-equivalence-characterizes-calibration-for-the-fixed-compton-clock-and-does-not-by-itself-classify-arbitrary-nonlinear-causal-maps"

zil attach isGloballyComptonCalibrated_refl where
  formalizes @ "claim:global-compton-clock-calibrations-contain-the-identity-affine-map"

zil attach IsGloballyComptonCalibrated.trans where
  formalizes @ "claim:global-compton-clock-calibrations-are-closed-under-composition",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTimeLinks.IsGloballyComptonCalibrated"

zil attach IsGloballyComptonCalibrated.symm where
  formalizes @ "claim:global-compton-clock-calibrations-are-closed-under-affine-inverse",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTimeLinks.IsGloballyComptonCalibrated"

zil attach isGloballyComptonCalibrated_iff_poincare where
  formalizes @ "claim:within-the-affine-causal-automorphism-class-global-compton-calibration-is-equivalent-to-a-lorentz-transformation-followed-by-translation-with-no-dilation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTimeLinks.comptonCalibration_is_poincare",
  supported_by @ "lean:Lorentz.Vector.IsLorentz",
  caveat @ "claim:this-is-an-iff-inside-the-repositorys-affine-causal-automorphism-carrier-and-does-not-supply-the-separate-nonlinear-collineation-to-affine-theorem"

zil attach derivedNewtonG_eq_from_comptonPhase where
  formalizes @ "claim:the-conditional-holographic-coupling-hbar-c-over-m-squared-is-exactly-reconstructed-from-one-nonzero-compton-phase-and-proper-time-interval",
  epistemic_status @ "inversion",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_newtonG_eq_from_clockFrequency",
  caveat @ "claim:this-algebraically-inverts-the-compton-phase-law-under-nonzero-calibrated-inputs-and-is-not-an-independent-numerical-prediction-of-newtons-constant"

zil attach comptonClockKernel_invariant_of_calibration where
  formalizes @ "claim:one-nonzero-timelike-compton-calibration-removes-the-malament-dilation-and-therefore-preserves-the-compton-sorkin-johnston-two-point-kernel-on-every-proper-time-interval",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MassOrigin.ComptonClockSorkinJohnstonState.clockKernel_isSJState",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTimeLinks.comptonCalibration_fixes_malamentScale"

zil attach comptonClockKernel_pair_invariant_of_calibration where
  formalizes @ "claim:one-nonzero-timelike-compton-calibration-preserves-the-full-sorkin-johnston-clock-kernel-on-two-independently-chosen-proper-time-intervals",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTimeLinks.comptonCalibration_fixes_malamentScale",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MassOrigin.ComptonClockSorkinJohnstonState.clockKernel"

zil attach comptonClockSJ_parts_invariant_of_calibration where
  formalizes @ "claim:calibrated-causal-invariance-of-the-compton-two-point-kernel-preserves-both-its-hadamard-symmetric-correlation-and-pauli-jordan-commutator-parts",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTimeLinks.comptonClockKernel_pair_invariant_of_calibration",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition.wightmanTwoPoint_hadamardPart_pauliJordanPart",
  caveat @ "claim:these-are-exact-clock-kernel-components-not-a-claim-that-the-kernel-has-the-full-distributional-hadamard-wavefront-set"

zil attach calibratedComptonClock_poincare_sj_unitary_holographic where
  formalizes @ "claim:a-calibrated-compton-clock-jointly-yields-poincare-causal-kinematics-the-clock-frequency-form-of-the-conditional-holographic-coupling-a-sorkin-johnston-causal-state-and-unitary-real-frequency-evolution",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTimeLinks.comptonCalibration_is_poincare",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_newtonG_eq_from_clockFrequency",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MassOrigin.ComptonClockSorkinJohnstonState.clockKernel_isSJState",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum.reversible_generator_flow_unitary",
  caveat @ "claim:the-clock-kernel-is-the-repositorys-existing-sorkin-johnston-carrier-not-a-new-full-distributional-hadamard-wavefront-set-theorem-and-the-holographic-coupling-remains-conditional"

zil_file_contract physlib.comptonClockMalamentProperTimeLinks where
  promises "The Compton-de Broglie clock reading Malament's proper time links to the wider clock arc. The Dirac zitterbewegung frequency is twice Compton, so its phase over proper time is twice the de Broglie phase with the same exact causal-invariant ratios. A Schmidt two-mode entanglement of rapidity eta and a kinematic momentum boost theta multiply the clock by cosh theta times cosh eta keeping the form omega equals E over hbar, so the entanglement-reparametrized phase is cosh theta cosh eta times the Compton phase, whose ratios remain exact causal invariants because the boosts cancel in a ratio like the Malament dilation. For nonzero physical clock parameters the Compton phase is injective in proper time and has the explicit inverse hbar times phase divided by m c squared; global phase preservation is exactly global proper-time preservation. Global calibrations contain the identity and are closed under composition and inverse; inside the affine causal-automorphism class they are exactly Lorentz transformations followed by translations. One preserved nonzero timelike Compton reading therefore calibrates Malament's remaining positive conformal scale uniquely to one, fixes every proper-time interval, and reduces the affine causal automorphism to a Lorentz transformation followed by translation. At fixed kinematic boost and nonzero interval, the nonnegative Schmidt rapidity is uniquely identified by the entanglement-reparametrized phase and constructively recovered by arcosh. At fixed nonzero c, hbar, and interval, the phase also determines the Compton mass parameter uniquely. At the three-origin mass the clock rate is the Verlinde horizon-entropy rate c cubed A-dot over four G hbar with Newton's constant only through the horizon area rate, the Compton mass being at once the Yukawa, horizon, and Witten Chern-Simons topological mass. The clock's two-point kernel is a Sorkin-Johnston causal vacuum state and its reversible real-frequency generator sits on the unitary edge of the three-clock reversibility spectrum, separated from the entropic contracting clocks. The conditional coupling hbar c over mass squared can be reconstructed directly from a nonzero Compton phase. Calibrated causal maps preserve the full two-interval clock kernel and its Hadamard and Pauli-Jordan parts, and the capstone joins Poincare kinematics, the clock-frequency coupling, the causal state, and unitary evolution."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime.comptonPhase",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegungFrequency",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization.doubly_boosted_compton_clock"
  ]
  forbids_substitutes [
    "reading the entanglement or kinematic boost of the clock frequency as an invariance rather than only its ratios",
    "claiming the three-origin mass or Sorkin-Johnston-state identifications are proved here rather than cited",
    "dropping the nonzero clock-interval assumptions needed for operational uniqueness",
    "using the inverse clock formula after dropping any nonzero mass light-speed or Planck-constant hypothesis",
    "extending rapidity uniqueness beyond the fixed-kinematic-boost nonnegative branch",
    "calling calibrated mass identifiability or the phase-inverted coupling an independent numerical prediction",
    "promoting the clock Sorkin-Johnston carrier to a full distributional Hadamard wavefront-set result"
  ]
  witnessed_by [
    zitterbewegungPhase_eq_two_comptonPhase,
    zitterbewegungPhase_ratio_causalAutomorphism,
    entangledComptonPhase_eq,
    entangledComptonPhase_ratio_causalAutomorphism,
    comptonPhase_injective,
    comptonCalibration_fixes_malamentScale,
    entanglementRapidity_unique_of_phase,
    comptonCalibration_is_poincare,
    entanglementRapidity_eq_arcosh_phaseRatio,
    comptonMass_unique_of_phase,
    properTime_reconstruct_from_comptonPhase,
    globalComptonCalibration_iff_properTimeInvariant,
    isGloballyComptonCalibrated_refl,
    IsGloballyComptonCalibrated.trans,
    IsGloballyComptonCalibrated.symm,
    isGloballyComptonCalibrated_iff_poincare,
    derivedNewtonG_eq_from_comptonPhase,
    comptonClockKernel_invariant_of_calibration,
    comptonClockKernel_pair_invariant_of_calibration,
    comptonClockSJ_parts_invariant_of_calibration,
    calibratedComptonClock_poincare_sj_unitary_holographic
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.comptonClockMalamentProperTimeLinks
