/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.CauchyBroadening
public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelPageWootters
meta import Zil

/-!
# One calibrated rate across linewidth, relaxation, and entropy production

This module closes the cross-observable surface of the one-level LDDL carrier.
The same `RateData.gamma`, fixed independently from counted in/out transitions,
controls three disjoint observables:

* the Lorentzian spectral line has half-width `γ` and full width `2γ`;
* the population relaxation `exp (-2γt)` has time constant `T₁ = 1/(2γ)`;
* the exact Bernoulli relative-entropy derivative uses that same `γ` in its
  production rate.

The result is an anti-circular *cross-observable consistency theorem*.  It does
not claim that a measured system obeys the one-level Markov/GKSL model, nor that
pure dephasing contributes to population relaxation.  Those remain empirical
model-selection obligations.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics.LindbladDrivenLeads

/-! ## A. Lorentzian half-maximum geometry -/

/-- The lower-frequency half-maximum point of the one-level Lorentzian. -/
def lorentzHalfMaximumLeft (r : RateData) (epsilon : ℝ) : ℝ :=
  epsilon - r.gamma

/-- The upper-frequency half-maximum point of the one-level Lorentzian. -/
def lorentzHalfMaximumRight (r : RateData) (epsilon : ℝ) : ℝ :=
  epsilon + r.gamma

/-- Half the distance between the two proved half-maximum points. -/
def lorentzHWHM (r : RateData) (epsilon : ℝ) : ℝ :=
  (lorentzHalfMaximumRight r epsilon - lorentzHalfMaximumLeft r epsilon) / 2

/-- The distance between the two proved half-maximum points. -/
def lorentzFWHM (r : RateData) (epsilon : ℝ) : ℝ :=
  lorentzHalfMaximumRight r epsilon - lorentzHalfMaximumLeft r epsilon

/-- The left boundary `ε - γ` has exactly half the peak height. -/
theorem lorentzPeak_left_halfMaximum (r : RateData) (epsilon : ℝ) :
    lorentzPeak r.gamma epsilon (lorentzHalfMaximumLeft r epsilon) =
      lorentzPeak r.gamma epsilon epsilon / 2 := by
  unfold lorentzPeak lorentzHalfMaximumLeft
  field_simp [r.gamma_pos.ne']; ring

/-- The right boundary `ε + γ` has exactly half the peak height. -/
theorem lorentzPeak_right_halfMaximum (r : RateData) (epsilon : ℝ) :
    lorentzPeak r.gamma epsilon (lorentzHalfMaximumRight r epsilon) =
      lorentzPeak r.gamma epsilon epsilon / 2 := by
  unfold lorentzPeak lorentzHalfMaximumRight
  field_simp [r.gamma_pos.ne']; ring

/-- The two displayed boundaries are the only half-maximum frequencies.  This
prevents `HWHM`/`FWHM` from being mere names attached to chosen points. -/
theorem lorentzPeak_eq_halfMaximum_iff (r : RateData) (epsilon omega : ℝ) :
    lorentzPeak r.gamma epsilon omega = lorentzPeak r.gamma epsilon epsilon / 2 ↔
      omega = lorentzHalfMaximumLeft r epsilon ∨
        omega = lorentzHalfMaximumRight r epsilon := by
  constructor
  · intro h
    have hden : (omega - epsilon) ^ 2 + r.gamma ^ 2 ≠ 0 :=
      (greenDenominator_pos r epsilon omega).ne'
    have hcenter : lorentzPeak r.gamma epsilon epsilon = r.gamma⁻¹ := by
      unfold lorentzPeak
      simp only [sub_self]
      field_simp [r.gamma_pos.ne']; ring
    rw [hcenter] at h
    unfold lorentzPeak at h
    rw [div_eq_iff hden] at h
    have hsquare : (omega - epsilon) ^ 2 = r.gamma ^ 2 := by
      field_simp [r.gamma_pos.ne'] at h
      nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hplus | hminus
    · right
      unfold lorentzHalfMaximumRight
      linarith
    · left
      unfold lorentzHalfMaximumLeft
      linarith
  · rintro (hleft | hright)
    · simpa [hleft] using lorentzPeak_left_halfMaximum r epsilon
    · simpa [hright] using lorentzPeak_right_halfMaximum r epsilon

/-- **Lorentzian half-width:** the distance from the center to either
half-maximum boundary is `γ`. -/
theorem lorentzHWHM_eq_gamma (r : RateData) (epsilon : ℝ) :
    lorentzHWHM r epsilon = r.gamma := by
  unfold lorentzHWHM lorentzHalfMaximumRight lorentzHalfMaximumLeft
  ring

/-- **Lorentzian full width:** the separation of the two half-maximum
boundaries is `2γ`. -/
theorem lorentzFWHM_eq_two_gamma (r : RateData) (epsilon : ℝ) :
    lorentzFWHM r epsilon = 2 * r.gamma := by
  unfold lorentzFWHM lorentzHalfMaximumRight lorentzHalfMaximumLeft
  ring

/-! ## B. Population relaxation time -/

/-- The population relaxation time of `exp (-2γt)`. -/
def RateData.populationRelaxationTime (r : RateData) : ℝ :=
  (2 * r.gamma)⁻¹

theorem RateData.populationRelaxationTime_pos (r : RateData) :
    0 < r.populationRelaxationTime := by
  unfold RateData.populationRelaxationTime
  exact inv_pos.mpr (mul_pos (by norm_num) r.gamma_pos)

/-- At one relaxation time the occupation deviation has fallen by exactly
`e⁻¹`.  This gives mathematical content to `T₁ = 1/(2γ)` beyond unfolding its
definition. -/
theorem RateData.predictedOccupation_at_populationRelaxationTime
    (r : RateData) (N₀ : ℝ) :
    r.predictedOccupation N₀ r.populationRelaxationTime - r.occupation =
      (N₀ - r.occupation) * Real.exp (-1) := by
  rw [RateData.predictedOccupation_sub_occupation]
  unfold RateData.populationRelaxationTime
  have htwo : 2 * r.gamma ≠ 0 := mul_ne_zero (by norm_num) r.gamma_pos.ne'
  have hexponent : -2 * r.gamma * (2 * r.gamma)⁻¹ = -1 := by
    calc
      -2 * r.gamma * (2 * r.gamma)⁻¹ = -(2 * r.gamma) * (2 * r.gamma)⁻¹ := by ring
      _ = -((2 * r.gamma) * (2 * r.gamma)⁻¹) := by ring
      _ = -1 := by rw [mul_inv_cancel₀ htwo]
  rw [hexponent]

/-- Independent transition counts fix the relaxation time as the reciprocal
of their total rate. -/
theorem RateData.ofInOutRates_populationRelaxationTime
    (Γin Γout : ℝ) (hin : 0 < Γin) (hout : 0 < Γout) :
    (RateData.ofInOutRates Γin Γout hin hout).populationRelaxationTime =
      (Γin + Γout)⁻¹ := by
  unfold RateData.populationRelaxationTime RateData.ofInOutRates
  congr 1
  ring

/-! ## C. Pure-dephasing-aware transverse relaxation -/

/-- The transverse coherence-decay rate when `γφ` is calibrated independently
as pure dephasing.  The loss/gain channel contributes `γ`; number dephasing
contributes `γφ`. -/
def RateData.coherenceDecayRate (r : RateData) (γφ : ℝ) : ℝ :=
  r.gamma + γφ

/-- The transverse relaxation time `T₂ = 1/(γ+γφ)`. -/
def RateData.transverseRelaxationTime (r : RateData) (γφ : ℝ) : ℝ :=
  (r.coherenceDecayRate γφ)⁻¹

theorem RateData.coherenceDecayRate_pos (r : RateData) (γφ : ℝ)
    (hγφ : 0 ≤ γφ) :
    0 < r.coherenceDecayRate γφ :=
  add_pos_of_pos_of_nonneg r.gamma_pos hγφ

theorem RateData.transverseRelaxationTime_pos (r : RateData) (γφ : ℝ)
    (hγφ : 0 ≤ γφ) :
    0 < r.transverseRelaxationTime γφ :=
  inv_pos.mpr (r.coherenceDecayRate_pos γφ hγφ)

/-- A spectral-line `RateData` carrying the transverse rate `γ+γφ`.  This
reuses the existing normalized Cauchy/Lorentzian infrastructure without
reinterpreting pure dephasing as a population transition. -/
def RateData.coherenceLineData (r : RateData) (γφ : ℝ) (hγφ : 0 ≤ γφ) :
    RateData where
  gamma := r.coherenceDecayRate γφ
  occupation := r.occupation
  gamma_pos := r.coherenceDecayRate_pos γφ hγφ
  occupation_nonneg := r.occupation_nonneg
  occupation_le_one := r.occupation_le_one

/-- The dephasing-aware Lorentzian HWHM is the transverse rate `γ+γφ`. -/
theorem RateData.coherenceLine_HWHM
    (r : RateData) (γφ : ℝ) (hγφ : 0 ≤ γφ) (epsilon : ℝ) :
    lorentzHWHM (r.coherenceLineData γφ hγφ) epsilon =
      r.coherenceDecayRate γφ := by
  exact lorentzHWHM_eq_gamma (r.coherenceLineData γφ hγφ) epsilon

/-- The dephasing-aware Lorentzian FWHM is `2(γ+γφ)`. -/
theorem RateData.coherenceLine_FWHM
    (r : RateData) (γφ : ℝ) (hγφ : 0 ≤ γφ) (epsilon : ℝ) :
    lorentzFWHM (r.coherenceLineData γφ hγφ) epsilon =
      2 * r.coherenceDecayRate γφ := by
  exact lorentzFWHM_eq_two_gamma (r.coherenceLineData γφ hγφ) epsilon

/-- **The exact `T₁/T₂` separation:**
`T₂⁻¹ = (2T₁)⁻¹ + γφ`.  Thus the independently calibrated pure-dephasing
rate affects coherence/linewidth but not the population equation. -/
theorem RateData.inverse_transverseRelaxationTime_eq
    (r : RateData) (γφ : ℝ) :
    (r.transverseRelaxationTime γφ)⁻¹ =
      (2 * r.populationRelaxationTime)⁻¹ + γφ := by
  unfold RateData.transverseRelaxationTime RateData.coherenceDecayRate
    RateData.populationRelaxationTime
  field_simp [r.gamma_pos.ne']

/-- With no pure dephasing, the textbook amplitude-damping relation
`T₂ = 2T₁` is recovered exactly. -/
theorem RateData.transverseRelaxationTime_zero
    (r : RateData) :
    r.transverseRelaxationTime 0 = 2 * r.populationRelaxationTime := by
  unfold RateData.transverseRelaxationTime RateData.coherenceDecayRate
    RateData.populationRelaxationTime
  field_simp [r.gamma_pos.ne']
  ring

/-- **Dephasing-aware calibration closure.**  The actual GKSL generator proves
that `γφ` leaves population relaxation unchanged and adds only to coherence
decay; the same transverse rate then fixes the Lorentzian HWHM and the exact
`T₁/T₂` relation. -/
theorem calibrated_rate_pureDephasing_separation
    (r : RateData) (γφ : ℝ) (hγφ : 0 ≤ γφ)
    (epsilon : ℝ) (ρ : Matrix Qubit Qubit ℂ) :
    oneLevelGKSLWithPureDephasingMatrix r γφ ρ 1 1 =
        oneLevelGKSLMatrix r ρ 1 1 ∧
      oneLevelGKSLWithPureDephasingMatrix r γφ ρ 0 1 =
        -(((r.coherenceDecayRate γφ : ℝ) : ℂ) * ρ 0 1) ∧
      lorentzHWHM (r.coherenceLineData γφ hγφ) epsilon =
        r.coherenceDecayRate γφ ∧
      (r.transverseRelaxationTime γφ)⁻¹ =
        (2 * r.populationRelaxationTime)⁻¹ + γφ := by
  exact ⟨oneLevelGKSLWithPureDephasing_population_eq r γφ hγφ ρ,
    oneLevelGKSLWithPureDephasing_coherence_eq r γφ hγφ ρ,
    r.coherenceLine_HWHM γφ hγφ epsilon,
    r.inverse_transverseRelaxationTime_eq γφ⟩

/-! ## D. Frozen-calibration cross-observable theorem -/

/-- **One independently calibrated coefficient predicts linewidth, relaxation,
and KL production.**  Positive counted transition rates define one `RateData`.
Its spectral HWHM is `γ`, its FWHM is the counted total rate, its population
relaxation time is the reciprocal total rate, and the exact KL derivative uses
the same `γ` in `entropyProductionRate`.

The final conjunct is a derivative identity on held-out positive-time
occupation data.  It does not use a linewidth or trajectory fit to redefine
`γ`. -/
theorem calibrated_rate_linewidth_relaxation_KL_chain
    (Γin Γout : ℝ) (hin : 0 < Γin) (hout : 0 < Γout)
    (epsilon N₀ t : ℝ) (hN₀0 : 0 < N₀) (hN₀1 : N₀ < 1) (ht : 0 ≤ t) :
    let r := RateData.ofInOutRates Γin Γout hin hout
    lorentzHWHM r epsilon = r.gamma ∧
      lorentzFWHM r epsilon = Γin + Γout ∧
      r.populationRelaxationTime = (Γin + Γout)⁻¹ ∧
      HasDerivAt (fun s => binaryKL (r.predictedOccupation N₀ s) r.occupation)
        (-(entropyProductionRate r.gamma
          (r.predictedOccupation N₀ t) r.occupation)) t := by
  let r := RateData.ofInOutRates Γin Γout hin hout
  change lorentzHWHM r epsilon = r.gamma ∧
    lorentzFWHM r epsilon = Γin + Γout ∧
    r.populationRelaxationTime = (Γin + Γout)⁻¹ ∧
    HasDerivAt (fun s => binaryKL (r.predictedOccupation N₀ s) r.occupation)
      (-(entropyProductionRate r.gamma
        (r.predictedOccupation N₀ t) r.occupation)) t
  have hf0 : 0 < r.occupation := by
    dsimp [r, RateData.ofInOutRates]
    positivity
  have hf1 : r.occupation < 1 := by
    dsimp [r, RateData.ofInOutRates]
    rw [div_lt_one (by positivity)]
    linarith
  refine ⟨lorentzHWHM_eq_gamma r epsilon, ?_, ?_, ?_⟩
  · calc
      lorentzFWHM r epsilon = 2 * r.gamma := lorentzFWHM_eq_two_gamma r epsilon
      _ = Γin + Γout := by
        simpa [r] using RateData.ofInOutRates_two_gamma Γin Γout hin hout
  · simpa [r] using
      RateData.ofInOutRates_populationRelaxationTime Γin Γout hin hout
  · exact binaryKL_predictedOccupation_hasDerivAt r hN₀0 hN₀1 hf0 hf1 ht

end QuantumMechanics.LindbladDrivenLeads

/- ZIL-BEGIN -/

zil attach QuantumMechanics.LindbladDrivenLeads.lorentzHWHM_eq_gamma where
  formalizes @ "claim:the-one-level-lorentzian-has-half-width-at-half-maximum-equal-to-the-rate-gamma",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.lorentzPeak_left_halfMaximum",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.lorentzPeak_right_halfMaximum",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.lorentzPeak_eq_halfMaximum_iff",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.lorentzFWHM_eq_two_gamma where
  formalizes @ "claim:the-one-level-lorentzian-full-width-at-half-maximum-is-two-gamma",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.lorentzHWHM_eq_gamma",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.predictedOccupation_at_populationRelaxationTime where
  formalizes @ "claim:at-the-population-relaxation-time-one-over-two-gamma-the-one-level-occupation-deviation-is-reduced-by-exactly-exp-minus-one",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.predictedOccupation_sub_occupation",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.RateData.inverse_transverseRelaxationTime_eq where
  discloses @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLWithPureDephasingMatrix_eq",
  formalizes @ "claim:the-dephasing-aware-one-level-times-obey-the-exact-relation-t2-inverse-equals-two-t1-inverse-plus-gamma-phi",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLWithPureDephasingMatrix_eq",
  epistemic_status @ "consistency-identity"

zil attach QuantumMechanics.LindbladDrivenLeads.calibrated_rate_pureDephasing_separation where
  formalizes @ "claim:the-explicit-gksl-carrier-separates-population-loss-from-pure-dephasing-the-latter-changes-coherence-decay-lorentzian-linewidth-and-t2-without-changing-t1",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLWithPureDephasing_population_eq",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.coherenceLine_HWHM",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.inverse_transverseRelaxationTime_eq",
  epistemic_status @ "conditional-model",
  requires @ "assumption:the-observed-coherence-line-is-lorentzian-and-gamma-phi-is-calibrated-independently-rather-than-fit-as-population-loss",
  caveat @ "scope:this-closes-the-model-level-t1-t2-separation-it-does-not-predict-the-material-specific-pure-dephasing-rate-from-first-principles"

zil attach QuantumMechanics.LindbladDrivenLeads.calibrated_rate_linewidth_relaxation_KL_chain where
  formalizes @ "claim:one-gamma-fixed-by-independent-in-out-transition-counts-simultaneously-fixes-lorentzian-linewidth-population-relaxation-time-and-the-exact-KL-production-law",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.ofInOutRates_two_gamma",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.binaryKL_predictedOccupation_hasDerivAt",
  epistemic_status @ "conditional-model",
  requires @ "assumption:the-observed-carrier-is-described-by-the-one-level-markov-gksl-rate-model-and-any-pure-dephasing-is-either-negligible-or-separated-by-calibrated-rate-puredephasing-separation",
  caveat @ "scope:the-formal-chain-is-anti-circular-because-gamma-is-fixed-from-transition-counts-but-experimental-cross-carrier-validation-and-comparison-with-conventional-open-system-models-remain-external"

/- ZIL-END -/
