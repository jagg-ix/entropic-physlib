/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor
public import Physlib.Relativity.Special.TwinParadox.EntropicInterference

meta import Zil

/-!
# The Compton-anchored action rate sets the coherence time

`EntropicClockComptonAnchor.comptonAnchored_entropicTime_eq_geometricProperTime` reads the
geometric proper time off the entropic clock, but only under the hypothesis

  `hcal : ΔS_I = m c² Δτ`

which the anchor's own file contract records as untested by any cited experiment.  What has been
missing is the *cost* of that hypothesis, and it is fixed by machinery already in the library.

`TwinParadox.EntropicInterference` carries the interference layer for the same entropy-arrow
clock.  Its `entropicPathAmplitude φ τ_ent = e^{iφ} · e^{−τ_ent}` splits the two physical roles
cleanly — `norm_entropicPathAmplitude` shows the entropic proper time is the **modulus** while the
unitary phase is the **argument**.  Combining the two facts is immediate and decisive: `hcal`
forces `Δτ_ent = ω_C Δτ`, so the interfering amplitude is damped by `e^{−ω_C Δτ}` with
`ω_C = m c²/ħ` the Compton frequency.

The consequence, `comptonAnchored_coherenceTime_eq_inv_comptonFrequency`, is that the coherence
time under `hcal` is the Compton time `ħ/(m c²)` — about `8 × 10⁻²⁷ s` for a rubidium-87 atom.
Any interferometer that recombines with visible fringes over a longer window therefore falsifies
`hcal` *for that system*, without needing a new experiment: existing Stern–Gerlach interferometry
holds coherence for milliseconds, some twenty-three orders of magnitude beyond this bound.

This is a statement about the **operational identification** `hcal`, in the sense of the library's
three-layer separation: it constrains which physical quantity may play the role of `S_I_along`, and
leaves the algebraic entropic-clock theorems untouched.  Concretely it rules out reading `S_I_along`
as a dissipative rate (its `ofLindbladJump` instantiation, `S_I_along t = 2⟨ψ, H_I ψ⟩ t`) while
simultaneously demanding `hcal`; a reading on which `S_I` is phase-like in the mean survives, which
is what `entropicPathAmplitude` already encodes.

The visibility law such a reading predicts is likewise already proved, in
`EntropicInterference.asymmetric_visibility_suppression`: an extra entropic rate `δλ` applied over a
window `T` on one arm suppresses the fringe visibility by exactly `e^{−δλ T/2}`, with no free
parameter once `δλ T = ΔS_I/ħ` is measured independently.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonAnchorCoherenceTime

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.Relativity.Special.TwinParadox.EntropicInterference

/-! ### §A — The anchored entropic time advance -/

/-- **The entropic proper time forced by `hcal`.**  When the imaginary action accumulates at the
rest-energy rate over a geometric proper time `Δτ`, the entropic proper time `ΔS_I/ħ` is the
Compton frequency times `Δτ`. -/
lemma anchored_entropicTime_eq_comptonFrequency_mul
    (m c ħ dtau : ℝ) (hħ : ħ ≠ 0) :
    (m * c ^ 2 * dtau) / ħ = comptonFrequency m c ħ * dtau := by
  unfold comptonFrequency
  field_simp

/-! ### §B — The coherence cost -/

/-- **The anchored amplitude is damped at the Compton frequency.**  Under `hcal` the interfering
path amplitude has modulus `e^{−ω_C Δτ}`: the entropic clock that reads proper time also damps the
amplitude, and it does so at the rest-energy rate. -/
theorem norm_anchored_pathAmplitude
    (m c ħ dtau phi : ℝ) (hħ : ħ ≠ 0) :
    ‖entropicPathAmplitude phi ((m * c ^ 2 * dtau) / ħ)‖
      = Real.exp (-(comptonFrequency m c ħ * dtau)) := by
  rw [norm_entropicPathAmplitude, anchored_entropicTime_eq_comptonFrequency_mul m c ħ dtau hħ]

/-- **The coherence time is the Compton time.**  At `Δτ = ħ/(m c²)` the anchored amplitude has
fallen to `e^{−1}` of its initial modulus, so `hcal` fixes the `1/e` coherence time to the inverse
Compton frequency. -/
theorem comptonAnchored_coherenceTime_eq_inv_comptonFrequency
    (m c ħ phi : ℝ) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    ‖entropicPathAmplitude phi ((m * c ^ 2 * (ħ / (m * c ^ 2))) / ħ)‖ = Real.exp (-1) := by
  rw [norm_entropicPathAmplitude]
  congr 1
  have hmc : m * c ^ 2 ≠ 0 := by positivity
  field_simp

/-- **Coherence vanishes as the proper-time window grows.**  Under `hcal` the fringe modulus tends
to zero along `Δτ → ∞`: no interferometer with a positive rest mass can recombine coherently over a
long window.  This is the quantitative content of the incompatibility. -/
theorem comptonAnchored_coherence_tendsto_zero
    (m c ħ phi : ℝ) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    Filter.Tendsto
      (fun dtau : ℝ => ‖entropicPathAmplitude phi ((m * c ^ 2 * dtau) / ħ)‖)
      Filter.atTop (nhds 0) := by
  have hω : 0 < comptonFrequency m c ħ := by
    unfold comptonFrequency; positivity
  have hlin : Filter.Tendsto (fun dtau : ℝ => -(comptonFrequency m c ħ * dtau))
      Filter.atTop Filter.atBot := by
    have hneg : Filter.Tendsto (fun dtau : ℝ => (-(comptonFrequency m c ħ)) * dtau)
        Filter.atTop Filter.atBot :=
      Filter.Tendsto.const_mul_atTop_of_neg (by linarith) Filter.tendsto_id
    simpa [neg_mul] using hneg
  have hcomp := Real.tendsto_exp_atBot.comp hlin
  refine hcomp.congr fun dtau => ?_
  exact (norm_anchored_pathAmplitude m c ħ dtau phi (ne_of_gt hħ)).symm

/-! ### §C — What survives

The bound above constrains `hcal`, not the entropic clock itself.  The interference layer already
proves the law a phase-like `S_I` predicts:
`EntropicInterference.asymmetric_visibility_suppression` gives visibility suppression `e^{−δλ T/2}`
for an extra entropic rate `δλ` over a window `T` on one arm — a parameter-free prediction once
`δλ T = ΔS_I/ħ` is measured independently, and the observable a Stern–Gerlach test should target. -/

/-- **Reversible paths keep full coherence.**  With no entropy production the modulus is `1`: the
damping above is entirely the entropy's doing, not an artefact of the amplitude's form. -/
theorem norm_pathAmplitude_at_zero_entropy (phi : ℝ) :
    ‖entropicPathAmplitude phi 0‖ = 1 := by
  rw [norm_entropicPathAmplitude, neg_zero, Real.exp_zero]


/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonAnchorCoherenceTime.norm_anchored_pathAmplitude where
  formalizes @ "claim:under-the-rest-energy-action-rate-hypothesis-the-interfering-entropic-path-amplitude-has-modulus-exp-minus-compton-frequency-times-proper-time-so-the-clock-that-reads-proper-time-also-damps-the-amplitude-at-the-rest-energy-rate",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.Relativity.Special.TwinParadox.EntropicInterference.norm_entropicPathAmplitude",
  caveat @ "this-is-a-consequence-of-the-untested-calibration-hypothesis-delta-s-i-equals-m-c-squared-delta-tau-not-an-independent-derivation-of-the-damping"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonAnchorCoherenceTime.comptonAnchored_coherenceTime_eq_inv_comptonFrequency where
  supported_by @ "lean:Physlib.Relativity.Special.TwinParadox.EntropicInterference.norm_entropicPathAmplitude",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-calibration-hypothesis-fixes-the-one-over-e-coherence-time-of-the-entropic-path-amplitude-to-the-compton-time-hbar-over-m-c-squared",
  epistemic_status @ "conditional-model",
  requires @ "claim:under-the-rest-energy-action-rate-hypothesis-the-interfering-entropic-path-amplitude-has-modulus-exp-minus-compton-frequency-times-proper-time-so-the-clock-that-reads-proper-time-also-damps-the-amplitude-at-the-rest-energy-rate",
  caveat @ "empirical-reading-only-an-interferometer-recombining-coherently-over-a-window-longer-than-the-compton-time-falsifies-the-calibration-hypothesis-for-that-system-this-constrains-the-operational-identification-not-the-algebraic-entropic-clock-theorems"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonAnchorCoherenceTime.comptonAnchored_coherence_tendsto_zero where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonAnchorCoherenceTime.norm_anchored_pathAmplitude",
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:under-the-calibration-hypothesis-the-interfering-amplitude-modulus-tends-to-zero-as-the-proper-time-window-grows-so-no-massive-system-can-recombine-coherently-over-a-long-window",
  epistemic_status @ "conditional-model",
  requires @ "claim:the-calibration-hypothesis-fixes-the-one-over-e-coherence-time-of-the-entropic-path-amplitude-to-the-compton-time-hbar-over-m-c-squared",
  caveat @ "the-limit-is-in-the-proper-time-variable-at-fixed-mass-it-does-not-assert-that-any-particular-experiment-has-been-performed"

zil_file_contract physlib.comptonAnchorCoherenceTime where
  promises "The Compton anchor reads geometric proper time off the entropic clock only under the calibration hypothesis that the imaginary action accumulates at the rest energy rate, and that hypothesis carries a coherence cost which is computed here from machinery already in the library. The entropic path amplitude of the twin-paradox interference layer factors as a unit-modulus phase times the entropic damping, so the entropic proper time is the modulus while the unitary phase is the argument. Composing that factorization with the calibration hypothesis gives an interfering amplitude damped by exp of minus the Compton frequency times the proper time, a one-over-e coherence time equal to the Compton time hbar over m c squared, and a modulus tending to zero as the proper-time window grows. The empirical reading is that any interferometer recombining with visible fringes over a window longer than the Compton time falsifies the calibration hypothesis for that system without a new experiment. This constrains which physical quantity may play the role of the imaginary action along the worldline: it rules out reading it as a dissipative rate, as in the Lindblad-jump instantiation where the imaginary action is twice the expected dissipator times the parameter, while simultaneously demanding the calibration hypothesis. A reading on which the imaginary action is phase-like in the mean survives, and the visibility law that reading predicts is already proved as the asymmetric visibility suppression of the interference layer, exponential in minus half the extra entropic rate times the window, parameter-free once that product is measured independently."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Relativity.Special.TwinParadox.EntropicInterference.entropicPathAmplitude",
    "lean:Physlib.Relativity.Special.TwinParadox.EntropicInterference.norm_entropicPathAmplitude",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicClockComptonAnchor.comptonAnchored_entropicTime_eq_geometricProperTime"]
  forbids_substitutes ["reading the coherence bound as a refutation of the algebraic entropic-clock theorems rather than of the operational calibration hypothesis",
    "treating the imaginary action along the worldline as simultaneously a dissipative Lindblad rate and a quantity accumulating at the rest-energy rate",
    "presenting the Compton-time coherence bound as a measured result rather than a consequence of the untested calibration hypothesis"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonAnchorCoherenceTime.norm_anchored_pathAmplitude,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonAnchorCoherenceTime.comptonAnchored_coherenceTime_eq_inv_comptonFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonAnchorCoherenceTime.comptonAnchored_coherence_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonAnchorCoherenceTime.norm_pathAmplitude_at_zero_entropy]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonAnchorCoherenceTime

end
