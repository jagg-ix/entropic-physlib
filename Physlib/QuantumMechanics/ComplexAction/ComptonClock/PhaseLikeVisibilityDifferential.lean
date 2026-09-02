/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.Special.TwinParadox.EntropicInterference
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

meta import Zil

/-!
# Why the surviving reading of `S_I` survives: visibility is a differential channel

`ComptonAnchorCoherenceTime` refuted one reading of the imaginary action.  If `S_I` accumulates as
a *dissipative* rate at the Compton frequency, the interfering amplitude is damped by
`exp(−ω_C τ)` and the `1/e` coherence time is `ħ/mc² ≈ 8 × 10⁻²⁷ s` for Rb-87, against
interferometers that recombine over milliseconds.  That reading is dead.

A *phase-like* reading survives.  This file states what makes it survive, rather than leaving it as
the absence of a refutation: **on the phase-like reading the observable visibility is a differential
channel in the entropic rates, so the Compton-scale common mode is rejected exactly.**

`EntropicInterference.asymmetric_visibility_suppression` already gives the law: with path 1 at rate
`λ₀ + δλ` and path 2 at `λ₀` over a window `T`, the visibility is the symmetric one times
`exp(−δλ T/2)`.  The ratio depends on `δλ` and on nothing else — in particular not on `λ₀`.  §A
proves that dependence is *exactly* common-mode rejection: a shared rate cancels from the
entropic-time difference, and equal rates give zero signal.  `Δτ_ent = τ₁ − τ₂` is the same shape as
`SciamaAdSCPTMpembaNewtonObstructionHerglotz.differentialChannel`, whose common-mode rejection is
proved there; that module is not imported here, since the content needed is one subtraction and the
Sciama arc is a heavy dependency.

**Why that is the whole difference between the two readings.**  The refuted reading puts `λ₀` at the
Compton rate `mc²/ħ` and reads it in the *modulus*, so it predicts a mass-dependent coherence
collapse.  The surviving reading puts the same quantity in the *phase*, where it is common mode
across the two arms and cancels from the visibility.  Both readings agree on `S_I`; they disagree
about which part of the amplitude carries it, and only one of them is compatible with an
interferometer that works.

**What this makes testable.**  The surviving reading is not vacuous: it forbids a mass-dependent
visibility loss at the Compton scale (§B) while requiring a visibility deficit `exp(−δλ T/2)`
whenever the two arms genuinely differ in entropic rate.  A measured `δλ·T` predicts the deficit
with no free parameter.  The prediction is falsified by any interferometer that shows a
Compton-scale visibility loss common to both arms, or that shows no deficit when `δλ·T` is
independently nonzero.

Scope.  What is proved is the channel structure and the cancellation.  Identifying `δλ` with a
particular laboratory rate, and the claim that `S_I` is phase-like at all, both remain the
`conditional-model` calibration recorded in `EntropicClockComptonAnchor`; this file says what that
calibration commits to, not that it holds.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhaseLikeVisibilityDifferential

open Physlib.Relativity.Special.TwinParadox.EntropicInterference
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-! ### §A — the entropic-time difference is a differential channel -/

/-- **A rate shared by both arms is rejected exactly.**  Adding the same entropic rate `μ` to both
paths over the same window leaves the entropic-time difference unchanged.  This is the precise sense
in which the Compton-scale contribution — identical on the two arms — cannot appear in the
visibility, and it is why the phase-like reading is not touched by the coherence bound that killed
the dissipative one. -/
theorem common_entropic_rate_rejected (lambda1 lambda2 mu T : ℝ) :
    deltaTauEnt ((lambda1 + mu) * T) ((lambda2 + mu) * T)
      = deltaTauEnt (lambda1 * T) (lambda2 * T) := by
  unfold deltaTauEnt
  ring

/-- **Equal arms give no signal.**  If the two paths run at the same entropic rate the difference
vanishes identically, at every window length: the absolute rate is not the observable. -/
theorem equal_rates_no_signal (lambda T : ℝ) :
    deltaTauEnt (lambda * T) (lambda * T) = 0 := by
  unfold deltaTauEnt
  ring

/-! ### §B — the Compton common mode cancels, whatever the mass -/

/-- **The Compton rate cancels from the visibility.**  Putting the Compton frequency `ω_C = mc²/ħ`
on both arms — which is exactly what the refuted dissipative reading does — contributes nothing to
the entropic-time difference, for any mass.

This is the formal content of "the phase-like reading survives": the quantity whose *modulus*
reading predicted an `8 × 10⁻²⁷ s` coherence time enters the two-arm observable only as a common
mode, and common modes are rejected.  A mass-dependent visibility loss at the Compton scale is
therefore forbidden by this reading, not merely unobserved. -/
theorem compton_common_mode_cancels (m c ħ lambda1 lambda2 T : ℝ) :
    deltaTauEnt ((lambda1 + comptonFrequency m c ħ) * T)
        ((lambda2 + comptonFrequency m c ħ) * T)
      = deltaTauEnt (lambda1 * T) (lambda2 * T) :=
  common_entropic_rate_rejected lambda1 lambda2 (comptonFrequency m c ħ) T

/-- **Only the differential rate reaches the visibility.**  The asymmetric-configuration visibility
deficit is `exp(−δλ T/2)`, and it is unchanged by any rate common to both arms — so a measured
`δλ·T` fixes the deficit with no free parameter and no dependence on the absolute entropic rate. -/
theorem visibility_deficit_depends_only_on_differential (lambda0 mu dlambda T : ℝ) :
    Real.exp (-(deltaTauEnt (((lambda0 + mu) + dlambda) * T) ((lambda0 + mu) * T) / 2))
      = Real.exp (-(dlambda * T / 2)) := by
  have hdiff : deltaTauEnt (((lambda0 + mu) + dlambda) * T) ((lambda0 + mu) * T) = dlambda * T := by
    unfold deltaTauEnt; ring
  rw [hdiff]

/-! ### §C — the two readings, separated -/

/-- **The readings differ exactly on where the common mode goes.**  Under the surviving reading the
observable two-arm quantity is blind to any shared rate, including the Compton rate: shifting both
arms by `ω_C` changes neither the entropic-time difference nor the visibility deficit.  The refuted
reading placed that same shared rate in the modulus, where it does not cancel and predicts the
coherence collapse that experiment excludes. -/
theorem phaseLike_reading_blind_to_compton (m c ħ lambda1 lambda2 T : ℝ) :
    deltaTauEnt ((lambda1 + comptonFrequency m c ħ) * T)
        ((lambda2 + comptonFrequency m c ħ) * T)
      = deltaTauEnt (lambda1 * T) (lambda2 * T)
    ∧ Real.exp (-(deltaTauEnt ((lambda1 + comptonFrequency m c ħ) * T)
        ((lambda2 + comptonFrequency m c ħ) * T) / 2))
      = Real.exp (-(deltaTauEnt (lambda1 * T) (lambda2 * T) / 2)) := by
  refine ⟨compton_common_mode_cancels m c ħ lambda1 lambda2 T, ?_⟩
  rw [compton_common_mode_cancels m c ħ lambda1 lambda2 T]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhaseLikeVisibilityDifferential.compton_common_mode_cancels where
  formalizes @ "claim:on-the-phase-like-reading-of-the-imaginary-action-the-two-arm-interference-observable-rejects-any-entropic-rate-common-to-both-paths-including-the-compton-rate",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.Relativity.Special.TwinParadox.EntropicInterference.asymmetric_visibility_suppression",
  caveat @ "this-says-what-the-surviving-reading-commits-to-not-that-the-imaginary-action-is-phase-like-which-remains-the-conditional-model-calibration-of-entropic-clock-compton-anchor"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhaseLikeVisibilityDifferential.visibility_deficit_depends_only_on_differential where
  formalizes @ "claim:the-interference-visibility-deficit-is-fixed-by-the-differential-entropic-rate-times-the-window-alone-with-no-dependence-on-the-absolute-rate-and-no-free-parameter",
  epistemic_status @ "conditional-model",
  requires @ "claim:on-the-phase-like-reading-of-the-imaginary-action-the-two-arm-interference-observable-rejects-any-entropic-rate-common-to-both-paths-including-the-compton-rate",
  experimental_bound @ "value:atom-interferometers-recombine-coherently-over-milliseconds-while-the-compton-time-hbar-over-m-c-squared-is-about-8e-27-seconds-for-rubidium-87;test:the-surviving-reading-forbids-any-compton-scale-visibility-loss-common-to-both-arms-and-requires-a-deficit-exp-minus-half-delta-lambda-times-window-whenever-the-arms-differ-in-entropic-rate-so-an-independently-measured-delta-lambda-times-window-predicts-the-deficit-with-no-free-parameter",
  caveat @ "identifying-delta-lambda-with-a-particular-laboratory-rate-is-not-established-here-the-theorem-fixes-the-functional-form-not-the-value"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.PhaseLikeVisibilityDifferential

end
