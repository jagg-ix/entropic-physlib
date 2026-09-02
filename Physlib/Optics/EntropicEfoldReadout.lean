/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Optics.BoundaryCouplingRelaxation
public import Physlib.Thermodynamics.SecondLaw

meta import Zil

/-!
# Entropic time without `ℏ`: the clock reading is an e-fold count

`ClausiusEntropyArrow.EntropyArrowWorldline` defines the entropic clock by `τ_ent := S_I/ℏ`, which
makes it look as though testing entropic time requires a quantum system.  It does not.  The
`SciamaAdSCPTMpembaNewtonObstructionHerglotz.herglotz_efolds_lorentz_invariant` docstring already
records why: "the accumulated imaginary action `S_I = ℏ ρ t` is a Lorentz scalar, as an action must
be".  With `S_I = ℏ ρ t` the constant **cancels**,

  `τ_ent = S_I/ℏ = ρ t`,

so the entropic clock reads the dimensionless **e-fold count** of whatever rate drives the
dissipation.  That is the form in which every invariance already proved applies —
`herglotz_efolds_lorentz_invariant` (boosts), `crossing_calibration_scaling_invariant` (heating),
`mpemba_crossing_self_calibrates` ("a pure number, unit-free and clock-free") — and it contains no
`ℏ` at all.

The measurable consequence
--------------------------
An exponentially relaxing amplitude `A t = A₀ e^{−ρ t}` satisfies

  `log (A₀ / A t) = ρ t = τ_ent t`,

so **the entropic clock reading is the log of an amplitude ratio** — read straight off a decay trace,
with no absolute clock, no calibrated units, and no `ℏ`.  This is what makes the entropic-clock
content testable on a classical bench: a PT-symmetric LRC dimer, where the loss and gain rates are
independently tunable and `γ_eff = γ_loss − γ_gain` is the ringdown envelope, realizes
`MaterialTimescales.EffectiveDampingDecomposition` directly, and its ringdown *is* the entropic
clock.

What this does and does not replace
-----------------------------------
It replaces the `ℏ`-laden *presentation* of the clock, not its content: `τ_ent = ρ t` is what
`τ_ent = S_I/ℏ` reduces to under the linear accumulation `S_I = ℏ ρ t` that the Lindblad
instantiation already supplies (`ofLindbladJump`, `S_I_along t = 2⟨ψ, H_I ψ⟩ t`).  What it does not
do is make the *Compton anchor* classical: fixing the clock's rate to `ω₀ = m c²/ℏ` is a separate,
genuinely quantum identification, and `ComptonAnchorCoherenceTime` shows what that costs.  A bench
experiment tests the clock's structure — invariance, self-calibration, the rate-gap readout — not
the anchoring of its unit.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Optics.EntropicEfoldReadout

open Physlib.Thermodynamics.SecondLaw

/-! ### §A — The `ℏ` cancels -/

/-- The dimensionless e-fold count accumulated at entropic rate `ρ` over duration `t`. -/
def entropicEfolds (rho t : ℝ) : ℝ := rho * t

/-- **The entropic clock reads e-folds, with no `ℏ` left in it.**  Under the linear accumulation
`S_I = ℏ ρ t` — the form `ofLindbladJump` supplies and `herglotz_efolds_lorentz_invariant` names —
the defining identity `τ_ent = S_I/ℏ` collapses to the e-fold count.  The action quantum appears on
both sides and cancels. -/
theorem tau_ent_eq_efolds (W : EntropyArrowWorldline) (rho t : ℝ)
    (hlin : W.S_I_along t = W.ℏ * (rho * t)) :
    W.τ_ent_along t = entropicEfolds rho t := by
  rw [W.τ_ent_eq t, hlin]
  unfold entropicEfolds
  field_simp [W.ℏ_pos.ne']

/-! ### §B — E-folds are a log amplitude ratio -/

/-- An exponentially relaxing amplitude at rate `ρ`. -/
def relaxingAmplitude (A₀ rho t : ℝ) : ℝ := A₀ * Real.exp (-(rho * t))

/-- **The clock reading is the log of an amplitude ratio.**  For an exponentially relaxing
amplitude, `log(A₀ / A t)` is exactly the accumulated e-fold count, hence exactly the entropic
clock's reading.  No absolute clock, no calibrated unit and no `ℏ` enters — which is what makes the
reading available on a bench oscilloscope. -/
theorem log_amplitude_ratio_eq_efolds {A₀ : ℝ} (hA : A₀ ≠ 0) (rho t : ℝ) :
    Real.log (A₀ / relaxingAmplitude A₀ rho t) = entropicEfolds rho t := by
  unfold relaxingAmplitude entropicEfolds
  rw [div_mul_eq_div_div, div_self hA, one_div, ← Real.exp_neg, Real.log_exp]
  ring

/-- **Rate scaling and time dilation cancel in the reading.**  Scaling the rate by `c` and the
duration by `1/c` leaves the e-fold count fixed — the same invariance
`herglotz_efolds_lorentz_invariant` states for boosts and
`crossing_calibration_scaling_invariant` for heating, here in the readout variable itself. -/
theorem efolds_scaling_invariant (rho t c : ℝ) (hc : c ≠ 0) :
    entropicEfolds (c * rho) (t / c) = entropicEfolds rho t := by
  unfold entropicEfolds
  field_simp

/-! ### §C — What a classical bench then measures

With `τ_ent = ρ t` read as `log(A₀/A t)`, the entropic clock is available wherever an exponential
decay is: the ringdown of a resonator, the relaxation of a driven mode, the two branches of a
PT-symmetric dimer.  `MaterialTimescales.EffectiveDampingDecomposition`'s `γ_eff = γ_Drude − β` is
then the difference of two such rates, and `MpembaCrossingReadsEffectiveDamping` reads it off the
crossing of the two log-amplitude traces — the measurement that has no optical counterpart because
there the two rates cannot be varied independently. -/

/-- **The difference of two e-fold counts is the gap times the duration.**  Two branches relaxing at
different rates separate in log-amplitude at exactly the rate gap, which is why the crossing of the
two traces reads `γ_eff` and why only the *difference* is needed. -/
theorem efolds_difference_eq_gap_mul (rho₁ rho₂ t : ℝ) :
    entropicEfolds rho₁ t - entropicEfolds rho₂ t = (rho₁ - rho₂) * t := by
  unfold entropicEfolds
  ring

/- ZIL-BEGIN -/

zil attach Physlib.Optics.EntropicEfoldReadout.tau_ent_eq_efolds where
  formalizes @ "claim:under-linear-accumulation-of-the-imaginary-action-at-a-fixed-rate-the-entropic-clock-reading-reduces-to-the-dimensionless-e-fold-count-and-the-action-quantum-cancels-so-the-clock-carries-no-planck-constant",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.herglotz_efolds_lorentz_invariant",
  caveat @ "the-linear-accumulation-is-a-hypothesis-supplied-per-worldline-it-is-what-the-lindblad-jump-instantiation-gives-but-it-is-not-forced-by-the-entropy-arrow-structure-alone"

zil attach Physlib.Optics.EntropicEfoldReadout.log_amplitude_ratio_eq_efolds where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.crossing_calibration_scaling_invariant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.herglotz_efolds_lorentz_invariant",
  formalizes @ "claim:for-an-exponentially-relaxing-amplitude-the-logarithm-of-the-initial-to-current-amplitude-ratio-is-exactly-the-entropic-clock-reading-so-the-clock-is-measurable-as-a-log-amplitude-ratio-with-no-absolute-clock-no-calibrated-unit-and-no-planck-constant",
  epistemic_status @ "consistency-identity",
  requires @ "claim:under-linear-accumulation-of-the-imaginary-action-at-a-fixed-rate-the-entropic-clock-reading-reduces-to-the-dimensionless-e-fold-count-and-the-action-quantum-cancels-so-the-clock-carries-no-planck-constant",
  caveat @ "this-makes-the-clock-structure-benchtop-accessible-it-does-not-make-the-compton-anchoring-of-the-clock-rate-classical-that-identification-remains-quantum-and-carries-its-own-coherence-cost"

zil attach Physlib.Optics.EntropicEfoldReadout.efolds_scaling_invariant where
  formalizes @ "claim:the-e-fold-reading-is-unchanged-when-the-rate-is-scaled-and-the-duration-inversely-scaled-which-is-the-boost-and-heating-invariance-of-the-entropic-clock-expressed-in-the-readout-variable",
  epistemic_status @ "consistency-identity"

zil_file_contract physlib.entropicEfoldReadout where
  promises "The entropy-arrow clock is defined by entropic time equals imaginary action over the action quantum, which makes it appear to need a quantum system. It does not. Under the linear accumulation in which the imaginary action is the action quantum times a rate times a duration, the form the Lindblad-jump instantiation supplies and the Herglotz e-fold invariance names, the action quantum cancels and the clock reads the dimensionless e-fold count of the dissipative rate. Every invariance already proved applies in that variable: boosts, heating rescalings, and the unit-free clock-free self-calibration of the Mpemba crossing. The measurable consequence is that for an exponentially relaxing amplitude the logarithm of the initial to current amplitude ratio equals the clock reading exactly, so the entropic clock is read off a decay trace with no absolute clock, no calibrated unit and no Planck constant, and the difference of two such readings is the rate gap times the duration, which is why the crossing of two log-amplitude traces reads the effective damping. This makes the clock structure accessible on a classical bench such as a PT-symmetric resonator pair whose loss and gain rates are independently tunable. It does not make the Compton anchoring of the clock rate classical: fixing the rate to the Compton frequency is a separate quantum identification carrying its own coherence cost."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Thermodynamics.SecondLaw.EntropyArrowWorldline",
    "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.herglotz_efolds_lorentz_invariant",
    "lean:Physlib.Optics.MpembaCrossingReadsEffectiveDamping.gammaEff_mul_crossingTime",
    "lean:Physlib.Optics.MaterialTimescales.EffectiveDampingDecomposition"]
  forbids_substitutes ["reading the e-fold form as making the Compton anchoring of the clock rate classical, when that identification stays quantum and carries the coherence cost of the anchor",
    "treating the linear accumulation of the imaginary action as forced by the entropy-arrow structure rather than supplied per worldline",
    "presenting a classical ringdown as a test of the entropic identification itself rather than of the clock structure it shares"]
  witnessed_by [Physlib.Optics.EntropicEfoldReadout.tau_ent_eq_efolds,
    Physlib.Optics.EntropicEfoldReadout.log_amplitude_ratio_eq_efolds,
    Physlib.Optics.EntropicEfoldReadout.efolds_scaling_invariant,
    Physlib.Optics.EntropicEfoldReadout.efolds_difference_eq_gap_mul]

/- ZIL-END -/

end Physlib.Optics.EntropicEfoldReadout

end
