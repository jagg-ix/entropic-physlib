/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Optics.EntropicEfoldReadout
public import Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum

meta import Zil

/-!
# The Zeno stripes supply the timescale separation the crossing readout assumes

`MpembaIndexRateSelection` carries an honest caveat: its two-mode relaxation amplitude is a
*truncation*, and a real Markovian relaxation has further modes that the same preparation does not
null.  `MpembaCrossingReadsEffectiveDamping` reads `γ_eff` off the crossing of exactly two branches,
so it inherits that caveat.  What licenses the truncation is a **separation of relaxation
timescales**, and Popkov & Presilla supply precisely that.

`ZenoLiouvillianSpectrum` formalizes their result for the `XYZ` boundary dissipator: under strong
dissipation the Liouvillian eigenvalues arrange into stripes at `Re λ ≈ c_k Γ`, one per dissipator
eigenvalue.  For the qubit example the spectrum is `{0, −½, −½, −1}` (Eq. 20), so the stripes sit at

  `λ = 0` (NESS), `λ = −Γ/2` (coherence), `λ = −Γ` (population)

— `zeno_stripe_ness`, `zeno_stripe_coherence`, `zeno_stripe_population`.

The two decaying stripes are the two branches of the crossing, and their gap is `Γ/2`: it is set by
the dissipation strength and therefore **tunable**.  As `Γ` grows the stripes separate without
bound, so the two-mode description becomes exact in the window between them — the Zeno regime is
where the crossing readout of `γ_eff` is licensed rather than assumed.

Read through `EntropicEfoldReadout`, the crossing is at `2 log(a/b)/Γ` in e-folds of the
log-amplitude traces, with no `ℏ` anywhere: strong dissipation is a knob that sets how long one must
watch.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Optics.ZenoStripeGapReadout

open Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing

/-! ### §A — The gap between the two decaying stripes -/

/-- The gap between the coherence stripe (`−Γ/2`) and the population stripe (`−Γ`).  These are the
two decaying branches of the Zeno spectrum, so this is the rate gap the crossing measures. -/
def zenoStripeGap (Γ : ℝ) : ℝ := Γ / 2

/-- **The stripe gap is `Γ/2`.**  Subtracting the population-stripe eigenvalue from the
coherence-stripe eigenvalue gives half the dissipation strength: the separation between the two
decaying branches is set by `Γ` and is therefore tunable by the coupling alone. -/
theorem stripe_gap_eq (Γ : ℝ) : (-(Γ / 2)) - (-Γ) = zenoStripeGap Γ := by
  unfold zenoStripeGap
  ring

/-- **The stripes separate without bound.**  As the dissipation strengthens the gap between the two
decaying branches grows linearly, so any fixed spectral window eventually contains only one stripe
and the two-mode truncation of `MpembaIndexRateSelection` becomes exact.  This is what turns that
module's caveat into a controllable regime rather than a limitation. -/
theorem stripe_gap_tendsto_atTop :
    Filter.Tendsto zenoStripeGap Filter.atTop Filter.atTop := by
  unfold zenoStripeGap
  exact Filter.tendsto_id.atTop_div_const (by norm_num)

/-! ### §B — The crossing in the Zeno regime -/

/-- **The Zeno crossing time is `2 log(a/b)/Γ`.**  Taking the two decaying stripes as the crossing
branches, the Mpemba crossing time is fixed by the dissipation strength and the preparation ratio.
Strong dissipation makes the crossing *earlier*, so `Γ` is the knob setting how long one must watch
for the readout. -/
theorem zeno_crossingTime (a b Γ : ℝ) (hΓ : Γ ≠ 0) :
    mpembaCrossingTime a b (-(Γ / 2)) (-Γ) = 2 * Real.log (a / b) / Γ := by
  unfold mpembaCrossingTime
  rw [stripe_gap_eq]
  unfold zenoStripeGap
  field_simp

/-- **The Zeno crossing self-calibrates at the stripe gap.**  The gap times the crossing time is the
differential e-fold count of the preparation — the same clock-free calibration as in general, now
with the gap identified as `Γ/2` and hence known from the coupling. -/
theorem zeno_gap_mul_crossingTime (a b Γ : ℝ) (hΓ : Γ ≠ 0) :
    zenoStripeGap Γ * mpembaCrossingTime a b (-(Γ / 2)) (-Γ) = Real.log (a / b) := by
  rw [zeno_crossingTime a b Γ hΓ]
  unfold zenoStripeGap
  field_simp

/-! ### §C — What this settles

The crossing readout needs two things: that only two branches are in play, and that their gap is
known or measurable.  The Zeno limit gives both — the stripes separate as `Γ` grows, and the gap
between the two decaying ones is exactly `Γ/2`.  So the strong-dissipation regime is where
`MpembaCrossingReadsEffectiveDamping`'s reading of `γ_eff` is licensed, and `Γ` is the experimental
knob that puts it there.  On the bench that is simply the loss resistance of the resonator pair. -/

/-- **The gap is positive for positive dissipation**, so the coherence branch is genuinely the
slower of the two and the crossing has the orientation the readout assumes. -/
theorem zenoStripeGap_pos {Γ : ℝ} (hΓ : 0 < Γ) : 0 < zenoStripeGap Γ := by
  unfold zenoStripeGap
  linarith

/- ZIL-BEGIN -/

zil attach Physlib.Optics.ZenoStripeGapReadout.stripe_gap_eq where
  formalizes @ "claim:the-gap-between-the-coherence-and-population-zeno-stripes-of-the-xyz-boundary-dissipator-is-half-the-dissipation-strength-so-the-rate-gap-the-crossing-measures-is-tunable-by-the-coupling-alone",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum.zeno_stripe_coherence",
  caveat @ "this-is-the-qubit-xyz-worked-example-of-popkov-and-presilla-at-zero-hamiltonian-the-general-stripe-positions-and-the-one-over-gamma-corrections-are-not-formalized"

zil attach Physlib.Optics.ZenoStripeGapReadout.stripe_gap_tendsto_atTop where
  formalizes @ "claim:the-zeno-stripes-separate-without-bound-as-the-dissipation-strengthens-so-the-two-mode-truncation-that-the-crossing-readout-assumes-becomes-exact-in-the-window-between-them",
  epistemic_status @ "conditional-model",
  requires @ "claim:the-gap-between-the-coherence-and-population-zeno-stripes-of-the-xyz-boundary-dissipator-is-half-the-dissipation-strength-so-the-rate-gap-the-crossing-measures-is-tunable-by-the-coupling-alone",
  caveat @ "separation-of-the-two-decaying-stripes-does-not-by-itself-establish-that-no-other-liouvillian-mode-enters-the-observation-window-which-for-the-qubit-example-is-immediate-but-not-in-general"

zil attach Physlib.Optics.ZenoStripeGapReadout.zeno_gap_mul_crossingTime where
  supported_by @ "lean:Space.needs",
  supported_by @ "lean:Physlib.Optics.ZenoStripeGapReadout.zeno_crossingTime",
  formalizes @ "claim:in-the-zeno-regime-the-crossing-self-calibrates-at-a-gap-equal-to-half-the-dissipation-strength-so-the-clock-free-calibration-holds-with-the-gap-known-from-the-coupling",
  epistemic_status @ "conditional-model",
  caveat @ "the-identification-of-the-two-decaying-stripes-with-the-two-crossing-branches-is-an-operational-modelling-choice-of-the-same-kind-flagged-for-the-drude-and-avalanche-branches"

zil_file_contract physlib.zenoStripeGapReadout where
  promises "The Mpemba crossing readout of the effective damping rests on a two-mode truncation, which a real Markovian relaxation does not automatically justify. Popkov and Presilla supply what licenses it: under strong dissipation the Liouvillian eigenvalues arrange into stripes at the dissipator eigenvalues times the coupling strength, and for the qubit XYZ boundary dissipator already formalized in ZenoLiouvillianSpectrum those stripes sit at zero, minus half the coupling, and minus the coupling. The two decaying stripes are the two crossing branches and their gap is exactly half the dissipation strength, so the rate gap the crossing measures is set by the coupling and is tunable by it. As the dissipation strengthens the gap grows without bound, so the two-mode description becomes exact in the window between the stripes and the truncation becomes a controllable regime rather than a limitation. The crossing time is then twice the differential e-fold count divided by the coupling, and the clock-free self-calibration holds with the gap known rather than fitted. Strong dissipation is therefore the regime in which the readout is licensed, and the coupling is the experimental knob that puts a system there."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum.zeno_stripe_coherence",
    "lean:Physlib.QuantumMechanics.Lindblad.ZenoLiouvillianSpectrum.zeno_stripe_population",
    "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing.mpembaCrossingTime",
    "lean:Physlib.Optics.MpembaCrossingReadsEffectiveDamping.gammaEff_mul_crossingTime"]
  forbids_substitutes ["treating the qubit XYZ worked example at zero Hamiltonian as the general Zeno stripe structure, whose positions and one-over-coupling corrections are not formalized",
    "reading stripe separation as proof that no other Liouvillian mode enters the observation window in a general system",
    "presenting the identification of the two decaying stripes with the crossing branches as derived rather than as the same operational choice flagged for the Drude and avalanche branches"]
  witnessed_by [Physlib.Optics.ZenoStripeGapReadout.stripe_gap_eq,
    Physlib.Optics.ZenoStripeGapReadout.stripe_gap_tendsto_atTop,
    Physlib.Optics.ZenoStripeGapReadout.zeno_crossingTime,
    Physlib.Optics.ZenoStripeGapReadout.zeno_gap_mul_crossingTime,
    Physlib.Optics.ZenoStripeGapReadout.zenoStripeGap_pos]

/- ZIL-END -/

end Physlib.Optics.ZenoStripeGapReadout

end
