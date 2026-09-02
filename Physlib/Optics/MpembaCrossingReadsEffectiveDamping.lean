/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Optics.MaterialTimescales
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz

meta import Zil

/-!
# The Mpemba crossing reads the effective damping

`MaterialTimescales.EffectiveDampingDecomposition` carries Pendry's
`γ_eff = γ_Drude − β`, and the whole ENZ arc hangs on it.  It has never been measured: every
input is an equilibrium property, a model output, or a fitted timescale, and the one anchor that
claimed to measure a non-Hermitian rate turned out to be an analytic band structure (corrected in
`MaterialTimescales`).  The obstruction is that `γ_eff ≈ 10¹⁴ s⁻¹` demands either femtosecond
timing or a linewidth fit on a *pumped* film.

The Mpemba layer removes that obstruction, because `γ_eff` is a **rate gap** and the Mpemba
crossing measures exactly a rate gap — without a calibrated clock.

`SciamaAdSCPTQuantumMpembaCrossing.mpembaCrossingTime a b lam₂ lam₃ = log(a/b)/(lam₂ − lam₃)` is
the time at which two exponentially relaxing amplitudes cross, and
`mpemba_crossing_self_calibrates` states the crossing's defining property: the product
`(lam₂ − lam₃) · t*` equals `log(a/b)`, a pure number fixed by the **preparation amplitudes
alone**.  Identifying `lam₂ = γ_Drude` (the loss branch) and `lam₃ = β` (the gain branch) makes
that gap literally `γ_eff`, so:

  `γ_eff · t* = log(a/b)`

Measuring the crossing time `t*` and the prepared amplitude ratio `a/b` therefore yields `γ_eff`
with no absolute rate measurement, no femtosecond timing, and no model inversion — the quantity is
read off a ratio and a single event.

The regime is visible in the *sign*.  In the decay mode (`γ_eff > 0`) a crossing occurs at
positive time; in the gain mode (`γ_eff < 0`) the crossing time is negative, i.e. no crossing
happens in the future.  So **whether a crossing is observed at all** is the gain/decay regime
indicator that `ITOAvalancheCase`'s five pump instances predict but which no visibility
measurement can supply — visibility being blind to common gain, and a model-class mismatch in a
photon-conserving regime.

Experimentally this is not far off.  Galiffi et al. already excite both branches at once —
counterpropagating probes select "both gain and loss mode", with the relative weight set by the
Ancilla-to-Signal intensity ratio and the relative phase.  That is the `a/b` of the crossing.  What
is missing from the published work is a time-resolved readout of the two amplitudes, not a new
apparatus.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Optics.MpembaCrossingReadsEffectiveDamping

open Physlib.Optics.MaterialTimescales
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz

variable (D : EffectiveDampingDecomposition)

/-! ### §A — The effective damping is the Mpemba rate gap -/

/-- **The loss/gain crossing time is `log(a/b)/γ_eff`.**  Taking the Drude branch as the slow rate
and the avalanche branch as the fast one, the Mpemba crossing time of the two amplitudes is set by
the effective damping. -/
theorem crossingTime_eq_log_div_gammaEff (a b : ℝ) :
    mpembaCrossingTime a b D.γ_Drude_inv_s D.β_inv_s
      = Real.log (a / b) / D.γ_eff_inv_s := by
  unfold mpembaCrossingTime
  rw [D.decomp]

/-- **The crossing reads `γ_eff` without a calibrated clock.**  The rate-gap × duration product at
the crossing is the differential e-fold count of the preparation, a pure number.  Measuring `t*`
and the prepared ratio `a/b` therefore determines `γ_eff` directly. -/
theorem gammaEff_mul_crossingTime (a b : ℝ) (hne : D.γ_Drude_inv_s ≠ D.β_inv_s) :
    D.γ_eff_inv_s * mpembaCrossingTime a b D.γ_Drude_inv_s D.β_inv_s = Real.log (a / b) := by
  rw [D.decomp]
  exact mpemba_crossing_self_calibrates a b hne

/-! ### §B — The regime shows in the sign of the crossing time -/

/-- **A crossing at positive time means the decay mode.**  For a preparation with `a > b > 0` the
crossing time is positive exactly when the effective damping is positive, i.e. exactly in the decay
regime. -/
theorem crossingTime_pos_iff_isDecayMode {a b : ℝ} (hab : b < a) (hb : 0 < b) :
    0 < mpembaCrossingTime a b D.γ_Drude_inv_s D.β_inv_s ↔ IsDecayMode D := by
  have hlog : 0 < Real.log (a / b) := Real.log_pos ((one_lt_div hb).mpr hab)
  rw [crossingTime_eq_log_div_gammaEff]
  unfold IsDecayMode
  exact div_pos_iff_of_pos_left hlog

/-- **In the gain mode no crossing lies in the future.**  With `a > b > 0` a gain-mode
decomposition puts the crossing at negative time: the amplitudes have already separated and never
cross again.  Observing whether a crossing occurs is therefore the regime indicator. -/
theorem crossingTime_neg_of_isGainMode {a b : ℝ} (hab : b < a) (hb : 0 < b)
    (hg : IsGainMode D) :
    mpembaCrossingTime a b D.γ_Drude_inv_s D.β_inv_s < 0 := by
  have hlog : 0 < Real.log (a / b) := Real.log_pos ((one_lt_div hb).mpr hab)
  rw [crossingTime_eq_log_div_gammaEff]
  exact div_neg_of_pos_of_neg hlog hg

/-! ### §C — Equal preparation carries no information

The crossing degenerates when the two branches are prepared equally: with `a = b` the differential
e-fold count vanishes and the crossing sits at the origin whatever the rates are.  The measurement
therefore requires an *asymmetric* preparation, which is what the Ancilla-to-Signal ratio supplies. -/

/-- **Equal amplitudes give no leverage.**  At `a = b` the crossing time is zero independently of
the rates, so a symmetric preparation determines nothing about `γ_eff`. -/
theorem crossingTime_at_equal_amplitudes {a : ℝ} (ha : a ≠ 0) :
    mpembaCrossingTime a a D.γ_Drude_inv_s D.β_inv_s = 0 := by
  unfold mpembaCrossingTime
  rw [div_self ha, Real.log_one, zero_div]

/-! ### §D — The readout is licensed by the MECHANISM, and one preparation cannot test it

Ghosh, Pathak, Chatterjee & Das (arXiv:2407.06954) classify the Mpemba effect by what drives it,
and find at least two mechanisms that are not the spectral one used above: in TIP4P/Ice water
"delay in nucleation, due to metastability, can alone be a driving factor", while in Lennard-Jones
and Ising systems "the ME appears purely as an outcome of the influence of critical fluctuations on
the nonequilibrium growth process" — the effect occurring "in absence of metastability as well".

So the observable — a hotter preparation relaxing first — does **not** identify the mechanism, and
the identification `γ_eff = λ₂ − λ₃` above is licensed only by the spectral one.  Observing a
crossing is therefore not sufficient to read `γ_eff` off it.

What distinguishes the spectral mechanism is a *law*: `t* = log(a/b)/γ_eff` is log-linear in the
preparation ratio with a slope fixed across preparations.  Nucleation induction times and
critical-fluctuation scaling produce no such relation.  §D makes that testable and records why a
single measurement cannot do it. -/

/-- The crossing time predicted by the spectral mechanism at preparation ratio `r`. -/
def spectralCrossingTime (gap r : ℝ) : ℝ := Real.log r / gap

/-- **A single preparation cannot test the mechanism.**  For any observed crossing time at any
ratio, some gap reproduces it exactly — one equation in one unknown.  So a single measured crossing
fits the spectral law automatically and falsifies nothing, which is the same
two-parameters-on-two-points trap that defeated the earlier visibility fits. -/
theorem single_preparation_underdetermines {r t : ℝ} (hlog : Real.log r ≠ 0) :
    spectralCrossingTime (Real.log r / t) r = t := by
  unfold spectralCrossingTime
  field_simp

/-- **Two preparations give a parameter-free consistency condition.**  Under the spectral law the
crossing times at two ratios satisfy `t*(r₁) · log r₂ = t*(r₂) · log r₁` — a cross-ratio identity
with the gap eliminated.  Failing it refutes the spectral mechanism without needing to know
`γ_eff`; passing it is the evidence that licenses reading `γ_eff` off either measurement. -/
theorem spectral_crossing_cross_ratio (gap r₁ r₂ : ℝ) :
    spectralCrossingTime gap r₁ * Real.log r₂ = spectralCrossingTime gap r₂ * Real.log r₁ := by
  unfold spectralCrossingTime
  ring

/-- **The gap is then overdetermined.**  Given the cross-ratio consistency, either preparation
returns the same gap, so a third measurement is a genuine check rather than a further fit — the
design that the earlier two-point analyses lacked. -/
theorem gap_from_crossing (gap r : ℝ) (hgap : gap ≠ 0) (hlog : Real.log r ≠ 0) :
    Real.log r / spectralCrossingTime gap r = gap := by
  unfold spectralCrossingTime
  field_simp

/- ZIL-BEGIN -/

zil attach Physlib.Optics.MpembaCrossingReadsEffectiveDamping.gammaEff_mul_crossingTime where
  formalizes @ "claim:the-effective-drude-bender-damping-is-a-rate-gap-so-the-mpemba-crossing-of-the-loss-and-gain-branches-reads-it-off-the-preparation-amplitude-ratio-and-the-crossing-time-without-a-calibrated-clock-or-an-absolute-rate-measurement",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.mpemba_crossing_self_calibrates",
  requires @ "claim:the-pendry-effective-damping-decomposition-writes-the-effective-rate-as-the-equilibrium-drude-rate-minus-the-avalanche-rate",
  caveat @ "the-identification-of-the-two-mpemba-branches-with-the-drude-loss-and-avalanche-gain-modes-is-an-operational-modelling-choice-and-the-crossing-has-not-been-measured-in-any-epsilon-near-zero-experiment"

zil attach Physlib.Optics.MpembaCrossingReadsEffectiveDamping.crossingTime_pos_iff_isDecayMode where
  supported_by @ "lean:Physlib.Optics.MpembaCrossingReadsEffectiveDamping.crossingTime_eq_log_div_gammaEff",
  formalizes @ "claim:for-an-asymmetric-preparation-the-mpemba-crossing-lies-at-positive-time-exactly-in-the-decay-regime-so-whether-a-crossing-is-observed-at-all-indicates-the-gain-decay-regime",
  epistemic_status @ "conditional-model",
  caveat @ "this-is-a-sign-criterion-on-the-effective-damping-it-does-not-by-itself-supply-the-magnitude-and-it-assumes-the-two-branches-relax-exponentially-with-the-quoted-rates"

zil attach Physlib.Optics.MpembaCrossingReadsEffectiveDamping.single_preparation_underdetermines where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:a-single-measured-crossing-fits-the-spectral-law-automatically-since-some-gap-reproduces-any-observed-time-so-one-preparation-falsifies-nothing-and-cannot-establish-the-mechanism",
  epistemic_status @ "consistency-identity",
  caveat @ "this-is-the-honesty-constraint-on-the-readout-not-a-physical-limitation-of-the-crossing-itself"

zil attach Physlib.Optics.MpembaCrossingReadsEffectiveDamping.spectral_crossing_cross_ratio where
  formalizes @ "claim:under-the-spectral-mechanism-two-preparations-satisfy-a-cross-ratio-identity-with-the-gap-eliminated-so-failing-it-refutes-the-spectral-reading-without-knowing-the-effective-damping-and-passing-it-licenses-the-readout",
  epistemic_status @ "conditional-model",
  caveat @ "the-mpemba-effect-also-arises-from-metastable-nucleation-delay-and-from-critical-fluctuations-ghosh-et-al-2024-so-observing-a-crossing-does-not-by-itself-identify-the-spectral-mechanism"

zil_file_contract physlib.mpembaCrossingReadsEffectiveDamping where
  promises "The Pendry effective damping is a difference of two rates, and the Mpemba crossing measures exactly a difference of two rates, so the crossing reads the effective damping. Identifying the slow Mpemba branch with the equilibrium Drude loss rate and the fast branch with the avalanche gain rate makes the crossing time the logarithm of the preparation amplitude ratio divided by the effective damping, and the self-calibration property of the crossing then gives the effective damping times the crossing time as that pure logarithm, fixed by the preparation amplitudes alone. So the effective damping is obtained from a ratio and a single timed event, with no absolute rate measurement, no femtosecond timing and no model inversion, which is what has blocked every other route. The regime appears in the sign: for an asymmetric preparation the crossing lies at positive time exactly in the decay regime, and in the gain regime the crossing time is negative so no crossing occurs in the future, making the presence or absence of a crossing the regime indicator that fringe visibility cannot supply. A symmetric preparation is degenerate and determines nothing, so the measurement needs an asymmetric one."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Optics.MaterialTimescales.EffectiveDampingDecomposition",
    "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTQuantumMpembaCrossing.mpembaCrossingTime",
    "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMpembaNewtonObstructionHerglotz.mpemba_crossing_self_calibrates",
    "lean:Physlib.Optics.MaterialTimescales.IsGainMode"]
  forbids_substitutes ["presenting the crossing as a measured anchor for the effective damping rather than as the measurement that would supply one",
    "treating the identification of the Mpemba branches with the Drude and avalanche modes as derived rather than as an operational modelling choice",
    "using a symmetric preparation, where the crossing time vanishes identically and carries no information about the rates"]
  witnessed_by [Physlib.Optics.MpembaCrossingReadsEffectiveDamping.single_preparation_underdetermines,
    Physlib.Optics.MpembaCrossingReadsEffectiveDamping.spectral_crossing_cross_ratio,
    Physlib.Optics.MpembaCrossingReadsEffectiveDamping.gap_from_crossing,
    Physlib.Optics.MpembaCrossingReadsEffectiveDamping.crossingTime_eq_log_div_gammaEff,
    Physlib.Optics.MpembaCrossingReadsEffectiveDamping.gammaEff_mul_crossingTime,
    Physlib.Optics.MpembaCrossingReadsEffectiveDamping.crossingTime_pos_iff_isDecayMode,
    Physlib.Optics.MpembaCrossingReadsEffectiveDamping.crossingTime_neg_of_isGainMode,
    Physlib.Optics.MpembaCrossingReadsEffectiveDamping.crossingTime_at_equal_amplitudes]

/- ZIL-END -/

end Physlib.Optics.MpembaCrossingReadsEffectiveDamping

end
