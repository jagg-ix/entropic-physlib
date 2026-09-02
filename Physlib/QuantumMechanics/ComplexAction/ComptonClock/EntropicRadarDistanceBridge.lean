/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
public import Physlib.QuantumMechanics.RelationalTime.SignalDelayCausalReach

meta import Zil

/-!
# The bridge test: entanglement fixes a round-trip time

`analysis/empirical-discrimination-plan.md` §12 records why sector-by-sector testing is the wrong
test for a unification, and that CAT/EPT's discriminating content is **cross-sector**: a quantity
fixed on one side constraining the other.  This module writes that test down for the sharpest
available pair, because both determinations already exist in the library and neither is built from
the other.

**The two determinations, and their independence.**

* `RelationalTime.radarDistance T c = cT/2` — purely **operational**: bounce a signal, read the
  round-trip time on a local clock.  No entanglement quantity enters its definition.
* `ComptonClock.EntropicProperDistance.entropicProperDistance m c ħ η = λ_C · log K`,
  `K = coth η` — **derived**, from the vacuum-correlation decay.  No geometric measurement enters
  its definition.

That independence is the whole point: §9 killed T1–T5 because their "second route" turned out to be
constructed from the first, and T3/T5 because the operating point was chosen from the answer.  Here
the two sides genuinely come from different physics.

**The claim under test.**  `EntropicProperDistance`'s own docstring says the entropic distance is
"not operational but *derived*", offered as a principled replacement for Szabados' operational
empirical distance.  Equating it with the radar distance is therefore a **substantive claim**, not a
definition — exactly the shape a unification's content should have.  §A puts it in falsifiable form:

  `radarDistance T c = entropicProperDistance m c ħ η  ↔  T = 2ħ·log K/(mc²)`.

So **the entanglement of the vacuum between two regions predicts the round-trip light time between
them**, with no free parameter once the field's mass is fixed.  Nothing in quantum mechanics alone
says a Schmidt number sets a light-travel time; nothing in relativity alone knows about `K`.

**What this is not.**  `entropicProperDistance` is a *vacuum* correlation scale, not the separation
of a prepared entangled pair.  Laboratory Bell pairs at kilometre separations with `K = 2` therefore
do **not** refute it — a reading that looks decisive and is wrong.  The relevant experimental setting
is vacuum entanglement between spacelike regions (entanglement harvesting), where the detector
separation is operational and the harvested entanglement gives `K`.

Scope.  What is proved is the equivalence of §A — the exact condition under which the two
determinations agree, written so that a measured pair `(T, K)` either satisfies it or does not.  That
the entropic distance *is* the physical separation is the claim being tested, not an input; and which
mass sets `λ_C` for a given field is a modelling choice this module does not make.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicRadarDistanceBridge

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.RelationalTime

/-! ### §A — the two determinations agree exactly on one round-trip time -/

/-- **The round-trip time the entanglement predicts.**  Setting the operational radar distance equal
to the derived entropic distance fixes the round-trip clock reading at `2ħ log K/(mc²)` — the Compton
time times twice the log Schmidt number.

This is the bridge in falsifiable form: the left side is measured with a clock and a signal, the
right side with state tomography, and the equivalence says a measured pair either satisfies it or
refutes the identification. -/
theorem radarDistance_eq_entropicProperDistance_iff {T m c ħ η : ℝ}
    (hc : c ≠ 0) (hm : m ≠ 0) :
    radarDistance T c = entropicProperDistance m c ħ η
      ↔ T = 2 * ħ * Real.log (schmidtNumber η) / (m * c ^ 2) := by
  unfold radarDistance entropicProperDistance comptonWavelength
  constructor
  · intro h
    field_simp at h ⊢
    linarith [h]
  · intro h
    rw [h]
    field_simp

/-- **The predicted time is the Compton time scaled by the entanglement.**  Writing the same
condition through the Compton frequency `ω_C = mc²/ħ` makes the content visible: the round trip takes
`2 log K` Compton periods, so the entanglement is read directly as a clock count. -/
theorem bridge_time_eq_two_log_schmidt_comptonTimes {m c ħ η : ℝ}
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    2 * ħ * Real.log (schmidtNumber η) / (m * c ^ 2)
      = 2 * Real.log (schmidtNumber η) / comptonFrequency m c ħ := by
  unfold comptonFrequency
  field_simp

/-! ### §B — the separable point -/

/-- **No entanglement, no separation.**  At `K = 1` — the separable point, `S_I = 0` — the predicted
round-trip time is zero: the derived distance vanishes exactly when the vacuum correlation carries no
entanglement suppression.  A nonzero measured separation between regions whose harvested state is
separable therefore falsifies the identification outright. -/
theorem bridge_time_zero_of_separable {m c ħ η : ℝ} (hK : schmidtNumber η = 1) :
    2 * ħ * Real.log (schmidtNumber η) / (m * c ^ 2) = 0 := by
  rw [hK, Real.log_one]
  ring

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicRadarDistanceBridge.radarDistance_eq_entropicProperDistance_iff where
  formalizes @ "claim:the-vacuum-entanglement-between-two-regions-predicts-the-operational-round-trip-light-time-between-them-as-twice-the-log-schmidt-number-in-compton-periods",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.radarDistance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance",
  experimental_bound @ "value:no-measurement-yet-relates-harvested-vacuum-entanglement-to-detector-separation-at-the-compton-scale;test:entanglement-harvesting-between-spacelike-regions-at-operationally-measured-separation-must-return-a-schmidt-number-satisfying-r-equals-compton-wavelength-times-log-k-which-for-an-electron-field-puts-k-equals-two-at-about-two-point-seven-times-ten-to-the-minus-thirteen-metres",
  caveat @ "the-entropic-distance-is-a-vacuum-correlation-scale-not-the-separation-of-a-prepared-pair-so-laboratory-bell-pairs-at-kilometre-separations-with-schmidt-number-two-do-not-refute-it-and-which-mass-sets-the-compton-wavelength-for-a-given-field-is-a-modelling-choice-not-fixed-here"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicRadarDistanceBridge

end
