/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.Special.PhaseClock.Geometric
public import Physlib.Relativity.Special.PhaseClock.Relativistic
public import Physlib.SpaceAndTime.EntropicProperTime
public import Physlib.QuantumMechanics.FiniteTarget.EntropyControlledSchrodinger
public import Physlib.Thermodynamics.SecondLaw.ClausiusEntropyArrow

meta import Zil

/-!
# Entropic time ↔ oscillator phase clock agreement

Connects metric entropic time to the operational phase clock. The
claim is *not* "entropic time = geometric time"; it is the conditional: **given
a witness** that the dimensionally scaled relative-entropy gap equals the
oscillator-inferred proper time, entropic time equals the geometric (or lapse)
proper time. A frozen-limit recovery record closes the bridge.


## References

- **Kuchař 1992** — *Time and interpretations of quantum gravity*
- **Page & Wootters 1983** — *Evolution without evolution*
- **Rovelli 2011** — *Forget time*
-/

@[expose] public section

noncomputable section


open Physlib.Relativity.Special.PhaseClockGeometric Physlib.Relativity.Special.PhaseClockRelativistic
open Physlib.QuantumMechanics.Clock.Phase
open Physlib.SpaceTime
namespace Physlib.QuantumMechanics.Clock.EntropicAgreement

open QuantumInfo.Finite QuantumMechanics.FiniteTarget

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {sd : ℕ}

/-! ## A. Geometric agreement -/

/-- Witness that metric entropic time agrees with an oscillator clock over a
spacetime interval. -/
structure EntropicOscillatorClockAgreement
    (U : EntropicTimeUnits) (C : PhaseClock)
    (q p : SpaceTime sd) (ρ σ : MState d) where
  /-- The geometric phase witness. -/
  witness : OscillatorGeometricProperTimeWitness C q p
  /-- Entropic metric time equals the phase-derived time. -/
  entropic_equals_phase_time :
    entropicProperTimeMetric U ρ σ = C.properTimeFromPhase witness.phase

lemma EntropicOscillatorClockAgreement.entropic_equals_geometric
    (U : EntropicTimeUnits) (C : PhaseClock)
    (q p : SpaceTime sd) (ρ σ : MState d)
    (A : EntropicOscillatorClockAgreement U C q p ρ σ) :
    entropicProperTimeMetric U ρ σ = SpaceTime.properTime q p := by
  rw [A.entropic_equals_phase_time]
  exact A.witness.recovers_geometric_time C q p

/-! ## B. Static-lapse agreement -/

/-- Witness that metric entropic time equals the proper time read by an
oscillator at lapse `N(x)`. -/
structure EntropicLapseOscillatorAgreement
    (U : EntropicTimeUnits) (C : PhaseClock)
    (L : Lapse sd) (x : SpaceTime sd) (deltaT : ℝ) (ρ σ : MState d) where
  /-- The agreement condition. -/
  agreement :
    entropicProperTimeMetric U ρ σ =
      C.properTimeFromPhase (lapseOscillatorPhaseConstant C L x deltaT)

lemma EntropicLapseOscillatorAgreement.entropic_eq_lapse_proper_time
    (U : EntropicTimeUnits) (C : PhaseClock)
    (L : Lapse sd) (x : SpaceTime sd) (deltaT : ℝ) (ρ σ : MState d)
    (A : EntropicLapseOscillatorAgreement U C L x deltaT ρ σ) :
    entropicProperTimeMetric U ρ σ = lapseProperTimeConstant L x deltaT := by
  rw [A.agreement]
  exact lapsePhase_recovers_lapseProperTime C L x deltaT

/-! ## C. Operational identification of entropic and physical time

`EntropyArrowWorldline.τ_ent_along = S_I / ℏ` is dimensionless.  It is therefore
an accumulated *phase*, not a duration in seconds.  A positive-frequency phase
clock supplies the missing physical unit.  The following definition first takes
the change of the entropic phase, then applies the already independent
`PhaseClock.properTimeFromPhase`.

The load-bearing physical premise is kept separate:

`ΔS_I = ℏ * ω₀ * Δτ_phys`.

This is an action-rate calibration that can be tested against a clock.  It is
not an assumption that the two time readings are equal.  The equality is proved
below from this calibration, the defining entropy/action relation, and the
phase-clock inverse theorem.
-/

open Physlib.Thermodynamics.SecondLaw

/-- The physical duration read from the change in an entropy-arrow worldline's
dimensionless entropic phase. -/
def entropicPhysicalTimeAdvance
    (C : PhaseClock) (W : EntropyArrowWorldline) (t₁ t₂ : ℝ) : ℝ :=
  C.properTimeFromPhase (W.τ_ent_along t₂ - W.τ_ent_along t₁)

/-- A calibration of an entropy-producing clock against an independently
specified physical proper-time reading.

Only the imaginary-action accumulation rate is supplied.  In particular, this
record has no field asserting `entropicPhysicalTimeAdvance = Δτ_phys`. -/
structure EntropicPhysicalClockCalibration
    (C : PhaseClock) (W : EntropyArrowWorldline) (τphys : ℝ → ℝ) : Prop where
  /-- Imaginary action accumulates at the clock action rate `ℏω₀` per unit
  physical proper time. -/
  action_advance_eq : ∀ t₁ t₂,
    W.S_I_along t₂ - W.S_I_along t₁ =
      W.ℏ * C.omega0 * (τphys t₂ - τphys t₁)

/-- The calibrated imaginary-action increment gives exactly the phase accumulated
by the physical clock.  This is the dimensionally correct identification before
phase is converted to a duration. -/
@[zil_level physical_theorem]
theorem entropic_phase_advance_eq_physical_phase
    (C : PhaseClock) (W : EntropyArrowWorldline) (τphys : ℝ → ℝ)
    (K : EntropicPhysicalClockCalibration C W τphys) (t₁ t₂ : ℝ) :
    W.τ_ent_along t₂ - W.τ_ent_along t₁ =
      C.phaseAccumulated (τphys t₂ - τphys t₁) := by
  rw [W.τ_ent_eq, W.τ_ent_eq, ← sub_div, K.action_advance_eq]
  unfold PhaseClock.phaseAccumulated
  field_simp [W.ℏ_pos.ne']

/-- **Formal operational identification of entropic time with physical time.**

After the imaginary-action clock is calibrated by
`ΔS_I = ℏω₀ Δτ_phys`, its entropic-time advance, converted by the independently
defined phase clock, is exactly the physical proper-time advance.

This does not claim that entropy alone determines an SI second or that every
entropy arrow has this calibration.  It proves the equality for precisely the
systems for which the displayed action-rate law has been established. -/
@[zil_level physical_theorem]
theorem entropicPhysicalTimeAdvance_eq_physicalTime
    (C : PhaseClock) (W : EntropyArrowWorldline) (τphys : ℝ → ℝ)
    (K : EntropicPhysicalClockCalibration C W τphys) (t₁ t₂ : ℝ) :
    entropicPhysicalTimeAdvance C W t₁ t₂ = τphys t₂ - τphys t₁ := by
  unfold entropicPhysicalTimeAdvance
  rw [entropic_phase_advance_eq_physical_phase C W τphys K t₁ t₂]
  exact C.properTimeFromPhase_phaseAccumulated (τphys t₂ - τphys t₁)

/-- Direct spacetime form: if the imaginary-action increment is calibrated to
the physical clock rate times a geometric proper-time interval, the entropic
clock reads that geometric proper time. -/
@[zil_level physical_theorem]
theorem entropicPhysicalTimeAdvance_eq_geometricProperTime
    (C : PhaseClock) (W : EntropyArrowWorldline) (t₁ t₂ : ℝ)
    (q p : SpaceTime sd)
    (hcal :
      W.S_I_along t₂ - W.S_I_along t₁ =
        W.ℏ * C.omega0 * SpaceTime.properTime q p) :
    entropicPhysicalTimeAdvance C W t₁ t₂ = SpaceTime.properTime q p := by
  unfold entropicPhysicalTimeAdvance
  rw [W.τ_ent_eq, W.τ_ent_eq, ← sub_div, hcal]
  unfold PhaseClock.properTimeFromPhase
  field_simp [W.ℏ_pos.ne', C.omega0_pos.ne']

/-! ## D. Frozen-limit recovery -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Frozen-limit recovery for the metric oscillator clock: zero metric entropic
time, zero phase-time, and reversible/norm-preserving evolution at `H_I = 0`. -/
structure MetricClockFrozenRecovery
    (U : EntropicTimeUnits) (C : PhaseClock)
    (S : EntropyControlledSchrodingerSystem (H := H)) (ρ : MState d) (ψ : H) :
    Prop where
  /-- Metric entropic time vanishes on the diagonal. -/
  entropic_zero : entropicProperTimeMetric U ρ ρ = 0
  /-- Zero phase reads zero proper time. -/
  oscillator_zero_phase_time : C.properTimeFromPhase 0 = 0
  /-- `H_I = 0` gives reversible evolution. -/
  generator_recovers_reversible : S.H_I = 0 → S.H_C = S.H_R
  /-- `H_I = 0` gives zero entropy production. -/
  entropyRate_zero : S.H_I = 0 → S.entropyRate ψ = 0
  /-- `H_I = 0` preserves the norm. -/
  normDecayRate_zero : S.H_I = 0 → S.normDecayRate ψ = 0

lemma metric_clock_frozen_recovery
    (U : EntropicTimeUnits) (C : PhaseClock)
    (S : EntropyControlledSchrodingerSystem (H := H)) (ρ : MState d) (ψ : H) :
    MetricClockFrozenRecovery U C S ρ ψ where
  entropic_zero := entropicProperTimeMetric_self U ρ
  oscillator_zero_phase_time := by
    unfold PhaseClock.properTimeFromPhase; simp
  generator_recovers_reversible := fun h => S.zero_HI_implies_unitary_generator h
  entropyRate_zero := fun h => S.zero_HI_implies_zero_entropyRate h ψ
  normDecayRate_zero := fun h => (S.zero_HI_frozen_reduction h ψ).2.2

/- ZIL-BEGIN -/

zil_theorem_intent Physlib.QuantumMechanics.Clock.EntropicAgreement.entropic_phase_advance_eq_physical_phase where
  at_level physical_theorem
  must_mention [Physlib.Thermodynamics.SecondLaw.EntropyArrowWorldline,
    Physlib.QuantumMechanics.Clock.Phase.PhaseClock.phaseAccumulated]

zil attach Physlib.QuantumMechanics.Clock.EntropicAgreement.entropic_phase_advance_eq_physical_phase where
  formalizes @ "claim:a-calibrated-imaginary-action-increment-delta-s-i-equals-hbar-omega-zero-delta-tau-physical-produces-exactly-the-phase-omega-zero-delta-tau-physical",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.Thermodynamics.SecondLaw.EntropyArrowWorldline.τ_ent_eq",
  caveat @ "claim:the-action-rate-calibration-is-the-explicit-load-bearing-physical-premise;the-theorem-does-not-infer-an-si-time-unit-from-entropy-alone"

zil_theorem_intent Physlib.QuantumMechanics.Clock.EntropicAgreement.entropicPhysicalTimeAdvance_eq_physicalTime where
  at_level physical_theorem
  must_mention [Physlib.QuantumMechanics.Clock.EntropicAgreement.EntropicPhysicalClockCalibration,
    Physlib.QuantumMechanics.Clock.Phase.PhaseClock.properTimeFromPhase]

zil attach Physlib.QuantumMechanics.Clock.EntropicAgreement.entropicPhysicalTimeAdvance_eq_physicalTime where
  formalizes @ "claim:after-calibration-by-delta-s-i-equals-hbar-omega-zero-delta-tau-physical-the-entropic-clock-read-through-an-independent-phase-clock-equals-physical-proper-time",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:a-calibrated-imaginary-action-increment-delta-s-i-equals-hbar-omega-zero-delta-tau-physical-produces-exactly-the-phase-omega-zero-delta-tau-physical",
  supported_by @ "lean:Physlib.QuantumMechanics.Clock.Phase.PhaseClock.properTimeFromPhase_phaseAccumulated",
  caveat @ "claim:operational-identification-for-calibrated-systems-not-a-universal-derivation-that-every-entropy-arrow-is-physical-time"

zil attach Physlib.QuantumMechanics.Clock.EntropicAgreement.entropicPhysicalTimeAdvance_eq_geometricProperTime where
  supported_by @ "lean:QuantumMechanics.OneDimension.HarmonicOscillator.PhaseClock",
  formalizes @ "claim:an-entropic-clock-whose-imaginary-action-advance-is-hbar-omega-zero-times-a-spacetime-proper-time-interval-reads-exactly-that-geometric-proper-time",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:after-calibration-by-delta-s-i-equals-hbar-omega-zero-delta-tau-physical-the-entropic-clock-read-through-an-independent-phase-clock-equals-physical-proper-time",
  caveat @ "claim:the-geometric-action-rate-premise-must-be-established-by-the-specific-dynamical-clock-model"

zil_file_contract physlib.entropicPhysicalTimeIdentification where
  promises "Entropic time is identified operationally with physical proper time without storing the desired equality as a witness: S_I divided by hbar is first treated as a dimensionless phase, an independently defined positive-frequency phase clock converts that phase to duration, and the explicit testable action-rate calibration delta S_I equals hbar omega_0 delta tau_phys then proves exact equality with physical and geometric proper time. The calibration remains a visible model premise, so the result does not claim that entropy alone defines an SI second."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Thermodynamics.SecondLaw.EntropyArrowWorldline",
    "lean:Physlib.QuantumMechanics.Clock.Phase.PhaseClock",
    "lean:Physlib.QuantumMechanics.Clock.EntropicAgreement.EntropicPhysicalClockCalibration"]
  forbids_substitutes ["assuming entropic time equals physical time directly instead of deriving it through the action-rate calibration and phase-clock inverse",
    "calling the dimensionless ratio S_I divided by hbar a duration before a positive clock frequency converts phase to time",
    "claiming that every entropy-producing worldline satisfies the model-specific action-rate calibration"]
  witnessed_by [Physlib.QuantumMechanics.Clock.EntropicAgreement.entropic_phase_advance_eq_physical_phase,
    Physlib.QuantumMechanics.Clock.EntropicAgreement.entropicPhysicalTimeAdvance_eq_physicalTime,
    Physlib.QuantumMechanics.Clock.EntropicAgreement.entropicPhysicalTimeAdvance_eq_geometricProperTime]

/- ZIL-END -/

end Physlib.QuantumMechanics.Clock.EntropicAgreement

end
