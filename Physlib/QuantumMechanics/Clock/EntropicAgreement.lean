/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.Special.PhaseClock.Geometric
public import Physlib.Relativity.Special.PhaseClock.Relativistic
public import Physlib.SpaceAndTime.EntropicProperTime
public import Physlib.QuantumMechanics.FiniteTarget.EntropyControlledSchrodinger

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

theorem EntropicOscillatorClockAgreement.entropic_equals_geometric
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

theorem EntropicLapseOscillatorAgreement.entropic_eq_lapse_proper_time
    (U : EntropicTimeUnits) (C : PhaseClock)
    (L : Lapse sd) (x : SpaceTime sd) (deltaT : ℝ) (ρ σ : MState d)
    (A : EntropicLapseOscillatorAgreement U C L x deltaT ρ σ) :
    entropicProperTimeMetric U ρ σ = lapseProperTimeConstant L x deltaT := by
  rw [A.agreement]
  exact lapsePhase_recovers_lapseProperTime C L x deltaT

/-! ## C. Frozen-limit recovery -/

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

theorem metric_clock_frozen_recovery
    (U : EntropicTimeUnits) (C : PhaseClock)
    (S : EntropyControlledSchrodingerSystem (H := H)) (ρ : MState d) (ψ : H) :
    MetricClockFrozenRecovery U C S ρ ψ where
  entropic_zero := entropicProperTimeMetric_self U ρ
  oscillator_zero_phase_time := by
    unfold PhaseClock.properTimeFromPhase; simp
  generator_recovers_reversible := fun h => S.zero_HI_implies_unitary_generator h
  entropyRate_zero := fun h => S.zero_HI_implies_zero_entropyRate h ψ
  normDecayRate_zero := fun h => (S.zero_HI_frozen_reduction h ψ).2.2

end Physlib.QuantumMechanics.Clock.EntropicAgreement

end
