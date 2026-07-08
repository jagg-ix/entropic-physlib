/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Clock.Phase
public import Physlib.SpaceAndTime.SpaceTime.Lapse
public import Physlib.Relativity.Special.ProperTime

/-!
# Phase clock vs. geometric proper time

A witness that a phase reading measures the geometric Lorentz proper time
between two spacetime events: `phase = ω₀ · τ_geom`, hence `phase / ω₀ = τ_geom`.

-/

@[expose] public section

noncomputable section


open Physlib.QuantumMechanics.Clock.Phase
open Physlib.SpaceTime
namespace Physlib.Relativity.Special.PhaseClockGeometric


variable {sd : ℕ}

/-- Witness that an oscillator phase measures the geometric proper time between
two events `q`, `p`. -/
structure OscillatorGeometricProperTimeWitness
    (C : PhaseClock) (q p : SpaceTime sd) where
  /-- The measured phase. -/
  phase : ℝ
  /-- It is the phase accumulated over the geometric proper time. -/
  phase_eq : phase = C.phaseAccumulated (SpaceTime.properTime q p)

theorem OscillatorGeometricProperTimeWitness.recovers_geometric_time
    (C : PhaseClock) (q p : SpaceTime sd)
    (W : OscillatorGeometricProperTimeWitness C q p) :
    C.properTimeFromPhase W.phase = SpaceTime.properTime q p := by
  rw [W.phase_eq, PhaseClock.properTimeFromPhase_phaseAccumulated]

end Physlib.Relativity.Special.PhaseClockGeometric

end
