/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Phase clock (generic operational clock algebra)

A `PhaseClock` accumulates phase at a constant proper angular frequency `ω₀ > 0`:
`Δφ = ω₀ · Δτ`, hence `Δτ = Δφ / ω₀`. This is the pure operational algebra of a
clock that reads time off accumulated phase; it has no dependency on any specific
oscillator model (those are wrappers, see `MetricClock.QuantumOscillator`).

-/

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Clock.Phase

/-- A clock that reads proper time from accumulated phase at frequency `ω₀ > 0`. -/
structure PhaseClock where
  /-- Proper angular frequency. -/
  omega0 : ℝ
  /-- The frequency is positive (so phase is invertible to time). -/
  omega0_pos : 0 < omega0

namespace PhaseClock

/-- Phase accumulated over a proper-time interval `tau`: `Δφ = ω₀ · τ`. -/
def phaseAccumulated (C : PhaseClock) (tau : ℝ) : ℝ :=
  C.omega0 * tau

/-- Proper time inferred from accumulated phase: `Δτ = Δφ / ω₀`. -/
def properTimeFromPhase (C : PhaseClock) (phase : ℝ) : ℝ :=
  phase / C.omega0

/-- **Phase-time inverse**: applying `properTimeFromPhase` to
`phaseAccumulated τ` recovers `τ`.  Pure mul/div cancellation by `ω₀ ≠ 0`.

complex-action/entropic-time comparator: `claim_level := 2` (calibrated operational proxy).
Does not prove: phase is intrinsically entropic; phase spectrum is
discrete; the calibration `ω₀` is uniquely fixed by entropic content.
The same conclusion holds for `ω₀ := 1` (identity calibration), where
phase literally is `τ`.
-/
@[simp] theorem properTimeFromPhase_phaseAccumulated (C : PhaseClock) (tau : ℝ) :
    C.properTimeFromPhase (C.phaseAccumulated tau) = tau := by
  unfold properTimeFromPhase phaseAccumulated
  exact mul_div_cancel_left₀ tau C.omega0_pos.ne'

@[simp] theorem phaseAccumulated_properTimeFromPhase (C : PhaseClock) (phase : ℝ) :
    C.phaseAccumulated (C.properTimeFromPhase phase) = phase := by
  unfold phaseAccumulated properTimeFromPhase
  rw [← mul_div_assoc]
  exact mul_div_cancel_left₀ phase C.omega0_pos.ne'

end PhaseClock

end Physlib.QuantumMechanics.Clock.Phase

end
