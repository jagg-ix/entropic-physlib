/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Clock.Phase
public import Physlib.SpaceAndTime.SpaceTime.Lapse
public import Physlib.Thermodynamics.SecondLaw

/-!
# Relativistic phase-clock specializations (`c = 1`)

* SR, constant velocity: `Δτ = Δt √(1 − v²)`, so `Δφ = ω₀ Δt √(1 − v²)`
  (phase time dilation).
* Static lapse field: `Δτ = N(x) Δt`, so `Δφ = ω₀ N(x) Δt`, and the recovered
  proper time is `Δφ/ω₀ = N(x) Δt` (gravitational redshift of the clock rate).

-/

@[expose] public section

noncomputable section


open Physlib.QuantumMechanics.Clock.Phase
open Physlib.SpaceTime
namespace Physlib.Relativity.Special.PhaseClockRelativistic


variable {sd : ℕ}

/-! ## A. Special relativity (constant velocity, `c = 1`) -/

/-- SR proper time for constant coordinate velocity `v`. -/
def srProperTimeConstantVelocity (deltaT v : ℝ) : ℝ :=
  deltaT * Real.sqrt (1 - v ^ 2)

/-- SR oscillator phase under constant velocity. -/
def srOscillatorPhase (C : PhaseClock) (deltaT v : ℝ) : ℝ :=
  C.phaseAccumulated (srProperTimeConstantVelocity deltaT v)

theorem srOscillatorPhase_eq (C : PhaseClock) (deltaT v : ℝ) :
    srOscillatorPhase C deltaT v = C.omega0 * deltaT * Real.sqrt (1 - v ^ 2) := by
  unfold srOscillatorPhase PhaseClock.phaseAccumulated srProperTimeConstantVelocity
  ring

/-! ## B. Static lapse field (`c = 1`) -/

/-- Proper time from coordinate time under constant lapse: `Δτ = N(x)·Δt`. -/
def lapseProperTimeConstant (L : Lapse sd) (x : SpaceTime sd) (deltaT : ℝ) : ℝ :=
  L.N x * deltaT

/-- Oscillator phase accumulated under constant lapse. -/
def lapseOscillatorPhaseConstant
    (C : PhaseClock) (L : Lapse sd) (x : SpaceTime sd) (deltaT : ℝ) : ℝ :=
  C.phaseAccumulated (lapseProperTimeConstant L x deltaT)

theorem lapseOscillatorPhaseConstant_eq
    (C : PhaseClock) (L : Lapse sd) (x : SpaceTime sd) (deltaT : ℝ) :
    lapseOscillatorPhaseConstant C L x deltaT = C.omega0 * L.N x * deltaT := by
  unfold lapseOscillatorPhaseConstant PhaseClock.phaseAccumulated lapseProperTimeConstant
  ring

/-- The lapse oscillator phase recovers the lapse proper time: `Δφ/ω₀ = N(x)·Δt`. -/
theorem lapsePhase_recovers_lapseProperTime
    (C : PhaseClock) (L : Lapse sd) (x : SpaceTime sd) (deltaT : ℝ) :
    C.properTimeFromPhase (lapseOscillatorPhaseConstant C L x deltaT) =
      lapseProperTimeConstant L x deltaT := by
  unfold lapseOscillatorPhaseConstant
  rw [PhaseClock.properTimeFromPhase_phaseAccumulated]

/-! ## C. Entropic-time connection — relativistic phase clock ↔ `EntropyArrowWorldline`

The `deltaT` parameter in the relativistic phase-clock formulas above is
a generic coordinate-time interval `ℝ`.  In the entropic-time framework
, the operational time is `τ_ent = S_I/ℏ` along an
`EntropyArrowWorldline`, not an external coordinate.  This section
provides the constitutive coupling between the two via a single
identification:

  `proper-time interval (SR or lapse)  ≡  τ_ent advance along W`.

The pattern matches `TwinParadox/Entropic.lean`'s
`BridgeSRandEntropic` — a structural identification supplied by the
consumer per physical model.  With it in place, the phase-clock formulas
become statements about how the oscillator phase advances **with the
entropic clock**, not with an external coordinate time.
-/

open Physlib.Thermodynamics.SecondLaw

/-! ### C.1 — SR constant velocity ↔ entropic worldline -/

/-- **Coupling between an SR constant-velocity trajectory and an
`EntropyArrowWorldline`**.  Identifies the SR proper-time advance over
the coordinate-time interval `[t₁, t₂]` with the worldline's entropic-
time advance.  Constitutive identification supplied by the consumer
(matches the `BridgeSRandEntropic` pattern). -/
structure SRConstantVelocityEntropicCoupling
    (W : EntropyArrowWorldline) (v : ℝ) : Prop where
  /-- The bridge identification: the worldline's `τ_ent` advance over
  the coordinate-time interval `[t₁, t₂]` equals the SR proper time
  `(t₂ - t₁) · √(1 - v²)`. -/
  tauEnt_advance_eq_srProperTime : ∀ t₁ t₂ : ℝ,
    W.τ_ent_along t₂ - W.τ_ent_along t₁
      = srProperTimeConstantVelocity (t₂ - t₁) v

/-- **SR oscillator phase advance = `ω₀ · Δτ_ent` along the coupled
worldline.**  The relativistic phase-clock phase increment equals the
oscillator frequency times the entropic-time advance: the phase clock
is reading entropic time, not coordinate time. -/
theorem srOscillatorPhase_eq_omega0_tauEnt_advance
    (C : PhaseClock) (W : EntropyArrowWorldline) (v : ℝ)
    (B : SRConstantVelocityEntropicCoupling W v) (t₁ t₂ : ℝ) :
    srOscillatorPhase C (t₂ - t₁) v
      = C.omega0 * (W.τ_ent_along t₂ - W.τ_ent_along t₁) := by
  rw [B.tauEnt_advance_eq_srProperTime]
  unfold srOscillatorPhase PhaseClock.phaseAccumulated
    srProperTimeConstantVelocity
  ring

/-- **The SR oscillator's recovered proper time equals the entropic-time
advance.** From `properTimeFromPhase ∘ phaseAccumulated = id` plus the
coupling: the proper time recovered from the SR oscillator's phase is
exactly the worldline's `Δτ_ent`. -/
theorem srPhase_recovers_tauEnt_advance
    (C : PhaseClock) (W : EntropyArrowWorldline) (v : ℝ)
    (B : SRConstantVelocityEntropicCoupling W v) (t₁ t₂ : ℝ) :
    C.properTimeFromPhase (srOscillatorPhase C (t₂ - t₁) v)
      = W.τ_ent_along t₂ - W.τ_ent_along t₁ := by
  unfold srOscillatorPhase
  rw [PhaseClock.properTimeFromPhase_phaseAccumulated]
  exact (B.tauEnt_advance_eq_srProperTime t₁ t₂).symm

/-! ### C.2 — Static lapse field ↔ entropic worldline -/

/-- **Coupling between a static-lapse trajectory and an
`EntropyArrowWorldline`**.  Identifies the lapse-induced proper-time
advance over coordinate-time `[t₁, t₂]` at spatial point `x` with the
worldline's entropic-time advance. -/
structure LapseEntropicCoupling
    (W : EntropyArrowWorldline) (L : Lapse sd) (x : SpaceTime sd) :
    Prop where
  tauEnt_advance_eq_lapseProperTime : ∀ t₁ t₂ : ℝ,
    W.τ_ent_along t₂ - W.τ_ent_along t₁
      = lapseProperTimeConstant L x (t₂ - t₁)

/-- **Lapse-clock phase advance = `ω₀ · Δτ_ent` along the coupled
worldline.**  The lapse oscillator-phase increment equals the
oscillator frequency times the entropic-time advance.  Gravitational
phase rate is the entropic-clock rate. -/
theorem lapseOscillatorPhase_eq_omega0_tauEnt_advance
    (C : PhaseClock) (W : EntropyArrowWorldline) (L : Lapse sd)
    (x : SpaceTime sd) (B : LapseEntropicCoupling W L x) (t₁ t₂ : ℝ) :
    lapseOscillatorPhaseConstant C L x (t₂ - t₁)
      = C.omega0 * (W.τ_ent_along t₂ - W.τ_ent_along t₁) := by
  rw [B.tauEnt_advance_eq_lapseProperTime]
  unfold lapseOscillatorPhaseConstant PhaseClock.phaseAccumulated
    lapseProperTimeConstant
  ring

/-- **The lapse oscillator's recovered proper time equals the
entropic-time advance.** -/
theorem lapsePhase_recovers_tauEnt_advance
    (C : PhaseClock) (W : EntropyArrowWorldline) (L : Lapse sd)
    (x : SpaceTime sd) (B : LapseEntropicCoupling W L x) (t₁ t₂ : ℝ) :
    C.properTimeFromPhase (lapseOscillatorPhaseConstant C L x (t₂ - t₁))
      = W.τ_ent_along t₂ - W.τ_ent_along t₁ := by
  unfold lapseOscillatorPhaseConstant
  rw [PhaseClock.properTimeFromPhase_phaseAccumulated]
  exact (B.tauEnt_advance_eq_lapseProperTime t₁ t₂).symm

end Physlib.Relativity.Special.PhaseClockRelativistic

end
