/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Physlib.ClassicalMechanics.InertialFrame

/-!
# Classical Kuramoto oscillator network

Classical-mechanics representative for **N coupled phase oscillators** —
the Kuramoto model (Kuramoto 1975):

  `dθ_i/dt = ω_i + (K/N) · ∑_j sin(θ_j − θ_i)`

with:

* `N` oscillators indexed by `i : Fin N`,
* intrinsic frequencies `ω : Fin N → ℝ`,
* global coupling strength `K ≥ 0` (the density proxy: weak
  coupling at low physical density, strong at high density).

In the QIF program, this structure represents the **classical
analog** of the multi-subsystem QIF (`MultiQIF` in
`QuantumInertialFrameMultiSystem.lean`) at the density-locality
limit: each oscillator is a classical phase clock, and the coupling
`K` is the density-dependent inter-oscillator interaction.

## The "density-as-locality" picture (in classical terms)

* **At `K = 0`** (decoupled, sparse limit): each oscillator
  evolves independently at its intrinsic frequency `ω_i`.  Each is
  its own classical inertial frame (`θ_i(t) = ω_i·t + θ_i^0`, a
  linear trajectory in phase space).
* **At `K > K_c`** (above the Kuramoto synchronization threshold):
  oscillators lock into a collective mean phase; the synchronized
  cluster is a single classical inertial frame in the mean-phase
  coordinate.
* **At `0 < K < K_c`**: partial synchronization, no clean inertial
  frame.

## Contents

* `KuramotoNetwork N` structure: `(ω : Fin N → ℝ, K : ℝ, K_nonneg : 0 ≤ K)`.
* `KuramotoNetwork.IsDecoupled` — predicate `K = 0`.
* `KuramotoNetwork.freeTrajectory ω_i` — the linear trajectory
  `t ↦ ω_i · t` of an *individual* oscillator in the decoupled
  limit.
* `KuramotoNetwork.freeTrajectoryIsClassicalInertialFrame` — the
  load-bearing theorem: at the decoupled regime, each oscillator's
  trajectory is a classical inertial frame in the sense of
  `Physlib/ClassicalMechanics/InertialFrame.lean` (Bridge 3).

## What this file does NOT ship

The synchronization-threshold theorem `K > K_c ⟹ synchronized` is
**not** formalised — it requires substantial real-analysis
infrastructure (Strogatz-Mirollo continuum analysis, mean-field
limit, etc.) outside the present scope.

What IS formalised: the decoupled limit (`K = 0`), where each
oscillator independently realises Newton's first law in phase
space.  This is the "sparse limit" of the density-locality
picture, with strict Lean-proven content.


## References

* Kuramoto 1975 *International Symposium on Mathematical Problems
  in Theoretical Physics* — Kuramoto model.
* Strogatz 2000 *From Kuramoto to Crawford* — review of
  synchronization theory.
* Acebrón, Bonilla, Pérez Vicente, Ritort, Spigler 2005 *The
  Kuramoto model: A simple paradigm for synchronization phenomena*
  Rev. Mod. Phys. 77, 137.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.ClassicalMechanics

/-! ## §1 — Kuramoto network structure -/

/-- **Kuramoto oscillator network**: `N` coupled phase oscillators
with intrinsic frequencies `ω : Fin N → ℝ` and global coupling
strength `K ≥ 0`.

In the QIF framework, this is the classical-mechanics analog of a
`MultiQIF N H` (`QuantumInertialFrameMultiSystem.lean`).  The
coupling `K` is the operational density parameter: dilute systems
have `K ≈ 0` (each drop is independent); dense systems have
`K > K_c` (synchronized).

The structure does **not** include the dynamical equation
(`dθ_i/dt = ω_i + (K/N) ∑_j sin(θ_j − θ_i)`) as a structure field
— that would require an `ℝ → (Fin N → ℝ)` trajectory bundled with
a differential-equation predicate, which is heavier than needed
here.  Instead, the structure supplies the parameters; the dynamical
content for the **decoupled regime** (`K = 0`) is provided by the
theorems below. -/
structure KuramotoNetwork (N : ℕ) where
  /-- Intrinsic angular frequencies of each oscillator. -/
  ω         : Fin N → ℝ
  /-- Global coupling strength. -/
  K         : ℝ
  /-- Coupling is non-negative. -/
  K_nonneg  : 0 ≤ K

namespace KuramotoNetwork

variable {N : ℕ}

/-- **Decoupled regime**: the coupling is zero.  Each oscillator
evolves independently at its intrinsic frequency. -/
def IsDecoupled (K : KuramotoNetwork N) : Prop :=
  K.K = 0

/-! ## §2 — Free trajectory at the decoupled limit -/

/-- **Free phase trajectory** of oscillator `i` at the decoupled
limit: `θ_i(t) = ω_i · t`.

At `K = 0`, the Kuramoto equation reduces to `dθ_i/dt = ω_i`,
which integrates to `θ_i(t) = ω_i · t + θ_i^0`.  This function
gives the trajectory with `θ_i^0 = 0`. -/
def freeTrajectory (K : KuramotoNetwork N) (i : Fin N) (t : ℝ) : ℝ :=
  K.ω i * t

/-- The free trajectory at `t = 0` is `0`. -/
@[simp] theorem freeTrajectory_zero (K : KuramotoNetwork N) (i : Fin N) :
    K.freeTrajectory i 0 = 0 := by
  unfold freeTrajectory; ring

/-- The free trajectory is linear: `θ_i(t) = ω_i · t`. -/
theorem freeTrajectory_eq (K : KuramotoNetwork N) (i : Fin N) (t : ℝ) :
    K.freeTrajectory i t = K.ω i * t := rfl

/-! ## §3 — Each free oscillator is a classical inertial frame -/

/-- **Each free oscillator's phase trajectory is a classical
inertial frame**: in the decoupled regime, oscillator `i`'s phase
satisfies the affine condition `θ_i(t) = q + t • u` for some `q`
(the initial phase, here `0`) and `u` (the angular velocity `ω_i`).

This is the **load-bearing operational theorem** of the file: at
zero coupling, each oscillator independently realises Newton's
first law in *phase space* — its phase advances at constant
angular velocity, no fictitious forces (no synchronization torque),
the phase is a linear function of time. -/
def freeTrajectoryIsClassicalInertialFrame
    (K : KuramotoNetwork N) (_h_decoupled : K.IsDecoupled) (i : Fin N) :
    ClassicalInertialFrame ℝ where
  worldline := K.freeTrajectory i
  isAffine  := ⟨0, K.ω i, fun t => by
    rw [freeTrajectory_eq, zero_add]
    simp [smul_eq_mul, mul_comm]⟩

/-- **The decoupled Kuramoto network is a family of N classical
inertial frames** — one per oscillator, all evolving independently.

This is the *N-version* of the previous theorem: at `K = 0`, every
oscillator gives its own classical inertial frame, and the N
inertial frames are *mutually independent* (no inter-oscillator
coupling in the dynamics). -/
def decoupledInertialFamily
    (K : KuramotoNetwork N) (h_decoupled : K.IsDecoupled) :
    Fin N → ClassicalInertialFrame ℝ :=
  fun i => K.freeTrajectoryIsClassicalInertialFrame h_decoupled i

/-- **Sparse-limit Newton's first law for each oscillator**:
at the decoupled regime, each oscillator's phase satisfies the
integrated form of Newton's first law (constant angular velocity). -/
theorem newton_first_law_per_oscillator
    (K : KuramotoNetwork N) (_h_decoupled : K.IsDecoupled)
    (i : Fin N) (t₁ t₂ : ℝ) :
    K.freeTrajectory i t₂ - K.freeTrajectory i t₁ = (t₂ - t₁) • K.ω i := by
  unfold freeTrajectory
  rw [smul_eq_mul]
  ring

end KuramotoNetwork

end Physlib.ClassicalMechanics

end
