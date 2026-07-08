/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Classical inertial frame (Newton's first law) — Bridge 3

Minimal representative for **classical inertial frames** in Newtonian
mechanics: trajectories with **constant velocity** along a worldline
parameter.  This is Newton's first law in its integrated /
displacement form: equal time-intervals produce equal displacements
along a uniform direction.

Bridge 3 of four in the QIF → SR → classical chain.  Bridge 4
(`QIFClassicalReduction.lean`) is the main theorem: a proof that the
QIF `IsInertial` predicate **reduces to Newton's first law** in this
structure's sense.

## Why a new file in `ClassicalMechanics/`?

physlib's existing classical-mechanics infrastructure
(`FreeParticle/Basic.lean`,  `RigidBody/Basic.lean`) encodes
inertiality **implicitly** via `m·q'' = 0` on a `Trajectory` type.
We need an **explicit** structure — a frame — whose data is the
trajectory itself + the inertiality witness (constant velocity),
so we can target it as the codomain of the QIF-classical reduction
map.

## Contents

* `ClassicalInertialFrame V` — a worldline `ℝ → V` (any normed
  ℝ-vector space) plus the **constant-velocity / affine condition**:
  `∃ q u, ∀ t, worldline t = q + t • u`.
* `displacement_eq_velocity_smul_interval` — the integrated form of
  Newton's first law: displacement is velocity × time interval.
* `velocity_invariant` — the velocity 4-tuple is the same at every
  parameter (Newton's first law in its differential reading).

## Cross-references

* physlib's `FreeParticle/Basic.lean` `NewtonsSecondLaw s q := m·q'' = 0`
  is the differential form; this file provides the integrated form
  (no derivatives needed; works in any normed space).


## References

* Newton 1687 *Principia*, Law I — Newton's first law.
* Landau-Lifshitz *Mechanics* §3 — inertial frames in classical
  mechanics.
* MTW *Gravitation* §1.2 — inertial frames as affine trajectories
  (Newtonian limit of SR inertiality).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.ClassicalMechanics

/-! ## §1 — Classical inertial frame structure -/

/-- **Classical inertial frame** on a normed ℝ-vector space `V`:

A worldline `worldline : ℝ → V` satisfying Newton's first law in its
integrated form — the worldline is **affine** in the parameter:

  `∃ q u : V, ∀ t, worldline t = q + t • u`.

Here `q : V` is the spatial origin at parameter `t = 0`, and `u : V`
is the (constant) velocity vector.  No fictitious forces, no
acceleration, no curvature — pure Newton's first law.

The structure accepts any normed ℝ-vector space `V` (including
`EuclideanSpace ℝ (Fin d)` for `d`-dimensional Euclidean space, the
canonical classical-mechanics phase-space-fragment); the same
predicate works at any dimension.  -/
structure ClassicalInertialFrame (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] where
  /-- The worldline trajectory in the underlying space. -/
  worldline : ℝ → V
  /-- **Newton's first law (integrated form)**: the worldline is
  affine — constant-velocity motion.  No acceleration, no fictitious
  forces. -/
  isAffine  : ∃ q u : V, ∀ t : ℝ, worldline t = q + t • u

namespace ClassicalInertialFrame

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The **origin** of the inertial frame (the worldline's value at
`t = 0`, up to the choice of witness). -/
def origin (F : ClassicalInertialFrame V) : V :=
  F.isAffine.choose

/-- The **constant velocity vector** of the inertial frame. -/
def velocity (F : ClassicalInertialFrame V) : V :=
  F.isAffine.choose_spec.choose

/-- The worldline factors as `worldline t = origin + t • velocity`. -/
theorem worldline_eq (F : ClassicalInertialFrame V) (t : ℝ) :
    F.worldline t = F.origin + t • F.velocity :=
  F.isAffine.choose_spec.choose_spec t

/-- **Displacement-equals-velocity-times-interval**: the integrated
form of Newton's first law in classical mechanics. -/
theorem displacement_eq_velocity_smul_interval
    (F : ClassicalInertialFrame V) (t₁ t₂ : ℝ) :
    F.worldline t₂ - F.worldline t₁ = (t₂ - t₁) • F.velocity := by
  rw [F.worldline_eq, F.worldline_eq, sub_smul]
  abel

/-- **The velocity is the same at every parameter**.  Differential
form of Newton's first law: the velocity is *constant* — no
acceleration. -/
theorem velocity_invariant (F : ClassicalInertialFrame V) (t : ℝ) (Δt : ℝ)
    (hΔt : Δt ≠ 0) :
    (Δt)⁻¹ • (F.worldline (t + Δt) - F.worldline t) = F.velocity := by
  rw [displacement_eq_velocity_smul_interval F t (t + Δt)]
  rw [show t + Δt - t = Δt by ring]
  rw [smul_smul, inv_mul_cancel₀ hΔt, one_smul]

/-- **Newton's first law (structure form)**: the velocity computed
between any two parameters is the same constant velocity. -/
theorem newton_first_law (F : ClassicalInertialFrame V)
    (t₁ t₂ : ℝ) (h : t₁ ≠ t₂) :
    (t₂ - t₁)⁻¹ • (F.worldline t₂ - F.worldline t₁) = F.velocity := by
  have h_ne : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  rw [displacement_eq_velocity_smul_interval]
  rw [smul_smul, inv_mul_cancel₀ h_ne, one_smul]

end ClassicalInertialFrame

end Physlib.ClassicalMechanics

end
