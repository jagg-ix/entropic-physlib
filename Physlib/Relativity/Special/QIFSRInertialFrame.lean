/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.Special.QuantumInertialFrameLorentzian

/-!
# SR Inertial Frame from a Lorentzian QIF (Bridge 1)

First of four bridge files connecting the QIF framework to SR and to
classical mechanics:

* **Bridge 1** (this file): a `LorentzianQIFWorldline` at `IsInertial`
  gives an **SR inertial frame** (affine worldline in Minkowski).
* Bridge 2 (`QIFLorentzFrameChange.lean`): Lorentz-invariance of the
  entropic rate.
* Bridge 3 (`Physlib/ClassicalMechanics/InertialFrame.lean`):
  classical inertial-frame structure (constant-velocity trajectories).
* Bridge 4 (`QIFClassicalReduction.lean`): the **main theorem** —
  inertial QIF reduces to Newton's first law in the classical limit.

## Contents

* `SRInertialFrame sd` — a representative for SR inertial frames: an affine
  worldline `worldline t = q + t • u` on `SpaceTime sd`.
* `SRInertialFrame.fromLorentzianQIFWorldline` — constructs an SR
  inertial frame from any `LorentzianQIFWorldline` at `IsInertial`.
* `SRInertialFrame.fourVelocity` and constant-displacement theorem
  `displacement_eq_fourVelocity_smul_interval`: the integrated
  Newton's-first-law statement at the SR level (displacement equals
  4-velocity times proper-time interval).


## References

* MTW *Gravitation*, §1.2 — inertial frames in SR as affine
  trajectories on Minkowski spacetime.
* Rindler 1991 *Introduction to Special Relativity* — 4-velocity
  as the tangent vector of an inertial worldline.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special.QuantumInertialFrameLorentzian

open QuantumMechanics.FiniteTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-! ## §1 — SR inertial frame structure -/

/-- **Special-relativistic inertial frame**: a worldline
`γ : ℝ → SpaceTime sd` that is **affine** — there exist
`q u : SpaceTime sd` such that `γ t = q + t • u` for every `t`.

Operationally: `q` is the origin event, `u` is the (constant)
4-velocity per unit parameter; the parameter `t` is proper time
when `u` is normalised to a timelike unit vector.  No fictitious
forces, no acceleration — Newton's first law at the SR level. -/
structure SRInertialFrame (sd : ℕ) where
  /-- The worldline embedding. -/
  worldline : ℝ → SpaceTime sd
  /-- **Affine condition**: the worldline is `q + t • u` for some
  origin event `q` and 4-velocity `u`. -/
  isAffine  : ∃ q u : SpaceTime sd, ∀ t : ℝ, worldline t = q + t • u

namespace SRInertialFrame

variable {sd : ℕ}

/-- An origin event for the inertial worldline (`q` in `γ t = q + t • u`).
Uses `Classical.choose` on the `isAffine` witness; the *specific* point
chosen is implementation detail, but any other choice differs by an
additive constant absorbed into `q`. -/
def origin (F : SRInertialFrame sd) : SpaceTime sd :=
  F.isAffine.choose

/-- The **4-velocity** (per-unit-parameter tangent) of the inertial
worldline (`u` in `γ t = q + t • u`).  Constant by hypothesis. -/
def fourVelocity (F : SRInertialFrame sd) : SpaceTime sd :=
  F.isAffine.choose_spec.choose

/-- The worldline factors through the origin and 4-velocity. -/
theorem worldline_eq (F : SRInertialFrame sd) (t : ℝ) :
    F.worldline t = F.origin + t • F.fourVelocity :=
  F.isAffine.choose_spec.choose_spec t

/-- **Displacement-equals-4-velocity-times-interval** — the integrated
form of Newton's first law at the SR level.  Across any two parameter
values, the spacetime displacement is exactly `Δt • u`. -/
theorem displacement_eq_fourVelocity_smul_interval
    (F : SRInertialFrame sd) (t₁ t₂ : ℝ) :
    F.worldline t₂ - F.worldline t₁ = (t₂ - t₁) • F.fourVelocity := by
  rw [F.worldline_eq, F.worldline_eq, sub_smul]
  abel

end SRInertialFrame

/-! ## §2 — Bridge from `LorentzianQIFWorldline` to `SRInertialFrame` -/

/-- **From any inertial QIF worldline, get an SR inertial frame**.

The map is just identity-on-worldline: `LQW.IsInertial.1` already
witnesses the affine condition (`IsGeodesicAffine`).  The QIF's
quantum content (operator-level `H_R, H_I, ℏ`) is dropped; what
remains is the *spacetime geometric* content.

This is Bridge 1 of the four-bridge chain QIF → SR → classical. -/
def SRInertialFrame.fromLorentzianQIFWorldline
    {sd : ℕ} (LQW : LorentzianQIFWorldline H sd) (h : LQW.IsInertial) :
    SRInertialFrame sd where
  worldline := LQW.worldline
  isAffine  := h.1

/-- The SR inertial frame's worldline is the QIF's worldline. -/
@[simp] theorem SRInertialFrame.fromLorentzianQIFWorldline_worldline
    {sd : ℕ} (LQW : LorentzianQIFWorldline H sd) (h : LQW.IsInertial) (t : ℝ) :
    (SRInertialFrame.fromLorentzianQIFWorldline LQW h).worldline t
      = LQW.worldline t := rfl

end Physlib.Relativity.Special.QuantumInertialFrameLorentzian

end
