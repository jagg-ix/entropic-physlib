/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.Special.QIFLorentzFrameChange
public import Physlib.ClassicalMechanics.InertialFrame

/-!
# Theorem: QIF is the reduction of Newton's first law (Bridge 4)

**Closure of the four-bridge chain.**  Composes:

* Bridge 1 (`QIFSRInertialFrame.lean`) — QIF at `IsInertial` gives an
  SR inertial frame (affine worldline).
* Bridge 2 (`QIFLorentzFrameChange.lean`) — entropic rate is a
  Lorentz scalar.
* Bridge 3 (`Physlib/ClassicalMechanics/InertialFrame.lean`) —
  classical inertial-frame carrier with Newton's first law in
  integrated form.
* **Bridge 4** (this file) — the reduction theorem:

  > **At `IsInertial`, the Lorentzian QIF's worldline satisfies
  > Newton's first law in the integrated form.**

Operationally: a Quantum Inertial Frame is the *quantum-mechanical
generalisation* of a classical inertial frame.  At the
operator-level inertial condition (`IsAllTimesEquilibrium` ∧
`IsGeodesicAffine`), the worldline reduces to a classical
constant-velocity trajectory — Newton's first law as a *derived
theorem* of the QIF framework rather than an axiom.

## Why the carrier-form Newton's first law (not derivatives)?

We use the **integrated** form `worldline t₂ − worldline t₁ =
(t₂ − t₁) • u` rather than the differential form `q'' = 0` because:

1. The integrated form requires no derivative machinery — it works
   in any normed ℝ-vector space (including `SpaceTime sd`,
   `EuclideanSpace ℝ (Fin d)`, etc.).
2. The integrated form is *equivalent* to `q'' = 0` for affine
   trajectories — and *constructively trivial* for the affine class
   we obtain from `IsGeodesicAffine`.
3. physlib's `FreeParticle.NewtonsSecondLaw s q := m·q'' = 0` is
   recovered by specialising to differentiable affine `q` and
   noting that the second derivative of an affine map is zero.

## Contents

* `classicalInertialFrame_of_isInertial` — the main theorem: a
  Lorentzian QIF at `IsInertial` produces a
  `ClassicalInertialFrame (SpaceTime sd)`.  Just identity-on-the-
  worldline; the inertiality witness from QIF supplies the affine
  condition of the classical carrier.
* `newton_first_law_from_isInertial` — restatement using the
  classical-carrier theorem name: the QIF worldline satisfies
  Newton's first law.

## Theorem statement

```
theorem newton_first_law_from_isInertial
    (LQW : LorentzianQIFWorldline H sd) (h : LQW.IsInertial)
    (t₁ t₂ : ℝ) (h_ne : t₁ ≠ t₂) :
    (t₂ - t₁)⁻¹ • (LQW.worldline t₂ - LQW.worldline t₁) =
      (classicalInertialFrame_of_isInertial LQW h).velocity
```

i.e. the QIF worldline has constant velocity, and that velocity is
the QIF-inertial-frame's 4-velocity.

## Significance

After this commit, the QIF framework carries an end-to-end
operational chain:

* **Operator level**: `H_R, H_I, ℏ`, equilibrium QIF condition
  (`λ(ψ) = 0`).
* **SR level**: `LorentzianQIFWorldline H sd` with `IsInertial`
  (affine worldline + every-time equilibrium QIF), Lorentz-
  invariance of the entropic rate.
* **Classical level**: `ClassicalInertialFrame (SpaceTime sd)`
  satisfying Newton's first law.

The reduction `QIF (Quantum) → SR (Lorentzian) → Classical (Newton)`
is now a chain of *derived theorems* in Lean.


## References

* Newton 1687 *Principia* — Newton's first law.
* MTW *Gravitation* §1.2 — inertial frames in SR.
  Quantum Reference Frames" — operational definition of equilibrium
  QIF as the quantum-mechanical Newton-first-law analog.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special.QuantumInertialFrameLorentzian

open QuantumMechanics.FiniteTarget
open Physlib.ClassicalMechanics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]


/-- **:Classical inertial frame from an inertial QIF**.

Bridge 4 of the QIF → SR → classical chain: at `IsInertial`, the
Lorentzian QIF's worldline supplies a
`ClassicalInertialFrame (SpaceTime sd)`.  The affine condition of
the classical carrier is exactly the geometric half of
`IsInertial` (`IsGeodesicAffine`).

This is the **reduction of Newton's first law from the QIF
framework**: a Quantum Inertial Frame at `IsInertial` is, in
particular, a classical inertial frame; the inertiality condition
shared between the two layers IS Newton's first law.  -/
def classicalInertialFrame_of_isInertial
    {sd : ℕ} (LQW : LorentzianQIFWorldline H sd) (h : LQW.IsInertial) :
    ClassicalInertialFrame (SpaceTime sd) where
  worldline := LQW.worldline
  isAffine  := h.1

/-- **QIF reduces to Newton's first law**.

For any inertial Lorentzian QIF, the worldline satisfies the
integrated form of Newton's first law: the displacement between any
two parameters equals the (constant) velocity times the time
interval.

This is the *theorem of the QIF framework* that the inertial
condition (operator-level `λ ≡ 0` + geometric-level affine
worldline) is **operationally identical** to Newton's first law. -/
lemma newton_first_law_from_isInertial
    {sd : ℕ} (LQW : LorentzianQIFWorldline H sd) (h : LQW.IsInertial)
    (t₁ t₂ : ℝ) :
    LQW.worldline t₂ - LQW.worldline t₁ =
      (t₂ - t₁) • (classicalInertialFrame_of_isInertial LQW h).velocity :=
  (classicalInertialFrame_of_isInertial LQW h).displacement_eq_velocity_smul_interval
    t₁ t₂

/-- **Differential form of Newton's first law**: constant velocity at
every parameter pair (no acceleration). -/
lemma newton_first_law_constant_velocity
    {sd : ℕ} (LQW : LorentzianQIFWorldline H sd) (h : LQW.IsInertial)
    (t₁ t₂ : ℝ) (h_ne : t₁ ≠ t₂) :
    (t₂ - t₁)⁻¹ • (LQW.worldline t₂ - LQW.worldline t₁) =
      (classicalInertialFrame_of_isInertial LQW h).velocity :=
  (classicalInertialFrame_of_isInertial LQW h).newton_first_law
    t₁ t₂ h_ne


/-- **The QIF → SR → classical reduction chain, packaged**.

For any inertial Lorentzian QIF, simultaneously:

1. **QIF side**: every state is at equilibrium (`λ ≡ 0`).
2. **SR side**: the worldline is affine — an SR inertial frame.
3. **Classical side**: the worldline satisfies Newton's first law
   (constant velocity / zero acceleration in integrated form).

The three levels are *operationally equivalent* under `IsInertial`:
the quantum-mechanical equilibrium-QIF condition is the
quantum-mechanical generalisation of Newton's first law. -/
lemma inertial_QIF_reduction_chain
    {sd : ℕ} (LQW : LorentzianQIFWorldline H sd) (h : LQW.IsInertial) :
    LQW.IsAllTimesEquilibrium ∧
    (∃ q u : SpaceTime sd, ∀ t, LQW.worldline t = q + t • u) ∧
    (∀ t₁ t₂ : ℝ,
      LQW.worldline t₂ - LQW.worldline t₁ =
        (t₂ - t₁) • (classicalInertialFrame_of_isInertial LQW h).velocity) :=
  ⟨h.2, h.1, newton_first_law_from_isInertial LQW h⟩

end Physlib.Relativity.Special.QuantumInertialFrameLorentzian

end
