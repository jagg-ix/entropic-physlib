/-
Copyright (c) 2026 Jorge Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge Garcia
-/
module

public import Mathlib

/-!
# Canonical constrained systems

This module defines a small abstract interface for canonical constrained systems,
intended as a foundation for canonical gravity and Kuchar-style
deparametrization.

The interface is deliberately conservative. It does not assume a specific
spacetime model, a specific Poisson-bracket construction, or a specific choice
of clock variables.
-/

@[expose] public section

namespace Physlib.Gravity.Canonical

universe u v w

/--
A canonical constrained system.

`Point` labels spatial points or smearing labels.

`Index` labels spatial components.

`PhaseExpr` is the type of formal phase-space expressions.

`WeakEq` is equality on the constraint surface.
-/
structure CanonicalSystem where
  Point : Type u
  Index : Type v
  PhaseExpr : Type w

  zero : PhaseExpr
  add : PhaseExpr → PhaseExpr → PhaseExpr
  neg : PhaseExpr → PhaseExpr
  bracket : PhaseExpr → PhaseExpr → PhaseExpr

  WeakEq : PhaseExpr → PhaseExpr → Prop

  /-- Scalar or Hamiltonian constraint, usually written `H_perp(x) approx 0`. -/
  scalarConstraint : Point → PhaseExpr

  /-- Spatial diffeomorphism or momentum constraint, usually written `H_i(x) approx 0`. -/
  momentumConstraint : Point → Index → PhaseExpr

/-- All scalar constraints vanish weakly. -/
def ScalarConstraintSurface (C : CanonicalSystem) : Prop :=
  ∀ x : C.Point, C.WeakEq (C.scalarConstraint x) C.zero

/-- All momentum constraints vanish weakly. -/
def MomentumConstraintSurface (C : CanonicalSystem) : Prop :=
  ∀ x : C.Point, ∀ i : C.Index,
    C.WeakEq (C.momentumConstraint x i) C.zero

/-- Full canonical constraint surface. -/
def ConstraintSurface (C : CanonicalSystem) : Prop :=
  ScalarConstraintSurface C ∧ MomentumConstraintSurface C

theorem scalarConstraintSurface_of_constraintSurface
    (C : CanonicalSystem) (h : ConstraintSurface C) :
    ScalarConstraintSurface C :=
  h.1

theorem momentumConstraintSurface_of_constraintSurface
    (C : CanonicalSystem) (h : ConstraintSurface C) :
    MomentumConstraintSurface C :=
  h.2

end Physlib.Gravity.Canonical
