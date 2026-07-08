/-
Copyright (c) 2026 Jorge Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge Garcia
-/
module

public import Physlib.Gravity.Canonical.ProblemOfTime
public import Physlib.ClassicalMechanics.HamiltonsEquations
public import Physlib.SpaceAndTime.SpaceTime.TimeSlice

/-!
# Bridge from canonical constraints to existing Physlib mechanics

This module connects the abstract canonical-gravity interface to existing
Physlib APIs for Hamiltonian mechanics and spacetime time-slicing.

The bridge is intentionally packaged as data. It does not assert that every
canonical constrained system is Hamiltonian, or that every time-sliced field
comes from canonical gravity. Instead, it records the exact compatibility data
needed when a concrete system is later related to Physlib's mechanics and
spacetime APIs.
-/

@[expose] public section

namespace Physlib.Gravity.Canonical

open InnerProductSpace Time

/--
A finite-dimensional Hamiltonian system in the form used by
`ClassicalMechanics.hamiltonEqOp`.
-/
structure HamiltonianPhaseSystem
    (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] where
  /-- Hamiltonian `H(t, p, q)`. -/
  Hamiltonian : Time → X → X → ℝ
  /-- Momentum path `p(t)`. -/
  momentumPath : Time → X
  /-- Configuration path `q(t)`. -/
  configurationPath : Time → X

/--
The Hamiltonian equation operator vanishes for a packaged Hamiltonian phase
system.
-/
def HamiltonianEquationsHold
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (S : HamiltonianPhaseSystem X) : Prop :=
  ClassicalMechanics.hamiltonEqOp S.Hamiltonian S.momentumPath S.configurationPath = 0

/--
The packaged Hamiltonian equation condition is exactly Physlib's existing
Hamilton-equation theorem.
-/
theorem hamiltonianEquationsHold_iff_hamiltons_equations
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (S : HamiltonianPhaseSystem X) :
    HamiltonianEquationsHold S ↔
      (∀ t,
        ∂ₜ S.configurationPath t =
          gradient (fun x => S.Hamiltonian t x (S.configurationPath t)) (S.momentumPath t)) ∧
      (∀ t,
        ∂ₜ S.momentumPath t =
          -gradient (fun x => S.Hamiltonian t (S.momentumPath t) x) (S.configurationPath t)) := by
  exact ClassicalMechanics.hamiltonEqOp_eq_zero_iff_hamiltons_equations
    S.Hamiltonian S.momentumPath S.configurationPath

/--
A representation of an abstract canonical constrained system by an existing
Physlib Hamiltonian phase system.

This is not a vacuous placeholder: the field is the compatibility theorem
identifying the abstract constraint surface with the vanishing of
`ClassicalMechanics.hamiltonEqOp`.
-/
structure HamiltonianRepresentation
    (C : CanonicalSystem)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (S : HamiltonianPhaseSystem X) where
  /-- Constraint-surface membership is equivalent to Hamiltonian flow. -/
  constraintSurface_iff_hamiltonianEquations :
    ConstraintSurface C ↔ HamiltonianEquationsHold S

theorem constraintSurface_iff_hamiltonianEquations_of_representation
    (C : CanonicalSystem)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (S : HamiltonianPhaseSystem X)
    (R : HamiltonianRepresentation C S) :
    ConstraintSurface C ↔ HamiltonianEquationsHold S :=
  R.constraintSurface_iff_hamiltonianEquations

theorem constraintSurface_iff_hamiltons_equations_of_representation
    (C : CanonicalSystem)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (S : HamiltonianPhaseSystem X)
    (R : HamiltonianRepresentation C S) :
    ConstraintSurface C ↔
      (∀ t,
        ∂ₜ S.configurationPath t =
          gradient (fun x => S.Hamiltonian t x (S.configurationPath t)) (S.momentumPath t)) ∧
      (∀ t,
        ∂ₜ S.momentumPath t =
          -gradient (fun x => S.Hamiltonian t (S.momentumPath t) x) (S.configurationPath t)) := by
  exact R.constraintSurface_iff_hamiltonianEquations.trans
    (hamiltonianEquationsHold_iff_hamiltons_equations S)

/--
A spacetime field together with the time-sliced field supplied by
`SpaceTime.timeSlice`.
-/
structure SpacetimeFieldSlicing (d : ℕ) (M : Type) where
  /-- Choice of units for the speed of light. -/
  c : SpeedOfLight
  /-- Relativistic field on spacetime. -/
  spacetimeField : SpaceTime d → M
  /-- The same field in time-indexed spatial form. -/
  slicedField : Time → Space d → M
  /-- The sliced field is obtained by Physlib's `SpaceTime.timeSlice`. -/
  sliced_eq_timeSlice : slicedField = SpaceTime.timeSlice c spacetimeField

theorem slicedField_eq_timeSlice
    {d : ℕ} {M : Type} (S : SpacetimeFieldSlicing d M) :
    S.slicedField = SpaceTime.timeSlice S.c S.spacetimeField :=
  S.sliced_eq_timeSlice

end Physlib.Gravity.Canonical
