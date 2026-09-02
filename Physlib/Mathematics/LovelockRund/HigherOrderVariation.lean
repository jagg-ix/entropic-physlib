/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.ClassicalMechanics.EulerLagrange
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Higher-order Euler--Lagrange operators

This module formalizes the operator structure of Lovelock--Rund Section 6.7.
For a second-order Lagrangian `L(t, q, qdot, qddot)`, the Euler--Lagrange
residual is

`∂L/∂q - d/dt (∂L/∂qdot) + d²/dt² (∂L/∂qddot)`.

The field-component index type is arbitrary, so the componentwise equation
also applies to infinite collections of degrees of freedom. No finite sum over
field components is introduced.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LovelockRund

/-- First-order Euler--Lagrange residual in one parameter. -/
def firstOrderEulerLagrangeTime
    (dLdq dLdqdot : ℝ → ℝ) : ℝ → ℝ :=
  fun t => dLdq t - deriv dLdqdot t

/-- Second-order Euler--Lagrange residual in one parameter. -/
def secondOrderEulerLagrangeTime
    (dLdq dLdqdot dLdqddot : ℝ → ℝ) : ℝ → ℝ :=
  fun t => dLdq t - deriv dLdqdot t + deriv (deriv dLdqddot) t

/-- If the Lagrangian has no second-derivative dependence, the second-order
operator reduces to the ordinary Euler--Lagrange operator. -/
theorem secondOrderEulerLagrangeTime_of_no_secondDerivative
    (dLdq dLdqdot : ℝ → ℝ) :
    secondOrderEulerLagrangeTime dLdq dLdqdot 0 =
      firstOrderEulerLagrangeTime dLdq dLdqdot := by
  funext t
  simp [secondOrderEulerLagrangeTime, firstOrderEulerLagrangeTime]

/-- Pointwise expansion of the second-order equation. -/
theorem secondOrderEulerLagrangeTime_apply
    (dLdq dLdqdot dLdqddot : ℝ → ℝ) (t : ℝ) :
    secondOrderEulerLagrangeTime dLdq dLdqdot dLdqddot t =
      dLdq t - deriv dLdqdot t + deriv (deriv dLdqddot) t :=
  rfl

/-- Componentwise first-order Euler--Lagrange residual for an arbitrary index
type of field components. -/
def indexedFirstOrderEulerLagrange
    {ι : Type*}
    (dLdq dLdqdot : ι → ℝ → ℝ) : ι → ℝ → ℝ :=
  fun i => firstOrderEulerLagrangeTime (dLdq i) (dLdqdot i)

/-- Componentwise second-order Euler--Lagrange residual for an arbitrary,
possibly infinite, field-component index type. -/
def indexedSecondOrderEulerLagrange
    {ι : Type*}
    (dLdq dLdqdot dLdqddot : ι → ℝ → ℝ) : ι → ℝ → ℝ :=
  fun i => secondOrderEulerLagrangeTime
    (dLdq i) (dLdqdot i) (dLdqddot i)

/-- The indexed second-order operator reduces componentwise to the first-order
operator when the highest-derivative momentum vanishes. -/
theorem indexedSecondOrderEulerLagrange_of_no_secondDerivative
    {ι : Type*}
    (dLdq dLdqdot : ι → ℝ → ℝ) :
    indexedSecondOrderEulerLagrange dLdq dLdqdot 0 =
      indexedFirstOrderEulerLagrange dLdq dLdqdot := by
  funext i t
  simp [indexedSecondOrderEulerLagrange,
    indexedFirstOrderEulerLagrange,
    secondOrderEulerLagrangeTime,
    firstOrderEulerLagrangeTime]

/-- A second-order extremal is a curve for which the second-order
Euler--Lagrange residual vanishes identically. -/
def IsSecondOrderExtremal
    (dLdq dLdqdot dLdqddot : ℝ → ℝ) : Prop :=
  secondOrderEulerLagrangeTime dLdq dLdqdot dLdqddot = 0

/-- Componentwise characterization of an indexed higher-order extremal. -/
theorem indexedSecondOrderExtremal_iff
    {ι : Type*}
    (dLdq dLdqdot dLdqddot : ι → ℝ → ℝ) :
    indexedSecondOrderEulerLagrange dLdq dLdqdot dLdqddot = 0 ↔
      ∀ i, IsSecondOrderExtremal
        (dLdq i) (dLdqdot i) (dLdqddot i) := by
  constructor
  · intro h i
    funext t
    exact congrFun (congrFun h i) t
  · intro h
    funext i t
    exact congrFun (h i) t

end Physlib.Mathematics.LovelockRund

end
