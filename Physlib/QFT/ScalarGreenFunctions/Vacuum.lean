/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.ExternalField
public import Physlib.QFT.Wick.Consistency

/-!
# Scalar Schrödinger vacuum and source displacement

This file formalizes the Gaussian vacuum calculation in Rivers, Section 1.9,
at the level of one diagonalized scalar mode. A finite free field decomposes
into such modes after diagonalizing its positive quadratic operator.

For

`S(A) = (1/2) k A² - j A`,

the source-induced classical field is `A_c = j/k`. Completing the square gives

`S(A) = (1/2) k (A-A_c)² - j²/(2k)`.

Consequently the relative action is nonnegative for `k > 0`, vanishes only at
`A_c`, and the corresponding complex-action weight has maximal unit modulus
there. This makes precise the chapter's statement that the vacuum wave
functional is peaked around the classical field induced by the source.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open Physlib.QFT.Wick.Consistency

/-- One-mode quadratic free-field action with a linear source. -/
def gaussianVacuumAction (k j A : ℝ) : ℝ :=
  (1 / 2) * k * A ^ 2 - j * A

/-- Classical source-induced field `A_c = j/k`. -/
def classicalSourceField (k j : ℝ) : ℝ :=
  j / k

/-- The classical source field solves `k A_c = j`. -/
lemma classicalSourceField_equation (k j : ℝ) (hk : k ≠ 0) :
    k * classicalSourceField k j = j := by
  rw [classicalSourceField, mul_div_cancel₀ j hk]

/-- Completing the square in the source-coupled Gaussian action. -/
lemma gaussianVacuumAction_completeSquare
    (k j A : ℝ) (hk : k ≠ 0) :
    gaussianVacuumAction k j A =
      (1 / 2) * k * (A - classicalSourceField k j) ^ 2 -
        j ^ 2 / (2 * k) := by
  unfold gaussianVacuumAction classicalSourceField
  field_simp [hk]
  ring

/-- Action relative to the source-induced classical configuration. -/
def vacuumRelativeAction (k j A : ℝ) : ℝ :=
  gaussianVacuumAction k j A -
    gaussianVacuumAction k j (classicalSourceField k j)

/-- The relative action is the positive quadratic displacement from the
classical source field. -/
lemma vacuumRelativeAction_eq
    (k j A : ℝ) (hk : k ≠ 0) :
    vacuumRelativeAction k j A =
      (1 / 2) * k * (A - classicalSourceField k j) ^ 2 := by
  unfold vacuumRelativeAction
  rw [gaussianVacuumAction_completeSquare k j A hk,
    gaussianVacuumAction_completeSquare
      k j (classicalSourceField k j) hk]
  ring

/-- For a positive free kernel, the source-relative vacuum action is
nonnegative. -/
lemma vacuumRelativeAction_nonneg
    (k j A : ℝ) (hk : 0 < k) :
    0 ≤ vacuumRelativeAction k j A := by
  rw [vacuumRelativeAction_eq k j A hk.ne']
  positivity

/-- The relative action vanishes at the classical source field. -/
@[simp] lemma vacuumRelativeAction_at_center
    (k j : ℝ) (hk : k ≠ 0) :
    vacuumRelativeAction k j (classicalSourceField k j) = 0 := by
  rw [vacuumRelativeAction_eq k j (classicalSourceField k j) hk]
  ring

/-- For a strictly positive kernel, the classical source field is the unique
zero and minimizer of the relative action. -/
lemma vacuumRelativeAction_eq_zero_iff
    (k j A : ℝ) (hk : 0 < k) :
    vacuumRelativeAction k j A = 0 ↔
      A = classicalSourceField k j := by
  rw [vacuumRelativeAction_eq k j A hk.ne']
  constructor
  · intro h
    have hcoef : (1 / 2 : ℝ) * k ≠ 0 :=
      mul_ne_zero (by norm_num) hk.ne'
    have hsquare : (A - classicalSourceField k j) ^ 2 = 0 := by
      exact (mul_eq_zero.mp h).resolve_left hcoef
    nlinarith
  · rintro rfl
    ring

/-- Dimensionless imaginary-action or entropic-time cost of a vacuum
configuration relative to the classical center. -/
def vacuumEntropicTime (k j A hbar : ℝ) : ℝ :=
  vacuumRelativeAction k j A / hbar

lemma vacuumEntropicTime_nonneg
    (k j A hbar : ℝ) (hk : 0 < k) (hhbar : 0 < hbar) :
    0 ≤ vacuumEntropicTime k j A hbar := by
  unfold vacuumEntropicTime
  exact div_nonneg (vacuumRelativeAction_nonneg k j A hk) hhbar.le

/-- Complex-action weight of a vacuum configuration. Its real action is set
to zero, so only the relative Gaussian selection cost remains. -/
def vacuumComplexWeight (k j A hbar : ℝ) : ℂ :=
  complexActionWeight 0 (vacuumRelativeAction k j A) hbar

/-- The modulus of the vacuum weight is exactly `exp(-tau_ent)`. -/
lemma norm_vacuumComplexWeight
    (k j A hbar : ℝ) :
    ‖vacuumComplexWeight k j A hbar‖ =
      Real.exp (-(vacuumEntropicTime k j A hbar)) := by
  unfold vacuumComplexWeight vacuumEntropicTime
  rw [norm_complexActionWeight]

/-- Positive quadratic action makes the vacuum weight contractive. -/
lemma norm_vacuumComplexWeight_le_one
    (k j A hbar : ℝ) (hk : 0 < k) (hhbar : 0 < hbar) :
    ‖vacuumComplexWeight k j A hbar‖ ≤ 1 := by
  rw [norm_vacuumComplexWeight, Real.exp_le_one_iff]
  exact neg_nonpos.mpr
    (vacuumEntropicTime_nonneg k j A hbar hk hhbar)

/-- At the source-induced classical field the relative imaginary action and
entropic time vanish, so the vacuum weight has unit modulus. -/
@[simp] lemma norm_vacuumComplexWeight_at_center
    (k j hbar : ℝ) (hk : k ≠ 0) :
    ‖vacuumComplexWeight k j (classicalSourceField k j) hbar‖ = 1 := by
  rw [norm_vacuumComplexWeight]
  simp [vacuumEntropicTime, vacuumRelativeAction_at_center k j hk]

/-- The vacuum center combines the unique zero-action statement with maximal
unit path weight. -/
lemma vacuumCenter_unique_and_unitWeight
    (k j hbar : ℝ) (hk : 0 < k) :
    (∀ A, vacuumRelativeAction k j A = 0 ↔
        A = classicalSourceField k j) ∧
      ‖vacuumComplexWeight k j (classicalSourceField k j) hbar‖ = 1 :=
  ⟨fun A => vacuumRelativeAction_eq_zero_iff k j A hk,
    norm_vacuumComplexWeight_at_center k j hbar hk.ne'⟩

end Physlib.QFT.ScalarGreenFunctions

end
