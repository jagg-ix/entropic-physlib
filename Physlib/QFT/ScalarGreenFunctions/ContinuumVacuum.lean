/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.Continuum
public import Physlib.QFT.ScalarGreenFunctions.Vacuum

/-!
# Continuum Gaussian scalar vacuum

Rivers' Schrödinger-picture vacuum is a Gaussian field functional centered at
the classical field induced by the source. The one-mode calculation in
`Vacuum.lean` is lifted here pointwise and then integrated over `Space d`.

For real profiles `k`, `j`, and `A`, with `k(x) ≠ 0`,

`(1/2) k(x) A(x)^2 - j(x) A(x)`

is completed pointwise around `A_c(x) = j(x)/k(x)`. If `k(x) ≥ 0`, the
integrated relative action

`∫ dx (1/2) k(x) (A(x)-A_c(x))^2`

is nonnegative and vanishes at the classical profile. The same quantity is
used as the imaginary-action cost of the continuum vacuum weight.

The quadratic profile is also exposed as Physlib's existing maximal-domain
pointwise multiplication operator on `L²(Space d, ℂ)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open MeasureTheory
open Physlib.QFT.Wick.Consistency

/-- A real continuum scalar profile. -/
abbrev RealContinuumScalarField (d : ℕ) := Space d → ℝ

/-- Pointwise classical field induced by the source. -/
def continuumClassicalSourceField {d : ℕ}
    (k j : RealContinuumScalarField d) : RealContinuumScalarField d :=
  fun x => j x / k x

/-- Pointwise source-coupled Gaussian action density. -/
def continuumGaussianVacuumDensity {d : ℕ}
    (k j A : RealContinuumScalarField d) (x : Space d) : ℝ :=
  (1 / 2) * k x * (A x) ^ 2 - j x * A x

/-- Pointwise completing-square identity for the continuum Gaussian field. -/
lemma continuumGaussianVacuumDensity_completeSquare {d : ℕ}
    (k j A : RealContinuumScalarField d) (x : Space d)
    (hk : k x ≠ 0) :
    continuumGaussianVacuumDensity k j A x =
      (1 / 2) * k x *
          (A x - continuumClassicalSourceField k j x) ^ 2 -
        (j x) ^ 2 / (2 * k x) := by
  unfold continuumGaussianVacuumDensity continuumClassicalSourceField
  field_simp [hk]
  ring

/-- Relative Gaussian action density around the pointwise classical field. -/
def continuumVacuumRelativeDensity {d : ℕ}
    (k j A : RealContinuumScalarField d) (x : Space d) : ℝ :=
  (1 / 2) * k x *
    (A x - continuumClassicalSourceField k j x) ^ 2

/-- The relative density is nonnegative for a nonnegative quadratic kernel. -/
lemma continuumVacuumRelativeDensity_nonneg {d : ℕ}
    (k j A : RealContinuumScalarField d)
    (hk : ∀ x, 0 ≤ k x) (x : Space d) :
    0 ≤ continuumVacuumRelativeDensity k j A x := by
  unfold continuumVacuumRelativeDensity
  have hkx : 0 ≤ k x := hk x
  positivity

/-- Integrated continuum relative action. -/
def continuumVacuumRelativeAction {d : ℕ}
    (k j A : RealContinuumScalarField d) : ℝ :=
  ∫ x, continuumVacuumRelativeDensity k j A x

/-- The integrated relative action is nonnegative. -/
lemma continuumVacuumRelativeAction_nonneg {d : ℕ}
    (k j A : RealContinuumScalarField d)
    (hk : ∀ x, 0 ≤ k x) :
    0 ≤ continuumVacuumRelativeAction k j A := by
  unfold continuumVacuumRelativeAction
  exact integral_nonneg (continuumVacuumRelativeDensity_nonneg k j A hk)

/-- The pointwise classical field has zero relative action. -/
@[simp] lemma continuumVacuumRelativeAction_at_center {d : ℕ}
    (k j : RealContinuumScalarField d) :
    continuumVacuumRelativeAction k j
      (continuumClassicalSourceField k j) = 0 := by
  simp [continuumVacuumRelativeAction,
    continuumVacuumRelativeDensity]

/-- Dimensionless continuum vacuum entropic-time cost. -/
def continuumVacuumEntropicTime {d : ℕ}
    (k j A : RealContinuumScalarField d) (hbar : ℝ) : ℝ :=
  continuumVacuumRelativeAction k j A / hbar

lemma continuumVacuumEntropicTime_nonneg {d : ℕ}
    (k j A : RealContinuumScalarField d) (hbar : ℝ)
    (hk : ∀ x, 0 ≤ k x) (hhbar : 0 < hbar) :
    0 ≤ continuumVacuumEntropicTime k j A hbar := by
  unfold continuumVacuumEntropicTime
  exact div_nonneg
    (continuumVacuumRelativeAction_nonneg k j A hk) hhbar.le

/-- Complex-action weight of a continuum vacuum profile. -/
def continuumVacuumComplexWeight {d : ℕ}
    (k j A : RealContinuumScalarField d) (hbar : ℝ) : ℂ :=
  complexActionWeight 0 (continuumVacuumRelativeAction k j A) hbar

/-- The continuum vacuum modulus is `exp(-tau_ent)`. -/
lemma norm_continuumVacuumComplexWeight {d : ℕ}
    (k j A : RealContinuumScalarField d) (hbar : ℝ) :
    ‖continuumVacuumComplexWeight k j A hbar‖ =
      Real.exp (-(continuumVacuumEntropicTime k j A hbar)) := by
  unfold continuumVacuumComplexWeight continuumVacuumEntropicTime
  rw [norm_complexActionWeight]

/-- A nonnegative quadratic kernel makes the continuum vacuum weight
contractive. -/
lemma norm_continuumVacuumComplexWeight_le_one {d : ℕ}
    (k j A : RealContinuumScalarField d) (hbar : ℝ)
    (hk : ∀ x, 0 ≤ k x) (hhbar : 0 < hbar) :
    ‖continuumVacuumComplexWeight k j A hbar‖ ≤ 1 := by
  rw [norm_continuumVacuumComplexWeight, Real.exp_le_one_iff]
  exact neg_nonpos.mpr
    (continuumVacuumEntropicTime_nonneg k j A hbar hk hhbar)

/-- The classical continuum profile has unit path-weight modulus. -/
@[simp] lemma norm_continuumVacuumComplexWeight_at_center {d : ℕ}
    (k j : RealContinuumScalarField d) (hbar : ℝ) :
    ‖continuumVacuumComplexWeight k j
        (continuumClassicalSourceField k j) hbar‖ = 1 := by
  rw [norm_continuumVacuumComplexWeight]
  simp [continuumVacuumEntropicTime]

/-- The continuum quadratic kernel as the existing maximal-domain pointwise
multiplication operator on `L²`. -/
def continuumVacuumKernelOperator {d : ℕ}
    (k : RealContinuumScalarField d) :
    ContinuumScalarHilbertSpace d →ₗ.[ℂ] ContinuumScalarHilbertSpace d :=
  continuumScalarMulOperator (fun x => (k x : ℂ))

/-- Measurable quadratic kernels give densely defined pointwise operators. -/
lemma continuumVacuumKernelOperator_hasDenseDomain {d : ℕ}
    {k : RealContinuumScalarField d}
    (hk : AEStronglyMeasurable (fun x => (k x : ℂ))) :
    (continuumVacuumKernelOperator k).HasDenseDomain := by
  simpa [continuumVacuumKernelOperator] using
    (continuumScalarMulOperator_hasDenseDomain hk)

/-- The continuum vacuum kernel acts pointwise almost everywhere. -/
lemma continuumVacuumKernelOperator_apply_ae {d : ℕ}
    {k : RealContinuumScalarField d}
    (ψ : (continuumVacuumKernelOperator k).domain) :
    continuumVacuumKernelOperator k ψ =ᵐ[volume]
      (fun x => (k x : ℂ)) • ψ := by
  simpa [continuumVacuumKernelOperator] using
    (continuumScalarMulOperator_apply_ae
      (f := fun x => (k x : ℂ)) ψ)

end Physlib.QFT.ScalarGreenFunctions

end
