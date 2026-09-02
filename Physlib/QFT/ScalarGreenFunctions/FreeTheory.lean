/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.Classical
public import Physlib.QFT.ScalarGreenFunctions.DysonSchwinger
public import Mathlib.Data.Matrix.Basic

/-!
# Free scalar propagators and Gaussian generating functionals

This file formalizes the finite regularized free-field formulas used throughout
Rivers, Chapter 1.

* `FreeScalarPropagatorData` records the causal inverse relation
  `K Delta_F = -I`, the finite counterpart of Eqs. (1.33)--(1.35).
* `freeRealGeneratingFunctional` is the Gaussian functional
  `exp(-i/(2 hbar) J Delta_F J)`, Eq. (1.52).
* `realSourceBilinear` and `realSourceQuadratic_affine` expose the full
  polarization of that quadratic source carrier, including arbitrary
  background sources and variation directions.
* its invariance under `J -> -J` explains the vanishing of odd free Green
  functions and the even/odd decoupling of the quartic hierarchy;
* `freeComplexGeneratingFunctional` is the independent-source complex-scalar
  Gaussian `exp(-i/hbar Jstar Delta_F J)`, Eq. (1.83).

No inverse of an infinite differential operator is asserted. The finite matrix
is the repository's regularized carrier; continuum passage is handled by
existing limit interfaces.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open scoped BigOperators Matrix

/-- Finite regularized inverse free propagator and Feynman propagator. -/
structure FreeScalarPropagatorData (n : ℕ) where
  kinetic : Matrix (Fin n) (Fin n) ℂ
  propagator : Matrix (Fin n) (Fin n) ℂ
  /-- `K Delta_F = -I`. -/
  left_inverse : kinetic * propagator = -1
  /-- Symmetry of a neutral scalar propagator. -/
  symmetric : propagator.transpose = propagator

/-- Finite source quadratic form `J Delta J`. -/
def realSourceQuadratic {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (J : Fin n → ℂ) : ℂ :=
  ∑ x, ∑ y, J x * Delta x y * J y

@[simp] lemma realSourceQuadratic_zero {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) :
    realSourceQuadratic Delta (fun _ => 0) = 0 := by
  simp [realSourceQuadratic]

/-- The source quadratic form is even. -/
lemma realSourceQuadratic_neg {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (J : Fin n → ℂ) :
    realSourceQuadratic Delta (fun x => -J x) =
      realSourceQuadratic Delta J := by
  unfold realSourceQuadratic
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Homogeneity `Q(cJ)=c²Q(J)`. -/
lemma realSourceQuadratic_smul {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (J : Fin n → ℂ) :
    realSourceQuadratic Delta (fun x => c * J x) =
      c ^ 2 * realSourceQuadratic Delta J := by
  unfold realSourceQuadratic
  calc
    (∑ x, ∑ y, (c * J x) * Delta x y * (c * J y)) =
        ∑ x, ∑ y, c ^ 2 * (J x * Delta x y * J y) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = c ^ 2 * ∑ x, ∑ y, J x * Delta x y * J y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]

/-- The bilinear source pairing `J Δ H` associated to a finite propagator
matrix.  Its diagonal is `realSourceQuadratic`. -/
def realSourceBilinear {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ)
    (J H : Fin n → ℂ) : ℂ :=
  ∑ x, ∑ y, J x * Delta x y * H y

/-- The diagonal bilinear pairing recovers the existing source quadratic
form. -/
lemma realSourceBilinear_self {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (J : Fin n → ℂ) :
    realSourceBilinear Delta J J = realSourceQuadratic Delta J := rfl

/-- Exact polarization of the source quadratic along an affine source line:
`Q(J+tH)=Q(J)+t(B(J,H)+B(H,J))+t²Q(H)`. -/
lemma realSourceQuadratic_affine {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ)
    (J H : Fin n → ℂ) (t : ℂ) :
    realSourceQuadratic Delta (fun i => J i + t * H i) =
      realSourceQuadratic Delta J +
        t * (realSourceBilinear Delta J H +
          realSourceBilinear Delta H J) +
        t ^ 2 * realSourceQuadratic Delta H := by
  have hsum (c : ℂ) (f : Fin n → Fin n → ℂ) :
      (∑ x, ∑ y, c * f x y) = c * ∑ x, ∑ y, f x y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
  unfold realSourceQuadratic realSourceBilinear
  calc
    (∑ x, ∑ y,
        (J x + t * H x) * Delta x y * (J y + t * H y)) =
        ∑ x, ∑ y,
          (J x * Delta x y * J y +
            t * (J x * Delta x y * H y) +
            t * (H x * Delta x y * J y) +
            t ^ 2 * (H x * Delta x y * H y)) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = (∑ x, ∑ y, J x * Delta x y * J y) +
        (∑ x, ∑ y, t * (J x * Delta x y * H y)) +
        (∑ x, ∑ y, t * (H x * Delta x y * J y)) +
        (∑ x, ∑ y, t ^ 2 * (H x * Delta x y * H y)) := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ x, ∑ y, J x * Delta x y * J y) +
        t * ((∑ x, ∑ y, J x * Delta x y * H y) +
          ∑ x, ∑ y, H x * Delta x y * J y) +
        t ^ 2 * ∑ x, ∑ y, H x * Delta x y * H y := by
      rw [hsum t, hsum t, hsum (t ^ 2)]
      ring

/-- A symmetric neutral-scalar propagator makes the associated source
bilinear pairing symmetric. -/
lemma realSourceBilinear_comm_of_transpose_eq {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ)
    (hsymm : Delta.transpose = Delta) (J H : Fin n → ℂ) :
    realSourceBilinear Delta H J = realSourceBilinear Delta J H := by
  unfold realSourceBilinear
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  have hxy : Delta y x = Delta x y := by
    have h := congrFun (congrFun hsymm x) y
    simpa using h
  rw [hxy]
  ring

/-- The affine quadratic expansion for a symmetric propagator has cross term
`2t JΔH`. -/
lemma realSourceQuadratic_affine_of_transpose_eq {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ)
    (hsymm : Delta.transpose = Delta) (J H : Fin n → ℂ) (t : ℂ) :
    realSourceQuadratic Delta (fun i => J i + t * H i) =
      realSourceQuadratic Delta J +
        2 * t * realSourceBilinear Delta J H +
        t ^ 2 * realSourceQuadratic Delta H := by
  rw [realSourceQuadratic_affine,
    realSourceBilinear_comm_of_transpose_eq Delta hsymm H J]
  ring

/-- Free neutral-scalar Gaussian generating functional. -/
def freeRealGeneratingFunctional {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (hbar : ℝ)
    (J : Fin n → ℂ) : ℂ :=
  Complex.exp
    (-(Complex.I / (2 * (hbar : ℂ))) * realSourceQuadratic Delta J)

@[simp] lemma freeRealGeneratingFunctional_zero {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (hbar : ℝ) :
    freeRealGeneratingFunctional Delta hbar (fun _ => 0) = 1 := by
  simp [freeRealGeneratingFunctional]

/-- `Z₀[-J]=Z₀[J]`; hence the free neutral scalar has no odd source
coefficients. -/
lemma freeRealGeneratingFunctional_neg_source {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (hbar : ℝ)
    (J : Fin n → ℂ) :
    freeRealGeneratingFunctional Delta hbar (fun x => -J x) =
      freeRealGeneratingFunctional Delta hbar J := by
  rw [freeRealGeneratingFunctional, freeRealGeneratingFunctional,
    realSourceQuadratic_neg]

/-- Mixed complex-scalar quadratic form `Jstar Delta J`. -/
def complexSourceQuadratic {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ)
    (J Jstar : Fin n → ℂ) : ℂ :=
  ∑ x, ∑ y, Jstar x * Delta x y * J y

@[simp] lemma complexSourceQuadratic_zero_left {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (J : Fin n → ℂ) :
    complexSourceQuadratic Delta J (fun _ => 0) = 0 := by
  simp [complexSourceQuadratic]

@[simp] lemma complexSourceQuadratic_zero_right {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (Jstar : Fin n → ℂ) :
    complexSourceQuadratic Delta (fun _ => 0) Jstar = 0 := by
  simp [complexSourceQuadratic]

/-- Free complex-scalar Gaussian generating functional with independent
sources `J` and `Jstar`. -/
def freeComplexGeneratingFunctional {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (hbar : ℝ)
    (J Jstar : Fin n → ℂ) : ℂ :=
  Complex.exp
    (-(Complex.I / (hbar : ℂ)) * complexSourceQuadratic Delta J Jstar)

@[simp] lemma freeComplexGeneratingFunctional_zero {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) (hbar : ℝ) :
    freeComplexGeneratingFunctional Delta hbar
      (fun _ => 0) (fun _ => 0) = 1 := by
  simp [freeComplexGeneratingFunctional]

/-- Simultaneous opposite phase rescaling of particle and antiparticle sources
leaves the mixed Gaussian invariant. -/
lemma complexSourceQuadratic_opposite_scaling {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (hc : c ≠ 0) (J Jstar : Fin n → ℂ) :
    complexSourceQuadratic Delta (fun x => c * J x)
        (fun x => c⁻¹ * Jstar x) =
      complexSourceQuadratic Delta J Jstar := by
  unfold complexSourceQuadratic
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  field_simp [hc]

lemma freeComplexGeneratingFunctional_opposite_scaling {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ)
    (hbar : ℝ) (c : ℂ) (hc : c ≠ 0)
    (J Jstar : Fin n → ℂ) :
    freeComplexGeneratingFunctional Delta hbar
        (fun x => c * J x) (fun x => c⁻¹ * Jstar x) =
      freeComplexGeneratingFunctional Delta hbar J Jstar := by
  rw [freeComplexGeneratingFunctional, freeComplexGeneratingFunctional,
    complexSourceQuadratic_opposite_scaling Delta c hc J Jstar]

end Physlib.QFT.ScalarGreenFunctions

end
