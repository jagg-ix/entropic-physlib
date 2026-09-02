/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.ExternalField
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Trace-log and determinant identities for external scalar fields

Rivers Eqs. (1.70)--(1.78) use

`dL/dg = -tr(B Delta_g)`

and

`det(1 + M) = exp(tr log(1 + M))`.

For a finite regulator diagonalized in one common basis, the trace-log is the
sum of the logarithms of the eigenvalues and the determinant is their product.
This file proves the exact exponentiated trace-log identity, its determinant
ratio form, and the real spectral derivative of the loop action.

The diagonalized formulation is the mathematically exact finite-dimensional
content used by Rivers when deriving Eq. (1.78). It composes with the general
matrix resolvent identities in `ExternalField.lean`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open scoped BigOperators Matrix

/-- Trace-log of a diagonal finite regulator. -/
def diagonalTraceLog {n : ℕ} (lambda : Fin n → ℂ) : ℂ :=
  ∑ i, Complex.log (lambda i)

/-- Exponentiating the diagonal trace-log gives the determinant. -/
lemma exp_diagonalTraceLog_eq_det {n : ℕ}
    (lambda : Fin n → ℂ) (hlambda : ∀ i, lambda i ≠ 0) :
    Complex.exp (diagonalTraceLog lambda) =
      (Matrix.diagonal lambda).det := by
  calc
    Complex.exp (diagonalTraceLog lambda) =
        ∏ i, Complex.exp (Complex.log (lambda i)) := by
      simpa [diagonalTraceLog] using
        (Complex.exp_sum (Finset.univ : Finset (Fin n))
          (fun i => Complex.log (lambda i)))
    _ = ∏ i, lambda i := by
      apply Finset.prod_congr rfl
      intro i hi
      exact Complex.exp_log (hlambda i)
    _ = (Matrix.diagonal lambda).det := by
      rw [Matrix.det_diagonal]

/-- Ratio of two diagonalized finite determinants. -/
def diagonalDeterminantRatio {n : ℕ}
    (lambda0 lambdaG : Fin n → ℂ) : ℂ :=
  (Matrix.diagonal lambda0).det / (Matrix.diagonal lambdaG).det

/-- The determinant ratio is the exponential of the trace-log difference. -/
lemma diagonalDeterminantRatio_eq_exp_traceLog_sub {n : ℕ}
    (lambda0 lambdaG : Fin n → ℂ)
    (h0 : ∀ i, lambda0 i ≠ 0)
    (hG : ∀ i, lambdaG i ≠ 0) :
    diagonalDeterminantRatio lambda0 lambdaG =
      Complex.exp (diagonalTraceLog lambda0 - diagonalTraceLog lambdaG) := by
  unfold diagonalDeterminantRatio
  rw [Complex.exp_sub,
    exp_diagonalTraceLog_eq_det lambda0 h0,
    exp_diagonalTraceLog_eq_det lambdaG hG]

/-- Diagonalized real loop action
`L(g) = sum_i log(a_i + g b_i)`. -/
def realDiagonalLoopAction {n : ℕ}
    (a b : Fin n → ℝ) (g : ℝ) : ℝ :=
  ∑ i, Real.log (a i + g * b i)

/-- Spectral derivative of the diagonalized loop action:
`L'(g) = sum_i b_i / (a_i + g b_i)`.

When `Delta_g = -(A + gB)⁻¹`, this is the diagonal spectral form of Rivers'
`dL/dg = -tr(B Delta_g)`. -/
lemma realDiagonalLoopAction_hasDerivAt {n : ℕ}
    (a b : Fin n → ℝ) (g : ℝ)
    (h_nonzero : ∀ i, a i + g * b i ≠ 0) :
    HasDerivAt (realDiagonalLoopAction a b)
      (∑ i, b i / (a i + g * b i)) g := by
  unfold realDiagonalLoopAction
  apply HasDerivAt.fun_sum
  intro i hi
  have hlin :
      HasDerivAt (fun t : ℝ => a i + t * b i) (b i) g := by
    simpa using ((hasDerivAt_id g).mul_const (b i)).const_add (a i)
  exact hlin.log (h_nonzero i)

/-- Derivative of the negative loop action, matching the sign convention
`-tr(B Delta_g)` when the propagator is defined as a negative inverse. -/
lemma neg_realDiagonalLoopAction_hasDerivAt {n : ℕ}
    (a b : Fin n → ℝ) (g : ℝ)
    (h_nonzero : ∀ i, a i + g * b i ≠ 0) :
    HasDerivAt (fun t => -realDiagonalLoopAction a b t)
      (-(∑ i, b i / (a i + g * b i))) g := by
  exact (realDiagonalLoopAction_hasDerivAt a b g h_nonzero).neg

/-- Determinant consequence of the free inverse relation. -/
lemma freePropagator_det_mul_kinetic_det {n : ℕ}
    (D : ExternalFieldResolventData n) :
    D.freePropagator.det * D.kinetic.det =
      (-1 : Matrix (Fin n) (Fin n) ℂ).det := by
  have h := congrArg
    (fun M : Matrix (Fin n) (Fin n) ℂ => M.det)
    D.free_right_inverse
  simpa [Matrix.det_mul] using h

/-- Determinant consequence of the dressed inverse relation. -/
lemma dressedOperator_det_mul_propagator_det {n : ℕ}
    (D : ExternalFieldResolventData n) :
    (D.kinetic + D.coupling • D.background).det *
        D.dressedPropagator.det =
      (-1 : Matrix (Fin n) (Fin n) ℂ).det := by
  have h := congrArg
    (fun M : Matrix (Fin n) (Fin n) ℂ => M.det)
    D.dressed_left_inverse
  simpa [Matrix.det_mul] using h

end Physlib.QFT.ScalarGreenFunctions

end
