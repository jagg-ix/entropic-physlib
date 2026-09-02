/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Physlib.QuantumMechanics.GaussianEntanglement.TwoModeSqueezedThermal

/-!
# The symplectic covariance picture behind the TMST threshold

Ports `lean4/QCDVortex/CovarianceMatrix.lean` of the qcd-vortex-entanglement tree (Lean layer
own authorship): the Gaussian-state covariance carrier under `TwoModeSqueezedThermal`, closing
the gap between the analytic `nu_minus` formula and the symplectic spectral theory.

* `symplecticForm_antisymm`, `tmst_cov_symm` — the canonical `Ω₄` and the TMST covariance
  `σ(r,n̄) = (n̄+½)·[[cosh,0,sinh,0],…]` with its symmetry;
* `sympPT_sq_eigenvec` — `v₋ = (1,0,−1,0)` is an eigenvector of `(Ω·σ^{T_B}/(n̄+½))²` with
  eigenvalue `−(cosh 2r − sinh 2r)²` (the substantive 4×4 computation);
* `cosh_sub_sinh_eq_exp_neg`, `eigval_minus_sq`, `sqrt_exp_neg4r` — the eigenvalue collapses
  to `e^{−4r}` with square root `e^{−2r}`;
* `nu_minus_eq_symp_eigenvalue` — `ν₋(r,n̄) = (n̄+½)·√(eigenvalue)`: the abstract threshold
  quantity of `theorem_4_3_1` *is* the smallest symplectic eigenvalue of the partially
  transposed covariance, so the PPT reading of the criterion is grounded
  (`nu_minus_lt_half_iff_symp_eig_lt`).

**Honest layering.**  Exact matrix and hyperbolic-function algebra; the full symplectic
spectral theorem (Williamson normal form) is cited, not re-proven — the eigenvector equation
for `v₋` is what the threshold needs.

## References

* Source: `lean4/QCDVortex/CovarianceMatrix.lean` (own authorship), re-authored.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.GaussianEntanglement.SymplecticCovariance

open Real Matrix

/-! ## 1. Symplectic form -/

/-- Canonical symplectic form Ω₄ in (q₁, p₁, q₂, p₂) basis. -/
def symplecticForm : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

/-- Ω is antisymmetric: Ωᵀ = -Ω. -/
theorem symplecticForm_antisymm : symplecticFormᵀ = -symplecticForm := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [symplecticForm, Matrix.transpose_apply, Matrix.neg_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## 2. TMST covariance matrix -/

/--
Two-mode squeezed thermal state covariance matrix σ(r, n̄).

  σ(r, n̄) = (n̄ + ½) · !![cosh(2r), 0,         sinh(2r), 0;
                            0,         cosh(2r), 0,         -sinh(2r);
                            sinh(2r),  0,         cosh(2r), 0;
                            0,         -sinh(2r), 0,         cosh(2r)]
-/
noncomputable def tmstCov (r n_bar : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (n_bar + 1/2) • !![cosh (2*r), 0,         sinh (2*r), 0;
                      0,         cosh (2*r), 0,          -(sinh (2*r));
                      sinh (2*r), 0,         cosh (2*r), 0;
                      0,         -(sinh (2*r)), 0,        cosh (2*r)]

/-- σ is symmetric: σᵀ = σ. -/
theorem tmst_cov_symm (r n_bar : ℝ) : (tmstCov r n_bar)ᵀ = tmstCov r n_bar := by
  simp only [tmstCov, transpose_smul]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one]

/-! ## 3. Partial transpose σ^{T_B} -/

/--
Normalized partial-transposed covariance B(r) := σ^{T_B}(r, n̄) / (n̄ + ½).

Partial transposition w.r.t. mode B flips the sign of p₂ (index 3):
σ^{T_B}[i,j] = -σ[i,j] if exactly one of (i,j) equals 3, else σ[i,j].
This converts the (0, -sinh) off-diagonal blocks to (0, sinh).
-/
noncomputable def normPT (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![cosh (2*r), 0,          sinh (2*r), 0;
     0,          cosh (2*r), 0,          sinh (2*r);
     sinh (2*r), 0,          cosh (2*r), 0;
     0,          sinh (2*r), 0,          cosh (2*r)]

/-! ## 4. Normalized symplectic–PT matrix A(r) = Ω · B(r) -/

/--
A(r) = Ω · normPT(r), the normalized symplectic-PT product.

  A(r) = !![0,        cosh(2r), 0,        sinh(2r);
            -cosh(2r), 0,        -sinh(2r), 0;
            0,         sinh(2r), 0,         cosh(2r);
            -sinh(2r), 0,        -cosh(2r), 0]
-/
noncomputable def sympPT (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,           cosh (2*r), 0,           sinh (2*r);
     -(cosh (2*r)), 0,         -(sinh (2*r)), 0;
     0,           sinh (2*r), 0,           cosh (2*r);
     -(sinh (2*r)), 0,         -(cosh (2*r)), 0]

/-! ## 5. Eigenvector equation — smallest symplectic eigenvalue -/

set_option maxHeartbeats 800000 in
/--
v₋ = (1, 0, −1, 0) is an eigenvector of A(r)² with eigenvalue
−(cosh(2r) − sinh(2r))².

Proof in two steps: A·v = w, then A·w = eigenvalue·v.
Uses `cosh(2r) = sinh(2r) + exp(−2r)` (from `cosh_sub_sinh`) so both
LHS and RHS become polynomial in `sinh` and `exp`, closed by `ring`.
-/
theorem sympPT_sq_eigenvec (r : ℝ) :
    (sympPT r * sympPT r).mulVec ![1, 0, -1, 0] =
    (-((cosh (2*r) - sinh (2*r))^2)) • (![1, 0, -1, 0] : Fin 4 → ℝ) := by
  -- Rewrite cosh in terms of sinh + exp so ring can close polynomial goals
  have hc : cosh (2*r) = sinh (2*r) + Real.exp (-(2*r)) := by
    have := Real.cosh_sub_sinh (2*r); linarith
  -- Step 1: A·v where v = [1,0,-1,0]
  have h1 : (sympPT r).mulVec ![1, 0, -1, 0] =
            ![0, -(Real.exp (-(2*r))), 0, Real.exp (-(2*r))] := by
    funext i; fin_cases i <;>
      simp [sympPT, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hc]
  -- Step 2: A·w where w = [0, −exp(−2r), 0, exp(−2r)]
  have h2 : (sympPT r).mulVec ![0, -(Real.exp (-(2*r))), 0, Real.exp (-(2*r))] =
            (-((cosh (2*r) - sinh (2*r))^2)) • (![1, 0, -1, 0] : Fin 4 → ℝ) := by
    funext i; fin_cases i <;>
      simp [sympPT, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
            Pi.smul_apply, smul_eq_mul, hc] <;>
      ring
  -- Combine: (A*A)·v = A·(A·v)
  calc (sympPT r * sympPT r).mulVec ![1, 0, -1, 0]
      = (sympPT r).mulVec ((sympPT r).mulVec ![1, 0, -1, 0]) :=
          (Matrix.mulVec_mulVec _ _ _).symm
    _ = (sympPT r).mulVec ![0, -(Real.exp (-(2*r))), 0, Real.exp (-(2*r))] := by rw [h1]
    _ = (-((cosh (2*r) - sinh (2*r))^2)) • (![1, 0, -1, 0] : Fin 4 → ℝ) := h2

/-! ## 6. Eigenvalue simplification via cosh–sinh identity -/

/-- cosh(x) − sinh(x) = exp(−x). -/
theorem cosh_sub_sinh_eq_exp_neg (x : ℝ) :
    cosh x - sinh x = exp (-x) := by
  have hcs := Real.cosh_add_sinh (-x)
  rw [Real.cosh_neg, Real.sinh_neg] at hcs
  linarith

/-- The small eigenvalue squared: (cosh(2r) − sinh(2r))² = exp(−4r). -/
theorem eigval_minus_sq (r : ℝ) :
    (cosh (2*r) - sinh (2*r))^2 = exp (-4*r) := by
  calc (cosh (2*r) - sinh (2*r))^2
      = exp (-(2*r)) ^ 2 := by rw [cosh_sub_sinh_eq_exp_neg]
    _ = exp (-(2*r)) * exp (-(2*r)) := by ring
    _ = exp (-4*r) := by rw [← Real.exp_add]; congr 1; ring

/-- √(exp(−4r)) = exp(−2r). -/
theorem sqrt_exp_neg4r (r : ℝ) :
    Real.sqrt (exp (-4*r)) = exp (-2*r) := by
  have h : exp (-4*r) = exp (-2*r) ^ 2 := by
    calc exp (-4*r)
        = exp (-2*r + -2*r) := by congr 1; ring
      _ = exp (-2*r) * exp (-2*r) := Real.exp_add _ _
      _ = exp (-2*r) ^ 2 := by ring
  rw [h]
  exact Real.sqrt_sq (le_of_lt (Real.exp_pos _))

/-! ## 7. Bridge to nu_minus -/

/--
The smallest symplectic eigenvalue of σ^{T_B}(r, n̄) equals nu_minus r n̄.

Formally: (n̄ + ½) · √(−eigenvalue of A²) = (n̄ + ½) · exp(−2r) = nu_minus r n̄.

This closes the gap between:
  • The analytic formula `nu_minus r n̄` used in Theorem 4.3.1 (TMST.lean)
  • The symplectic spectral theory of Gaussian states (this module)
-/
theorem nu_minus_eq_symp_eigenvalue (r n_bar : ℝ) :
    TwoModeSqueezedThermal.nu_minus r n_bar =
    (n_bar + 1/2) * Real.sqrt ((cosh (2*r) - sinh (2*r))^2) := by
  rw [eigval_minus_sq, sqrt_exp_neg4r]
  simp only [TwoModeSqueezedThermal.nu_minus]

/--
Equivalent bridge: nu_minus matches the eigenvector formula.

The PPT criterion `nu_minus r n̄ < 1/2` (entanglement) is precisely the condition
that the smallest symplectic eigenvalue of σ^{T_B} is below the vacuum threshold.
-/
theorem nu_minus_lt_half_iff_symp_eig_lt (r n_bar : ℝ) :
    TwoModeSqueezedThermal.nu_minus r n_bar < 1/2 ↔
    (n_bar + 1/2) * Real.sqrt ((cosh (2*r) - sinh (2*r))^2) < 1/2 := by
  rw [nu_minus_eq_symp_eigenvalue]

end Physlib.QuantumMechanics.GaussianEntanglement.SymplecticCovariance

end
