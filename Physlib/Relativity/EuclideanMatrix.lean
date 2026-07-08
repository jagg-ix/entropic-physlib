/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.MinkowskiMatrix
public import Mathlib.Data.Complex.Basic

/-!
# Euclidean metric matrix and Wick rotation at the matrix / typed-tensor level

The companion to `Physlib.Relativity.MinkowskiMatrix`: the **Euclidean metric
matrix** `δ = diag(1, 1, …, 1)` (the identity matrix in `(d+1)`-dimensions)
together with the typed **Wick-rotation matrix** `W = diag(−i, 1, 1, …, 1)`
which Wick-rotates the time component of a Lorentzian vector.

## The load-bearing identity

`Wᵀ · η · W = −1`

(or equivalently `Wᵀ · η · W = −(euclideanMatrix : Matrix _ _ ℂ)`), where `η`
is the Minkowski matrix.  Reading row-by-row:

* time entry `(0, 0)`: `(−i)² · 1 = −1`;
* space entries `(i, i)` for `i ≥ 1`: `1² · (−1) = −1`;
* off-diagonals: `0`.

The result is that the Lorentzian quadratic form `vᵀ η v` evaluated at the
**Wick-rotated vector** `W·v` (time component multiplied by `−i`) equals
`−vᵀ·v` — **minus the Euclidean norm squared**.  This is the standard
"Lorentzian → Euclidean" reduction at the typed-matrix level.

## Structure

* `euclideanMatrix : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ` — the
  Euclidean identity metric.  Components and self-inverting property.
* `wickRotationMatrix : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℂ` — the
  diagonal complex Wick-rotation matrix.  Components and transpose
  identity.
* `wickRotation_of_minkowski_eq_neg_euclidean` — the key matrix-level
  identity `Wᵀ · η · W = −1`.

-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Relativity

open Matrix Complex
open minkowskiMatrix

/-! ## §1 — Euclidean metric matrix `δ = diag(1, 1, …, 1)` -/

/-- **Euclidean metric matrix** in `(d+1)`-dimensions: the identity matrix
`diag(1, 1, …, 1)` on `Fin 1 ⊕ Fin d`, the same index space as
`minkowskiMatrix`.  This is the all-`+` signature metric that the
Lorentzian Minkowski metric Wick-rotates to (up to a global sign). -/
def euclideanMatrix {d : ℕ} : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ := 1

namespace euclideanMatrix

variable {d : ℕ}

/-- The Euclidean metric as a diagonal matrix `diag(1, 1, …, 1)`. -/
lemma as_diagonal : @euclideanMatrix d = diagonal (fun _ => 1) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [euclideanMatrix]
  · simp [euclideanMatrix, diagonal, h]

/-- Notation `δ` for the Euclidean metric matrix (scoped to this namespace). -/
scoped notation "δ" => @euclideanMatrix

/-- The time-time component of the Euclidean metric is `1`. -/
@[simp]
lemma inl_0_inl_0 : (@euclideanMatrix d) (Sum.inl 0) (Sum.inl 0) = 1 :=
  Matrix.one_apply_eq _

/-- The space-space diagonal components of the Euclidean metric are `1`. -/
@[simp]
lemma inr_i_inr_i (i : Fin d) :
    (@euclideanMatrix d) (Sum.inr i) (Sum.inr i) = 1 :=
  Matrix.one_apply_eq _

/-- The off-diagonal components of the Euclidean metric are `0`. -/
@[simp]
lemma off_diag_zero {μ ν : Fin 1 ⊕ Fin d} (h : μ ≠ ν) :
    (@euclideanMatrix d) μ ν = 0 :=
  Matrix.one_apply_ne h

/-- The Euclidean metric is self-inverting (`δ² = 1`). -/
@[simp]
lemma sq : @euclideanMatrix d * euclideanMatrix = 1 := by
  unfold euclideanMatrix
  exact one_mul _

end euclideanMatrix

/-! ## §2 — Wick-rotation matrix `W = diag(−i, 1, 1, …, 1)` -/

/-- **Wick-rotation matrix** `W = diag(−i, 1, 1, …, 1)` over `ℂ`.

Acting on a Lorentzian vector `v` by `W · v`, this multiplies the time
component by `−i` and leaves the space components unchanged — the
coordinate-level realisation of the substitution `t = −i · τ_E`. -/
noncomputable def wickRotationMatrix {d : ℕ} :
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℂ :=
  Matrix.diagonal (Sum.elim (fun _ => -Complex.I) (fun _ => 1))

namespace wickRotationMatrix

variable {d : ℕ}

/-- The time-time component is `−i`. -/
@[simp]
lemma inl_0_inl_0 :
    (@wickRotationMatrix d) (Sum.inl 0) (Sum.inl 0) = -Complex.I := by
  simp [wickRotationMatrix, Matrix.diagonal_apply_eq]

/-- The space diagonal components are `1`. -/
@[simp]
lemma inr_i_inr_i (i : Fin d) :
    (@wickRotationMatrix d) (Sum.inr i) (Sum.inr i) = 1 := by
  simp [wickRotationMatrix, Matrix.diagonal_apply_eq]

/-- The off-diagonal components are `0`. -/
@[simp]
lemma off_diag_zero {μ ν : Fin 1 ⊕ Fin d} (h : μ ≠ ν) :
    (@wickRotationMatrix d) μ ν = 0 := by
  simp [wickRotationMatrix, Matrix.diagonal_apply_ne _ h]

/-- The Wick-rotation matrix is diagonal, hence symmetric (its transpose
equals itself). -/
@[simp]
lemma transpose_eq : (@wickRotationMatrix d).transpose = wickRotationMatrix := by
  unfold wickRotationMatrix
  exact Matrix.diagonal_transpose _

/-- Squaring the Wick-rotation matrix gives `diag(−1, 1, 1, …, 1)`. -/
lemma sq :
    @wickRotationMatrix d * wickRotationMatrix =
      Matrix.diagonal (Sum.elim (fun _ => (-1 : ℂ)) (fun _ => 1)) := by
  unfold wickRotationMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext μ
  cases μ with
  | inl _ =>
      simp only [Sum.elim_inl]
      have : -Complex.I * -Complex.I = Complex.I * Complex.I := by ring
      rw [this, Complex.I_mul_I]
  | inr _ => simp [Sum.elim_inr]

end wickRotationMatrix

/-! ## §3 — Wick rotation of the Minkowski metric

The key matrix-level identity: under similarity by the Wick-rotation matrix
`W`, the Minkowski metric `η` becomes `−1` (minus the Euclidean identity). -/

/-- The Minkowski matrix as a complex matrix (via the real-to-complex
coercion `Complex.ofReal`). -/
noncomputable def minkowskiMatrixC {d : ℕ} :
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℂ :=
  (@minkowskiMatrix d).map (fun x : ℝ => (x : ℂ))

/-- The complexified Minkowski matrix is `diag(1, −1, …, −1)` over `ℂ`. -/
lemma minkowskiMatrixC_as_diagonal {d : ℕ} :
    @minkowskiMatrixC d =
      Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext i j
  unfold minkowskiMatrixC
  rw [Matrix.map_apply]
  cases i with
  | inl i₀ => cases j with
    | inl j₀ =>
        have hi : i₀ = (0 : Fin 1) := Subsingleton.elim _ _
        have hj : j₀ = (0 : Fin 1) := Subsingleton.elim _ _
        subst hi; subst hj
        rw [minkowskiMatrix.inl_0_inl_0]
        simp [Matrix.diagonal_apply_eq]
    | inr j₁ =>
        have hne : (Sum.inl i₀ : Fin 1 ⊕ Fin d) ≠ Sum.inr j₁ := by
          intro hh; cases hh
        simp
  | inr i₁ => cases j with
    | inl j₀ =>
        have hne : (Sum.inr i₁ : Fin 1 ⊕ Fin d) ≠ Sum.inl j₀ := by
          intro hh; cases hh
        simp
    | inr j₁ =>
        by_cases h : i₁ = j₁
        · subst h
          simp [minkowskiMatrix.inr_i_inr_i, Matrix.diagonal_apply_eq]
        · have hne : (Sum.inr i₁ : Fin 1 ⊕ Fin d) ≠ Sum.inr j₁ := by
            intro hh; injection hh; contradiction
          simp [minkowskiMatrix.off_diag_zero hne,
            Matrix.diagonal_apply_ne _ hne]

/-- **Key matrix-level identity (Wick rotation of the Minkowski metric).**

Under similarity by the Wick-rotation matrix `W = diag(−i, 1, …, 1)`, the
Minkowski metric `η` becomes `−1` (minus the Euclidean identity):

  `Wᵀ · η · W  =  −1  =  −(euclideanMatrix : ℂ)`.

Reading the diagonal entries:

* `(0, 0)` (time): `(−i) · 1 · (−i) = −1`;
* `(i, i)` (space) for `i ≥ 1`: `1 · (−1) · 1 = −1`.

Off-diagonals are zero because `W`, `η`, and their product are all
diagonal. -/
theorem wickRotation_of_minkowski_eq_neg_euclidean {d : ℕ} :
    (@wickRotationMatrix d).transpose * @minkowskiMatrixC d *
        @wickRotationMatrix d =
      -(1 : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℂ) := by
  rw [wickRotationMatrix.transpose_eq, minkowskiMatrixC_as_diagonal,
    wickRotationMatrix]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  rw [show -(1 : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℂ) =
      Matrix.diagonal (fun _ => (-1 : ℂ)) from by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.diagonal_apply_eq, Matrix.neg_apply, Matrix.one_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.neg_apply, Matrix.one_apply_ne h]]
  congr 1
  funext μ
  cases μ with
  | inl _ =>
      simp only [Sum.elim_inl]
      have : -Complex.I * (1 : ℂ) * -Complex.I = Complex.I * Complex.I := by ring
      rw [this, Complex.I_mul_I]
  | inr _ => simp [Sum.elim_inr]

/-- **Equivalent identification**: the Wick-rotated Minkowski metric is the
negative of the (complexified) Euclidean metric. -/
theorem wickRotation_of_minkowski_eq_neg_euclidean_matrix {d : ℕ} :
    (@wickRotationMatrix d).transpose * @minkowskiMatrixC d *
        @wickRotationMatrix d =
      -((@euclideanMatrix d).map (fun x : ℝ => (x : ℂ))) := by
  rw [wickRotation_of_minkowski_eq_neg_euclidean]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.neg_apply, Matrix.one_apply_eq, euclideanMatrix]
  · simp [Matrix.neg_apply, Matrix.one_apply_ne h, euclideanMatrix]

end Physlib.Relativity

end
