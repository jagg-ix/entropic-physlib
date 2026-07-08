/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.EuclideanMatrix
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Vector-level and quadratic-form Wick rotation: Lorentzian → −Euclidean

The vector-level companion of
`Physlib.Relativity.EuclideanMatrix`.  Where `EuclideanMatrix.lean`
proves the matrix-level identity `Wᵀ · η · W = −1`, this module lifts
that result to **vectors** and **quadratic / bilinear forms**:

* `wickRotateVec v μ = W μ μ · v μ` — multiply the time component by `−i`,
  leave the space components unchanged.
* `minkowskiQuadForm v = vᵀ · η · v = v₀² − Σᵢ vᵢ²` — the Lorentzian
  quadratic form.
* `euclideanQuadForm v = Σ_μ vᵐ²` — the squared `ℓ²` norm.
* `minkowskiBilin u v = uᵀ · η · v` — the Lorentzian inner product.
* `euclideanBilin u v = Σ_μ uᵐ · vᵐ` — the Euclidean inner product.

## Load-bearing identities

* `minkowskiQuadFormC_wickRotateVec_eq_neg_euclideanQuadForm` —
  Lorentzian quadratic form of the Wick-rotated vector equals **minus**
  the Euclidean norm squared.
* `minkowskiBilinC_wickRotateVec_eq_neg_euclideanBilin` — the bilinear
  analog for two vectors.

Composes with `Physlib.QFT.PathIntegral.WickClock` (coordinate-level
`wickRotate_sq`) and `Physlib.Relativity.EuclideanMatrix`
(matrix-level `Wᵀ·η·W = −1`).

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity

open Complex Matrix Finset
open minkowskiMatrix

/-! ## §1 — Vector-level Wick rotation -/

/-- **Wick rotation of a Lorentzian vector.**  Multiplies the time
component by `−i`; leaves space components unchanged.  Equivalent to
left-multiplication by the diagonal matrix `wickRotationMatrix`. -/
noncomputable def wickRotateVec {d : ℕ}
    (v : (Fin 1 ⊕ Fin d) → ℝ) : (Fin 1 ⊕ Fin d) → ℂ :=
  fun μ => @wickRotationMatrix d μ μ * (v μ : ℂ)

/-- Time component of the Wick-rotated vector: `−i · v(0)`. -/
@[simp]
theorem wickRotateVec_inl_0 {d : ℕ} (v : (Fin 1 ⊕ Fin d) → ℝ) :
    wickRotateVec v (Sum.inl 0) = -Complex.I * (v (Sum.inl 0) : ℂ) := by
  unfold wickRotateVec
  rw [wickRotationMatrix.inl_0_inl_0]

/-- Space components of the Wick-rotated vector are unchanged. -/
@[simp]
theorem wickRotateVec_inr {d : ℕ} (v : (Fin 1 ⊕ Fin d) → ℝ) (i : Fin d) :
    wickRotateVec v (Sum.inr i) = (v (Sum.inr i) : ℂ) := by
  unfold wickRotateVec
  rw [wickRotationMatrix.inr_i_inr_i, one_mul]

/-! ## §2 — Helper: `(-i)² = -1` -/

/-- The squared Wick scalar `(−i)² = −1`. -/
private lemma neg_I_sq : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
  rw [show -Complex.I * -Complex.I = Complex.I * Complex.I from by ring,
    Complex.I_mul_I]

/-! ## §3 — Lorentzian and Euclidean quadratic forms -/

/-- **Lorentzian quadratic form** `vᵀ · η · v = v₀² − Σᵢ vᵢ²`. -/
noncomputable def minkowskiQuadForm {d : ℕ}
    (v : (Fin 1 ⊕ Fin d) → ℝ) : ℝ :=
  ∑ μ : Fin 1 ⊕ Fin d, @minkowskiMatrix d μ μ * v μ ^ 2

/-- **Euclidean quadratic form** `vᵀ · δ · v = Σ_μ vᵐ²`. -/
noncomputable def euclideanQuadForm {d : ℕ}
    (v : (Fin 1 ⊕ Fin d) → ℝ) : ℝ :=
  ∑ μ : Fin 1 ⊕ Fin d, v μ ^ 2

/-- The Euclidean quadratic form is non-negative. -/
theorem euclideanQuadForm_nonneg {d : ℕ} (v : (Fin 1 ⊕ Fin d) → ℝ) :
    0 ≤ euclideanQuadForm v := by
  unfold euclideanQuadForm
  exact Finset.sum_nonneg (fun μ _ => sq_nonneg _)

/-- **Lorentzian quadratic form, expanded into time and space sums**:
`v₀² − Σᵢ vᵢ²`. -/
theorem minkowskiQuadForm_eq_time_minus_space {d : ℕ}
    (v : (Fin 1 ⊕ Fin d) → ℝ) :
    minkowskiQuadForm v =
      v (Sum.inl 0) ^ 2 - ∑ i : Fin d, v (Sum.inr i) ^ 2 := by
  unfold minkowskiQuadForm
  rw [Fintype.sum_sum_type, Fin.sum_univ_one,
    minkowskiMatrix.inl_0_inl_0]
  have hsp :
      ∑ i : Fin d, @minkowskiMatrix d (Sum.inr i) (Sum.inr i)
            * v (Sum.inr i) ^ 2 =
        -(∑ i : Fin d, v (Sum.inr i) ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [minkowskiMatrix.inr_i_inr_i]; ring
  rw [hsp]; ring

/-- **Euclidean quadratic form, expanded into time and space sums**:
`v₀² + Σᵢ vᵢ²`. -/
theorem euclideanQuadForm_eq_time_plus_space {d : ℕ}
    (v : (Fin 1 ⊕ Fin d) → ℝ) :
    euclideanQuadForm v =
      v (Sum.inl 0) ^ 2 + ∑ i : Fin d, v (Sum.inr i) ^ 2 := by
  unfold euclideanQuadForm
  rw [Fintype.sum_sum_type, Fin.sum_univ_one]

/-! ## §4 — Wick rotation: Lorentzian quadratic form → −Euclidean -/

/-- The **complexified Lorentzian quadratic form** on a complex vector. -/
noncomputable def minkowskiQuadFormC {d : ℕ}
    (v : (Fin 1 ⊕ Fin d) → ℂ) : ℂ :=
  ∑ μ : Fin 1 ⊕ Fin d, @minkowskiMatrixC d μ μ * v μ ^ 2

/-- **Key vector-level identity.**  The Lorentzian quadratic form
evaluated at the Wick-rotated vector equals **minus** the Euclidean
quadratic form. -/
theorem minkowskiQuadFormC_wickRotateVec_eq_neg_euclideanQuadForm
    {d : ℕ} (v : (Fin 1 ⊕ Fin d) → ℝ) :
    minkowskiQuadFormC (wickRotateVec v) =
      -((euclideanQuadForm v : ℝ) : ℂ) := by
  -- Per-index identity: `η_μμ · (W·v) μ² = −(v μ : ℂ)²` for every μ.
  have h : ∀ μ : Fin 1 ⊕ Fin d,
      @minkowskiMatrixC d μ μ * (wickRotateVec v μ) ^ 2 =
        -((v μ : ℂ)) ^ 2 := by
    intro μ
    rw [minkowskiMatrixC_as_diagonal, Matrix.diagonal_apply_eq]
    cases μ with
    | inl i =>
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        subst hi
        rw [wickRotateVec_inl_0]
        simp only [Sum.elim_inl]
        rw [mul_pow]
        rw [show (-Complex.I) ^ 2 = (-1 : ℂ) from by
          rw [pow_two]; exact neg_I_sq]
        ring
    | inr i =>
        rw [wickRotateVec_inr]
        simp only [Sum.elim_inr]
        ring
  unfold minkowskiQuadFormC euclideanQuadForm
  rw [Finset.sum_congr rfl (fun μ _ => h μ)]
  rw [Finset.sum_neg_distrib]
  congr 1
  have hmap :=
    map_sum Complex.ofRealHom (fun μ : Fin 1 ⊕ Fin d => v μ ^ 2) Finset.univ
  simp only [Complex.ofRealHom_eq_coe, Complex.ofReal_pow] at hmap
  exact hmap.symm

/-! ## §5 — Bilinear form: Lorentzian inner product → −Euclidean -/

/-- **Lorentzian inner product** `uᵀ · η · v = u₀·v₀ − Σᵢ uᵢ·vᵢ`. -/
noncomputable def minkowskiBilin {d : ℕ}
    (u v : (Fin 1 ⊕ Fin d) → ℝ) : ℝ :=
  ∑ μ : Fin 1 ⊕ Fin d, @minkowskiMatrix d μ μ * u μ * v μ

/-- **Euclidean inner product** `uᵀ · δ · v = Σ_μ uᵐ · vᵐ`. -/
noncomputable def euclideanBilin {d : ℕ}
    (u v : (Fin 1 ⊕ Fin d) → ℝ) : ℝ :=
  ∑ μ : Fin 1 ⊕ Fin d, u μ * v μ

/-- The Euclidean bilinear form expanded by time + space. -/
theorem euclideanBilin_eq_time_plus_space {d : ℕ}
    (u v : (Fin 1 ⊕ Fin d) → ℝ) :
    euclideanBilin u v =
      u (Sum.inl 0) * v (Sum.inl 0) +
        ∑ i : Fin d, u (Sum.inr i) * v (Sum.inr i) := by
  unfold euclideanBilin
  rw [Fintype.sum_sum_type, Fin.sum_univ_one]

/-- The Lorentzian bilinear form expanded by time + space. -/
theorem minkowskiBilin_eq_time_minus_space {d : ℕ}
    (u v : (Fin 1 ⊕ Fin d) → ℝ) :
    minkowskiBilin u v =
      u (Sum.inl 0) * v (Sum.inl 0) -
        ∑ i : Fin d, u (Sum.inr i) * v (Sum.inr i) := by
  unfold minkowskiBilin
  rw [Fintype.sum_sum_type, Fin.sum_univ_one,
    minkowskiMatrix.inl_0_inl_0]
  have hsp :
      ∑ i : Fin d, @minkowskiMatrix d (Sum.inr i) (Sum.inr i)
            * u (Sum.inr i) * v (Sum.inr i) =
        -(∑ i : Fin d, u (Sum.inr i) * v (Sum.inr i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [minkowskiMatrix.inr_i_inr_i]; ring
  rw [hsp]; ring

/-- **Complexified Lorentzian bilinear form**. -/
noncomputable def minkowskiBilinC {d : ℕ}
    (u v : (Fin 1 ⊕ Fin d) → ℂ) : ℂ :=
  ∑ μ : Fin 1 ⊕ Fin d, @minkowskiMatrixC d μ μ * u μ * v μ

/-- **Bilinear vector-level identity**: the complex Lorentzian inner
product of two Wick-rotated vectors equals **minus** the Euclidean
inner product. -/
theorem minkowskiBilinC_wickRotateVec_eq_neg_euclideanBilin
    {d : ℕ} (u v : (Fin 1 ⊕ Fin d) → ℝ) :
    minkowskiBilinC (wickRotateVec u) (wickRotateVec v) =
      -((euclideanBilin u v : ℝ) : ℂ) := by
  -- Per-index identity: η_μμ · (W·u) μ · (W·v) μ = −(u μ · v μ : ℂ).
  have h : ∀ μ : Fin 1 ⊕ Fin d,
      @minkowskiMatrixC d μ μ
            * (wickRotateVec u μ) * (wickRotateVec v μ) =
        -((u μ : ℂ) * (v μ : ℂ)) := by
    intro μ
    rw [minkowskiMatrixC_as_diagonal, Matrix.diagonal_apply_eq]
    cases μ with
    | inl i =>
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        subst hi
        rw [wickRotateVec_inl_0, wickRotateVec_inl_0]
        simp only [Sum.elim_inl]
        rw [show (1 : ℂ) * (-Complex.I * (u (Sum.inl 0) : ℂ))
                * (-Complex.I * (v (Sum.inl 0) : ℂ))
              = (-Complex.I * -Complex.I)
                  * ((u (Sum.inl 0) : ℂ) * (v (Sum.inl 0) : ℂ)) from by ring,
          neg_I_sq]
        ring
    | inr i =>
        rw [wickRotateVec_inr, wickRotateVec_inr]
        simp only [Sum.elim_inr]
        ring
  unfold minkowskiBilinC euclideanBilin
  rw [Finset.sum_congr rfl (fun μ _ => h μ)]
  rw [Finset.sum_neg_distrib]
  congr 1
  have hmap :=
    map_sum Complex.ofRealHom
      (fun μ : Fin 1 ⊕ Fin d => u μ * v μ) Finset.univ
  simp only [Complex.ofRealHom_eq_coe, Complex.ofReal_mul] at hmap
  exact hmap.symm

/-! ## §6 — Wick-rotated time-element preserves space, flips time -/

/-- The **squared Wick-rotated time component** is `−v₀²`: this is the
vector-level expression of the metric-signature flip
`dt² ↦ −dτ_E²`. -/
theorem wickRotateVec_inl_0_sq {d : ℕ} (v : (Fin 1 ⊕ Fin d) → ℝ) :
    (wickRotateVec v (Sum.inl 0)) ^ 2 = -((v (Sum.inl 0) : ℂ) ^ 2) := by
  rw [wickRotateVec_inl_0, mul_pow]
  rw [show (-Complex.I) ^ 2 = (-1 : ℂ) from by
    rw [pow_two]; exact neg_I_sq]
  ring

/-- The **squared Wick-rotated space component** is `+vᵢ²` (unchanged). -/
theorem wickRotateVec_inr_sq {d : ℕ} (v : (Fin 1 ⊕ Fin d) → ℝ)
    (i : Fin d) :
    (wickRotateVec v (Sum.inr i)) ^ 2 = (v (Sum.inr i) : ℂ) ^ 2 := by
  rw [wickRotateVec_inr]

end Physlib.Relativity

end
