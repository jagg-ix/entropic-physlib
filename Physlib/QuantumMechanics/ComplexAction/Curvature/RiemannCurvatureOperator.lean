/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.WeylTensorTraceFree

/-!
# The Ricci contraction operator, the Einstein tensor, and the tetrad metric

Connects the 4-index Riemann/Weyl curvature tensors (`Curvature.RiemannCurvatureTensor`, `Curvature.WeylTensorTraceFree`) to the
rest of physlib's tensor/operator machinery.

* **§A — the Ricci contraction as a linear operator.** The metric contraction `Rm ↦ gᵃᶜ R_{abcd}` is an
  `ℝ`-linear map `ricciLinearMap : RiemannTensor ι →ₗ[ℝ] Matrix ι ι ℝ` (`ricciLinearMap_apply`,
  `ricci_add`, `ricci_smul`). The trace-free property of the Weyl tensor is then exactly the statement that
  **the Weyl tensor lies in the kernel of the Ricci operator** (`weyl_mem_ker_ricciLinearMap`).
* **§B — the Einstein tensor from the 4-index curvature.** Feeding the contracted Ricci and scalar curvature
  into the matrix `einsteinTensor` (`ComplexEinstein.EinsteinFieldEquationsPhysLean`) gives the Einstein tensor of a
  Riemann tensor (`curvatureEinsteinTensor`); it splits as traceless Ricci plus a scalar term
  (`curvatureEinsteinTensor_eq_tracelessRicci`) and vanishes in vacuum
  (`curvatureEinsteinTensor_vacuum`).
* **§C — on the tetrad metric.** The trace-free property holds for the Levi-Civita/Lusanna tetrad metric
  `g = coordCongruence E η` (`LeviCivita.TetradInvariant`), whose symmetry comes for free from a
  symmetric `η` (`weyl_traceFree_tetrad`).

## References

* F. Moulin (2024), arXiv:2405.03698; L. P. Eisenhart. structure: `Physlib`.

No new axioms.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.ArbitraryCoordinates

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §A — the Ricci contraction as a linear operator -/

/-- **The Ricci contraction as an `ℝ`-linear operator** `Rm ↦ gᵃᶜ R_{abcd}` from 4-index Riemann tensors to
the 2-index Ricci `Matrix`. -/
noncomputable def ricciLinearMap (gInv : Matrix ι ι ℝ) : RiemannTensor ι →ₗ[ℝ] Matrix ι ι ℝ where
  toFun := ricci gInv
  map_add' Rm1 Rm2 := by
    ext b d
    simp only [ricci, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' c Rm := by
    ext b d
    simp only [ricci, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c' _ => by ring

omit [DecidableEq ι] in
@[simp] theorem ricciLinearMap_apply (gInv : Matrix ι ι ℝ) (Rm : RiemannTensor ι) :
    ricciLinearMap gInv Rm = ricci gInv Rm := rfl

omit [DecidableEq ι] in
/-- **[The Ricci contraction is additive] `Ric(Rm₁ + Rm₂) = Ric Rm₁ + Ric Rm₂`.** -/
theorem ricci_add (gInv : Matrix ι ι ℝ) (Rm1 Rm2 : RiemannTensor ι) :
    ricci gInv (Rm1 + Rm2) = ricci gInv Rm1 + ricci gInv Rm2 :=
  (ricciLinearMap gInv).map_add Rm1 Rm2

omit [DecidableEq ι] in
/-- **[The Ricci contraction is homogeneous] `Ric(c • Rm) = c • Ric Rm`.** -/
theorem ricci_smul (gInv : Matrix ι ι ℝ) (c : ℝ) (Rm : RiemannTensor ι) :
    ricci gInv (c • Rm) = c • ricci gInv Rm :=
  (ricciLinearMap gInv).map_smul c Rm

variable {g gInv : Matrix ι ι ℝ}

/-- **[The Weyl tensor lies in the kernel of the Ricci operator].** The operator-theoretic form of trace-
freeness: `C ∈ ker(Ricci contraction)`. -/
theorem weyl_mem_ker_ricciLinearMap (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0) :
    weylTensor (Fintype.card ι) g (ricci gInv Rm) (scalarCurvature gInv Rm) Rm
      ∈ LinearMap.ker (ricciLinearMap gInv) := by
  rw [LinearMap.mem_ker, ricciLinearMap_apply]
  ext b d
  simpa using weyl_traceFree hg hgi hinv h hn1 hn2 b d

/-! ## §B — the Einstein tensor from the 4-index curvature -/

/-- **The Einstein tensor of a 4-index Riemann tensor** `G_{bd} = R_{bd} − ½ R g_{bd}`, built by contracting
the Riemann tensor and feeding the matrix `einsteinTensor`. -/
noncomputable def curvatureEinsteinTensor (gInv g : Matrix ι ι ℝ) (Rm : RiemannTensor ι) : Matrix ι ι ℝ :=
  einsteinTensor (ricci gInv Rm) (scalarCurvature gInv Rm) g

omit [DecidableEq ι] in
/-- **[Einstein tensor splits as traceless Ricci + scalar]** `G = S + (R/n − R/2) g`. -/
theorem curvatureEinsteinTensor_eq_tracelessRicci (gInv g : Matrix ι ι ℝ) (Rm : RiemannTensor ι) :
    curvatureEinsteinTensor gInv g Rm
      = tracelessRicci (ricci gInv Rm) g (scalarCurvature gInv Rm) (Fintype.card ι)
        + (scalarCurvature gInv Rm / (Fintype.card ι) - scalarCurvature gInv Rm / 2) • g :=
  einsteinTensor_eq_tracelessRicci_add _ _ _ _

/-- **[Vacuum ⇒ zero Einstein tensor] `Rm = 0 ⇒ G = 0`.** -/
@[simp] theorem curvatureEinsteinTensor_vacuum (gInv g : Matrix ι ι ℝ) :
    curvatureEinsteinTensor gInv g (0 : RiemannTensor ι) = 0 := by
  simp [curvatureEinsteinTensor, scalarCurvature, ricciScalarContraction, einsteinTensor]

/-! ## §C — on the tetrad metric -/

/-- **[The Weyl tensor is trace-free on the Lusanna/Levi-Civita tetrad metric] `g = coordCongruence E η`.**
The metric symmetry is inherited from a symmetric Minkowski `η`. -/
theorem weyl_traceFree_tetrad (E η gInv : Matrix ι ι ℝ) (hη : ηᵀ = η)
    (hgi : gInvᵀ = gInv) (hinv : gInv * coordCongruence E η = 1)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0) (b d : ι) :
    ricci gInv (weylTensor (Fintype.card ι) (coordCongruence E η)
      (ricci gInv Rm) (scalarCurvature gInv Rm) Rm) b d = 0 :=
  weyl_traceFree (coordCongruence_isSymm E η hη) hgi hinv h hn1 hn2 b d

end Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

end
