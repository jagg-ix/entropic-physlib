/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.MoulinDoubleDualCotton

/-!
# Moulin's generalized field equation with a cosmological constant

Implements §5.3 of F. Moulin, *Generalization of Einstein's gravitational field equations*
(arXiv:2405.03698): the cosmological constant `Λ` is introduced into the generalized 4-index equation, and
contracting recovers Einstein's equation *with* the cosmological term.

Adding `−2Λ` to the Lagrangian modifies the 4-index field equation (Moulin Eq. 68) to

  `*R*_{ijkl} + (n−3)/(n−1) Λ (g_{ik}g_{jl} − g_{il}g_{jk}) = χ(n−3) T_{ijkl}`

(`CosmologicalFourIndexEquation`). Contracting over the first and third indices recovers Einstein's equation
with a cosmological constant (Moulin Eq. 69),

  `R_{bd} − ½ R g_{bd} + Λ g_{bd} = χ (gᵃᶜ T_{abcd})`

— physlib's `einsteinFieldEquationCosmological` (`cosmological_imp_einsteinFieldEquationCosmological`). The
contraction uses that the double-dual contracts to `(n−3)` times the Einstein tensor and the metric-structure
tensor to `(n−1)` times the metric, with the `(n−3)` factor cancelling.

## References

* F. Moulin (2024), arXiv:2405.03698, §5.3, Eqs. 67–69. Carrier: `Physlib`
  (`GravitationalFieldEquations.MoulinDoubleDualCotton`, `ComplexEinstein.EinsteinFieldEquationsPhysLean`).


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {g gInv : Matrix ι ι ℝ}

/-- **[The metric-structure tensor contracts to `(n−1) g`].** `gᵃᶜ(g_{ac}g_{bd} − g_{ad}g_{bc}) = (n−1)
g_{bd}` as a matrix identity, the constant-curvature `K = 1` model. -/
lemma ricci_constantCurvature_one (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1) :
    ricci gInv (constantCurvature 1 g) = ((Fintype.card ι : ℝ) - 1) • g := by
  ext b d
  show (∑ a, ∑ c, gInv a c * constantCurvature 1 g a b c d) = _
  simp only [constantCurvature, one_mul]
  rw [contraction_metricStructure hg hgi hinv, Matrix.smul_apply, smul_eq_mul]

/-- **Moulin's 4-index field equation with a cosmological constant** (Eq. 68)
`*R*_{ijkl} + (n−3)/(n−1) Λ (g_{ik}g_{jl} − g_{il}g_{jk}) = χ(n−3) T_{ijkl}`. -/
def CosmologicalFourIndexEquation (Λ χ : ℝ) (g Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (Rm T4 : RiemannTensor ι) : Prop :=
  doubleDualRiemann g Ric scalarR Rm
      + (((Fintype.card ι : ℝ) - 3) / ((Fintype.card ι : ℝ) - 1) * Λ) • constantCurvature 1 g
    = (χ * ((Fintype.card ι : ℝ) - 3)) • T4

/-- **[Moulin Eq. 69] the cosmological 4-index equation implies Einstein's equation with a cosmological
constant.** Contracting `*R* + (n−3)/(n−1) Λ g_{ijkl} = χ(n−3) T` over the first and third indices yields
`G_{bd} + Λ g_{bd} = χ (gᵃᶜ T_{abcd})`. -/
lemma cosmological_imp_einsteinFieldEquationCosmological (Λ χ : ℝ) (T4 : RiemannTensor ι)
    (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0)
    (hn3 : ((Fintype.card ι : ℝ) - 3) ≠ 0)
    (heq : CosmologicalFourIndexEquation Λ χ g (ricci gInv Rm) (scalarCurvature gInv Rm) Rm T4) :
    einsteinFieldEquationCosmological (ricci gInv Rm) (scalarCurvature gInv Rm) g (ricci gInv T4) Λ χ := by
  have hc := congrArg (ricciLinearMap gInv) heq
  simp only [map_add, map_smul, ricciLinearMap_apply] at hc
  rw [doubleDual_contraction hg hgi hinv h hn1 hn2 hn3, ricci_constantCurvature_one hg hgi hinv,
    smul_smul, show ((Fintype.card ι : ℝ) - 3) / ((Fintype.card ι : ℝ) - 1) * Λ
        * ((Fintype.card ι : ℝ) - 1) = ((Fintype.card ι : ℝ) - 3) * Λ from by field_simp,
    show χ * ((Fintype.card ι : ℝ) - 3) = ((Fintype.card ι : ℝ) - 3) * χ from mul_comm _ _] at hc
  rw [einsteinFieldEquationCosmological]
  refine smul_right_injective (Matrix ι ι ℝ) hn3 ?_
  show ((Fintype.card ι : ℝ) - 3) • (einsteinTensor (ricci gInv Rm) (scalarCurvature gInv Rm) g + Λ • g)
      = ((Fintype.card ι : ℝ) - 3) • (χ • ricci gInv T4)
  rw [smul_add, smul_smul, smul_smul]
  simpa using hc

end Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

end
