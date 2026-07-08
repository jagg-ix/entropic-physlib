/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureOperator
public import Mathlib.Tactic.LinearCombination

/-!
# The Weyl tensor has the algebraic symmetries of a curvature tensor

Completes the characterization of the Weyl conformal tensor (`weylTensor`, Moulin 2024 Eq. 35): beyond being
trace-free (`weyl_traceFree`), it includes the **full algebraic curvature symmetries** of the Riemann tensor —
`IsRiemannCurvature (weylTensor n g Ric scalarR Rm)` (`isRiemannCurvature_weylTensor`), for a symmetric metric
`g` and symmetric Ricci `Ric`, given that `Rm` is itself a Riemann tensor (Moulin Eq. 2: `R_{ijkl} = −R_{jikl}
= −R_{ijlk} = R_{klij}` plus the first Bianchi identity).

The two metric-built correction terms — `g_{ac}R_{bd} − g_{ad}R_{bc} − g_{bc}R_{ad} + g_{bd}R_{ac}` and
`g_{ac}g_{bd} − g_{ad}g_{bc}` — are designed to have exactly these symmetries (Moulin §2.1), so the antisymmetries
hold by pure algebra, the pair-exchange and first Bianchi by the symmetry of `g` and `Ric`.

Combined with `weyl_traceFree`, this says the Weyl tensor is the **trace-free part of the Riemann tensor**: a
curvature tensor whose every contraction vanishes (`weyl_isTraceFreeCurvature`).

## References

* F. Moulin (2024), arXiv:2405.03698, §2.1 and Eq. 35; L. P. Eisenhart. structure: `Physlib`
  (`Curvature.RiemannCurvatureTensor`, `Curvature.WeylTensorTraceFree`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

open Matrix

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **[The Weyl tensor has the algebraic curvature symmetries].** For a symmetric metric `g` and symmetric
Ricci `Ric`, with `Rm` a Riemann tensor, the Weyl tensor satisfies first/second-pair antisymmetry,
pair-exchange symmetry, and the first Bianchi identity. -/
theorem isRiemannCurvature_weylTensor (n scalarR : ℝ) (g Ric : Matrix ι ι ℝ)
    (hg_sym : ∀ i j, g i j = g j i) (hRic_sym : ∀ i j, Ric i j = Ric j i)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm) :
    IsRiemannCurvature (weylTensor n g Ric scalarR Rm) := by
  refine ⟨fun a b c d => ?_, fun a b c d => ?_, fun a b c d => ?_, fun a b c d => ?_⟩
  · -- antisymmetry in the first pair
    simp only [weylTensor]; rw [h.antisymm_left a b c d]; ring
  · -- antisymmetry in the second pair
    simp only [weylTensor]; rw [h.antisymm_right a b c d]; ring
  · -- pair-exchange symmetry
    simp only [weylTensor]
    rw [hg_sym c a, hg_sym c b, hg_sym d a, hg_sym d b, hRic_sym d b, hRic_sym d a,
      hRic_sym c b, hRic_sym c a]
    linear_combination h.pair_symm a b c d
  · -- first Bianchi identity
    simp only [weylTensor]
    rw [hg_sym c b, hg_sym d b, hg_sym d c, hRic_sym c b, hRic_sym d b, hRic_sym d c]
    linear_combination h.bianchi a b c d

variable {g gInv : Matrix ι ι ℝ}

/-- **[The Weyl tensor is a trace-free curvature tensor].** With `Ric = ricci gInv Rm` (symmetric by
`ricci_symm`), the Weyl tensor of a Riemann tensor is itself a Riemann tensor (`IsRiemannCurvature`) *and*
trace-free (`ricci gInv (weylTensor …) = 0`) — the trace-free part of the Riemann tensor. -/
theorem weyl_isTraceFreeCurvature (hg : gᵀ = g) (hgi : gInvᵀ = gInv) (hinv : gInv * g = 1)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm)
    (hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0) (hn2 : ((Fintype.card ι : ℝ) - 2) ≠ 0) :
    IsRiemannCurvature (weylTensor (Fintype.card ι) g (ricci gInv Rm) (scalarCurvature gInv Rm) Rm)
      ∧ ∀ b d, ricci gInv (weylTensor (Fintype.card ι) g
          (ricci gInv Rm) (scalarCurvature gInv Rm) Rm) b d = 0 := by
  have g_sym : ∀ i j, g i j = g j i := fun i j => by
    have := congrFun (congrFun hg j) i; rwa [Matrix.transpose_apply] at this
  refine ⟨isRiemannCurvature_weylTensor _ _ g (ricci gInv Rm) g_sym
    (ricci_symm gInv Rm hgi h) h, ?_⟩
  intro b d
  exact weyl_traceFree hg hgi hinv h hn1 hn2 b d

end Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

end
