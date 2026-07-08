/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.MoulinDoubleDualCotton
public import Physlib.QuantumMechanics.ComplexAction.Curvature.WeylTensorSymmetries
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation
public import Mathlib.Tactic.LinearCombination

/-!
# The double-dual Riemann tensor is a curvature tensor, and the Bianchi link

Connects the double (Hodge) dual Riemann tensor and the Weyl tensor (`GravitationalFieldEquations.MoulinDoubleDualCotton`,
`Curvature.WeylTensorSymmetries`) to the existing first-Bianchi infrastructure of `LeviCivita.BianchiValidation`.

* **§A — the double-dual is a curvature tensor.** `*R*_{ijkl}` includes the full algebraic curvature symmetries
  (`isRiemannCurvature_doubleDualRiemann`), just as the Weyl tensor does — both being built linearly from a
  Riemann tensor and metric terms.
* **§B — the Bianchi link.** The `bianchi` field of `IsRiemannCurvature` *is* the `FirstBianchi` predicate of
  `LeviCivita.BianchiValidation` (`IsRiemannCurvature.firstBianchi`), so every curvature tensor in this
  development — the Riemann tensor, the Weyl tensor, the double-dual — satisfies the first Bianchi identity
  (`weyl_firstBianchi`, `doubleDual_firstBianchi`) and hence Levi-Civita's Ricci-contraction relation
  (`doubleDual_ricci_relation`).
* **§C — vacuum.** With vanishing Ricci and scalar curvature the double-dual is `−Rm`
  (`doubleDual_vacuum_eq_neg`), i.e. minus the Riemann tensor — which in vacuum is the Weyl tensor.

## References

* F. Moulin (2024), arXiv:2405.03698, §5; T. Levi-Civita. structure: `Physlib`
  (`GravitationalFieldEquations.MoulinDoubleDualCotton`, `LeviCivita.BianchiValidation`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §A — the double-dual is a curvature tensor -/

omit [Fintype ι] [DecidableEq ι] in
/-- **[The double-dual Riemann tensor has the algebraic curvature symmetries].** For a symmetric metric `g`
and symmetric Ricci `Ric`, with `Rm` a Riemann tensor, `*R*_{ijkl}` satisfies first/second-pair antisymmetry,
pair-exchange symmetry, and the first Bianchi identity — it is itself a Riemann tensor. -/
theorem isRiemannCurvature_doubleDualRiemann (scalarR : ℝ) (g Ric : Matrix ι ι ℝ)
    (hg_sym : ∀ i j, g i j = g j i) (hRic_sym : ∀ i j, Ric i j = Ric j i)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm) :
    IsRiemannCurvature (doubleDualRiemann g Ric scalarR Rm) := by
  refine ⟨fun a b c d => ?_, fun a b c d => ?_, fun a b c d => ?_, fun a b c d => ?_⟩
  · simp only [doubleDualRiemann]; rw [h.antisymm_left a b c d]; ring
  · simp only [doubleDualRiemann]; rw [h.antisymm_right a b c d]; ring
  · simp only [doubleDualRiemann]
    rw [hg_sym c a, hg_sym c b, hg_sym d a, hg_sym d b, hRic_sym d b, hRic_sym d a,
      hRic_sym c b, hRic_sym c a]
    linear_combination -h.pair_symm a b c d
  · simp only [doubleDualRiemann]
    rw [hg_sym c b, hg_sym d b, hg_sym d c, hRic_sym c b, hRic_sym d b, hRic_sym d c]
    linear_combination -h.bianchi a b c d

/-! ## §B — the Bianchi link -/

omit [Fintype ι] [DecidableEq ι] in
/-- **[`IsRiemannCurvature` implies `FirstBianchi`].** The first Bianchi identity packaged in
`IsRiemannCurvature` is exactly the `FirstBianchi` predicate of `LeviCivita.BianchiValidation`. -/
theorem IsRiemannCurvature.firstBianchi {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm) :
    FirstBianchi Rm := h.bianchi

omit [Fintype ι] [DecidableEq ι] in
/-- **[The Weyl tensor satisfies the first Bianchi identity].** -/
theorem weyl_firstBianchi (n scalarR : ℝ) (g Ric : Matrix ι ι ℝ)
    (hg_sym : ∀ i j, g i j = g j i) (hRic_sym : ∀ i j, Ric i j = Ric j i)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm) :
    FirstBianchi (weylTensor n g Ric scalarR Rm) :=
  (isRiemannCurvature_weylTensor n scalarR g Ric hg_sym hRic_sym h).firstBianchi

omit [Fintype ι] [DecidableEq ι] in
/-- **[The double-dual Riemann tensor satisfies the first Bianchi identity].** -/
theorem doubleDual_firstBianchi (scalarR : ℝ) (g Ric : Matrix ι ι ℝ)
    (hg_sym : ∀ i j, g i j = g j i) (hRic_sym : ∀ i j, Ric i j = Ric j i)
    {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm) :
    FirstBianchi (doubleDualRiemann g Ric scalarR Rm) :=
  (isRiemannCurvature_doubleDualRiemann scalarR g Ric hg_sym hRic_sym h).firstBianchi

omit [DecidableEq ι] in
/-- **[Levi-Civita's Ricci-contraction relation for the double-dual].** The two metric contractions of the
double-dual Riemann tensor are tied together by the first Bianchi identity. -/
theorem doubleDual_ricci_relation (scalarR : ℝ) (g Ric Q : Matrix ι ι ℝ)
    (hg_sym : ∀ i j, g i j = g j i) (hRic_sym : ∀ i j, Ric i j = Ric j i)
    (hQ : ∀ a b, Q a b = Q b a) {Rm : RiemannTensor ι} (h : IsRiemannCurvature Rm) (i k : ι) :
    (∑ j, ∑ l, Q j l * doubleDualRiemann g Ric scalarR Rm i j k l)
      + (∑ j, ∑ l, Q j l * doubleDualRiemann g Ric scalarR Rm i l j k) = 0 :=
  firstBianchi_ricci_relation hQ
    (isRiemannCurvature_doubleDualRiemann scalarR g Ric hg_sym hRic_sym h).antisymm_right
    (doubleDual_firstBianchi scalarR g Ric hg_sym hRic_sym h) i k

/-! ## §C — vacuum -/

omit [Fintype ι] [DecidableEq ι] in
/-- **[Vacuum double-dual is `−Rm`] `Ric = 0 ∧ R = 0 ⇒ *R* = −Rm`.** In vacuum the double-dual Riemann tensor
is minus the Riemann tensor — which there is the Weyl tensor (`weyl_eq_riemann_of_vacuum`). -/
theorem doubleDual_vacuum_eq_neg (g : Matrix ι ι ℝ) (Rm : RiemannTensor ι) :
    doubleDualRiemann g 0 0 Rm = -Rm := by
  funext i j k l; simp [doubleDualRiemann]

end Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

end
