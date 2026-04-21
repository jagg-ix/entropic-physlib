/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Odd.BasisLinear.ShiftPlane
/-!
# The combined basis for the odd case

This file combines the symmetric and shifted planes into a single basis for the linear solutions
of `PureU1 (2 * n + 1)`. Every linear solution is the sum of a point from each plane.

## Key results

- `span_basis` : Every linear solution is the sum of a point from each plane.
- `symmPlane` : The inclusion of the symmetric plane into linear solutions.
- `shiftPlane` : The inclusion of the shifted plane into linear solutions.
- `basis_linear_independent` : The combined basis vectors are linearly independent.
- `basisAsBasis` : The combined basis as a `Basis`.

## Table of contents

- 1. The combined basis
  - 1.1. The combined basis as `LinSols`
  - 1.2. The inclusion of the span of the combined basis into charges
  - 1.3. Components of the inclusion
  - 1.4. Kernel of the inclusion into charges
  - 1.5. The inclusion of the span of the combined basis into LinSols
  - 1.6. The combined basis vectors are linearly independent
  - 1.7. Injectivity of the inclusion into linear solutions
  - 1.8. Cardinality of the basis
  - 1.9. The basis vectors as a basis
- 2. Every linear solution is the sum of a point from each plane
  - 2.1. Relation under permutations

-/

@[expose] public section

open Module Nat Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeOddPlane

/-!

## 1. The combined basis

-/

/-!

### 1.1. The combined basis as `LinSols`

-/

/-- The whole basis as `LinSols`. -/
def basis : Fin n ⊕ Fin n → (PureU1 (2 * n + 1)).LinSols := fun i =>
  match i with
  | .inl i => symmBasis i
  | .inr i => shiftBasis i

/-!

### 1.2. The inclusion of the span of the combined basis into charges

-/

/-- A point in the span of the basis as a charge. -/
def basisCharge (f : Fin n → ℚ) (g : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges :=
  symmPlaneAsCharges f + shiftPlaneAsCharges g

/-!

### 1.3. Components of the inclusion

-/

lemma basisCharge_oddShiftShiftZero (f g : Fin n.succ → ℚ) : basisCharge f g oddShiftShiftZero = f 0 := by
  rw [basisCharge]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftZero_eq_oddFst_zero]
  rw [oddShiftShiftZero_eq_oddShiftZero]
  rw [shiftPlaneAsCharges_oddShiftZero, oddShiftZero_eq_oddFst, symmPlaneAsCharges_oddFst]
  exact Rat.add_zero (f 0)

lemma basisCharge_oddShiftShiftFst (f g : Fin n.succ → ℚ) (j : Fin n) :
    basisCharge f g (oddShiftShiftFst j) = f j.succ + g j.castSucc := by
  rw [basisCharge]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftFst_eq_oddFst_succ]
  rw [oddShiftShiftFst_eq_oddShiftFst_castSucc]
  rw [shiftPlaneAsCharges_oddShiftFst, oddShiftFst_castSucc_eq_oddFst_succ, symmPlaneAsCharges_oddFst]

lemma basisCharge_oddShiftShiftMid (f g : Fin n.succ → ℚ) :
    basisCharge f g oddShiftShiftMid = g (Fin.last n) := by
  rw [basisCharge]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftMid_eq_oddMid]
  rw [oddShiftShiftMid_eq_oddShiftFst_last]
  rw [shiftPlaneAsCharges_oddShiftFst, oddShiftFst_last_eq_oddMid, symmPlaneAsCharges_oddMid]
  exact Rat.zero_add (g (Fin.last n))

lemma basisCharge_oddShiftShiftSnd (f g : Fin n.succ → ℚ) (j : Fin n.succ) :
    basisCharge f g (oddShiftShiftSnd j) = - f j - g j := by
  rw [basisCharge]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [oddShiftShiftSnd_eq_oddSnd]
  rw [oddShiftShiftSnd_eq_oddShiftSnd]
  rw [shiftPlaneAsCharges_oddShiftSnd, oddShiftSnd_eq_oddSnd, symmPlaneAsCharges_oddSnd]
  ring

/-!

### 1.4. Kernel of the inclusion into charges

-/

set_option backward.isDefEq.respectTransparency false in
lemma basisCharge_zero (f g : Fin n.succ → ℚ) (h : basisCharge f g = 0) :
    ∀ i, f i = 0 := by
  have h₃ := basisCharge_oddShiftShiftZero f g
  rw [h] at h₃
  change 0 = _ at h₃
  intro i
  have hinduc (iv : ℕ) (hiv : iv < n.succ) : f ⟨iv, hiv⟩ = 0 := by
    induction iv
    exact h₃.symm
    rename_i iv hi
    have hivi : iv < n.succ := lt_of_succ_lt hiv
    have hi2 := hi hivi
    have h1 := basisCharge_oddShiftShiftSnd f g ⟨iv, hivi⟩
    rw [h, hi2] at h1
    change 0 = _ at h1
    simp only [neg_zero, succ_eq_add_one, zero_sub, zero_eq_neg] at h1
    have h2 := basisCharge_oddShiftShiftFst f g ⟨iv, succ_lt_succ_iff.mp hiv⟩
    simp only [succ_eq_add_one, h, Fin.succ_mk, Fin.castSucc_mk, h1, add_zero] at h2
    exact h2.symm
  exact hinduc i.val i.prop

lemma basisCharge_zero_shift (f g : Fin n.succ → ℚ) (h : basisCharge f g = 0) :
    ∀ i, g i = 0 := by
  have hf := basisCharge_zero f g h
  rw [basisCharge, symmPlaneAsCharges] at h
  simp only [succ_eq_add_one, hf, zero_smul, sum_const_zero, zero_add] at h
  exact shiftPlaneAsCharges_zero g h

/-!

### 1.5. The inclusion of the span of the combined basis into LinSols

-/

/-- A point in the span of the whole basis. -/
def basisLinSol (f : (Fin n) ⊕ (Fin n) → ℚ) : (PureU1 (2 * n + 1)).LinSols :=
    ∑ i, f i • basis i

lemma basisLinSol_symmPlane_shiftPlane (f : (Fin n) ⊕ (Fin n) → ℚ) :
    basisLinSol f = symmPlane (f ∘ Sum.inl) + shiftPlane (f ∘ Sum.inr) := by
  exact Fintype.sum_sum_type _

/-!

### 1.6. The combined basis vectors are linearly independent

-/

theorem basis_linear_independent : LinearIndependent ℚ (@basis n.succ) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change basisLinSol f = 0 at h
  have h1 : (basisLinSol f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [basisLinSol_symmPlane_shiftPlane] at h1
  change (symmPlane (f ∘ Sum.inl)).val + (shiftPlane (f ∘ Sum.inr)).val = 0 at h1
  rw [shiftPlane_val, symmPlane_val] at h1
  change basisCharge (f ∘ Sum.inl) (f ∘ Sum.inr) = 0 at h1
  have hf := basisCharge_zero (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  have hg := basisCharge_zero_shift (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  intro i
  simp_all only [succ_eq_add_one, Function.comp_apply]
  cases i
  · simp_all
  · simp_all

/-!

### 1.7. Injectivity of the inclusion into linear solutions

-/

lemma basisLinSol_eq (f f' : (Fin n.succ) ⊕ (Fin n.succ) → ℚ) : basisLinSol f = basisLinSol f' ↔ f = f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · funext i
    rw [basisLinSol, basisLinSol] at h
    have h1 : ∑ i : Fin n.succ ⊕ Fin n.succ, (f i + (- f' i)) • basis i = 0 := by
      simp only [add_smul, neg_smul]
      rw [Finset.sum_add_distrib]
      rw [h]
      rw [← Finset.sum_add_distrib]
      simp
    have h2 : ∀ i, (f i + (- f' i)) = 0 := by
      exact Fintype.linearIndependent_iff.mp (@basis_linear_independent n)
        (fun i => f i + -f' i) h1
    have h2i := h2 i
    linarith
  · rw [h]

lemma basisLinSol_elim_eq_iff (g g' : Fin n.succ → ℚ) (f f' : Fin n.succ → ℚ) :
    basisLinSol (Sum.elim g f) = basisLinSol (Sum.elim g' f') ↔ basisCharge g f = basisCharge g' f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [basisLinSol_eq, Sum.elim_eq_iff] at h
    rw [h.left, h.right]
  · apply ACCSystemLinear.LinSols.ext
    rw [basisLinSol_symmPlane_shiftPlane, basisLinSol_symmPlane_shiftPlane]
    simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val,
      symmPlane_val, shiftPlane_val]
    exact h

lemma basisCharge_eq (g g' : Fin n.succ → ℚ) (f f' : Fin n.succ → ℚ) :
    basisCharge g f = basisCharge g' f' ↔ g = g' ∧ f = f' := by
  rw [← basisLinSol_elim_eq_iff]
  rw [← Sum.elim_eq_iff]
  exact basisLinSol_eq _ _

/-!

### 1.8. Cardinality of the basis

-/

lemma basis_card : Fintype.card ((Fin n.succ) ⊕ (Fin n.succ)) =
    Module.finrank ℚ (PureU1 (2 * n.succ + 1)).LinSols := by
  erw [BasisLinear.finrank_AnomalyFreeLinear]
  simp only [Fintype.card_sum, Fintype.card_fin]
  exact Eq.symm (Nat.two_mul n.succ)

/-!

### 1.9. The basis vectors as a basis

-/

/-- The basis formed out of our basis vectors. -/
noncomputable def basisAsBasis :
    Basis (Fin n.succ ⊕ Fin n.succ) ℚ (PureU1 (2 * n.succ + 1)).LinSols :=
  basisOfLinearIndependentOfCardEqFinrank (@basis_linear_independent n) basis_card

/-!

## 2. Every linear solution is the sum of a point from each plane

-/

lemma span_basis (S : (PureU1 (2 * n.succ + 1)).LinSols) :
    ∃ (g f : Fin n.succ → ℚ), S.val = symmPlaneAsCharges g + shiftPlaneAsCharges f := by
  have h := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (Basis.mem_span basisAsBasis S)
  obtain ⟨f, hf⟩ := h
  simp only [succ_eq_add_one, basisAsBasis, coe_basisOfLinearIndependentOfCardEqFinrank,
    Fintype.sum_sum_type] at hf
  change symmPlane _ + shiftPlane _ = S at hf
  use f ∘ Sum.inl
  use f ∘ Sum.inr
  rw [← hf]
  simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val,
    symmPlane_val, shiftPlane_val]
  rfl

/-!

### 2.1. Relation under permutations

-/

lemma span_basis_swapShift {S : (PureU1 (2 * n.succ + 1)).LinSols} (j : Fin n.succ)
    (hS : ((FamilyPermutations (2 * n.succ + 1)).linSolRep
    (Equiv.swap (oddShiftFst j) (oddShiftSnd j))) S = S') (g f : Fin n.succ → ℚ)
    (hS1 : S.val = symmPlaneAsCharges g + shiftPlaneAsCharges f) : ∃ (g' f' : Fin n.succ → ℚ),
    S'.val = symmPlaneAsCharges g' + shiftPlaneAsCharges f' ∧ shiftPlaneAsCharges f' = shiftPlaneAsCharges f +
    (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • shiftBasisAsCharges j ∧ g' = g := by
  let X := shiftPlaneAsCharges f +
    (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • shiftBasisAsCharges j
  have hf : shiftPlaneAsCharges f ∈ Submodule.span ℚ (Set.range shiftBasisAsCharges) := by
    rw [(Submodule.mem_span_range_iff_exists_fun ℚ)]
    use f
    rfl
  have hP : (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • shiftBasisAsCharges j ∈
      Submodule.span ℚ (Set.range shiftBasisAsCharges) := by
    apply Submodule.smul_mem
    apply SetLike.mem_of_subset
    apply Submodule.subset_span
    simp_all only [Set.mem_range, exists_apply_eq_apply]
  have hX : X ∈ Submodule.span ℚ (Set.range (shiftBasisAsCharges)) := by
    apply Submodule.add_mem
    exact hf
    exact hP
  have hXsum := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hX
  obtain ⟨f', hf'⟩ := hXsum
  use g
  use f'
  change shiftPlaneAsCharges f' = _ at hf'
  erw [hf']
  simp only [and_self, and_true, X]
  rw [← add_assoc, ← hS1]
  apply linSolRep_swap_oddShift_eq_add at hS
  exact hS

end VectorLikeOddPlane

end PureU1
