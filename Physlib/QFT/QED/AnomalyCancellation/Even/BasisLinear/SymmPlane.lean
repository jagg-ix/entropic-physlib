/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.BasisLinear
public import Physlib.QFT.QED.AnomalyCancellation.VectorLike
/-!

# The symmetric plane for the even case

## i. Overview

This module defines the *symmetric plane* for the even case of anomaly cancellation
in `PureU1 (2 * n.succ)`. It is called "symmetric" because these positions come from
the symmetric (even) split `n.succ + n.succ`, where the first and second halves are
paired symmetrically.

## ii. Key definitions and results

- `symmBasisAsCharges` : The basis vectors of the symmetric plane as charges.
- `symmBasis` : The basis vectors as `LinSols`.
- `symmPlane` : A point in the span of the symmetric basis as a charge,
    i.e., the inclusion of the symmetric plane into charges.
- `symmPlaneLinSols` : The inclusion of the symmetric plane into linear solutions.
- `symmPlane_accCube` : Charges from the symmetric plane satisfy the cubic ACC.
- `symmBasis_linear_independent` : The symmetric basis vectors are linearly independent.
- `vectorLikeEven_in_span` : Every vector-like even solution is in the span of the symmetric basis.

## iii. Table of contents

- A.1. The even split: Splitting the charges up via `n.succ + n.succ`
- B. The first plane (symmetric plane)
  - B.1. The basis vectors of the symmetric plane as charges
  - B.2. Components of the basis vectors
  - B.3. The basis vectors satisfy the linear ACCs
  - B.4. The basis vectors satisfy the cubic ACC
  - B.5. The basis vectors as linear solutions
  - B.6. The inclusion of the symmetric plane into charges
  - B.7. Components of the inclusion into charges
  - B.8. The inclusion into charges satisfies the linear and cubic ACCs
  - B.9. Kernel of the inclusion into charges
  - B.10. The inclusion of the plane into linear solutions
  - B.11. The basis vectors are linearly independent
  - B.12. Every vector-like even solution is in the span of the basis of the symmetric plane

## iv. References

- https://arxiv.org/pdf/1912.04804.pdf

-/

@[expose] public section

open Nat Module Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeEvenPlane

/-!

### A.1. The even split: Spltting the charges up via `n.succ + n.succ`

-/

/-- The inclusion of `Fin n.succ` into `Fin (n.succ + n.succ)` via the first `n.succ`,
  casted into `Fin (2 * n.succ)`. -/
def evenFst (j : Fin n.succ) : Fin (2 * n.succ) :=
  Fin.cast (split_equal n.succ) (Fin.castAdd n.succ j)

/-- The inclusion of `Fin n.succ` into `Fin (n.succ + n.succ)` via the second `n.succ`,
  casted into `Fin (2 * n.succ)`. -/
def evenSnd (j : Fin n.succ) : Fin (2 * n.succ) :=
  Fin.cast (split_equal n.succ) (Fin.natAdd n.succ j)

lemma ext_even (S T : Fin (2 * n.succ) → ℚ) (h1 : ∀ i, S (evenFst i) = T (evenFst i))
    (h2 : ∀ i, S (evenSnd i) = T (evenSnd i)) : S = T := by
  funext i
  by_cases hi : i.val < n.succ
  · let j : Fin n.succ := ⟨i, hi⟩
    have h2 := h1 j
    have h3 : evenFst j = i := rfl
    rw [h3] at h2
    exact h2
  · let j : Fin n.succ := ⟨i - n.succ, by omega⟩
    have h2 := h2 j
    have h3 : evenSnd j = i := by
      simp only [succ_eq_add_one, evenSnd, Fin.ext_iff, Fin.val_cast, Fin.val_natAdd, j]
      omega
    rw [h3] at h2
    exact h2

lemma sum_even (S : Fin (2 * n.succ) → ℚ) :
    ∑ i, S i = ∑ i : Fin n.succ, ((S ∘ evenFst) i + (S ∘ evenSnd) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin (n.succ + n.succ), S (Fin.cast (split_equal n.succ) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (split_equal n.succ)).symm.toEquiv]
    · intro i
      simp only [mem_univ, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv]
    · exact fun _ _=> rfl
  rw [h1, Fin.sum_univ_add, Finset.sum_add_distrib]
  rfl

/-!

## B. The first plane (symmetric plane)

-/

/-!

### B.1. The basis vectors of the symmetric plane as charges

-/

/-- The basis vectors of the symmetric plane as charges. -/
def symmBasisAsCharges (j : Fin n.succ) : (PureU1 (2 * n.succ)).Charges :=
  fun i =>
  if i = evenFst j then
    1
  else
    if i = evenSnd j then
      - 1
    else
      0

/-!

### B.2. Components of the basis vectors

-/

lemma symmBasisAsCharges_on_evenFst_self (j : Fin n.succ) :
    symmBasisAsCharges j (evenFst j) = 1 := by
  simp [symmBasisAsCharges]

lemma symmBasisAsCharges_on_evenFst_other {k j : Fin n.succ} (h : k ≠ j) :
    symmBasisAsCharges k (evenFst j) = 0 := by
  simp only [symmBasisAsCharges, succ_eq_add_one, PureU1_numberCharges, evenFst, evenSnd]
  split
  · rename_i h1
    rw [Fin.ext_iff] at h1
    simp_all
    rw [Fin.ext_iff] at h
    simp_all
  · split
    · rename_i h1 h2
      simp_all only [succ_eq_add_one, ne_eq, Fin.natAdd_eq_addNat, Fin.cast_inj, neg_eq_zero,
        one_ne_zero]
      rw [Fin.ext_iff] at h2
      simp only [Fin.val_castAdd, Fin.val_addNat] at h2
      omega
    · rfl

lemma symmBasisAsCharges_on_other {k : Fin n.succ} {j : Fin (2 * n.succ)} (h1 : j ≠ evenFst k)
    (h2 : j ≠ evenSnd k) : symmBasisAsCharges k j = 0 := by
  simp only [symmBasisAsCharges, succ_eq_add_one, PureU1_numberCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma symmBasisAsCharges_evenSnd_eq_neg_evenFst (j i : Fin n.succ) :
    symmBasisAsCharges j (evenSnd i) = - symmBasisAsCharges j (evenFst i) := by
  simp only [symmBasisAsCharges, succ_eq_add_one, PureU1_numberCharges, evenSnd, evenFst]
  split <;> split
  any_goals split
  any_goals rfl
  any_goals split
  any_goals rfl
  all_goals
    rename_i h1 h2
    rw [Fin.ext_iff] at h1 h2
    simp_all
  all_goals
    rename_i h3
    rw [Fin.ext_iff] at h3
    simp_all
  all_goals omega

lemma symmBasisAsCharges_on_evenSnd_self (j : Fin n.succ) :
    symmBasisAsCharges j (evenSnd j) = - 1 := by
  rw [symmBasisAsCharges_evenSnd_eq_neg_evenFst, symmBasisAsCharges_on_evenFst_self]

lemma symmBasisAsCharges_on_evenSnd_other {k j : Fin n.succ} (h : k ≠ j) :
    symmBasisAsCharges k (evenSnd j) = 0 := by
  rw [symmBasisAsCharges_evenSnd_eq_neg_evenFst, symmBasisAsCharges_on_evenFst_other h]
  rfl

/-!

### B.3. The basis vectors satisfy the linear ACCs

-/

lemma symmBasisAsCharges_linearACC (j : Fin n.succ) :
    (accGrav (2 * n.succ)) (symmBasisAsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_even]
  simp [symmBasisAsCharges_evenSnd_eq_neg_evenFst]
/-!

### B.4. The basis vectors satisfy the cubic ACC

-/
lemma symmBasisAsCharges_accCube (j : Fin n.succ) :
    accCube (2 * n.succ) (symmBasisAsCharges j) = 0 := by
  rw [accCube_explicit, sum_even]
  apply Finset.sum_eq_zero
  intro i _
  simp only [succ_eq_add_one, Function.comp_apply, symmBasisAsCharges_evenSnd_eq_neg_evenFst]
  ring

/-!

### B.5. The basis vectors as linear solutions

-/

/-- The basis vectors of the symmetric plane as `LinSols`. -/
@[simps!]
def symmBasis (j : Fin n.succ) : (PureU1 (2 * n.succ)).LinSols :=
  ⟨symmBasisAsCharges j, by
    intro i
    simp only [succ_eq_add_one, PureU1_numberLinear] at i
    match i with
    | 0 =>
    exact symmBasisAsCharges_linearACC j⟩

/-!

### B.6. The inclusion of the symmetric plane into charges

-/

/-- A point in the span of the symmetric basis as a charge. -/
def symmPlane (f : Fin n.succ → ℚ) : (PureU1 (2 * n.succ)).Charges :=
  ∑ i, f i • symmBasisAsCharges i

/-!

### B.7. Components of the inclusion into charges

-/

lemma symmPlane_evenFst (f : Fin n.succ → ℚ) (j : Fin n.succ) :
    symmPlane f (evenFst j) = f j := by
  rw [symmPlane, sum_of_charges]
  simp only [succ_eq_add_one, HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [symmBasisAsCharges_on_evenFst_self]
    exact Rat.mul_one (f j)
  · intro k _ hkj
    rw [symmBasisAsCharges_on_evenFst_other hkj]
    exact Rat.mul_zero (f k)
  · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma symmPlane_evenSnd (f : Fin n.succ → ℚ) (j : Fin n.succ) :
    symmPlane f (evenSnd j) = - f j := by
  rw [symmPlane, sum_of_charges]
  simp only [succ_eq_add_one, HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · simp only [symmBasisAsCharges_on_evenSnd_self, mul_neg, mul_one]
  · intro k _ hkj
    simp only [symmBasisAsCharges_on_evenSnd_other hkj, mul_zero]
  · simp

lemma symmPlane_evenSnd_evenFst (f : Fin n.succ → ℚ) :
    symmPlane f ∘ evenSnd = - symmPlane f ∘ evenFst := by
  funext j
  simp only [PureU1_numberCharges, Function.comp_apply, Pi.neg_apply]
  rw [symmPlane_evenFst, symmPlane_evenSnd]

/-!

### B.8. The inclusion into charges satisfies the linear and cubic ACCs

-/

lemma symmPlane_linearACC (f : Fin n.succ → ℚ) :
    (accGrav (2 * n.succ)) (symmPlane f) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_even]
  simp [symmPlane_evenSnd, symmPlane_evenFst]

lemma symmPlane_accCube (f : Fin n.succ → ℚ) :
    accCube (2 * n.succ) (symmPlane f) = 0 := by
  rw [accCube_explicit, sum_even]
  apply Finset.sum_eq_zero
  intro i _
  simp only [succ_eq_add_one, Function.comp_apply, symmPlane_evenFst, symmPlane_evenSnd]
  ring

/-!

### B.9. Kernel of the inclusion into charges

-/

lemma symmPlane_zero (f : Fin n.succ → ℚ) (h : symmPlane f = 0) : ∀ i, f i = 0 := by
  intro i
  erw [← symmPlane_evenFst f]
  rw [h]
  rfl

/-!

### B.10. The inclusion of the plane into linear solutions

-/

/-- A point in the span of the symmetric basis as a linear solution. -/
def symmPlaneLinSols (f : Fin n.succ → ℚ) : (PureU1 (2 * n.succ)).LinSols :=
  ∑ i, f i • symmBasis i

lemma symmPlaneLinSols_val (f : Fin n.succ → ℚ) :
    (symmPlaneLinSols f).val = symmPlane f := by
  simp only [succ_eq_add_one, symmPlaneLinSols, symmPlane]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

/-!

### B.11. The basis vectors are linearly independent

-/

theorem symmBasis_linear_independent : LinearIndependent ℚ (@symmBasis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change symmPlaneLinSols f = 0 at h
  have h1 : (symmPlaneLinSols f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [symmPlaneLinSols_val] at h1
  exact symmPlane_zero f h1

/-!

### B.12. Every vector-like even solution is in the span of the basis of the symmetric plane

-/

lemma vectorLikeEven_in_span (S : (PureU1 (2 * n.succ)).LinSols)
    (hS : VectorLikeEven S.val) : ∃ (M : (FamilyPermutations (2 * n.succ)).group),
      (FamilyPermutations (2 * n.succ)).linSolRep M S ∈
        Submodule.span ℚ (Set.range symmBasis) := by
  use (Tuple.sort S.val).symm
  change sortAFL S ∈ Submodule.span ℚ (Set.range symmBasis)
  rw [Submodule.mem_span_range_iff_exists_fun ℚ]
  let f : Fin n.succ → ℚ := fun i => (sortAFL S).val (evenFst i)
  use f
  apply ACCSystemLinear.LinSols.ext
  rw [sortAFL_val]
  erw [symmPlaneLinSols_val]
  apply ext_even
  · intro i
    rw [symmPlane_evenFst]
    rfl
  · intro i
    rw [symmPlane_evenSnd]
    have ht := hS i
    change sort S.val (evenFst i) = - sort S.val (evenSnd i) at ht
    have h : sort S.val (evenSnd i) = - sort S.val (evenFst i) := by
      rw [ht]
      ring
    rw [h]
    rfl

end VectorLikeEvenPlane

end PureU1
