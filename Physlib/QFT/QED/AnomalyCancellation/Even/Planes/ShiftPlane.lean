/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Even.Planes.SymmPlane
/-!

# The shifted plane for the even case

## i. Overview

This module defines the *shifted plane* for the even case of anomaly cancellation
in `PureU1 (2 * n.succ)`. It is called "shifted" because these positions come from
the shifted even split `1 + (n + n + 1)`, where the charges are grouped around the
boundary rather than symmetrically.

## ii. Key definitions and results

- `shiftBasisAsCharges` : The basis vectors of the shifted plane as charges.
- `shiftBasis` : The basis vectors as `LinSols`.
- `shiftPlaneAsCharges` : A point in the span of the shifted basis as a charge,
    i.e., the inclusion of the shifted plane into charges.
- `shiftPlane` : The inclusion of the shifted plane into linear solutions.
- `shiftPlaneAsCharges_accCube` : Charges from the shifted plane satisfy the cubic ACC.
- `shiftBasis_linear_independent` : The shifted basis vectors are linearly independent.

## iii. Table of contents

- A.1. The shifted even split: Splitting the charges up via `1 + (n + n + 1)`
- A.2. Lemmas relating the two splittings
- B. The shifted plane
  - B.1. The basis vectors of the shifted plane as charges
  - B.2. Components of the basis vectors
  - B.3. The basis vectors satisfy the linear ACCs
  - B.4. The basis vectors satisfy the cubic ACC
  - B.5. The basis vectors as `LinSols`
  - B.6. The basis vectors are linearly independent
  - B.7. Permutations as additions of basis vectors
  - B.8. The inclusion of the shifted plane into charges
  - B.9. Components of the shifted plane
  - B.10. Points satisfy the cubic ACC
  - B.11. Kernel of the inclusion
  - B.12. The inclusion of the plane into `LinSols`

## iv. References

- https://arxiv.org/pdf/1912.04804.pdf

-/

@[expose] public section

open Nat Module Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeEvenPlane

/-!

### A.1. The shifted even split: Splitting the charges up via `1 + (n + n + 1)`

-/

lemma n_cond₂ (n : ℕ) : 1 + ((n + n) + 1) = 2 * n.succ := by
  linarith

/-- The inclusion of `Fin n` into `Fin (1 + (n + n + 1))` via the first `n`,
  casted into `Fin (2 * n.succ)`. -/
def evenShiftFst (j : Fin n) : Fin (2 * n.succ) := Fin.cast (n_cond₂ n)
  (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n j)))

/-- The inclusion of `Fin n` into `Fin (1 + (n + n + 1))` via the second `n`,
  casted into `Fin (2 * n.succ)`. -/
def evenShiftSnd (j : Fin n) : Fin (2 * n.succ) := Fin.cast (n_cond₂ n)
  (Fin.natAdd 1 (Fin.castAdd 1 (Fin.natAdd n j)))

/-- The element of `Fin (1 + (n + n + 1))` corresponding to the first `1`,
  casted into `Fin (2 * n.succ)`. -/
def evenShiftZero : Fin (2 * n.succ) := (Fin.cast (n_cond₂ n) (Fin.castAdd ((n + n) + 1) 0))

/-- The element of `Fin (1 + (n + n + 1))` corresponding to the second `1`,
  casted into `Fin (2 * n.succ)`. -/
def evenShiftLast : Fin (2 * n.succ) := (Fin.cast (n_cond₂ n) (Fin.natAdd 1 (Fin.natAdd (n + n) 0)))

lemma sum_evenShift (S : Fin (2 * n.succ) → ℚ) :
    ∑ i, S i = S evenShiftZero + S evenShiftLast +
    ∑ i : Fin n, ((S ∘ evenShiftFst) i + (S ∘ evenShiftSnd) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin (1 + ((n + n) + 1)), S (Fin.cast (n_cond₂ n) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (n_cond₂ n)).symm.toEquiv]
    · intro i
      simp only [mem_univ, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv]
    · exact fun _ _ => rfl
  rw [h1]
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add, Finset.sum_add_distrib]
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton, Function.comp_apply]
  repeat rw [Rat.add_assoc]
  apply congrArg
  rw [Rat.add_comm]
  rw [← Rat.add_assoc]
  nth_rewrite 2 [Rat.add_comm]
  repeat rw [Rat.add_assoc]
  nth_rewrite 2 [Rat.add_comm]
  rfl

/-!

### A.2. Lemmas relating the two splittings

-/
lemma evenShiftZero_eq_evenFst_zero : @evenShiftZero n = evenFst 0 := rfl

lemma evenShiftLast_eq_evenSnd_last: @evenShiftLast n = evenSnd (Fin.last n) := by
  rw [Fin.ext_iff]
  simp only [succ_eq_add_one, evenShiftLast, Fin.isValue, Fin.val_cast, Fin.val_natAdd,
    Fin.val_eq_zero, add_zero, evenSnd, Fin.natAdd_last, Fin.val_last]
  omega

lemma evenShiftFst_eq_evenFst_succ (j : Fin n) : evenShiftFst j = evenFst j.succ := by
  rw [Fin.ext_iff, evenFst, evenShiftFst]
  simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd, Fin.val_succ]
  ring

lemma evenShiftSnd_eq_evenSnd_castSucc (j : Fin n) : evenShiftSnd j = evenSnd j.castSucc := by
  rw [Fin.ext_iff, evenSnd, evenShiftSnd]
  simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd, Fin.val_castSucc]
  ring_nf
  rw [Nat.succ_eq_add_one]
  ring

/-!

## B. The shifted plane

-/

/-!

### B.1. The basis vectors of the shifted plane as charges

-/

/-- The basis vectors of the shifted plane as charges. -/
def shiftBasisAsCharges (j : Fin n) : (PureU1 (2 * n.succ)).Charges :=
  fun i =>
  if i = evenShiftFst j then
    1
  else
    if i = evenShiftSnd j then
      - 1
    else
      0
/-!

### B.2. Components of the basis vectors

-/

lemma shiftBasisAsCharges_on_evenShiftFst_self (j : Fin n) :
    shiftBasisAsCharges j (evenShiftFst j) = 1 := by
  simp [shiftBasisAsCharges]

lemma shiftBasisAsCharges_on_other {k : Fin n} {j : Fin (2 * n.succ)} (h1 : j ≠ evenShiftFst k)
    (h2 : j ≠ evenShiftSnd k) : shiftBasisAsCharges k j = 0 := by
  simp only [shiftBasisAsCharges, succ_eq_add_one, PureU1_numberCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma shiftBasisAsCharges_on_evenShiftFst_other {k j : Fin n} (h : k ≠ j) :
    shiftBasisAsCharges k (evenShiftFst j) = 0 := by
  simp only [shiftBasisAsCharges, succ_eq_add_one, PureU1_numberCharges]
  simp only [evenShiftFst, succ_eq_add_one, evenShiftSnd]
  split
  · rename_i h1
    rw [Fin.ext_iff] at h1
    simp_all
    rw [Fin.ext_iff] at h
    simp_all
  · split
    · rename_i h1 h2
      simp_all
      rw [Fin.ext_iff] at h2
      simp only [Fin.val_castAdd, Fin.val_addNat] at h2
      omega
    · rfl

lemma shiftBasisAsCharges_evenShiftSnd_eq_neg_evenShiftFst (j i : Fin n) :
    shiftBasisAsCharges j (evenShiftSnd i) = - shiftBasisAsCharges j (evenShiftFst i) := by
  simp only [shiftBasisAsCharges, succ_eq_add_one, PureU1_numberCharges, evenShiftSnd, evenShiftFst]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals
    rename_i h1 h2
    rw [Fin.ext_iff] at h1 h2
    simp_all only [Fin.natAdd_eq_addNat, Fin.cast_inj, Fin.val_cast, Fin.val_natAdd,
      Fin.val_castAdd, add_right_inj, Fin.val_addNat, add_eq_left]
  · subst h1
    exact Fin.elim0 i
  all_goals
    rename_i h3
    rw [Fin.ext_iff] at h3
    simp_all only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_addNat, not_true_eq_false]
  all_goals
    omega

lemma shiftBasisAsCharges_on_evenShiftSnd_self (j : Fin n) :
    shiftBasisAsCharges j (evenShiftSnd j) = - 1 := by
  rw [shiftBasisAsCharges_evenShiftSnd_eq_neg_evenShiftFst,
    shiftBasisAsCharges_on_evenShiftFst_self]

lemma shiftBasisAsCharges_on_evenShiftSnd_other {k j : Fin n} (h : k ≠ j) :
    shiftBasisAsCharges k (evenShiftSnd j) = 0 := by
  rw [shiftBasisAsCharges_evenShiftSnd_eq_neg_evenShiftFst,
    shiftBasisAsCharges_on_evenShiftFst_other h]
  rfl

lemma shiftBasisAsCharges_on_evenShiftZero (j : Fin n) :
    shiftBasisAsCharges j evenShiftZero = 0 := by
  simp only [shiftBasisAsCharges, succ_eq_add_one, PureU1_numberCharges]
  split<;> rename_i h
  · simp only [evenShiftZero, succ_eq_add_one, Fin.isValue, evenShiftFst, Fin.ext_iff,
    Fin.val_cast, Fin.val_castAdd, Fin.val_eq_zero, Fin.val_natAdd] at h
    omega
  · split <;> rename_i h2
    · simp only [evenShiftZero, succ_eq_add_one, Fin.isValue, evenShiftSnd, Fin.ext_iff,
      Fin.val_cast, Fin.val_castAdd, Fin.val_eq_zero, Fin.val_natAdd] at h2
      omega
    · rfl

lemma shiftBasisAsCharges_on_evenShiftLast (j : Fin n) :
    shiftBasisAsCharges j evenShiftLast = 0 := by
  simp only [shiftBasisAsCharges, succ_eq_add_one, PureU1_numberCharges]
  split <;> rename_i h
  · rw [Fin.ext_iff] at h
    simp only [succ_eq_add_one, evenShiftLast, Fin.isValue, Fin.val_cast, Fin.val_natAdd,
      Fin.val_eq_zero, add_zero, evenShiftFst, Fin.val_castAdd, add_right_inj] at h
    omega
  · split <;> rename_i h2
    · rw [Fin.ext_iff] at h2
      simp only [succ_eq_add_one, evenShiftLast, Fin.isValue, Fin.val_cast, Fin.val_natAdd,
        Fin.val_eq_zero, add_zero, evenShiftSnd, Fin.val_castAdd, add_right_inj] at h2
      omega
    · rfl

/-!

### B.3. The basis vectors satisfy the linear ACCs

-/

lemma shiftBasisAsCharges_linearACC (j : Fin n) :
    (accGrav (2 * n.succ)) (shiftBasisAsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_evenShift, shiftBasisAsCharges_on_evenShiftZero, shiftBasisAsCharges_on_evenShiftLast]
  simp [shiftBasisAsCharges_evenShiftSnd_eq_neg_evenShiftFst]

/-!

### B.4. The basis vectors satisfy the cubic ACC

-/

set_option backward.isDefEq.respectTransparency false in
lemma shiftBasisAsCharges_accCube (j : Fin n) :
    accCube (2 * n.succ) (shiftBasisAsCharges j) = 0 := by
  rw [accCube_explicit, sum_evenShift]
  rw [shiftBasisAsCharges_on_evenShiftLast, shiftBasisAsCharges_on_evenShiftZero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    Function.comp_apply, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp only [shiftBasisAsCharges_evenShiftSnd_eq_neg_evenShiftFst]
  ring

/-!

### B.5. The basis vectors as `LinSols`

-/
/-- The basis vectors of the shifted plane as `LinSols`. -/
@[simps!]
def shiftBasis (j : Fin n) : (PureU1 (2 * n.succ)).LinSols :=
  ⟨shiftBasisAsCharges j, by
    intro i
    simp only [succ_eq_add_one, PureU1_numberLinear] at i
    match i with
    | 0 =>
    exact shiftBasisAsCharges_linearACC j⟩

/-!

### B.6. The basis vectors are linearly independent

-/

theorem shiftBasis_linear_independent : LinearIndependent ℚ (@shiftBasis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  have h1 : (∑ i, f i • shiftBasis i).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  have h2 : shiftPlaneAsCharges f = 0 := by
    have : (∑ i, f i • shiftBasis i).val = shiftPlaneAsCharges f := by
      simp only [succ_eq_add_one, shiftPlaneAsCharges]
      funext i
      rw [sum_of_anomaly_free_linear, sum_of_charges]
      simp [shiftBasis_val]
    rw [← this, h1]
  exact shiftPlaneAsCharges_zero f h2

/-!

### B.7. Permutations as additions of basis vectors

-/

/-- Swapping the elements evenShiftFst j and evenShiftSnd j is equivalent to
  adding a vector shiftBasisAsCharges j. -/
lemma linSolRep_swap_evenShift_eq_add {S S' : (PureU1 (2 * n.succ)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n.succ)).linSolRep
    (Equiv.swap (evenShiftFst j) (evenShiftSnd j))) S = S') :
    S'.val = S.val + (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) •
      shiftBasisAsCharges j := by
  funext i
  rw [← hS, FamilyPermutations_anomalyFreeLinear_apply]
  by_cases hi : i = evenShiftFst j
  · subst hi
    simp [HSMul.hSMul, shiftBasisAsCharges_on_evenShiftFst_self, Equiv.swap_apply_left]
  · by_cases hi2 : i = evenShiftSnd j
    · simp [HSMul.hSMul, hi2, shiftBasisAsCharges_on_evenShiftSnd_self, Equiv.swap_apply_right]
    · simp only [succ_eq_add_one, Equiv.invFun_as_coe, HSMul.hSMul,
      ACCSystemCharges.chargesAddCommMonoid_add, ACCSystemCharges.chargesModule_smul]
      rw [shiftBasisAsCharges_on_other hi hi2]
      aesop

/-!

### B.8. The inclusion of the shifted plane into charges

-/

/-- A point in the span of the shifted basis as a charge. -/
def shiftPlaneAsCharges (f : Fin n → ℚ) : (PureU1 (2 * n.succ)).Charges :=
  ∑ i, f i • shiftBasisAsCharges i

/-!

### B.9. Components of the shifted plane

-/

lemma shiftPlaneAsCharges_evenShiftFst (f : Fin n → ℚ) (j : Fin n) :
    shiftPlaneAsCharges f (evenShiftFst j) = f j := by
  rw [shiftPlaneAsCharges, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [shiftBasisAsCharges_on_evenShiftFst_self]
    exact Rat.mul_one (f j)
  · intro k _ hkj
    rw [shiftBasisAsCharges_on_evenShiftFst_other hkj]
    exact Rat.mul_zero (f k)
  · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma shiftPlaneAsCharges_evenShiftSnd (f : Fin n → ℚ) (j : Fin n) :
    shiftPlaneAsCharges f (evenShiftSnd j) = - f j := by
  rw [shiftPlaneAsCharges, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [shiftBasisAsCharges_on_evenShiftSnd_self]
    exact mul_neg_one (f j)
  · intro k _ hkj
    rw [shiftBasisAsCharges_on_evenShiftSnd_other hkj]
    exact Rat.mul_zero (f k)
  · simp

lemma shiftPlaneAsCharges_evenShiftZero (f : Fin n → ℚ) : shiftPlaneAsCharges f (evenShiftZero) = 0 := by
  rw [shiftPlaneAsCharges, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, shiftBasisAsCharges_on_evenShiftZero]

lemma shiftPlaneAsCharges_evenShiftLast (f : Fin n → ℚ) : shiftPlaneAsCharges f evenShiftLast = 0 := by
  rw [shiftPlaneAsCharges, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, shiftBasisAsCharges_on_evenShiftLast]

/-!

### B.10. Points satisfy the cubic ACC

-/

set_option backward.isDefEq.respectTransparency false in
lemma shiftPlaneAsCharges_accCube (f : Fin n → ℚ) : accCube (2 * n.succ) (shiftPlaneAsCharges f) = 0 := by
  rw [accCube_explicit, sum_evenShift, shiftPlaneAsCharges_evenShiftZero, shiftPlaneAsCharges_evenShiftLast]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    Function.comp_apply, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp only [shiftPlaneAsCharges_evenShiftFst, shiftPlaneAsCharges_evenShiftSnd]
  ring

/-!

### B.11. Kernel of the inclusion

-/

lemma shiftPlaneAsCharges_zero (f : Fin n → ℚ) (h : shiftPlaneAsCharges f = 0) : ∀ i, f i = 0 := by
  intro i
  rw [← shiftPlaneAsCharges_evenShiftFst f]
  rw [h]
  rfl

lemma shiftPlaneAsCharges_in_span (f : Fin n → ℚ) :
    shiftPlaneAsCharges f ∈ Submodule.span ℚ (Set.range shiftBasisAsCharges) := by
  rw [(Submodule.mem_span_range_iff_exists_fun ℚ)]
  use f
  rfl

lemma smul_shiftBasisAsCharges_in_span (S : (PureU1 (2 * n.succ)).LinSols) (j : Fin n) :
    (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • shiftBasisAsCharges j ∈
    Submodule.span ℚ (Set.range shiftBasisAsCharges) := by
  apply Submodule.smul_mem
  apply SetLike.mem_of_subset
  · exact Submodule.subset_span
  · simp_all only [Set.mem_range, exists_apply_eq_apply]

/-!

### B.12. The inclusion of the plane into `LinSols`

-/

/-- A point in the span of the shifted basis as a linear solution. -/
def shiftPlane (f : Fin n → ℚ) : (PureU1 (2 * n.succ)).LinSols :=
  ∑ i, f i • shiftBasis i

lemma shiftPlane_val (f : Fin n → ℚ) :
    (shiftPlane f).val = shiftPlaneAsCharges f := by
  simp only [succ_eq_add_one, shiftPlane, shiftPlaneAsCharges]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

end VectorLikeEvenPlane

end PureU1
