/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.BasisLinear
public import Physlib.QFT.QED.AnomalyCancellation.VectorLike
/-!
# The symmetric plane for the odd case

This file defines the symmetric plane for `PureU1 (2 * n + 1)`.

The symmetric plane arises from the symmetric split `(n + 1) + n` of the `2 * n + 1` charges.
It is called "symmetric" because the positions (`oddFst`, `oddSnd`, `oddMid`) come from this
symmetric split, which divides the charges into two groups of size `n` and a middle element.

## Main definitions

- `symmPlaneAsCharges` : A point in the span of the symmetric basis as a charge assignment.
- `symmPlane` : A point in the span of the symmetric basis as a linear solution.
- `symmBasis` : The basis vectors of the symmetric plane as `LinSols`.
- `symmBasisAsCharges` : The basis vectors of the symmetric plane as charges.

## Key results

- `symmPlaneAsCharges_accCube` : Charges from the symmetric plane satisfy the cubic ACC.
- `symmBasis_linear_independent` : The symmetric basis vectors are linearly independent.

## Table of contents

- A.1. The symmetric split: Splitting the charges up via `(n + 1) + n`
- B. The first plane (symmetric plane)
  - B.1. The basis vectors of the first plane as charges
  - B.2. Components of the basis vectors as charges
  - B.3. The basis vectors satisfy the linear ACCs
  - B.4. The basis vectors as `LinSols`
  - B.5. The inclusion of the first plane into charges
  - B.6. Components of the first plane
  - B.7. Points on the first plane satisfies the ACCs
  - B.8. Kernel of the inclusion into charges
  - B.9. The inclusion of the first plane into `LinSols`
  - B.10. The basis vectors are linearly independent

-/

@[expose] public section

open Module Nat Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeOddPlane

/-!

## A.1. The symmetric split: Splitting the charges up via `(n + 1) + n`

We split `2 * n + 1` charges using the symmetric split `(n + 1) + n`.

-/

section theDeltas

lemma odd_shift_eq (n : ℕ) : (1 + n) + n = 2 * n +1 := by
  omega

/-- The inclusion of `Fin n` into `Fin ((n + 1) + n)` via the first `n`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddFst (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.castAdd n (Fin.castAdd 1 j))

/-- The inclusion of `Fin n` into `Fin ((n + 1) + n)` via the second `n`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddSnd (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.natAdd (n+1) j)

/-- The element representing `1` in `Fin ((n + 1) + n)`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddMid : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.castAdd n (Fin.natAdd n 1))

lemma sum_odd (S : Fin (2 * n + 1) → ℚ) :
    ∑ i, S i = S oddMid + ∑ i : Fin n, ((S ∘ oddFst) i + (S ∘ oddSnd) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin (n + 1 + n), S (Fin.cast (split_odd n) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (split_odd n)).symm.toEquiv]
    · intro i
      simp only [mem_univ, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv]
    · exact fun _ _ => rfl
  rw [h1]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton, Function.comp_apply]
  nth_rewrite 2 [add_comm]
  rw [add_assoc]
  rw [Finset.sum_add_distrib]
  rfl

end theDeltas

/-!

## B. The first plane (symmetric plane)

The symmetric plane is constructed from the symmetric split `(n + 1) + n`.

-/

/-!

### B.1. The basis vectors of the first plane as charges

-/

/-- The first part of the basis as charge assignments. -/
def symmBasisAsCharges (j : Fin n) : (PureU1 (2 * n + 1)).Charges :=
  fun i =>
  if i = oddFst j then
    1
  else
    if i = oddSnd j then
      - 1
    else
      0

/-!

### B.2. Components of the basis vectors as charges

-/

lemma symmBasisAsCharges_on_oddFst_self (j : Fin n) : symmBasisAsCharges j (oddFst j) = 1 := by
  simp [symmBasisAsCharges]

lemma symmBasisAsCharges_on_oddFst_other {k j : Fin n} (h : k ≠ j) :
    symmBasisAsCharges k (oddFst j) = 0 := by
  simp only [symmBasisAsCharges, PureU1_numberCharges]
  simp only [oddFst, oddSnd]
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
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
      omega
    · rfl

lemma symmBasisAsCharges_on_other {k : Fin n} {j : Fin (2 * n + 1)} (h1 : j ≠ oddFst k)
    (h2 : j ≠ oddSnd k) :
    symmBasisAsCharges k j = 0 := by
  simp only [symmBasisAsCharges, PureU1_numberCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma symmBasisAsCharges_oddSnd_eq_minus_oddFst (j i : Fin n) :
    symmBasisAsCharges j (oddSnd i) = - symmBasisAsCharges j (oddFst i) := by
  simp only [symmBasisAsCharges, PureU1_numberCharges, oddSnd, oddFst]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals
    rename_i h1 h2
    rw [Fin.ext_iff] at h1 h2
    simp_all only [Fin.cast_inj, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, neg_neg,
      add_eq_right, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
  all_goals
    rename_i h3
    rw [Fin.ext_iff] at h3
    simp_all only [Fin.val_natAdd, Fin.val_castAdd, add_eq_right,
      AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
  all_goals
    omega

lemma symmBasisAsCharges_on_oddSnd_self (j : Fin n) :
    symmBasisAsCharges j (oddSnd j) = - 1 := by
  rw [symmBasisAsCharges_oddSnd_eq_minus_oddFst, symmBasisAsCharges_on_oddFst_self]

lemma symmBasisAsCharges_on_oddSnd_other {k j : Fin n} (h : k ≠ j) :
    symmBasisAsCharges k (oddSnd j) = 0 := by
  rw [symmBasisAsCharges_oddSnd_eq_minus_oddFst, symmBasisAsCharges_on_oddFst_other h]
  rfl

lemma symmBasisAsCharges_on_oddMid (j : Fin n) : symmBasisAsCharges j oddMid = 0 := by
  simp only [symmBasisAsCharges, PureU1_numberCharges]
  split <;> rename_i h
  · rw [Fin.ext_iff] at h
    simp only [oddMid, Fin.isValue, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_eq_zero,
      add_zero, oddFst] at h
    omega
  · split <;> rename_i h2
    · rw [Fin.ext_iff] at h2
      simp only [oddMid, Fin.isValue, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
        Fin.val_eq_zero, add_zero, oddSnd] at h2
      omega
    · rfl

/-!

### B.3. The basis vectors satisfy the linear ACCs

-/

lemma symmBasisAsCharges_linearACC (j : Fin n) :
    (accGrav (2 * n + 1)) (symmBasisAsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  erw [sum_odd]
  simp [symmBasisAsCharges_oddSnd_eq_minus_oddFst, symmBasisAsCharges_on_oddMid]

/-!

### B.4. The basis vectors as `LinSols`

-/

/-- The first part of the basis as `LinSols`. -/
@[simps!]
def symmBasis (j : Fin n) : (PureU1 (2 * n + 1)).LinSols :=
  ⟨symmBasisAsCharges j, by
    intro i
    simp only [PureU1_numberLinear] at i
    match i with
    | 0 =>
    exact symmBasisAsCharges_linearACC j⟩

/-!

### B.5. The inclusion of the first plane into charges

-/

/-- A point in the span of the first part of the basis as a charge. -/
def symmPlaneAsCharges (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges :=
  ∑ i, f i • symmBasisAsCharges i

/-!

### B.6. Components of the first plane

-/

lemma symmPlaneAsCharges_oddFst (f : Fin n → ℚ) (j : Fin n) : symmPlaneAsCharges f (oddFst j) = f j := by
  rw [symmPlaneAsCharges, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [symmBasisAsCharges_on_oddFst_self]
    exact Rat.mul_one (f j)
  · intro k _ hkj
    rw [symmBasisAsCharges_on_oddFst_other hkj]
    exact Rat.mul_zero (f k)
  · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma symmPlaneAsCharges_oddSnd (f : Fin n → ℚ) (j : Fin n) : symmPlaneAsCharges f (oddSnd j) = - f j := by
  rw [symmPlaneAsCharges, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [symmBasisAsCharges_on_oddSnd_self]
    exact mul_neg_one (f j)
  · intro k _ hkj
    rw [symmBasisAsCharges_on_oddSnd_other hkj]
    exact Rat.mul_zero (f k)
  · simp

lemma symmPlaneAsCharges_oddMid (f : Fin n → ℚ) : symmPlaneAsCharges f oddMid = 0 := by
  rw [symmPlaneAsCharges, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, symmBasisAsCharges_on_oddMid]

/-!

### B.7. Points on the first plane satisfies the ACCs

-/

lemma symmPlaneAsCharges_linearACC (f : Fin n → ℚ) : (accGrav (2 * n + 1)) (symmPlaneAsCharges f) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_odd]
  simp [symmPlaneAsCharges_oddSnd, symmPlaneAsCharges_oddFst, symmPlaneAsCharges_oddMid]

set_option backward.isDefEq.respectTransparency false in
lemma symmPlaneAsCharges_accCube (f : Fin n → ℚ) : accCube (2 * n +1) (symmPlaneAsCharges f) = 0 := by
  rw [accCube_explicit, sum_odd, symmPlaneAsCharges_oddMid]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Function.comp_apply,
    zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp only [symmPlaneAsCharges_oddFst, symmPlaneAsCharges_oddSnd]
  ring

/-!

### B.8. Kernel of the inclusion into charges

-/

lemma symmPlaneAsCharges_zero (f : Fin n → ℚ) (h : symmPlaneAsCharges f = 0) : ∀ i, f i = 0 := by
  intro i
  erw [← symmPlaneAsCharges_oddFst f]
  rw [h]
  rfl

/-!

### B.9. The inclusion of the first plane into `LinSols`

-/

/-- A point in the span of the first part of the basis. -/
def symmPlane (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).LinSols :=
  ∑ i, f i • symmBasis i

lemma symmPlane_val (f : Fin n → ℚ) : (symmPlane f).val = symmPlaneAsCharges f := by
  simp only [symmPlane, symmPlaneAsCharges]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

/-!

### B.10. The basis vectors are linearly independent

-/

theorem symmBasis_linear_independent : LinearIndependent ℚ (@symmBasis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change symmPlane f = 0 at h
  have h1 : (symmPlane f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [symmPlane_val] at h1
  exact symmPlaneAsCharges_zero f h1

end VectorLikeOddPlane

end PureU1
