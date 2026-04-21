/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Odd.Planes.SymmPlane
/-!
# The shifted plane for the odd case

This file defines the shifted plane for `PureU1 (2 * n + 1)`.

The shifted plane arises from the shifted split `1 + n + n` of the `2 * n + 1` charges.
It is called "shifted" because the positions (`oddShiftFst`, `oddShiftSnd`, `oddShiftZero`)
come from this shifted split, which places the distinguished element at position `0` rather
than in the middle.

## Main definitions

- `shiftBasisAsCharges` : The basis vectors of the shifted plane as charges.
- `shiftBasis` : The basis vectors of the shifted plane as `LinSols`.
- `shiftPlaneAsCharges` : A point in the span of the shifted basis as a charge assignment.
- `shiftPlane` : A point in the span of the shifted basis as a linear solution.

## Key results

- `shiftPlaneAsCharges_accCube` : Charges from the shifted plane satisfy the cubic ACC.
- `shiftBasis_linear_independent` : The shifted basis vectors are linearly independent.
- `linSolRep_swap_oddShift_eq_add` : Swapping elements equals adding a basis vector.

## Table of contents

- A.1. The shifted split: Splitting the charges up via `1 + n + n`
- A.2. The shifted shifted split: Splitting the charges up via `((1+n)+1) + n.succ`
- A.3. Relating the splittings together
- B. The shifted plane
  - B.1. The basis vectors of the shifted plane as charges
  - B.2. Components of the basis vectors as charges
  - B.3. The basis vectors satisfy the linear ACCs
  - B.4. The basis vectors as `LinSols`
  - B.5. The basis vectors are linearly independent
  - B.6. Permutations equal adding basis vectors
  - B.7. The inclusion of the shifted plane into charges (`shiftPlaneAsCharges`)
  - B.8. Components of the shifted plane
  - B.9. Points on the shifted plane satisfy the ACCs
  - B.10. Kernel of the inclusion into charges
  - B.11. The inclusion of the shifted plane into `LinSols` (`shiftPlane`)

-/

@[expose] public section

open Module Nat Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeOddPlane

section theDeltas

/-!

### A.1. The shifted split: Splitting the charges up via `1 + n + n`

-/

/-- The inclusion of `Fin n` into `Fin (1 + n + n)` via the first `n`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddShiftFst (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (odd_shift_eq n) (Fin.castAdd n (Fin.natAdd 1 j))

/-- The inclusion of `Fin n` into `Fin (1 + n + n)` via the second `n`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddShiftSnd (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (odd_shift_eq n) (Fin.natAdd (1 + n) j)

/-- The element representing the `1` in `Fin (1 + n + n)`.
  This is then casted to `Fin (2 * n + 1)`. -/
def oddShiftZero : Fin (2 * n + 1) :=
  Fin.cast (odd_shift_eq n) (Fin.castAdd n (Fin.castAdd n 1))

lemma sum_oddShift (S : Fin (2 * n + 1) → ℚ) :
    ∑ i, S i = S oddShiftZero + ∑ i : Fin n, ((S ∘ oddShiftFst) i + (S ∘ oddShiftSnd) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin ((1+n)+n), S (Fin.cast (odd_shift_eq n) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (odd_shift_eq n)).symm.toEquiv]
    · intro i
      simp only [mem_univ, Fin.castOrderIso, RelIso.coe_fn_toEquiv]
    · exact fun _ _ => rfl
  rw [h1, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton, Function.comp_apply]
  rw [add_assoc, Finset.sum_add_distrib]
  rfl

/-!

### A.2. The shifted shifted split: Splitting the charges up via `((1+n)+1) + n.succ`

-/

lemma odd_shift_shift_eq (n : ℕ) : ((1+n)+1) + n.succ = 2 * n.succ + 1 := by
  omega

/-- The element representing the first `1` in `Fin (1 + n + 1 + n.succ)` casted
  to `Fin (2 * n.succ + 1)`. -/
def oddShiftShiftZero : Fin (2 * n.succ + 1) :=
  Fin.cast (odd_shift_shift_eq n) (Fin.castAdd n.succ (Fin.castAdd 1 (Fin.castAdd n 1)))

/-- The inclusion of `Fin n` into `Fin (1 + n + 1 + n.succ)` via the first `n` and casted
  to `Fin (2 * n.succ + 1)`. -/
def oddShiftShiftFst (j : Fin n) : Fin (2 * n.succ + 1) :=
  Fin.cast (odd_shift_shift_eq n) (Fin.castAdd n.succ (Fin.castAdd 1 (Fin.natAdd 1 j)))

/-- The element representing the second `1` in `Fin (1 + n + 1 + n.succ)` casted
  to `2 * n.succ + 1`. -/
def oddShiftShiftMid : Fin (2 * n.succ + 1) :=
  Fin.cast (odd_shift_shift_eq n) (Fin.castAdd n.succ (Fin.natAdd (1+n) 1))

/-- The inclusion of `Fin n.succ` into `Fin (1 + n + 1 + n.succ)` via the `n.succ` and casted
  to `Fin (2 * n.succ + 1)`. -/
def oddShiftShiftSnd (j : Fin n.succ) : Fin (2 * n.succ + 1) :=
  Fin.cast (odd_shift_shift_eq n) (Fin.natAdd ((1+n)+1) j)

/-!

### A.3. Relating the splittings together

-/
lemma oddShiftShiftZero_eq_oddFst_zero : @oddShiftShiftZero n = oddFst 0 :=
  Fin.rev_inj.mp rfl

lemma oddShiftShiftZero_eq_oddShiftZero : @oddShiftShiftZero n = oddShiftZero := rfl

lemma oddShiftShiftFst_eq_oddFst_succ (j : Fin n) :
    oddShiftShiftFst j = oddFst j.succ := by
  rw [Fin.ext_iff]
  simp only [succ_eq_add_one, oddShiftShiftFst, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
    oddFst, Fin.val_succ]
  exact Nat.add_comm 1 ↑j

lemma oddShiftShiftFst_eq_oddShiftFst_castSucc (j : Fin n) :
    oddShiftShiftFst j = oddShiftFst j.castSucc := by
  rfl

lemma oddShiftShiftMid_eq_oddMid : @oddShiftShiftMid n = oddMid := by
  rw [Fin.ext_iff]
  simp only [succ_eq_add_one, oddShiftShiftMid, Fin.isValue, Fin.val_cast, Fin.val_castAdd,
    Fin.val_natAdd, Fin.val_eq_zero, add_zero, oddMid]
  exact Nat.add_comm 1 n

lemma oddShiftShiftMid_eq_oddShiftFst_last : oddShiftShiftMid = oddShiftFst (Fin.last n) := by
  rfl

lemma oddShiftShiftSnd_eq_oddSnd (j : Fin n.succ) : oddShiftShiftSnd j = oddSnd j := by
  rw [Fin.ext_iff]
  simp only [succ_eq_add_one, oddShiftShiftSnd, Fin.val_cast, Fin.val_natAdd, oddSnd, add_left_inj]
  exact Nat.add_comm 1 n

lemma oddShiftShiftSnd_eq_oddShiftSnd (j : Fin n.succ) : oddShiftShiftSnd j = oddShiftSnd j := by
  rw [Fin.ext_iff]
  rfl

lemma oddSnd_eq_oddShiftSnd (j : Fin n) : oddSnd j = oddShiftSnd j := by
  rw [Fin.ext_iff]
  simp only [oddSnd, Fin.val_cast, Fin.val_natAdd, oddShiftSnd, add_left_inj]
  exact Nat.add_comm n 1

lemma oddShiftZero_eq_oddFst : oddShiftZero = oddFst (0 : Fin n.succ) := by
  ext
  simp [oddShiftZero, oddFst]

lemma oddShiftFst_castSucc_eq_oddFst_succ (j : Fin n) :
    oddShiftFst j.castSucc = oddFst j.succ := by
  rw [Fin.ext_iff]
  simp only [oddShiftFst, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, oddFst, Fin.val_succ]
  exact Nat.add_comm 1 ↑j

lemma oddShiftFst_last_eq_oddMid : oddShiftFst (Fin.last n) = oddMid := by
  rw [Fin.ext_iff]
  simp only [oddShiftFst, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, oddMid, Fin.val_last]
  exact Nat.add_comm 1 n

lemma oddShiftSnd_eq_oddSnd (j : Fin n) : oddShiftSnd j = oddSnd j := by
  rw [Fin.ext_iff]
  simp only [oddShiftSnd, Fin.val_cast, Fin.val_natAdd, oddSnd, add_left_inj]
  ring

end theDeltas

/-!

## B. The shifted plane

-/

/-!

### B.1. The basis vectors of the shifted plane as charges

-/

/-- The basis vectors of the shifted plane as charge assignments. -/
def shiftBasisAsCharges (j : Fin n) : (PureU1 (2 * n + 1)).Charges :=
  fun i =>
  if i = oddShiftFst j then
    1
  else
    if i = oddShiftSnd j then
      - 1
    else
      0

/-!

### B.2. Components of the basis vectors as charges

-/

lemma shiftBasisAsCharges_on_oddShiftFst_self (j : Fin n) :
    shiftBasisAsCharges j (oddShiftFst j) = 1 := by
  simp [shiftBasisAsCharges]

lemma shiftBasisAsCharges_on_oddShiftFst_other {k j : Fin n} (h : k ≠ j) :
    shiftBasisAsCharges k (oddShiftFst j) = 0 := by
  simp only [shiftBasisAsCharges, PureU1_numberCharges]
  simp only [oddShiftFst, oddShiftSnd]
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
    rfl

lemma shiftBasisAsCharges_on_other {k : Fin n} {j : Fin (2 * n + 1)}
    (h1 : j ≠ oddShiftFst k) (h2 : j ≠ oddShiftSnd k) :
    shiftBasisAsCharges k j = 0 := by
  simp only [shiftBasisAsCharges, PureU1_numberCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma shiftBasisAsCharges_oddShiftSnd_eq_minus_oddShiftFst (j i : Fin n) :
    shiftBasisAsCharges j (oddShiftSnd i) = - shiftBasisAsCharges j (oddShiftFst i) := by
  simp only [shiftBasisAsCharges, PureU1_numberCharges, oddShiftSnd, oddShiftFst]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals rename_i h1 h2
  all_goals rw [Fin.ext_iff] at h1 h2
  all_goals simp_all
  · subst h1
    exact Fin.elim0 i
  all_goals rename_i h3
  all_goals rw [Fin.ext_iff] at h3
  all_goals simp_all
  all_goals omega

lemma shiftBasisAsCharges_on_oddShiftSnd_self (j : Fin n) :
    shiftBasisAsCharges j (oddShiftSnd j) = - 1 := by
  rw [shiftBasisAsCharges_oddShiftSnd_eq_minus_oddShiftFst,
    shiftBasisAsCharges_on_oddShiftFst_self]

lemma shiftBasisAsCharges_on_oddShiftSnd_other {k j : Fin n} (h : k ≠ j) :
    shiftBasisAsCharges k (oddShiftSnd j) = 0 := by
  rw [shiftBasisAsCharges_oddShiftSnd_eq_minus_oddShiftFst,
    shiftBasisAsCharges_on_oddShiftFst_other h]
  rfl

lemma shiftBasisAsCharges_on_oddShiftZero (j : Fin n) :
    shiftBasisAsCharges j oddShiftZero = 0 := by
  simp only [shiftBasisAsCharges, PureU1_numberCharges]
  split <;> rename_i h
  · rw [Fin.ext_iff] at h
    simp only [oddShiftZero, Fin.isValue, Fin.val_cast, Fin.val_castAdd, Fin.val_eq_zero,
      oddShiftFst, Fin.val_natAdd] at h
    omega
  · split <;> rename_i h2
    · rw [Fin.ext_iff] at h2
      simp only [oddShiftZero, Fin.isValue, Fin.val_cast, Fin.val_castAdd, Fin.val_eq_zero,
        oddShiftSnd, Fin.val_natAdd] at h2
      omega
    · rfl

/-!

### B.3. The basis vectors satisfy the linear ACCs

-/

lemma shiftBasisAsCharges_linearACC (j : Fin n) :
    (accGrav (2 * n + 1)) (shiftBasisAsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_oddShift, shiftBasisAsCharges_on_oddShiftZero]
  simp [shiftBasisAsCharges_oddShiftSnd_eq_minus_oddShiftFst]

/-!

### B.4. The basis vectors as `LinSols`

-/

/-- The basis vectors of the shifted plane as `LinSols`. -/
@[simps!]
def shiftBasis (j : Fin n) : (PureU1 (2 * n + 1)).LinSols :=
  ⟨shiftBasisAsCharges j, by
    intro i
    simp only [PureU1_numberLinear] at i
    match i with
    | 0 =>
    exact shiftBasisAsCharges_linearACC j⟩

/-!

### B.5. The basis vectors are linearly independent

-/

theorem shiftBasis_linear_independent : LinearIndependent ℚ (@shiftBasis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change shiftPlane f = 0 at h
  have h1 : (shiftPlane f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [shiftPlane_val] at h1
  exact shiftPlaneAsCharges_zero f h1

/-!

### B.6. Permutations equal adding basis vectors

-/

/-- Swapping the elements oddShiftFst j and oddShiftSnd j is equivalent to adding a vector
  shiftBasisAsCharges j. -/
lemma linSolRep_swap_oddShift_eq_add {S S' : (PureU1 (2 * n + 1)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n + 1)).linSolRep
    (Equiv.swap (oddShiftFst j) (oddShiftSnd j))) S = S') :
    S'.val = S.val + (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) •
      shiftBasisAsCharges j := by
  funext i
  rw [← hS, FamilyPermutations_anomalyFreeLinear_apply]
  by_cases hi : i = oddShiftFst j
  · subst hi
    simp [HSMul.hSMul, shiftBasisAsCharges_on_oddShiftFst_self, Equiv.swap_apply_left]
  · by_cases hi2 : i = oddShiftSnd j
    · subst hi2
      simp [HSMul.hSMul, shiftBasisAsCharges_on_oddShiftSnd_self, Equiv.swap_apply_right]
    · simp only [Equiv.invFun_as_coe, HSMul.hSMul, ACCSystemCharges.chargesAddCommMonoid_add,
        ACCSystemCharges.chargesModule_smul]
      rw [shiftBasisAsCharges_on_other hi hi2]
      aesop

/-!

### B.7. The inclusion of the shifted plane into charges (`shiftPlaneAsCharges`)

-/

/-- A point in the span of the shifted plane basis as a charge. -/
def shiftPlaneAsCharges (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges :=
  ∑ i, f i • shiftBasisAsCharges i

/-!

### B.8. Components of the shifted plane

-/

lemma shiftPlaneAsCharges_oddShiftFst (f : Fin n → ℚ) (j : Fin n) :
    shiftPlaneAsCharges f (oddShiftFst j) = f j := by
  rw [shiftPlaneAsCharges, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [shiftBasisAsCharges_on_oddShiftFst_self]
    exact Rat.mul_one (f j)
  · intro k _ hkj
    rw [shiftBasisAsCharges_on_oddShiftFst_other hkj]
    exact Rat.mul_zero (f k)
  · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma shiftPlaneAsCharges_oddShiftSnd (f : Fin n → ℚ) (j : Fin n) :
    shiftPlaneAsCharges f (oddShiftSnd j) = - f j := by
  rw [shiftPlaneAsCharges, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [shiftBasisAsCharges_on_oddShiftSnd_self]
    exact mul_neg_one (f j)
  · intro k _ hkj
    rw [shiftBasisAsCharges_on_oddShiftSnd_other hkj]
    exact Rat.mul_zero (f k)
  · simp

lemma shiftPlaneAsCharges_oddShiftZero (f : Fin n → ℚ) : shiftPlaneAsCharges f oddShiftZero = 0 := by
  rw [shiftPlaneAsCharges, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, shiftBasisAsCharges_on_oddShiftZero]

/-!

### B.9. Points on the shifted plane satisfy the ACCs

-/

lemma shiftPlaneAsCharges_linearACC (f : Fin n → ℚ) :
    (accGrav (2 * n + 1)) (shiftPlaneAsCharges f) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_oddShift]
  simp [shiftPlaneAsCharges_oddShiftSnd, shiftPlaneAsCharges_oddShiftFst, shiftPlaneAsCharges_oddShiftZero]

set_option backward.isDefEq.respectTransparency false in
lemma shiftPlaneAsCharges_accCube (f : Fin n → ℚ) : accCube (2 * n +1) (shiftPlaneAsCharges f) = 0 := by
  rw [accCube_explicit, sum_oddShift, shiftPlaneAsCharges_oddShiftZero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Function.comp_apply,
    zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp only [shiftPlaneAsCharges_oddShiftFst, shiftPlaneAsCharges_oddShiftSnd]
  ring

/-!

### B.10. Kernel of the inclusion into charges

-/

lemma shiftPlaneAsCharges_zero (f : Fin n → ℚ) (h : shiftPlaneAsCharges f = 0) : ∀ i, f i = 0 := by
  intro i
  rw [← shiftPlaneAsCharges_oddShiftFst f]
  rw [h]
  rfl

/-!

### B.11. The inclusion of the shifted plane into `LinSols`

-/

/-- A point in the span of the shifted plane basis. -/
def shiftPlane (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).LinSols :=
  ∑ i, f i • shiftBasis i

lemma shiftPlane_val (f : Fin n → ℚ) :
    (shiftPlane f).val = shiftPlaneAsCharges f := by
  simp only [shiftPlane, shiftPlaneAsCharges]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

end VectorLikeOddPlane

end PureU1
