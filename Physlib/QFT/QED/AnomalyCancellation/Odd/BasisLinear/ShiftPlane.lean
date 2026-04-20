/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Odd.BasisLinear.ChargeSplits
/-!
# The shifted plane for the odd case basis
-/

@[expose] public section

open Module Nat Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeOddPlane

/-!

## C. The shifted plane

-/

/-!

### C.1. The basis vectors of the shifted plane as charges

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

### C.2. Components of the basis vectors as charges

-/

lemma shiftBasis_on_oddShiftFst_self (j : Fin n) : shiftBasisAsCharges j (oddShiftFst j) = 1 := by
  simp [shiftBasisAsCharges]

lemma shiftBasis_on_oddShiftFst_other {k j : Fin n} (h : k ≠ j) :
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

lemma shiftBasis_on_other {k : Fin n} {j : Fin (2 * n + 1)}
    (h1 : j ≠ oddShiftFst k) (h2 : j ≠ oddShiftSnd k) :
    shiftBasisAsCharges k j = 0 := by
  simp only [shiftBasisAsCharges, PureU1_numberCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma shiftBasis_oddShiftSnd_eq_minus_oddShiftFst (j i : Fin n) :
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

lemma shiftBasis_on_oddShiftSnd_self (j : Fin n) : shiftBasisAsCharges j (oddShiftSnd j) = - 1 := by
  rw [shiftBasis_oddShiftSnd_eq_minus_oddShiftFst, shiftBasis_on_oddShiftFst_self]

lemma shiftBasis_on_oddShiftSnd_other {k j : Fin n} (h : k ≠ j) :
    shiftBasisAsCharges k (oddShiftSnd j) = 0 := by
  rw [shiftBasis_oddShiftSnd_eq_minus_oddShiftFst, shiftBasis_on_oddShiftFst_other h]
  rfl

lemma shiftBasis_on_oddShiftZero (j : Fin n) : shiftBasisAsCharges j oddShiftZero = 0 := by
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

### C.3. The basis vectors satisfy the linear ACCs

-/

lemma shiftBasis_linearACC (j : Fin n) : (accGrav (2 * n + 1)) (shiftBasisAsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_oddShift, shiftBasis_on_oddShiftZero]
  simp [shiftBasis_oddShiftSnd_eq_minus_oddShiftFst]

/-!

### C.4. The basis vectors as `LinSols`

-/

/-- The basis vectors of the shifted plane as `LinSols`. -/
@[simps!]
def shiftBasis (j : Fin n) : (PureU1 (2 * n + 1)).LinSols :=
  ⟨shiftBasisAsCharges j, by
    intro i
    simp only [PureU1_numberLinear] at i
    match i with
    | 0 =>
    exact shiftBasis_linearACC j⟩

/-!

### C.5. Permutations equal adding basis vectors

-/

/-- Swapping the elements oddShiftFst j and oddShiftSnd j is equivalent to adding a vector
  shiftBasisAsCharges j. -/
lemma swapShift_as_add {S S' : (PureU1 (2 * n + 1)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n + 1)).linSolRep
    (Equiv.swap (oddShiftFst j) (oddShiftSnd j))) S = S') :
    S'.val = S.val + (S.val (oddShiftSnd j) - S.val (oddShiftFst j)) • shiftBasisAsCharges j := by
  funext i
  rw [← hS, FamilyPermutations_anomalyFreeLinear_apply]
  by_cases hi : i = oddShiftFst j
  · subst hi
    simp [HSMul.hSMul, shiftBasis_on_oddShiftFst_self, Equiv.swap_apply_left]
  · by_cases hi2 : i = oddShiftSnd j
    · subst hi2
      simp [HSMul.hSMul, shiftBasis_on_oddShiftSnd_self, Equiv.swap_apply_right]
    · simp only [Equiv.invFun_as_coe, HSMul.hSMul, ACCSystemCharges.chargesAddCommMonoid_add,
        ACCSystemCharges.chargesModule_smul]
      rw [shiftBasis_on_other hi hi2]
      aesop

/-!

### C.6. The inclusion of the shifted plane into charges

-/

/-- A point in the span of the shifted plane basis as a charge. -/
def Pshift (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges := ∑ i, f i • shiftBasisAsCharges i

/-!

### C.7. Components of the shifted plane

-/

lemma Pshift_oddShiftFst (f : Fin n → ℚ) (j : Fin n) : Pshift f (oddShiftFst j) = f j := by
  rw [Pshift, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [shiftBasis_on_oddShiftFst_self]
    exact Rat.mul_one (f j)
  · intro k _ hkj
    rw [shiftBasis_on_oddShiftFst_other hkj]
    exact Rat.mul_zero (f k)
  · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma Pshift_oddShiftSnd (f : Fin n → ℚ) (j : Fin n) : Pshift f (oddShiftSnd j) = - f j := by
  rw [Pshift, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [shiftBasis_on_oddShiftSnd_self]
    exact mul_neg_one (f j)
  · intro k _ hkj
    rw [shiftBasis_on_oddShiftSnd_other hkj]
    exact Rat.mul_zero (f k)
  · simp

lemma Pshift_oddShiftZero (f : Fin n → ℚ) : Pshift f oddShiftZero = 0 := by
  rw [Pshift, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, shiftBasis_on_oddShiftZero]

/-!

### C.8. Points on the shifted plane satisfy the ACCs

-/

lemma Pshift_linearACC (f : Fin n → ℚ) : (accGrav (2 * n + 1)) (Pshift f) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_oddShift]
  simp [Pshift_oddShiftSnd, Pshift_oddShiftFst, Pshift_oddShiftZero]

set_option backward.isDefEq.respectTransparency false in
lemma Pshift_accCube (f : Fin n → ℚ) : accCube (2 * n +1) (Pshift f) = 0 := by
  rw [accCube_explicit, sum_oddShift, Pshift_oddShiftZero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Function.comp_apply, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp only [Pshift_oddShiftFst, Pshift_oddShiftSnd]
  ring

/-!

### C.9. Kernel of the inclusion into charges

-/

lemma Pshift_zero (f : Fin n → ℚ) (h : Pshift f = 0) : ∀ i, f i = 0 := by
  intro i
  rw [← Pshift_oddShiftFst f]
  rw [h]
  rfl

/-!

### C.10. The inclusion of the shifted plane into LinSols

-/

/-- A point in the span of the shifted plane basis. -/
def Pshift' (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).LinSols := ∑ i, f i • shiftBasis i

lemma Pshift'_val (f : Fin n → ℚ) : (Pshift' f).val = Pshift f := by
  simp only [Pshift', Pshift]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

/-!

### C.11. The basis vectors are linearly independent

-/

theorem shiftBasis_linear_independent : LinearIndependent ℚ (@shiftBasis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change Pshift' f = 0 at h
  have h1 : (Pshift' f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [Pshift'_val] at h1
  exact Pshift_zero f h1

end VectorLikeOddPlane

end PureU1
