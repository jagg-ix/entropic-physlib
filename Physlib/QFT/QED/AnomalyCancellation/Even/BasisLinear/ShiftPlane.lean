/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear.ChargeSplits
/-!

# The shifted plane for the even case basis

-/

@[expose] public section

open Nat Module Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeEvenPlane

/-!

## C. The shifted plane

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

### C.2. Components of the vectors

-/

lemma shiftBasis_on_evenShiftFst_self (j : Fin n) : shiftBasisAsCharges j (evenShiftFst j) = 1 := by
  simp [shiftBasisAsCharges]

lemma shiftBasis_on_other {k : Fin n} {j : Fin (2 * n.succ)} (h1 : j ≠ evenShiftFst k)
    (h2 : j ≠ evenShiftSnd k) : shiftBasisAsCharges k j = 0 := by
  simp only [shiftBasisAsCharges, succ_eq_add_one, PureU1_numberCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma shiftBasis_on_evenShiftFst_other {k j : Fin n} (h : k ≠ j) :
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

lemma shiftBasis_evenShiftSnd_eq_neg_evenShiftFst (j i : Fin n) :
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

lemma shiftBasis_on_evenShiftSnd_self (j : Fin n) : shiftBasisAsCharges j (evenShiftSnd j) = - 1 := by
  rw [shiftBasis_evenShiftSnd_eq_neg_evenShiftFst, shiftBasis_on_evenShiftFst_self]

lemma shiftBasis_on_evenShiftSnd_other {k j : Fin n} (h : k ≠ j) :
    shiftBasisAsCharges k (evenShiftSnd j) = 0 := by
  rw [shiftBasis_evenShiftSnd_eq_neg_evenShiftFst, shiftBasis_on_evenShiftFst_other h]
  rfl

lemma shiftBasis_on_evenShiftZero (j : Fin n) : shiftBasisAsCharges j evenShiftZero = 0 := by
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

lemma shiftBasis_on_evenShiftLast (j : Fin n) : shiftBasisAsCharges j evenShiftLast = 0 := by
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

### C.3. The vectors satisfy the linear ACCs

-/

lemma shiftBasis_linearACC (j : Fin n) : (accGrav (2 * n.succ)) (shiftBasisAsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_evenShift, shiftBasis_on_evenShiftZero, shiftBasis_on_evenShiftLast]
  simp [shiftBasis_evenShiftSnd_eq_neg_evenShiftFst]

/-!

### C.4. The vectors satisfy the cubic ACC

-/

set_option backward.isDefEq.respectTransparency false in
lemma shiftBasis_accCube (j : Fin n) :
    accCube (2 * n.succ) (shiftBasisAsCharges j) = 0 := by
  rw [accCube_explicit, sum_evenShift]
  rw [shiftBasis_on_evenShiftLast, shiftBasis_on_evenShiftZero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Function.comp_apply,
    zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp only [shiftBasis_evenShiftSnd_eq_neg_evenShiftFst]
  ring

/-!

### C.6. The vectors as linear solutions

-/
/-- The basis vectors of the shifted plane as `LinSols`. -/
@[simps!]
def shiftBasis (j : Fin n) : (PureU1 (2 * n.succ)).LinSols :=
  ⟨shiftBasisAsCharges j, by
    intro i
    simp only [succ_eq_add_one, PureU1_numberLinear] at i
    match i with
    | 0 =>
    exact shiftBasis_linearACC j⟩

/-!

### C.7. The inclusion of the shifted plane into charges

-/

/-- A point in the span of the shifted plane basis as a charge. -/
def Pshift (f : Fin n → ℚ) : (PureU1 (2 * n.succ)).Charges := ∑ i, f i • shiftBasisAsCharges i

/-!

### C.8. Components of the inclusion into charges

-/

lemma Pshift_evenShiftFst (f : Fin n → ℚ) (j : Fin n) : Pshift f (evenShiftFst j) = f j := by
  rw [Pshift, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [shiftBasis_on_evenShiftFst_self]
    exact Rat.mul_one (f j)
  · intro k _ hkj
    rw [shiftBasis_on_evenShiftFst_other hkj]
    exact Rat.mul_zero (f k)
  · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma Pshift_evenShiftSnd (f : Fin n → ℚ) (j : Fin n) : Pshift f (evenShiftSnd j) = - f j := by
  rw [Pshift, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [shiftBasis_on_evenShiftSnd_self]
    exact mul_neg_one (f j)
  · intro k _ hkj
    rw [shiftBasis_on_evenShiftSnd_other hkj]
    exact Rat.mul_zero (f k)
  · simp

lemma Pshift_evenShiftZero (f : Fin n → ℚ) : Pshift f (evenShiftZero) = 0 := by
  rw [Pshift, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, shiftBasis_on_evenShiftZero]

lemma Pshift_evenShiftLast (f : Fin n → ℚ) : Pshift f evenShiftLast = 0 := by
  rw [Pshift, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, shiftBasis_on_evenShiftLast]

/-!

### C.9. The inclusion into charges satisfies the cubic ACC

-/

set_option backward.isDefEq.respectTransparency false in
lemma Pshift_accCube (f : Fin n → ℚ) : accCube (2 * n.succ) (Pshift f) = 0 := by
  rw [accCube_explicit, sum_evenShift, Pshift_evenShiftZero, Pshift_evenShiftLast]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Function.comp_apply,
    zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp only [Pshift_evenShiftFst, Pshift_evenShiftSnd]
  ring

/-!

### C.10. Kernel of the inclusion into charges

-/

lemma Pshift_zero (f : Fin n → ℚ) (h : Pshift f = 0) : ∀ i, f i = 0 := by
  intro i
  rw [← Pshift_evenShiftFst f]
  rw [h]
  rfl

/-!

### C.11. The inclusion of the shifted plane into the span of the basis

-/

lemma Pshift_in_span (f : Fin n → ℚ) : Pshift f ∈ Submodule.span ℚ (Set.range shiftBasisAsCharges) := by
  rw [(Submodule.mem_span_range_iff_exists_fun ℚ)]
  use f
  rfl

/-!

### C.12. The inclusion of the plane into linear solutions

-/

/-- A point in the span of the shifted plane basis. -/
def Pshift' (f : Fin n → ℚ) : (PureU1 (2 * n.succ)).LinSols := ∑ i, f i • shiftBasis i

lemma Pshift'_val (f : Fin n → ℚ) : (Pshift' f).val = Pshift f := by
  simp only [succ_eq_add_one, Pshift', Pshift]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

/-!

### C.13. The basis vectors are linearly independent

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

/-!

### C.14. Properties of the basis vectors relating to the span

-/

lemma smul_shiftBasisAsCharges_in_span (S : (PureU1 (2 * n.succ)).LinSols) (j : Fin n) :
    (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • shiftBasisAsCharges j ∈
    Submodule.span ℚ (Set.range shiftBasisAsCharges) := by
  apply Submodule.smul_mem
  apply SetLike.mem_of_subset
  · exact Submodule.subset_span
  · simp_all only [Set.mem_range, exists_apply_eq_apply]

/-!

### C.15. Permutations as additions of basis vectors

-/

/-- Swapping the elements evenShiftFst j and evenShiftSnd j is equivalent to
  adding a vector shiftBasisAsCharges j. -/
lemma swapShift_as_add {S S' : (PureU1 (2 * n.succ)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n.succ)).linSolRep
    (Equiv.swap (evenShiftFst j) (evenShiftSnd j))) S = S') :
    S'.val = S.val + (S.val (evenShiftSnd j) - S.val (evenShiftFst j)) • shiftBasisAsCharges j := by
  funext i
  rw [← hS, FamilyPermutations_anomalyFreeLinear_apply]
  by_cases hi : i = evenShiftFst j
  · subst hi
    simp [HSMul.hSMul, shiftBasis_on_evenShiftFst_self, Equiv.swap_apply_left]
  · by_cases hi2 : i = evenShiftSnd j
    · simp [HSMul.hSMul, hi2, shiftBasis_on_evenShiftSnd_self, Equiv.swap_apply_right]
    · simp only [succ_eq_add_one, Equiv.invFun_as_coe, HSMul.hSMul,
      ACCSystemCharges.chargesAddCommMonoid_add, ACCSystemCharges.chargesModule_smul]
      rw [shiftBasis_on_other hi hi2]
      aesop

end VectorLikeEvenPlane

end PureU1
