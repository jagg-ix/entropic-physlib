/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear.ChargeSplits
/-!

# The symmetric plane for the even case basis

-/

@[expose] public section

open Nat Module Finset BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeEvenPlane

/-!

## B. The symmetric plane

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

lemma symmBasis_on_evenFst_self (j : Fin n.succ) : symmBasisAsCharges j (evenFst j) = 1 := by
  simp [symmBasisAsCharges]

lemma symmBasis_on_evenFst_other {k j : Fin n.succ} (h : k ≠ j) :
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

lemma symmBasis_on_other {k : Fin n.succ} {j : Fin (2 * n.succ)} (h1 : j ≠ evenFst k)
    (h2 : j ≠ evenSnd k) : symmBasisAsCharges k j = 0 := by
  simp only [symmBasisAsCharges, succ_eq_add_one, PureU1_numberCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma symmBasis_evenSnd_eq_neg_evenFst (j i : Fin n.succ) :
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

lemma symmBasis_on_evenSnd_self (j : Fin n.succ) : symmBasisAsCharges j (evenSnd j) = - 1 := by
  rw [symmBasis_evenSnd_eq_neg_evenFst, symmBasis_on_evenFst_self]

lemma symmBasis_on_evenSnd_other {k j : Fin n.succ} (h : k ≠ j) : symmBasisAsCharges k (evenSnd j) = 0 := by
  rw [symmBasis_evenSnd_eq_neg_evenFst, symmBasis_on_evenFst_other h]
  rfl

/-!

### B.3. The basis vectors satisfy the linear ACCs

-/

lemma symmBasis_linearACC (j : Fin n.succ) : (accGrav (2 * n.succ)) (symmBasisAsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_even]
  simp [symmBasis_evenSnd_eq_neg_evenFst]
/-!

### B.4. The basis vectors satisfy the cubic ACC

-/
lemma symmBasis_accCube (j : Fin n.succ) :
    accCube (2 * n.succ) (symmBasisAsCharges j) = 0 := by
  rw [accCube_explicit, sum_even]
  apply Finset.sum_eq_zero
  intro i _
  simp only [succ_eq_add_one, Function.comp_apply, symmBasis_evenSnd_eq_neg_evenFst]
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
    exact symmBasis_linearACC j⟩

/-!

### B.6. The inclusion of the symmetric plane into charges

-/

/-- A point in the span of the symmetric plane basis as a charge. -/
def Psymm (f : Fin n.succ → ℚ) : (PureU1 (2 * n.succ)).Charges := ∑ i, f i • symmBasisAsCharges i

/-!

### B.7. Components of the inclusion into charges

-/

lemma Psymm_evenFst (f : Fin n.succ → ℚ) (j : Fin n.succ) : Psymm f (evenFst j) = f j := by
  rw [Psymm, sum_of_charges]
  simp only [succ_eq_add_one, HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [symmBasis_on_evenFst_self]
    exact Rat.mul_one (f j)
  · intro k _ hkj
    rw [symmBasis_on_evenFst_other hkj]
    exact Rat.mul_zero (f k)
  · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma Psymm_evenSnd (f : Fin n.succ → ℚ) (j : Fin n.succ) : Psymm f (evenSnd j) = - f j := by
  rw [Psymm, sum_of_charges]
  simp only [succ_eq_add_one, HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · simp only [symmBasis_on_evenSnd_self, mul_neg, mul_one]
  · intro k _ hkj
    simp only [symmBasis_on_evenSnd_other hkj, mul_zero]
  · simp

lemma Psymm_evenSnd_evenFst (f : Fin n.succ → ℚ) : Psymm f ∘ evenSnd = - Psymm f ∘ evenFst := by
  funext j
  simp only [PureU1_numberCharges, Function.comp_apply, Pi.neg_apply]
  rw [Psymm_evenFst, Psymm_evenSnd]

/-!

### B.8. The inclusion into charges satisfies the linear and cubic ACCs

-/

lemma Psymm_linearACC (f : Fin n.succ → ℚ) : (accGrav (2 * n.succ)) (Psymm f) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_even]
  simp [Psymm_evenSnd, Psymm_evenFst]

lemma Psymm_accCube (f : Fin n.succ → ℚ) : accCube (2 * n.succ) (Psymm f) = 0 := by
  rw [accCube_explicit, sum_even]
  apply Finset.sum_eq_zero
  intro i _
  simp only [succ_eq_add_one, Function.comp_apply, Psymm_evenFst, Psymm_evenSnd]
  ring

/-!

### B.9. Kernel of the inclusion into charges

-/

lemma Psymm_zero (f : Fin n.succ → ℚ) (h : Psymm f = 0) : ∀ i, f i = 0 := by
  intro i
  erw [← Psymm_evenFst f]
  rw [h]
  rfl

/-!

### B.10. The inclusion of the plane into linear solutions

-/

/-- A point in the span of the symmetric plane basis. -/
def Psymm' (f : Fin n.succ → ℚ) : (PureU1 (2 * n.succ)).LinSols := ∑ i, f i • symmBasis i

lemma Psymm'_val (f : Fin n.succ → ℚ) : (Psymm' f).val = Psymm f := by
  simp only [succ_eq_add_one, Psymm', Psymm]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

/-!

### B.11. The basis vectors are linearly independent

-/

theorem symmBasis_linear_independent : LinearIndependent ℚ (@symmBasis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change Psymm' f = 0 at h
  have h1 : (Psymm' f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [Psymm'_val] at h1
  exact Psymm_zero f h1

/-!

### B.12. Every vector-like even solution is in the span of the basis of the symmetric plane

-/

lemma vectorLikeEven_in_span (S : (PureU1 (2 * n.succ)).LinSols)
    (hS : VectorLikeEven S.val) : ∃ (M : (FamilyPermutations (2 * n.succ)).group),
      (FamilyPermutations (2 * n.succ)).linSolRep M S ∈ Submodule.span ℚ (Set.range symmBasis) := by
  use (Tuple.sort S.val).symm
  change sortAFL S ∈ Submodule.span ℚ (Set.range symmBasis)
  rw [Submodule.mem_span_range_iff_exists_fun ℚ]
  let f : Fin n.succ → ℚ := fun i => (sortAFL S).val (evenFst i)
  use f
  apply ACCSystemLinear.LinSols.ext
  rw [sortAFL_val]
  erw [Psymm'_val]
  apply ext_even
  · intro i
    rw [Psymm_evenFst]
    rfl
  · intro i
    rw [Psymm_evenSnd]
    have ht := hS i
    change sort S.val (evenFst i) = - sort S.val (evenSnd i) at ht
    have h : sort S.val (evenSnd i) = - sort S.val (evenFst i) := by
      rw [ht]
      ring
    rw [h]
    rfl

end VectorLikeEvenPlane

end PureU1
