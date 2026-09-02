/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedCone

/-!
# Explicit coordinates for multi-norm marked cones

This module formalizes the logarithmic part of Proposition 3.2 in
A. Hejna, A. Nagel, and F. Ricci, *Littlewood-Paley square functions and the
local Hardy space for Multi-Norm Structures on R^d* (arXiv:2507.09399).

For marks `p` and `q` of a marked partition `S`, the coefficient

`τ_S(p,q) = min_{l in block(q)} e(p,l) / e(q,l)`

controls the relative sizes of the marked coordinates. The main result proves
that the dominance-based cone `Γ_S` already defined in `MultiNormMarkedCone`
is exactly the set cut out by the paper's two explicit families of
inequalities: coordinates are controlled by the mark of their own block, and
marked coordinates are controlled pairwise by `τ_S`.

This is the algebraic input for the later maximal-tube and dyadic-cell
constructions. It does not assert that a marked cone has nonempty interior,
classify the singular tie locus, or construct frequency-space multipliers.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormMarkedPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! # A. Finite marked blocks and the coefficients `τ_S` -/

/-- A dotted index of `S`, bundled with the proof that it is an active mark. -/
def MarkedIndex (S : MultiNormMarkedPartition ι) :=
  {k : ι // k ∈ S.marks}

/-- The finite block carrying the index `k`. For an active mark this finset is
nonempty and contains `k`. -/
def blockFinset (S : MultiNormMarkedPartition ι) (k : ι) : Finset ι :=
  Finset.univ.filter fun i => S.mark i = k

@[simp] lemma mem_blockFinset_iff (S : MultiNormMarkedPartition ι)
    (i k : ι) :
    i ∈ S.blockFinset k ↔ S.mark i = k := by
  simp [blockFinset]

omit [Fintype ι] [DecidableEq ι] in
/-- Every bundled marked index is fixed by the mark map. -/
lemma MarkedIndex.mark_fixed (S : MultiNormMarkedPartition ι)
    (k : S.MarkedIndex) :
    S.mark k.1 = k.1 :=
  (S.mem_marks_iff_fixed k.1).mp k.2

/-- The finite block of an active mark is nonempty. -/
lemma blockFinset_nonempty (S : MultiNormMarkedPartition ι)
    (k : S.MarkedIndex) :
    (S.blockFinset k.1).Nonempty := by
  exact ⟨k.1, (S.mem_blockFinset_iff k.1 k.1).2 (MarkedIndex.mark_fixed S k)⟩

/-- The paper's coefficient
`τ_S(p,q) = min_{l in block(q)} e(p,l) / e(q,l)` for active marks `p,q`. -/
def tau (S : MultiNormMarkedPartition ι)
    (E : StandardMultiNormMatrix ι) (p q : S.MarkedIndex) : ℝ :=
  (S.blockFinset q.1).inf' (S.blockFinset_nonempty q)
    (fun l => E p.1 l / E q.1 l)

/-- The coefficient `τ_S(p,q)` is no larger than the matrix ratio at any
coordinate in the block marked by `q`. -/
lemma tau_le_ratio (S : MultiNormMarkedPartition ι)
    (E : StandardMultiNormMatrix ι) (p q : S.MarkedIndex)
    {i : ι} (hi : S.mark i = q.1) :
    S.tau E p q ≤ E p.1 i / E q.1 i := by
  exact Finset.inf'_le _ ((S.mem_blockFinset_iff i q.1).2 hi)

/-- The finite minimum defining `τ_S` is attained in the block marked by `q`. -/
lemma exists_tau_eq_ratio (S : MultiNormMarkedPartition ι)
    (E : StandardMultiNormMatrix ι) (p q : S.MarkedIndex) :
    ∃ i, S.mark i = q.1 ∧ S.tau E p q = E p.1 i / E q.1 i := by
  obtain ⟨i, hi, hmin⟩ := Finset.exists_mem_eq_inf'
    (S.blockFinset_nonempty q) (fun l => E p.1 l / E q.1 l)
  exact ⟨i, (S.mem_blockFinset_iff i q.1).mp hi, hmin⟩

/-- Every coefficient `τ_S(p,q)` is strictly positive. -/
lemma tau_pos (S : MultiNormMarkedPartition ι)
    (E : StandardMultiNormMatrix ι) (p q : S.MarkedIndex) :
    0 < S.tau E p q := by
  obtain ⟨i, -, hi⟩ := S.exists_tau_eq_ratio E p q
  rw [hi]
  exact div_pos (E.entry_pos p.1 i) (E.entry_pos q.1 i)

/-- A marked coordinate has unit relative coefficient with itself. -/
@[simp] lemma tau_self (S : MultiNormMarkedPartition ι)
    (E : StandardMultiNormMatrix ι) (p : S.MarkedIndex) :
    S.tau E p p = 1 := by
  apply Finset.inf'_eq_of_forall
  intro i hi
  exact div_self (E.entry_pos p.1 i).ne'

/-! # B. The explicit coordinate cone -/

/-- The explicit coordinate description of `Γ_S` from Proposition 3.2:
each coordinate is bounded by its block mark, while marked coordinates obey
the pairwise `τ_S` inequalities. -/
def explicitCone (S : MultiNormMarkedPartition ι)
    (E : StandardMultiNormMatrix ι) : Set (ι → ℝ) :=
  {t | (∀ i, 0 ≤ t i) ∧
    (∀ i, t i ≤ t (S.mark i) / E (S.mark i) i) ∧
    ∀ p q : S.MarkedIndex, t p.1 ≤ S.tau E p q * t q.1}

/-! # C. Equivalence with dominance -/

omit [Fintype ι] in
/-- Membership in the dominance cone implies the within-block coordinate
inequalities of the explicit cone. -/
lemma cone_withinBlock_le {S : MultiNormMarkedPartition ι}
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (ht : t ∈ S.cone E) (i : ι) :
    t i ≤ t (S.mark i) / E (S.mark i) i := by
  simpa [E.diagonal i] using ht.2 i i

/-- Membership in the dominance cone implies every pairwise marked-coordinate
inequality controlled by `τ_S`. -/
lemma cone_mark_le_tau_mul {S : MultiNormMarkedPartition ι}
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (ht : t ∈ S.cone E) (p q : S.MarkedIndex) :
    t p.1 ≤ S.tau E p q * t q.1 := by
  obtain ⟨i, hi, htau⟩ := S.exists_tau_eq_ratio E p q
  have hdom := ht.2 i p.1
  rw [hi] at hdom
  rw [htau, div_mul_eq_mul_div, le_div_iff₀ (E.entry_pos q.1 i)]
  rw [div_le_div_iff₀ (E.entry_pos p.1 i) (E.entry_pos q.1 i)] at hdom
  simpa [mul_comm] using hdom

/-- The paper's within-block and `τ_S` inequalities recover dominance in
every logarithmic gauge. -/
lemma dominates_of_explicitCone {S : MultiNormMarkedPartition ι}
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (ht : t ∈ S.explicitCone E) (i : ι) :
    E.Dominates (S.mark i) i t := by
  intro j
  let p : S.MarkedIndex := ⟨S.mark j, ⟨j, rfl⟩⟩
  let q : S.MarkedIndex := ⟨S.mark i, ⟨i, rfl⟩⟩
  have hwithin :
      t j / E j i ≤ t p.1 / E p.1 i := by
    calc
      t j / E j i ≤ (t p.1 / E p.1 j) / E j i := by
        apply (div_le_div_iff₀ (E.entry_pos j i) (E.entry_pos j i)).2
        simpa using mul_le_mul_of_nonneg_right
          (ht.2.1 j) (E.entry_pos j i).le
      _ = t p.1 / (E p.1 j * E j i) := by rw [div_div]
      _ ≤ t p.1 / E p.1 i := by
        apply (div_le_div_iff₀
          (mul_pos (E.entry_pos p.1 j) (E.entry_pos j i))
          (E.entry_pos p.1 i)).2
        exact mul_le_mul_of_nonneg_left
          (E.multiplicative_triangle p.1 j i) (ht.1 p.1)
  have htau : S.tau E p q ≤ E p.1 i / E q.1 i :=
    S.tau_le_ratio E p q rfl
  have hpq : t p.1 ≤ (E p.1 i / E q.1 i) * t q.1 :=
    (ht.2.2 p q).trans
      (mul_le_mul_of_nonneg_right htau (ht.1 q.1))
  have hmarks : t p.1 / E p.1 i ≤ t q.1 / E q.1 i := by
    rw [div_le_div_iff₀ (E.entry_pos p.1 i) (E.entry_pos q.1 i)]
    have hmul := mul_le_mul_of_nonneg_right hpq (E.entry_pos q.1 i).le
    calc
      t p.1 * E q.1 i ≤
          ((E p.1 i / E q.1 i) * t q.1) * E q.1 i := hmul
      _ = t q.1 * E p.1 i := by
        field_simp [E.entry_pos q.1 i |>.ne']
  exact hwithin.trans hmarks

/-- Proposition 3.2, logarithmic form: the dominance definition of `Γ_S` is
equivalent to its explicit within-block and pairwise `τ_S` inequalities. -/
lemma mem_cone_iff_explicitCone (S : MultiNormMarkedPartition ι)
    (E : StandardMultiNormMatrix ι) (t : ι → ℝ) :
    t ∈ S.cone E ↔ t ∈ S.explicitCone E := by
  constructor
  · intro ht
    exact ⟨ht.1, S.cone_withinBlock_le ht,
      fun p q => S.cone_mark_le_tau_mul ht p q⟩
  · intro ht
    exact ⟨ht.1, fun i => S.dominates_of_explicitCone ht i⟩

/-- Capstone: the existing marked cone is exactly the explicit coordinate cone
and therefore carries both families of inequalities from Proposition 3.2. -/
lemma markedCone_explicitCoordinate_characterization
    (S : MultiNormMarkedPartition ι) (E : StandardMultiNormMatrix ι) :
    S.cone E = S.explicitCone E := by
  ext t
  exact S.mem_cone_iff_explicitCone E t

end MultiNormMarkedPartition

end Physlib.Mathematics.HarmonicAnalysis
