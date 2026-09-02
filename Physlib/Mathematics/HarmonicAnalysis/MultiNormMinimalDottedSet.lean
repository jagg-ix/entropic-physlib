/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedConeCoordinates

/-!
# Minimal dotted sets for multi-norm marked cones

This module formalizes the finite combinatorial core of Lemma 3.4 in
A. Hejna, A. Nagel, and F. Ricci, *Littlewood-Paley square functions and the
local Hardy space for Multi-Norm Structures on R^d* (arXiv:2507.09399).

At a nonzero nonnegative logarithmic point `t`, consider the marked partitions
whose cones contain `t`. Among any nonempty such family there is a partition
with the least number of marks. Its distinct marked coordinates satisfy the
paper's strict separation inequality, and every one of its marks occurs in
every other marked partition whose cone contains `t`.

The proof implements the paper's block-merging argument. Merging the block
marked by `q` into the block marked by `p` removes exactly one mark, and cone
membership is preserved when `t q ≤ t p / e(p,q)`.

The module deliberately records existence of a containing marked cone as a
hypothesis. It does not yet prove global cone coverage, define the regions
`Γ(D)`, select maximal dyadic cubes, or construct the tubes `T_L`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormMarkedPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! # A. Finite sets of marks -/

/-- The finite set of active marks of a marked partition. -/
def marksFinset (S : MultiNormMarkedPartition ι) : Finset ι :=
  Finset.univ.filter fun k => S.mark k = k

@[simp] lemma mem_marksFinset_iff (S : MultiNormMarkedPartition ι) (k : ι) :
    k ∈ S.marksFinset ↔ k ∈ S.marks := by
  simp [marksFinset, S.mem_marks_iff_fixed]

/-- The number of dotted entries of a marked partition. -/
def markCount (S : MultiNormMarkedPartition ι) : ℕ :=
  S.marksFinset.card

/-! # B. Merging two marked blocks -/

/-- Merge the block marked by `q` into the block marked by the distinct mark
`p`, retaining `p` as the mark of the combined block. -/
def mergeBlocks (S : MultiNormMarkedPartition ι)
    (p q : S.MarkedIndex) (hpq : p.1 ≠ q.1) :
    MultiNormMarkedPartition ι where
  mark i := if S.mark i = q.1 then p.1 else S.mark i
  mark_idempotent i := by
    by_cases hi : S.mark i = q.1
    · simp [hi, MarkedIndex.mark_fixed S p, hpq]
    · have hfixed := S.mark_idempotent i
      simp [hi, hfixed]

omit [Fintype ι] in
@[simp] lemma mergeBlocks_mark (S : MultiNormMarkedPartition ι)
    (p q : S.MarkedIndex) (hpq : p.1 ≠ q.1) (i : ι) :
    (S.mergeBlocks p q hpq).mark i =
      if S.mark i = q.1 then p.1 else S.mark i := rfl

/-- Merging `q` into `p` removes exactly the mark `q`. -/
lemma marksFinset_mergeBlocks (S : MultiNormMarkedPartition ι)
    (p q : S.MarkedIndex) (hpq : p.1 ≠ q.1) :
    (S.mergeBlocks p q hpq).marksFinset = S.marksFinset.erase q.1 := by
  ext k
  simp only [mem_marksFinset_iff, mem_marks_iff_fixed, mergeBlocks_mark,
    Finset.mem_erase]
  constructor
  · intro hk
    by_cases hqk : S.mark k = q.1
    · rw [if_pos hqk] at hk
      subst k
      exact ⟨hpq, MarkedIndex.mark_fixed S p⟩
    · rw [if_neg hqk] at hk
      exact ⟨fun hkq => hqk (hk.trans hkq), hk⟩
  · rintro ⟨hkq, hk⟩
    rw [if_neg]
    · exact hk
    · intro hmark
      exact hkq (hk.symm.trans hmark)

/-- A block merge strictly lowers the number of active marks. -/
lemma markCount_mergeBlocks_lt (S : MultiNormMarkedPartition ι)
    (p q : S.MarkedIndex) (hpq : p.1 ≠ q.1) :
    (S.mergeBlocks p q hpq).markCount < S.markCount := by
  rw [markCount, markCount, S.marksFinset_mergeBlocks p q hpq,
    Finset.card_erase_of_mem ((S.mem_marksFinset_iff q.1).2 q.2)]
  have hpos : 0 < S.marksFinset.card :=
    Finset.card_pos.mpr ⟨q.1, (S.mem_marksFinset_iff q.1).2 q.2⟩
  omega

omit [Fintype ι] in
/-- If the coordinate marked by `p` is large enough relative to that marked
by `q`, merging the `q`-block into the `p`-block preserves cone membership. -/
lemma mem_cone_mergeBlocks {S : MultiNormMarkedPartition ι}
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (ht : t ∈ S.cone E) (p q : S.MarkedIndex)
    (hpq : p.1 ≠ q.1) (hscale : t q.1 ≤ t p.1 / E p.1 q.1) :
    t ∈ (S.mergeBlocks p q hpq).cone E := by
  refine ⟨ht.1, ?_⟩
  intro i
  by_cases hi : S.mark i = q.1
  · rw [mergeBlocks_mark, if_pos hi]
    intro j
    have hdom : t j / E j i ≤ t q.1 / E q.1 i := by
      simpa [hi] using ht.2 i j
    calc
      t j / E j i ≤ t q.1 / E q.1 i := hdom
      _ ≤ (t p.1 / E p.1 q.1) / E q.1 i := by
        apply (div_le_div_iff₀ (E.entry_pos q.1 i) (E.entry_pos q.1 i)).2
        simpa using mul_le_mul_of_nonneg_right hscale (E.entry_pos q.1 i).le
      _ = t p.1 / (E p.1 q.1 * E q.1 i) := by rw [div_div]
      _ ≤ t p.1 / E p.1 i := by
        apply (div_le_div_iff₀
          (mul_pos (E.entry_pos p.1 q.1) (E.entry_pos q.1 i))
          (E.entry_pos p.1 i)).2
        exact mul_le_mul_of_nonneg_left
          (E.multiplicative_triangle p.1 q.1 i) (ht.1 p.1)
  · rw [mergeBlocks_mark, if_neg hi]
    exact ht.2 i

/-! # C. Minimum-mark containing cones -/

/-- A point admits a marked cone when at least one marked partition has a cone
containing it. This assumption is separated from the finite minimization. -/
def AdmitsMarkedCone (E : StandardMultiNormMatrix ι) (t : ι → ℝ) : Prop :=
  ∃ S : MultiNormMarkedPartition ι, t ∈ S.cone E

/-- The proposition that `n` is realized as the mark count of a containing
marked cone. -/
def IsContainingMarkCount (E : StandardMultiNormMatrix ι)
    (t : ι → ℝ) (n : ℕ) : Prop :=
  ∃ S : MultiNormMarkedPartition ι, t ∈ S.cone E ∧ S.markCount = n

/-- The minimum number of marks among marked cones containing `t`. -/
def minimalMarkCount (E : StandardMultiNormMatrix ι) (t : ι → ℝ)
    (h : AdmitsMarkedCone E t) : ℕ :=
  by
    classical
    exact Nat.find (show ∃ n, IsContainingMarkCount E t n by
      obtain ⟨S, hS⟩ := h
      exact ⟨S.markCount, S, hS, rfl⟩)

/-- A chosen containing marked partition with the minimum number of marks. -/
def minimalMarkedPartition (E : StandardMultiNormMatrix ι) (t : ι → ℝ)
    (h : AdmitsMarkedCone E t) : MultiNormMarkedPartition ι :=
  by
    classical
    exact Classical.choose (Nat.find_spec
      (show ∃ n, IsContainingMarkCount E t n by
        obtain ⟨S, hS⟩ := h
        exact ⟨S.markCount, S, hS, rfl⟩))

/-- The chosen minimum-mark partition contains `t` and realizes the minimum
mark count. -/
lemma minimalMarkedPartition_spec (E : StandardMultiNormMatrix ι)
    (t : ι → ℝ) (h : AdmitsMarkedCone E t) :
    t ∈ (minimalMarkedPartition E t h).cone E ∧
      (minimalMarkedPartition E t h).markCount = minimalMarkCount E t h := by
  classical
  simp only [minimalMarkedPartition, minimalMarkCount]
  exact Classical.choose_spec (Nat.find_spec
    (show ∃ n, IsContainingMarkCount E t n by
      obtain ⟨S, hS⟩ := h
      exact ⟨S.markCount, S, hS, rfl⟩))

/-- The chosen mark count is no larger than that of any containing marked
partition. -/
lemma minimalMarkCount_le (E : StandardMultiNormMatrix ι)
    (t : ι → ℝ) (h : AdmitsMarkedCone E t)
    (S : MultiNormMarkedPartition ι) (hS : t ∈ S.cone E) :
    minimalMarkCount E t h ≤ S.markCount := by
  classical
  unfold minimalMarkCount
  apply Nat.find_min'
  exact ⟨S, hS, rfl⟩

/-! # D. The minimal dotted-set properties -/

/-- Every active mark is positive at a nonzero point of its marked cone. -/
lemma mark_pos_of_mem_cone {S : MultiNormMarkedPartition ι}
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (ht : t ∈ S.cone E) (hne : t ≠ 0) (p : S.MarkedIndex) :
    0 < t p.1 := by
  have hex : ∃ j, t j ≠ 0 := by
    by_contra h
    apply hne
    funext j
    exact not_ne_iff.mp ((not_exists.mp h) j)
  obtain ⟨j, hj⟩ := hex
  have hjpos : 0 < t j := lt_of_le_of_ne (ht.1 j) (Ne.symm hj)
  have hdom := ht.2 p.1 j
  rw [MarkedIndex.mark_fixed S p, E.diagonal] at hdom
  exact (div_pos hjpos (E.entry_pos j p.1)).trans_le (by simpa using hdom)

/-- Distinct marks of a minimum-mark containing cone satisfy the strict
separation inequality from Lemma 3.4(a). -/
lemma minimal_marks_strictlySeparated
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    {S : MultiNormMarkedPartition ι}
    (hS : t ∈ S.cone E)
    (hminimal : ∀ T : MultiNormMarkedPartition ι,
      t ∈ T.cone E → S.markCount ≤ T.markCount)
    (p q : S.MarkedIndex) (hpq : p.1 ≠ q.1) :
    t p.1 < E p.1 q.1 * t q.1 := by
  by_contra h
  have hscale : t q.1 ≤ t p.1 / E p.1 q.1 := by
    rw [le_div_iff₀ (E.entry_pos p.1 q.1)]
    simpa [mul_comm] using le_of_not_gt h
  have hmerged := S.mem_cone_mergeBlocks hS p q hpq hscale
  have hle := hminimal (S.mergeBlocks p q hpq) hmerged
  exact (not_lt_of_ge hle) (S.markCount_mergeBlocks_lt p q hpq)

/-- Every mark of a minimum-mark cone at a nonzero point occurs in every
other marked partition whose cone contains that point. This is Lemma 3.4(b). -/
lemma minimal_marks_subset_of_mem_cone
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    {S : MultiNormMarkedPartition ι}
    (hS : t ∈ S.cone E) (hne : t ≠ 0)
    (hminimal : ∀ U : MultiNormMarkedPartition ι,
      t ∈ U.cone E → S.markCount ≤ U.markCount)
    (T : MultiNormMarkedPartition ι) (hT : t ∈ T.cone E) :
    S.marks ⊆ T.marks := by
  intro k hkS
  by_contra hkT
  let kS : S.MarkedIndex := ⟨k, hkS⟩
  let m : T.MarkedIndex := ⟨T.mark k, ⟨k, rfl⟩⟩
  let p : S.MarkedIndex := ⟨S.mark m.1, ⟨m.1, rfl⟩⟩
  have hmk : m.1 ≠ k := by
    intro h
    apply hkT
    exact (T.mem_marks_iff_fixed k).2 h
  by_cases hpk : p.1 = k
  · have hTkm : t k ≤ t m.1 / E m.1 k := by
      have hwithin := T.cone_withinBlock_le hT k
      change t k ≤ t m.1 / E m.1 k at hwithin
      exact hwithin
    have hSkm : t m.1 ≤ t k / E k m.1 := by
      have hwithin := S.cone_withinBlock_le hS m.1
      change t m.1 ≤ t p.1 / E p.1 m.1 at hwithin
      simpa [hpk] using hwithin
    have h₁ : t k * E m.1 k ≤ t m.1 :=
      (le_div_iff₀ (E.entry_pos m.1 k)).mp hTkm
    have h₂ : t m.1 * E k m.1 ≤ t k :=
      (le_div_iff₀ (E.entry_pos k m.1)).mp hSkm
    have hcycle : t m.1 * (E k m.1 * E m.1 k) ≤ t m.1 := by
      calc
        t m.1 * (E k m.1 * E m.1 k) =
            (t m.1 * E k m.1) * E m.1 k := by ring
        _ ≤ t k * E m.1 k :=
          mul_le_mul_of_nonneg_right h₂ (E.entry_pos m.1 k).le
        _ ≤ t m.1 := h₁
    have hmpos : 0 < t m.1 := T.mark_pos_of_mem_cone hT hne m
    have hprod := E.strict_nondegenerate hmk.symm
    nlinarith
  · have hTkm : t k ≤ t m.1 / E m.1 k := by
      have hwithin := T.cone_withinBlock_le hT k
      change t k ≤ t m.1 / E m.1 k at hwithin
      exact hwithin
    have hSmp : t m.1 ≤ t p.1 / E p.1 m.1 := by
      have hwithin := S.cone_withinBlock_le hS m.1
      change t m.1 ≤ t p.1 / E p.1 m.1 at hwithin
      exact hwithin
    have hscale : t k ≤ t p.1 / E p.1 k := by
      calc
        t k ≤ t m.1 / E m.1 k := hTkm
        _ ≤ (t p.1 / E p.1 m.1) / E m.1 k := by
          apply (div_le_div_iff₀
            (E.entry_pos m.1 k) (E.entry_pos m.1 k)).2
          simpa using mul_le_mul_of_nonneg_right hSmp (E.entry_pos m.1 k).le
        _ = t p.1 / (E p.1 m.1 * E m.1 k) := by rw [div_div]
        _ ≤ t p.1 / E p.1 k := by
          apply (div_le_div_iff₀
            (mul_pos (E.entry_pos p.1 m.1) (E.entry_pos m.1 k))
            (E.entry_pos p.1 k)).2
          exact mul_le_mul_of_nonneg_left
            (E.multiplicative_triangle p.1 m.1 k) (hS.1 p.1)
    have hmerged := S.mem_cone_mergeBlocks hS p kS hpk hscale
    have hle := hminimal (S.mergeBlocks p kS hpk) hmerged
    exact (not_lt_of_ge hle) (S.markCount_mergeBlocks_lt p kS hpk)

/-- Any two minimum-mark containing cones at the same nonzero point have the
same dotted set, even when the marked partitions themselves are different. -/
lemma minimum_mark_sets_unique
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    {S T : MultiNormMarkedPartition ι}
    (hS : t ∈ S.cone E) (hT : t ∈ T.cone E) (hne : t ≠ 0)
    (hminimalS : ∀ U : MultiNormMarkedPartition ι,
      t ∈ U.cone E → S.markCount ≤ U.markCount)
    (hminimalT : ∀ U : MultiNormMarkedPartition ι,
      t ∈ U.cone E → T.markCount ≤ U.markCount) :
    S.marks = T.marks := by
  apply Set.Subset.antisymm
  · exact minimal_marks_subset_of_mem_cone hS hne hminimalS T hT
  · exact minimal_marks_subset_of_mem_cone hT hne hminimalT S hS

/-- The canonical minimal dotted set `D(t)`, obtained from a chosen
minimum-mark containing cone. Its characterization below makes it independent
of the particular minimum-mark partition. -/
def minimalDottedSet (E : StandardMultiNormMatrix ι) (t : ι → ℝ)
    (h : AdmitsMarkedCone E t) : Set ι :=
  (minimalMarkedPartition E t h).marks

/-- Capstone for Lemma 3.4: the chosen minimum-mark containing cone has
strictly separated marks, and its dotted set is contained in that of every
other containing marked cone. -/
lemma minimalMarkedPartition_dottedSet_characterization
    (E : StandardMultiNormMatrix ι) (t : ι → ℝ)
    (hne : t ≠ 0) (h : AdmitsMarkedCone E t) :
    let S := minimalMarkedPartition E t h
    t ∈ S.cone E ∧
      (∀ p q : S.MarkedIndex, p.1 ≠ q.1 →
        t p.1 < E p.1 q.1 * t q.1) ∧
      ∀ T : MultiNormMarkedPartition ι,
        t ∈ T.cone E → minimalDottedSet E t h ⊆ T.marks := by
  let S := minimalMarkedPartition E t h
  have hspec := minimalMarkedPartition_spec E t h
  have hminimal : ∀ T : MultiNormMarkedPartition ι,
      t ∈ T.cone E → S.markCount ≤ T.markCount := by
    intro T hT
    rw [hspec.2]
    exact minimalMarkCount_le E t h T hT
  exact ⟨hspec.1,
    fun p q hpq => minimal_marks_strictlySeparated hspec.1 hminimal p q hpq,
    fun T hT => by
      change S.marks ⊆ T.marks
      exact minimal_marks_subset_of_mem_cone
        hspec.1 hne hminimal T hT⟩

end MultiNormMarkedPartition

end Physlib.Mathematics.HarmonicAnalysis
