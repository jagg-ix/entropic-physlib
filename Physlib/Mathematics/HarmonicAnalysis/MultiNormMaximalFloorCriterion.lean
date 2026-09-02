/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadicTube

/-!
# The maximal-floor criterion for multi-norm dyadic scales

This module proves the robust form of the lattice criterion underlying
Section 3.4 of Hejna--Nagel--Ricci.  At a point on a wall, several marked
cones with the same dotted set may contain the point.  Maximality is therefore
equivalent to the floor equation in every such containing cone.

The universally quantified formulation is important.  The additional strict
pairwise `τ_S` inequality printed in Lemma 3.7xyz is not used: under the stated
standard-matrix assumptions it is stronger than maximality on tie walls.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormDyadic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open MultiNormMarkedPartition

/-! ## 1. Floor profiles -/

/-- The largest natural scale allowed in coordinate `i` by the mark of its
block in `S`. -/
def floorCoordinate (E : StandardMultiNormMatrix ι)
    (S : MultiNormMarkedPartition ι) (L : ι → ℕ) (i : ι) : ℕ :=
  ⌊(L (S.mark i) : ℝ) / E (S.mark i) i⌋₊

/-- The floor equations associated with one containing marked cone. -/
def SatisfiesFloorProfile (E : StandardMultiNormMatrix ι)
    (S : MultiNormMarkedPartition ι) (L : ι → ℕ) : Prop :=
  ∀ i, L i = floorCoordinate E S L i

/-- The wall-robust floor criterion: every marked cone with mark set `D`
that contains `L` gives the same floor profile. -/
def HasMaximalFloorProfile (E : StandardMultiNormMatrix ι) (D : Set ι)
    (L : ι → ℕ) : Prop :=
  ∀ S : MultiNormMarkedPartition ι,
    S.marks = D → toLogPoint L ∈ S.cone E → SatisfiesFloorProfile E S L

omit [Fintype ι] [Nonempty ι] in
/-- A marked coordinate automatically satisfies its floor equation. -/
lemma floorCoordinate_eq_of_mem_marks
    (E : StandardMultiNormMatrix ι) (S : MultiNormMarkedPartition ι)
    (L : ι → ℕ) {i : ι} (hi : i ∈ S.marks) :
    floorCoordinate E S L i = L i := by
  rw [floorCoordinate, (S.mem_marks_iff_fixed i).mp hi, E.diagonal]
  simp

/-! ## 2. One-coordinate cone geometry -/

/-- Increasing an undotted coordinate stays in a marked cone exactly when
the increment still lies below its block-mark bound. -/
lemma increment_mem_cone_iff
    (E : StandardMultiNormMatrix ι) (S : MultiNormMarkedPartition ι)
    (L : ι → ℕ) {j : ι} (hj : j ∉ S.marks)
    (hL : toLogPoint L ∈ S.cone E) :
    toLogPoint (increment L j) ∈ S.cone E ↔
      ((L j + 1 : ℕ) : ℝ) ≤
        (L (S.mark j) : ℝ) / E (S.mark j) j := by
  rw [S.mem_cone_iff_explicitCone E] at hL ⊢
  have hmark_ne : S.mark j ≠ j := by
    intro hfixed
    exact hj ((S.mem_marks_iff_fixed j).2 hfixed)
  constructor
  · intro h
    simpa [toLogPoint, increment_apply_of_ne L hmark_ne] using h.2.1 j
  · intro hbound
    refine ⟨fun i => by simp [toLogPoint], ?_, ?_⟩
    · intro i
      by_cases hij : i = j
      · subst i
        simpa [toLogPoint, increment_apply_of_ne L hmark_ne] using hbound
      · have hmark_ne : S.mark i ≠ j := by
          intro hmark
          apply hj
          exact ⟨i, hmark⟩
        simpa [toLogPoint, increment_apply_of_ne L hij,
          increment_apply_of_ne L hmark_ne] using hL.2.1 i
    · intro p q
      have hpj : p.1 ≠ j := fun hpj => hj (hpj ▸ p.2)
      have hqj : q.1 ≠ j := fun hqj => hj (hqj ▸ q.2)
      simpa [toLogPoint, increment_apply_of_ne L hpj,
        increment_apply_of_ne L hqj] using hL.2.2 p q

/-- Lowering one undotted coordinate from `L+e_j` back to `L` preserves
membership in the same marked cone. -/
lemma mem_cone_of_increment_mem_cone
    (E : StandardMultiNormMatrix ι) (S : MultiNormMarkedPartition ι)
    (L : ι → ℕ) {j : ι} (hj : j ∉ S.marks)
    (hinc : toLogPoint (increment L j) ∈ S.cone E) :
    toLogPoint L ∈ S.cone E := by
  rw [S.mem_cone_iff_explicitCone E] at hinc ⊢
  refine ⟨fun i => by simp [toLogPoint], ?_, ?_⟩
  · intro i
    by_cases hij : i = j
    · subst i
      have h := hinc.2.1 j
      have hmark_ne : S.mark j ≠ j := by
        intro hfixed
        exact hj ((S.mem_marks_iff_fixed j).2 hfixed)
      have hle : (L j : ℝ) ≤ (L j + 1 : ℕ) := by
        exact_mod_cast Nat.le_succ (L j)
      exact hle.trans (by
        simpa [toLogPoint, increment_apply_of_ne L hmark_ne] using h)
    · have hmark_ne : S.mark i ≠ j := by
        intro hmark
        apply hj
        exact ⟨i, hmark⟩
      simpa [toLogPoint, increment_apply_of_ne L hij,
        increment_apply_of_ne L hmark_ne] using hinc.2.1 i
  · intro p q
    have hpj : p.1 ≠ j := fun hpj => hj (hpj ▸ p.2)
    have hqj : q.1 ≠ j := fun hqj => hj (hqj ▸ q.2)
    simpa [toLogPoint, increment_apply_of_ne L hpj,
      increment_apply_of_ne L hqj] using hinc.2.2 p q

omit [Fintype ι] [Nonempty ι] in
/-- The strict dotted locus is unchanged by incrementing an undotted
coordinate. -/
lemma increment_mem_strictDottedLocus_iff
    (E : StandardMultiNormMatrix ι) (D : Set ι) (L : ι → ℕ)
    {j : ι} (hj : j ∉ D) :
    toLogPoint (increment L j) ∈ strictDottedLocus E D ↔
      toLogPoint L ∈ strictDottedLocus E D := by
  have unchanged {k : ι} (hk : k ∈ D) : increment L j k = L k := by
    apply increment_apply_of_ne
    intro hkj
    subst k
    exact hj hk
  constructor <;> intro h k hk
  · refine ⟨by simpa [toLogPoint, unchanged hk] using (h k hk).1, ?_⟩
    intro q hq hqk
    simpa [toLogPoint, unchanged hk, unchanged hq] using (h k hk).2 q hq hqk
  · refine ⟨by simpa [toLogPoint, unchanged hk] using (h k hk).1, ?_⟩
    intro q hq hqk
    simpa [toLogPoint, unchanged hk, unchanged hq] using (h k hk).2 q hq hqk

/-! ## 3. Corrected Lemma 3.7xyz -/

/-- Maximality implies the robust floor profile. -/
lemma hasMaximalFloorProfile_of_isMaximalDottedScale
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hmax : IsMaximalDottedScale E D L) :
    HasMaximalFloorProfile E D L := by
  intro S hmarks hS i
  by_cases hi : i ∈ D
  · exact (floorCoordinate_eq_of_mem_marks E S L (hmarks.symm ▸ hi)).symm
  · have hbound := S.cone_withinBlock_le hS i
    have hnot : ¬ ((L i + 1 : ℕ) : ℝ) ≤
        (L (S.mark i) : ℝ) / E (S.mark i) i := by
      intro hincBound
      have hincS : toLogPoint (increment L i) ∈ S.cone E :=
        (increment_mem_cone_iff E S L (hmarks ▸ hi) hS).2 hincBound
      have hstrict : toLogPoint L ∈ strictDottedLocus E D :=
        (mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD _).1
          hmax.1 |>.2
      have hincD : toLogPoint (increment L i) ∈ dottedRegion E D :=
        (mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD _).2
          ⟨⟨S, hmarks, hincS⟩,
            (increment_mem_strictDottedLocus_iff E D L hi).2 hstrict⟩
      exact hmax.2 i hi hincD
    have hx : 0 ≤ (L (S.mark i) : ℝ) / E (S.mark i) i :=
      div_nonneg (by positivity) (E.entry_pos _ _).le
    have hlt : (L (S.mark i) : ℝ) / E (S.mark i) i < (L i : ℝ) + 1 := by
      simpa using (lt_of_not_ge hnot)
    exact ((Nat.floor_eq_iff hx).2
      ⟨by simpa [toLogPoint] using hbound, hlt⟩).symm

/-- The wall-robust floor profile implies maximality. -/
lemma isMaximalDottedScale_of_hasMaximalFloorProfile
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hDmem : toLogPoint L ∈ dottedRegion E D)
    (hfloor : HasMaximalFloorProfile E D L) :
    IsMaximalDottedScale E D L := by
  refine ⟨hDmem, ?_⟩
  intro j hj hincD
  obtain ⟨⟨S, hmarks, hincS⟩, -⟩ :=
    (mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD _).1 hincD
  have hS : toLogPoint L ∈ S.cone E :=
    mem_cone_of_increment_mem_cone E S L (hmarks ▸ hj) hincS
  have hprofile := hfloor S hmarks hS j
  have hincBound := (increment_mem_cone_iff E S L (hmarks ▸ hj) hS).1 hincS
  have hlt : (L (S.mark j) : ℝ) / E (S.mark j) j < (L j + 1 : ℕ) := by
    have h := Nat.lt_floor_add_one
      ((L (S.mark j) : ℝ) / E (S.mark j) j)
    change (L (S.mark j) : ℝ) / E (S.mark j) j <
      (floorCoordinate E S L j : ℝ) + 1 at h
    rw [← hprofile] at h
    simpa using h
  exact (not_lt_of_ge hincBound) (by simpa using hlt)

/-- Correct wall-robust form of Lemma 3.7xyz: a lattice point already in
`Γ(D)` is maximal exactly when every containing marked cone with marks `D`
gives its floor profile. -/
lemma isMaximalDottedScale_iff_maximalFloorProfile
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hDmem : toLogPoint L ∈ dottedRegion E D) :
    IsMaximalDottedScale E D L ↔ HasMaximalFloorProfile E D L := by
  exact ⟨hasMaximalFloorProfile_of_isMaximalDottedScale E hD,
    isMaximalDottedScale_of_hasMaximalFloorProfile E hD hDmem⟩

end MultiNormDyadic

end Physlib.Mathematics.HarmonicAnalysis
