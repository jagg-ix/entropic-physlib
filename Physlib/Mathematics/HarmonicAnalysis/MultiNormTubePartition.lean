/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormUniqueMaximalApex

/-!
# Continuous multi-norm tube decomposition

This module completes the nonempty-region part of Lemma 3.7. It identifies
each logarithmic tube with an explicit finite product of closed intervals,
proves regionwise tube coverage, and proves that distinct maximal tubes have
disjoint genuine topological interiors.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormDyadic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open MultiNormMarkedPartition

/-! ## 1. Explicit closed boxes -/

/-- The coordinate interval of a logarithmic tube: dotted coordinates have
unit width at the apex, while undotted coordinates extend down to zero. -/
def logTubeInterval (D : Set ι) (L : ι → ℕ) (i : ι) : Set ℝ :=
  by
    classical
    exact if i ∈ D then
      Set.Icc (max 0 ((L i : ℝ) - 1 / 2)) ((L i : ℝ) + 1 / 2)
    else
      Set.Icc 0 ((L i : ℝ) + 1 / 2)

/-- The explicit finite-product box underlying `logTube D L`. -/
def logTubeBox (D : Set ι) (L : ι → ℕ) : Set (ι → ℝ) :=
  Set.univ.pi (logTubeInterval D L)

omit [Fintype ι] [Nonempty ι] in
/-- A point of a tube cell satisfies the corresponding tube-box bounds. -/
lemma mem_logTubeBox_of_mem_logCell
    {D : Set ι} {L M : ι → ℕ} (hM : M ∈ tubeIndexSet D L)
    {t : ι → ℝ} (ht : t ∈ logCell M) :
    t ∈ logTubeBox D L := by
  rw [logTubeBox, Set.mem_pi]
  intro i _
  have hti := ht i
  by_cases hi : i ∈ D
  · rw [logTubeInterval, if_pos hi, Set.mem_Icc]
    rw [hM.1 i hi] at hti
    exact ⟨max_le hti.1 hti.2.1, hti.2.2⟩
  · rw [logTubeInterval, if_neg hi, Set.mem_Icc]
    exact ⟨hti.1,
      hti.2.2.trans (by gcongr; exact_mod_cast hM.2 i hi)⟩

/-- Choose a tube index whose unit cell contains a given point of the
explicit tube box. -/
def boxCellIndex (D : Set ι) (L : ι → ℕ) (t : ι → ℝ) : ι → ℕ :=
  fun i => by
    classical
    exact if i ∈ D then L i else min (L i) ⌊t i + 1 / 2⌋₊

omit [Fintype ι] [Nonempty ι] in
/-- The selected box cell belongs to the discrete tube. -/
lemma boxCellIndex_mem_tubeIndexSet
    {D : Set ι} {L : ι → ℕ} (t : ι → ℝ) :
    boxCellIndex D L t ∈ tubeIndexSet D L := by
  refine ⟨?_, ?_⟩
  · intro i hi
    simp [boxCellIndex, hi]
  · intro i hi
    simp [boxCellIndex, hi]

omit [Fintype ι] [Nonempty ι] in
/-- The selected cell contains the original point of the tube box. -/
lemma mem_logCell_boxCellIndex
    {D : Set ι} {L : ι → ℕ} {t : ι → ℝ}
    (ht : t ∈ logTubeBox D L) :
    t ∈ logCell (boxCellIndex D L t) := by
  rw [logTubeBox, Set.mem_pi] at ht
  intro i
  have hti := ht i (Set.mem_univ i)
  by_cases hi : i ∈ D
  · rw [logTubeInterval, if_pos hi, Set.mem_Icc] at hti
    simp only [boxCellIndex, if_pos hi]
    exact ⟨hti.1.trans' (le_max_left 0 _),
      (le_max_right 0 _).trans hti.1, hti.2⟩
  · rw [logTubeInterval, if_neg hi, Set.mem_Icc] at hti
    have hx : 0 ≤ t i + 1 / 2 := by linarith
    let n := ⌊t i + 1 / 2⌋₊
    have hnle : (n : ℝ) ≤ t i + 1 / 2 := Nat.floor_le hx
    have htnext : t i + 1 / 2 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    simp only [boxCellIndex, if_neg hi]
    refine ⟨hti.1, ?_, ?_⟩
    · by_cases hnL : n ≤ L i
      · rw [min_eq_right hnL]
        linarith
      · rw [min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hnL))]
        have hLn : L i + 1 ≤ n := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hnL)
        have hLnR : ((L i + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hLn
        norm_num at hLnR ⊢
        linarith
    · by_cases hnL : n ≤ L i
      · rw [min_eq_right hnL]
        norm_num at htnext ⊢
        linarith
      · rw [min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hnL))]
        exact hti.2

/-- The union-of-cells tube is exactly its explicit closed product box. -/
lemma logTube_eq_logTubeBox (D : Set ι) (L : ι → ℕ) :
    logTube D L = logTubeBox D L := by
  ext t
  constructor
  · intro ht
    obtain ⟨M, hM, htM⟩ := Set.mem_iUnion₂.mp ht
    exact mem_logTubeBox_of_mem_logCell hM htM
  · intro ht
    exact logCell_subset_logTube (boxCellIndex_mem_tubeIndexSet t)
      (mem_logCell_boxCellIndex ht)

/-! ## 2. Genuine interiors and their lattice witnesses -/

/-- The actual topological interior of a logarithmic tube is the product of
the open interiors of its coordinate intervals. -/
lemma interior_logTube (D : Set ι) (L : ι → ℕ) :
    interior (logTube D L) =
      Set.univ.pi (fun i => interior (logTubeInterval D L i)) := by
  rw [logTube_eq_logTubeBox, logTubeBox, interior_pi_set Set.finite_univ]

/-- Round a logarithmic point to the natural lattice cell containing it. -/
def nearestCellIndex (t : ι → ℝ) : ι → ℕ :=
  fun i => ⌊t i + 1 / 2⌋₊

/-- A point in the genuine interior of a tube determines a lattice index in
that tube. -/
lemma nearestCellIndex_mem_tube_of_mem_interior
    {D : Set ι} {L : ι → ℕ} {t : ι → ℝ}
    (ht : t ∈ interior (logTube D L)) :
    nearestCellIndex t ∈ tubeIndexSet D L := by
  rw [interior_logTube, Set.mem_pi] at ht
  refine ⟨?_, ?_⟩
  · intro i hi
    have hti := ht i (Set.mem_univ i)
    rw [logTubeInterval, if_pos hi, interior_Icc, Set.mem_Ioo] at hti
    have hzero : 0 < t i := (le_max_left 0 _).trans_lt hti.1
    have hx : 0 ≤ t i + 1 / 2 := by linarith
    apply Nat.le_antisymm
    · have hlt : t i + 1 / 2 < ((L i + 1 : ℕ) : ℝ) := by
        norm_num
        linarith [hti.2]
      exact Nat.lt_succ_iff.mp ((Nat.floor_lt hx).2 hlt)
    · apply Nat.le_floor
      have : (L i : ℝ) ≤ t i + 1 / 2 := by
        have := (le_max_right 0 ((L i : ℝ) - 1 / 2)).trans_lt hti.1
        linarith
      exact this
  · intro i hi
    have hti := ht i (Set.mem_univ i)
    rw [logTubeInterval, if_neg hi, interior_Icc, Set.mem_Ioo] at hti
    have hx : 0 ≤ t i + 1 / 2 := by linarith
    have hlt : t i + 1 / 2 < ((L i + 1 : ℕ) : ℝ) := by
      norm_num
      linarith [hti.2]
    exact Nat.lt_succ_iff.mp ((Nat.floor_lt hx).2 hlt)

/-! ## 3. Regionwise coverage and disjoint interiors -/

/-- Every lattice index below a maximal apex belongs to the same canonical
dotted region. -/
lemma mem_dottedRegion_of_mem_maximalTube
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L M : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (hM : M ∈ tubeIndexSet D L) :
    toLogPoint M ∈ dottedRegion E D := by
  obtain ⟨⟨S, hmarks, hLS⟩, hstrict⟩ :=
    (mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD _).1 hmax.1
  have hMS := mem_cone_of_mem_tubeIndexSet E S hmarks hLS hM
  apply (mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD _).2
  refine ⟨⟨S, hmarks, hMS⟩, ?_⟩
  exact (strictDottedLocus_congr E D (fun i hi => by
    simp [toLogPoint, hM.1 i hi])).1 hstrict

/-- In a fixed nonempty region, distinct maximal apices have disjoint
discrete tubes. -/
lemma tubeIndexSet_disjoint_of_distinct_maximal
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L₁ L₂ : ι → ℕ} (h₁ : IsMaximalDottedScale E D L₁)
    (h₂ : IsMaximalDottedScale E D L₂) (hne : L₁ ≠ L₂) :
    Disjoint (tubeIndexSet D L₁) (tubeIndexSet D L₂) := by
  rw [Set.disjoint_left]
  intro M hM₁ hM₂
  have hMD := mem_dottedRegion_of_mem_maximalTube E hD h₁ hM₁
  obtain ⟨A, -, hunique⟩ := existsUnique_maximalApex E hD hMD
  exact hne ((hunique L₁ ⟨h₁, hM₁⟩).trans
    (hunique L₂ ⟨h₂, hM₂⟩).symm)

/-- Maximal tubes from any two nonempty canonical regions have disjoint
genuine topological interiors unless both their region and apex agree. -/
lemma interiors_disjoint_of_distinct_maximal
    (E : StandardMultiNormMatrix ι)
    {D₁ D₂ : Set ι} (hD₁ : D₁.Nonempty) (hD₂ : D₂.Nonempty)
    {L₁ L₂ : ι → ℕ} (h₁ : IsMaximalDottedScale E D₁ L₁)
    (h₂ : IsMaximalDottedScale E D₂ L₂)
    (hne : D₁ ≠ D₂ ∨ L₁ ≠ L₂) :
    Disjoint (interior (logTube D₁ L₁)) (interior (logTube D₂ L₂)) := by
  rw [Set.disjoint_left]
  intro t ht₁ ht₂
  let M := nearestCellIndex t
  have hM₁ : M ∈ tubeIndexSet D₁ L₁ :=
    nearestCellIndex_mem_tube_of_mem_interior ht₁
  have hM₂ : M ∈ tubeIndexSet D₂ L₂ :=
    nearestCellIndex_mem_tube_of_mem_interior ht₂
  have hMD₁ := mem_dottedRegion_of_mem_maximalTube E hD₁ h₁ hM₁
  have hMD₂ := mem_dottedRegion_of_mem_maximalTube E hD₂ h₂ hM₂
  have hD : D₁ = D₂ := dottedRegion_index_unique E (toLogPoint M) hMD₁ hMD₂
  subst D₂
  have hL : L₁ = L₂ := by
    obtain ⟨A, -, hunique⟩ := existsUnique_maximalApex E hD₁ hMD₁
    exact (hunique L₁ ⟨h₁, hM₁⟩).trans
      (hunique L₂ ⟨h₂, hM₂⟩).symm
  rcases hne with hDne | hLne
  · exact hDne rfl
  · exact hLne hL

/-- The union of maximal tubes in a nonempty region is exactly the union of
all unit cells whose centers belong to that region. -/
lemma dottedRegion_cellUnion_eq_maximalTubeUnion
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty) :
    (⋃ M : ι → ℕ, ⋃ (_ : toLogPoint M ∈ dottedRegion E D), logCell M) =
      ⋃ L : ι → ℕ, ⋃ (_ : IsMaximalDottedScale E D L), logTube D L := by
  ext t
  constructor
  · intro ht
    obtain ⟨M, hMD, htM⟩ := Set.mem_iUnion₂.mp ht
    obtain ⟨L, hL, -⟩ := existsUnique_maximalApex E hD hMD
    exact Set.mem_iUnion₂.mpr ⟨L, hL.1, logCell_subset_logTube hL.2 htM⟩
  · intro ht
    obtain ⟨L, hmax, htL⟩ := Set.mem_iUnion₂.mp ht
    obtain ⟨M, hM, htM⟩ := Set.mem_iUnion₂.mp htL
    exact Set.mem_iUnion₂.mpr
      ⟨M, mem_dottedRegion_of_mem_maximalTube E hD hmax hM, htM⟩

/-- Capstone for Lemma 3.7 on nonempty regions: lattice cells have unique
maximal apices, maximal tubes cover exactly their region's cell union, and
distinct maximal tubes have disjoint genuine interiors. -/
lemma uniqueMaximalApex_coverage_disjointInteriors
    (E : StandardMultiNormMatrix ι) :
    (∀ (D : Set ι), D.Nonempty → ∀ M : ι → ℕ,
      toLogPoint M ∈ dottedRegion E D →
        ∃! L : ι → ℕ,
          IsMaximalDottedScale E D L ∧ M ∈ tubeIndexSet D L) ∧
    (∀ (D : Set ι), D.Nonempty →
      (⋃ M : ι → ℕ, ⋃ (_ : toLogPoint M ∈ dottedRegion E D), logCell M) =
        ⋃ L : ι → ℕ, ⋃ (_ : IsMaximalDottedScale E D L), logTube D L) ∧
    (∀ (D₁ D₂ : Set ι), D₁.Nonempty → D₂.Nonempty →
      ∀ (L₁ L₂ : ι → ℕ), IsMaximalDottedScale E D₁ L₁ →
        IsMaximalDottedScale E D₂ L₂ → (D₁ ≠ D₂ ∨ L₁ ≠ L₂) →
          Disjoint (interior (logTube D₁ L₁))
            (interior (logTube D₂ L₂))) :=
  ⟨fun _ hD _ hM => existsUnique_maximalApex E hD hM,
    fun _ hD => dottedRegion_cellUnion_eq_maximalTubeUnion E hD,
    fun _ _ hD₁ hD₂ _ _ h₁ h₂ hne =>
      interiors_disjoint_of_distinct_maximal E hD₁ hD₂ h₁ h₂ hne⟩

end MultiNormDyadic

end Physlib.Mathematics.HarmonicAnalysis
