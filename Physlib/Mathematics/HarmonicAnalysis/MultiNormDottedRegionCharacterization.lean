/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormConeCoverage

/-!
# Characterization of canonical multi-norm dotted regions

This module proves Proposition 3.5 of Hejna--Nagel--Ricci in logarithmic
coordinates.  For a nonempty dotted set `D`, the canonical region `Γ(D)` is
exactly the union of the marked cones whose mark set is `D`, intersected with
the strict pairwise separation inequalities on the dotted coordinates.

The reverse implication is the substantive direction.  The canonical minimum
mark set is already contained in every competing mark set.  If a competing
mark were absent from the canonical set, the two containing cones would force
an equality between that mark and its canonical owner, contradicting strict
separation.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormMarkedPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-! ## 1. The two geometric factors in Proposition 3.5 -/

/-- The union of all marked cones whose active mark set is exactly `D`. -/
def markedConeUnion (E : StandardMultiNormMatrix ι) (D : Set ι) :
    Set (ι → ℝ) :=
  {t | ∃ S : MultiNormMarkedPartition ι, S.marks = D ∧ t ∈ S.cone E}

/-- The strict positive separation locus of the dotted coordinates in `D`. -/
def strictDottedLocus (E : StandardMultiNormMatrix ι) (D : Set ι) :
    Set (ι → ℝ) :=
  {t | ∀ k ∈ D, 0 < t k ∧
    ∀ q ∈ D, q ≠ k → t k < E k q * t q}

/-! ## 2. From a canonical region to the geometric factors -/

/-- A point of a nonempty canonical dotted region lies in a marked cone with
that mark set and satisfies strict positive separation on its marks. -/
lemma mem_markedConeUnion_and_strictDottedLocus_of_mem_dottedRegion
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {t : ι → ℝ} (htD : t ∈ dottedRegion E D) :
    t ∈ markedConeUnion E D ∩ strictDottedLocus E D := by
  obtain ⟨ht, hzero | ⟨hne, hcanonical⟩⟩ := htD
  · exact (hD.ne_empty hzero.2).elim
  · let C := canonicalMarkedPartition E t ht
    have hchar := canonicalDottedSet_characterization E t ht hne
    have hmarks : C.marks = D := by
      change canonicalDottedSet E t ht = D
      exact hcanonical
    refine ⟨⟨C, hmarks, hchar.1⟩, ?_⟩
    intro k hkD
    have hkC : k ∈ C.marks := hmarks.symm ▸ hkD
    let p : C.MarkedIndex := ⟨k, hkC⟩
    refine ⟨C.mark_pos_of_mem_cone hchar.1 hne p, ?_⟩
    intro q hqD hqk
    have hqC : q ∈ C.marks := hmarks.symm ▸ hqD
    let r : C.MarkedIndex := ⟨q, hqC⟩
    exact hchar.2.1 p r hqk.symm

/-! ## 3. Strict separation forces canonical minimality -/

/-- If a containing marked cone has strictly separated positive marks, its
mark set is the canonical dotted set. -/
lemma canonicalDottedSet_eq_marks_of_strict
    (E : StandardMultiNormMatrix ι) (S : MultiNormMarkedPartition ι)
    {t : ι → ℝ} (hS : t ∈ S.cone E)
    (hstrict : t ∈ strictDottedLocus E S.marks) :
    canonicalDottedSet E t hS.1 = S.marks := by
  have hne : t ≠ 0 := by
    obtain ⟨k, hkS⟩ := Set.range_nonempty S.mark
    intro hzero
    have hkpos := (hstrict k hkS).1
    simp [hzero] at hkpos
  let C := canonicalMarkedPartition E t hS.1
  have hchar := canonicalDottedSet_characterization E t hS.1 hne
  have hsubset : C.marks ⊆ S.marks := by
    change canonicalDottedSet E t hS.1 ⊆ S.marks
    exact hchar.2.2 S hS
  apply Set.Subset.antisymm hsubset
  intro k hkS
  by_contra hkC
  have hkfixed : S.mark k = k := (S.mem_marks_iff_fixed k).1 hkS
  let q := C.mark k
  have hqC : q ∈ C.marks := ⟨k, rfl⟩
  have hqS : q ∈ S.marks := hsubset hqC
  have hkq : k ≠ q := by
    intro hkq
    apply hkC
    apply (C.mem_marks_iff_fixed k).2
    exact hkq.symm
  have hcanonical_le : t k ≤ t q / E q k := by
    simpa [q, E.diagonal] using hchar.1.2 k k
  have hcompeting_le : t q / E q k ≤ t k := by
    simpa [hkfixed, E.diagonal] using hS.2 k q
  have heq : t q / E q k = t k := le_antisymm hcompeting_le hcanonical_le
  have hsep := (hstrict q hqS).2 k hkS hkq
  have hqeq : t q = t k * E q k := (div_eq_iff (E.entry_pos q k).ne').mp heq
  apply (lt_irrefl (t q))
  calc
    t q < E q k * t k := hsep
    _ = t q := by rw [hqeq]; ring

/-! ## 4. Proposition 3.5 -/

/-- Proposition 3.5, pointwise form: for nonempty `D`, membership in `Γ(D)`
is equivalent to membership in some marked cone with marks `D` together with
strict positive separation of the dotted coordinates. -/
lemma mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    (t : ι → ℝ) :
    t ∈ dottedRegion E D ↔
      t ∈ markedConeUnion E D ∩ strictDottedLocus E D := by
  constructor
  · exact mem_markedConeUnion_and_strictDottedLocus_of_mem_dottedRegion E hD
  · rintro ⟨⟨S, hmarks, hS⟩, hstrict⟩
    have hcanonical := canonicalDottedSet_eq_marks_of_strict E S hS (hmarks ▸ hstrict)
    have hne : t ≠ 0 := by
      obtain ⟨k, hkD⟩ := hD
      intro hzero
      have hkpos := (hstrict k hkD).1
      simp [hzero] at hkpos
    exact ⟨hS.1, Or.inr ⟨hne, hcanonical.trans hmarks⟩⟩

/-- Proposition 3.5, set form: `Γ(D)` is the intersection of the union of
all marked cones with mark set `D` and the strict dotted-coordinate locus. -/
lemma dottedRegion_eq_markedConeUnion_inter_strictDottedLocus
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty) :
    dottedRegion E D = markedConeUnion E D ∩ strictDottedLocus E D := by
  ext t
  exact mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD t

end MultiNormMarkedPartition

end Physlib.Mathematics.HarmonicAnalysis
