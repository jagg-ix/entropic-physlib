/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormMinimalDottedSet

/-!
# Coverage by marked cones and canonical dotted regions

This file removes the explicit marked-cone existence premise from the canonical
dotted-set construction. A finite maximum supplies a dominant coordinate for
each gauge. Self-dominant coordinates are fixed, while every other coordinate
is sent to a dominant one. Nonnegativity transfers dominance to the selected
coordinate itself, making this owner map idempotent.

The resulting marked partition contains every point of the nonnegative orthant.
It therefore supplies the existence witness needed by the minimum-cardinality
construction in `MultiNormMinimalDottedSet`. The final section packages the
canonical dotted sets as regions `dottedRegion E D`, corresponding to the
paper's notation `Γ(D)`, and proves that these regions partition the
nonnegative orthant.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace StandardMultiNormMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-! ## 1. Finite maximum dominance -/

/-- Every logarithmic gauge has a coordinate attaining its finite maximum. -/
lemma exists_dominant (E : StandardMultiNormMatrix ι) (t : ι → ℝ) (i : ι) :
    ∃ k, E.Dominates k i t := by
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j => t j / E j i)
  exact ⟨k, E.dominates_iff_logFrequencyGauge_eq.mpr hk⟩

end StandardMultiNormMatrix

namespace MultiNormMarkedPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-! ## 2. A total idempotent owner map -/

/-- Choose a dominant owner for gauge `i`, fixing `i` whenever it is already
self-dominant. -/
noncomputable def dominantOwner (E : StandardMultiNormMatrix ι) (t : ι → ℝ)
    (i : ι) : ι := by
  classical
  exact if h : E.Dominates i i t then i
    else Classical.choose (E.exists_dominant t i)

/-- The selected owner dominates the gauge it owns. -/
lemma dominantOwner_dominates (E : StandardMultiNormMatrix ι) (t : ι → ℝ)
    (i : ι) : E.Dominates (dominantOwner E t i) i t := by
  unfold dominantOwner
  split
  · assumption
  · exact Classical.choose_spec (E.exists_dominant t i)

/-- A self-dominant coordinate is fixed by the owner selection. -/
lemma dominantOwner_eq_self_of_dominates (E : StandardMultiNormMatrix ι)
    (t : ι → ℝ) (i : ι) (h : E.Dominates i i t) : dominantOwner E t i = i := by
  simp [dominantOwner, h]

/-- At a nonnegative point, every selected owner is itself self-dominant. -/
lemma dominantOwner_self_dominates (E : StandardMultiNormMatrix ι) (t : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (i : ι) :
    E.Dominates (dominantOwner E t i) (dominantOwner E t i) t :=
  E.dominates_self_of_dominates ht (dominantOwner_dominates E t i)

/-- The dominant-owner map is idempotent on the nonnegative orthant. -/
lemma dominantOwner_idempotent (E : StandardMultiNormMatrix ι) (t : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (i : ι) :
    dominantOwner E t (dominantOwner E t i) = dominantOwner E t i :=
  dominantOwner_eq_self_of_dominates E t _ (dominantOwner_self_dominates E t ht i)

/-! ## 3. Global marked-cone coverage -/

/-- The marked partition obtained from dominant owners of a nonnegative point. -/
noncomputable def coveringMarkedPartition (E : StandardMultiNormMatrix ι)
    (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) : MultiNormMarkedPartition ι where
  mark := dominantOwner E t
  mark_idempotent := dominantOwner_idempotent E t ht

/-- A nonnegative point lies in the cone of its dominant-owner partition. -/
lemma mem_coveringMarkedPartition_cone (E : StandardMultiNormMatrix ι)
    (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    t ∈ (coveringMarkedPartition E t ht).cone E := by
  refine ⟨ht, ?_⟩
  exact dominantOwner_dominates E t

/-- Every nonnegative logarithmic point is contained in a marked cone, including
points on dominance walls where several coordinates tie. -/
lemma admitsMarkedCone_of_nonnegative (E : StandardMultiNormMatrix ι)
    (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) : AdmitsMarkedCone E t :=
  ⟨coveringMarkedPartition E t ht, mem_coveringMarkedPartition_cone E t ht⟩

/-! ## 4. Premise-free canonical dotted sets -/

/-- A minimum-cardinality marked partition containing a nonnegative point. -/
noncomputable def canonicalMarkedPartition (E : StandardMultiNormMatrix ι)
    (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) : MultiNormMarkedPartition ι :=
  minimalMarkedPartition E t (admitsMarkedCone_of_nonnegative E t ht)

/-- The canonical minimum dotted set `D(t)` of a nonnegative logarithmic point. -/
noncomputable def canonicalDottedSet (E : StandardMultiNormMatrix ι)
    (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) : Set ι :=
  minimalDottedSet E t (admitsMarkedCone_of_nonnegative E t ht)

/-- The canonical dotted set no longer requires a separate marked-cone
existence premise: it contains `t`, has strict separation between distinct
marks when `t ≠ 0`, and is contained in every competing mark set. -/
lemma canonicalDottedSet_characterization (E : StandardMultiNormMatrix ι)
    (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (hne : t ≠ 0) :
    let S := canonicalMarkedPartition E t ht
    t ∈ S.cone E ∧
      (∀ p q : S.MarkedIndex, p.1 ≠ q.1 →
        t p.1 < E p.1 q.1 * t q.1) ∧
      ∀ T : MultiNormMarkedPartition ι, t ∈ T.cone E →
        canonicalDottedSet E t ht ⊆ T.marks := by
  simpa [canonicalMarkedPartition, canonicalDottedSet] using
    minimalMarkedPartition_dottedSet_characterization E t hne
      (admitsMarkedCone_of_nonnegative E t ht)

/-! ## 5. The canonical regions `Γ(D)` -/

/-- The canonical dotted region `Γ(D)` in the nonnegative orthant. The origin
belongs precisely to `Γ(∅)`; a nonzero point belongs to the region indexed by
its canonical minimum dotted set. -/
noncomputable def dottedRegion (E : StandardMultiNormMatrix ι) (D : Set ι) :
    Set (ι → ℝ) :=
  {t | ∃ ht : ∀ i, 0 ≤ t i,
    (t = 0 ∧ D = ∅) ∨ (t ≠ 0 ∧ canonicalDottedSet E t ht = D)}

/-- The origin belongs to the empty dotted region. -/
lemma zero_mem_dottedRegion_empty (E : StandardMultiNormMatrix ι) :
    (0 : ι → ℝ) ∈ dottedRegion E ∅ := by
  refine ⟨fun _ => le_rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- Every nonzero nonnegative point belongs to the region selected by its
canonical dotted set. -/
lemma mem_dottedRegion_canonical (E : StandardMultiNormMatrix ι) (t : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hne : t ≠ 0) :
    t ∈ dottedRegion E (canonicalDottedSet E t ht) :=
  ⟨ht, Or.inr ⟨hne, rfl⟩⟩

/-- A logarithmic point cannot belong to two differently indexed dotted
regions. -/
lemma dottedRegion_index_unique (E : StandardMultiNormMatrix ι) (t : ι → ℝ)
    {D D' : Set ι} (hD : t ∈ dottedRegion E D)
    (hD' : t ∈ dottedRegion E D') : D = D' := by
  obtain ⟨ht, htD⟩ := hD
  obtain ⟨ht', htD'⟩ := hD'
  rcases htD with ⟨rfl, rfl⟩ | ⟨hne, hcanonical⟩
  · rcases htD' with ⟨-, hD'⟩ | ⟨hne, -⟩
    · exact hD'.symm
    · exact (hne rfl).elim
  · rcases htD' with ⟨hzero, -⟩ | ⟨-, hcanonical'⟩
    · exact (hne hzero).elim
    · have hproof : ht = ht' := Subsingleton.elim _ _
      subst hproof
      exact hcanonical.symm.trans hcanonical'

/-- The regions `Γ(D)` form a genuine partition of the nonnegative orthant:
each nonnegative logarithmic point belongs to exactly one indexed region. -/
lemma existsUnique_dottedRegion (E : StandardMultiNormMatrix ι) (t : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) : ∃! D : Set ι, t ∈ dottedRegion E D := by
  by_cases hzero : t = 0
  · subst t
    refine ⟨∅, zero_mem_dottedRegion_empty E, ?_⟩
    intro D hD
    exact dottedRegion_index_unique E 0 hD (zero_mem_dottedRegion_empty E)
  · refine ⟨canonicalDottedSet E t ht,
      mem_dottedRegion_canonical E t ht hzero, ?_⟩
    intro D hD
    exact dottedRegion_index_unique E t hD
      (mem_dottedRegion_canonical E t ht hzero)

/-- Capstone: every nonnegative logarithmic point admits a containing marked
cone and belongs to exactly one canonical dotted region `Γ(D)`. -/
lemma nonnegativePoint_markedCone_and_uniqueDottedRegion
    (E : StandardMultiNormMatrix ι) (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    AdmitsMarkedCone E t ∧ ∃! D : Set ι, t ∈ dottedRegion E D :=
  ⟨admitsMarkedCone_of_nonnegative E t ht, existsUnique_dottedRegion E t ht⟩

end MultiNormMarkedPartition

end Physlib.Mathematics.HarmonicAnalysis
