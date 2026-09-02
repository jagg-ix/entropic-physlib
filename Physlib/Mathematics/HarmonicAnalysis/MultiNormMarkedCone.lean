/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormDominance

/-!
# Marked partitions and dominance cones for multi-norm geometry

This module formalizes the marked partitions and cones `Γ_S` from Section
3.1 of A. Hejna, A. Nagel, and F. Ricci, *Littlewood-Paley square functions
and the local Hardy space for Multi-Norm Structures on R^d*
(arXiv:2507.09399).

A finite partition with one marked member in every block is represented by
an idempotent map: its fibers are the blocks and its fixed points are the
marks. For a standard matrix `E`, the cone `Γ_S` consists of nonnegative
logarithmic points where the mark of each block dominates every gauge indexed
by that block. This is exactly equation (3.2rr) in functional form.

The principal marked partition is the identity map, and its marked cone is
proved equivalent to the principal standard-matrix cone. Finally, every
strict-dominance assignment from `MultiNormDominance` induces a unique marked
partition whose strict cone contains the point.

This module does not prove existence of strict dominants on the singular tie
locus, classify the minimal marked set there, or construct maximal dyadic
tubes, smooth frequency cells, or Littlewood--Paley partitions of unity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

/-! # A. Marked partitions as idempotent maps -/

/-- A marked partition of `ι`, represented by an idempotent mark map.
The fiber over a fixed point is one block and that fixed point is its mark. -/
structure MultiNormMarkedPartition (ι : Type*) where
  mark : ι → ι
  mark_idempotent : ∀ i, mark (mark i) = mark i

namespace MultiNormMarkedPartition

variable {ι : Type*}

/-- The block carrying mark `k`, defined as the fiber of the mark map at `k`. -/
def block (S : MultiNormMarkedPartition ι) (k : ι) : Set ι :=
  {i | S.mark i = k}

/-- The set of active, or dotted, marks of a marked partition. -/
def marks (S : MultiNormMarkedPartition ι) : Set ι :=
  Set.range S.mark

/-- The principal marked partition, whose blocks are all singletons. -/
def principal (ι : Type*) : MultiNormMarkedPartition ι where
  mark := id
  mark_idempotent _ := rfl

@[simp] lemma principal_mark (i : ι) :
    (principal ι).mark i = i := rfl

/-- An index belongs to the block selected by its mark. -/
lemma mem_block_mark (S : MultiNormMarkedPartition ι) (i : ι) :
    i ∈ S.block (S.mark i) := rfl

/-- The mark selected by an index belongs to the block that it marks. -/
lemma mark_mem_block (S : MultiNormMarkedPartition ι) (i : ι) :
    S.mark i ∈ S.block (S.mark i) :=
  S.mark_idempotent i

/-- Active marks are exactly the fixed points of the mark map. -/
lemma mem_marks_iff_fixed (S : MultiNormMarkedPartition ι) (k : ι) :
    k ∈ S.marks ↔ S.mark k = k := by
  constructor
  · rintro ⟨i, rfl⟩
    exact S.mark_idempotent i
  · intro hk
    exact ⟨k, hk⟩

/-- Blocks carrying different marks are disjoint. -/
lemma block_disjoint (S : MultiNormMarkedPartition ι)
    {k l : ι} (hkl : k ≠ l) :
    Disjoint (S.block k) (S.block l) := by
  rw [Set.disjoint_left]
  intro i hik hil
  exact hkl (hik.symm.trans hil)

/-- Two marked partitions are equal when their mark maps agree. -/
@[ext] lemma ext {S T : MultiNormMarkedPartition ι}
    (h : S.mark = T.mark) : S = T := by
  cases S
  cases T
  cases h
  congr

/-! # B. Marked dominance cones -/

variable [DecidableEq ι]

/-- The closed marked cone `Γ_S`: logarithmic coordinates are nonnegative,
and the mark of every block dominates each gauge indexed by that block. -/
def cone (S : MultiNormMarkedPartition ι)
    (E : StandardMultiNormMatrix ι) : Set (ι → ℝ) :=
  {t | (∀ i, 0 ≤ t i) ∧ ∀ i, E.Dominates (S.mark i) i t}

/-- The strict marked cone obtained by replacing dominance with strict
dominance away from the selected mark. -/
def strictCone (S : MultiNormMarkedPartition ι)
    (E : StandardMultiNormMatrix ι) : Set (ι → ℝ) :=
  {t | (∀ i, 0 ≤ t i) ∧ ∀ i, E.StrictlyDominates (S.mark i) i t}

/-- The strict marked cone is contained in the closed marked cone. -/
lemma strictCone_subset_cone (S : MultiNormMarkedPartition ι)
    (E : StandardMultiNormMatrix ι) :
    S.strictCone E ⊆ S.cone E := by
  intro t ht
  exact ⟨ht.1, fun i => (ht.2 i).dominates⟩

/-- The paper's principal marked cone is the principal standard-matrix cone,
with the common nonnegativity condition made explicit. -/
lemma mem_principal_cone_iff [Fintype ι] [Nonempty ι]
    (E : StandardMultiNormMatrix ι) (t : ι → ℝ) :
    t ∈ (principal ι).cone E ↔
      (∀ i, 0 ≤ t i) ∧ E.InPrincipalCone t := by
  rw [E.inPrincipalCone_iff_diagonal_dominance]
  rfl

end MultiNormMarkedPartition

/-! # C. Strict dominance induces a unique marked partition -/

namespace StandardMultiNormMatrix.StrictDominanceAssignment

variable {ι : Type*} [DecidableEq ι]

/-- The marked partition canonically induced by a strict-dominance assignment
at a nonnegative logarithmic point. -/
def toMarkedPartition {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (A : E.StrictDominanceAssignment t) (ht : ∀ i, 0 ≤ t i) :
    MultiNormMarkedPartition ι where
  mark := A.owner
  mark_idempotent := A.owner_idempotent ht

@[simp] lemma toMarkedPartition_mark
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (A : E.StrictDominanceAssignment t) (ht : ∀ i, 0 ≤ t i)
    (i : ι) :
    (A.toMarkedPartition ht).mark i = A.owner i := rfl

/-- The original logarithmic point belongs to the strict cone of its induced
marked partition. -/
lemma mem_strictCone_toMarkedPartition
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (A : E.StrictDominanceAssignment t) (ht : ∀ i, 0 ≤ t i) :
    t ∈ (A.toMarkedPartition ht).strictCone E :=
  ⟨ht, A.owner_strictlyDominates⟩

/-- The original logarithmic point belongs to the closed cone of its induced
marked partition. -/
lemma mem_cone_toMarkedPartition
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (A : E.StrictDominanceAssignment t) (ht : ∀ i, 0 ≤ t i) :
    t ∈ (A.toMarkedPartition ht).cone E :=
  MultiNormMarkedPartition.strictCone_subset_cone _ _
    (A.mem_strictCone_toMarkedPartition ht)

/-- A marked partition whose marks are strict dominants at `t` must equal the
partition induced by the strict-dominance assignment. This is the uniqueness
part of the paper's marked-partition construction away from the tie locus. -/
lemma eq_toMarkedPartition_of_strictDominates
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (A : E.StrictDominanceAssignment t) (ht : ∀ i, 0 ≤ t i)
    (S : MultiNormMarkedPartition ι)
    (hS : ∀ i, E.StrictlyDominates (S.mark i) i t) :
    S = A.toMarkedPartition ht := by
  apply MultiNormMarkedPartition.ext
  funext i
  exact E.strictlyDominant_unique
    (hS i) (A.owner_strictlyDominates i)

/-- Capstone: a strict-dominance assignment induces a marked partition whose
strict and closed cones contain `t`, and this marked partition is uniquely
determined by strict dominance at `t`. -/
lemma strictDominance_induces_unique_markedCone
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (A : E.StrictDominanceAssignment t) (ht : ∀ i, 0 ≤ t i) :
    t ∈ (A.toMarkedPartition ht).strictCone E ∧
    t ∈ (A.toMarkedPartition ht).cone E ∧
    ∀ S : MultiNormMarkedPartition ι,
      (∀ i, E.StrictlyDominates (S.mark i) i t) →
      S = A.toMarkedPartition ht := by
  exact ⟨A.mem_strictCone_toMarkedPartition ht,
    A.mem_cone_toMarkedPartition ht,
    fun S hS => A.eq_toMarkedPartition_of_strictDominates ht S hS⟩

end StandardMultiNormMatrix.StrictDominanceAssignment

end Physlib.Mathematics.HarmonicAnalysis
