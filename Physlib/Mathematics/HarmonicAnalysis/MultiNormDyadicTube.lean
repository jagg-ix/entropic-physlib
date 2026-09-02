/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormDottedRegionCharacterization

/-!
# Maximal dotted scales and discrete logarithmic tubes

This module introduces the first dyadic layer of Section 3.4 in
Hejna--Nagel--Ricci.  A lattice scale is maximal for a dotted region `Γ(D)`
when increasing any undotted coordinate by one leaves that region.  Its
discrete tube `𝕋_L` fixes dotted coordinates and allows every undotted
coordinate to range downward to zero.

The construction is deliberately separated from the later global selection
theorem.  This file proves the exact maximality predicate, the finiteness and
greatest-element geometry of `𝕋_L`, and the union-of-cells description of its
continuous logarithmic tube.  Existence and uniqueness of a maximal apex over
every lattice cell is the next theorem and will require the paper's floor and
`τ_S` characterization rather than an implicit choice assumption.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormDyadic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open MultiNormMarkedPartition

/-! ## 1. Lattice scales and unit logarithmic cells -/

/-- Embed a natural-valued dyadic scale into logarithmic real coordinates. -/
def toLogPoint (L : ι → ℕ) : ι → ℝ := fun i => L i

/-- Increase exactly one coordinate of a lattice scale by one. -/
def increment (L : ι → ℕ) (j : ι) : ι → ℕ :=
  Function.update L j (L j + 1)

omit [Fintype ι] [Nonempty ι] in
@[simp] lemma increment_apply_self (L : ι → ℕ) (j : ι) :
    increment L j j = L j + 1 := by
  simp [increment]

omit [Fintype ι] [Nonempty ι] in
@[simp] lemma increment_apply_of_ne (L : ι → ℕ) {i j : ι} (hij : i ≠ j) :
    increment L j i = L i := by
  simp [increment, hij]

/-- The closed unit logarithmic cell centered at the lattice scale `L`, clipped
to the nonnegative orthant at coordinate zero. -/
def logCell (L : ι → ℕ) : Set (ι → ℝ) :=
  {t | ∀ i, 0 ≤ t i ∧ (L i : ℝ) - 1 / 2 ≤ t i ∧ t i ≤ (L i : ℝ) + 1 / 2}

/-! ## 2. Maximal dotted lattice scales -/

/-- A lattice scale is maximal in the family indexed by `D` when it lies in
`Γ(D)` and no unit increment in an undotted coordinate remains in `Γ(D)`. -/
def IsMaximalDottedScale (E : StandardMultiNormMatrix ι) (D : Set ι)
    (L : ι → ℕ) : Prop :=
  toLogPoint L ∈ dottedRegion E D ∧
    ∀ j ∉ D, toLogPoint (increment L j) ∉ dottedRegion E D

/-- For nonempty `D`, maximality can be checked entirely using the marked-cone
union and strict dotted-coordinate separation from Proposition 3.5. -/
lemma isMaximalDottedScale_iff_geometric
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    (L : ι → ℕ) :
    IsMaximalDottedScale E D L ↔
      toLogPoint L ∈ markedConeUnion E D ∩ strictDottedLocus E D ∧
      ∀ j ∉ D,
        toLogPoint (increment L j) ∉
          markedConeUnion E D ∩ strictDottedLocus E D := by
  simp only [IsMaximalDottedScale,
    mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD]

/-! ## 3. The finite discrete tube `𝕋_L` -/

/-- The discrete tube below `L`: dotted coordinates are fixed at their apex
values and undotted coordinates range from zero through their apex values. -/
def tubeIndexSet (D : Set ι) (L : ι → ℕ) : Set (ι → ℕ) :=
  {M | (∀ i ∈ D, M i = L i) ∧ ∀ i ∉ D, M i ≤ L i}

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
@[simp] lemma mem_tubeIndexSet_iff {D : Set ι} {L M : ι → ℕ} :
    M ∈ tubeIndexSet D L ↔
      (∀ i ∈ D, M i = L i) ∧ ∀ i ∉ D, M i ≤ L i :=
  Iff.rfl

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The apex belongs to its own discrete tube. -/
lemma self_mem_tubeIndexSet (D : Set ι) (L : ι → ℕ) :
    L ∈ tubeIndexSet D L :=
  ⟨fun _ _ => rfl, fun _ _ => le_rfl⟩

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Every tube index is coordinatewise bounded above by its apex. -/
lemma le_apex_of_mem_tubeIndexSet {D : Set ι} {L M : ι → ℕ}
    (hM : M ∈ tubeIndexSet D L) : M ≤ L := by
  intro i
  by_cases hi : i ∈ D
  · exact (hM.1 i hi).le
  · exact hM.2 i hi

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The discrete tube has the advertised fixed dotted coordinates. -/
lemma eq_apex_on_dotted_of_mem_tubeIndexSet {D : Set ι} {L M : ι → ℕ}
    (hM : M ∈ tubeIndexSet D L) {i : ι} (hi : i ∈ D) :
    M i = L i :=
  hM.1 i hi

omit [DecidableEq ι] [Nonempty ι] in
/-- The discrete tube is finite. -/
lemma tubeIndexSet_finite (D : Set ι) (L : ι → ℕ) :
    (tubeIndexSet D L).Finite := by
  apply (Set.Finite.pi fun i => Set.finite_le_nat (L i)).subset
  intro M hM
  rw [Set.mem_pi]
  intro i _
  exact le_apex_of_mem_tubeIndexSet hM i

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The apex is a greatest element of its finite discrete tube. -/
lemma apex_isGreatest_tubeIndexSet (D : Set ι) (L : ι → ℕ) :
    L ∈ tubeIndexSet D L ∧ ∀ M ∈ tubeIndexSet D L, M ≤ L :=
  ⟨self_mem_tubeIndexSet D L, fun _ hM => le_apex_of_mem_tubeIndexSet hM⟩

omit [Fintype ι] [DecidableEq ι] in
/-- With every coordinate dotted, the discrete tube is the singleton apex. -/
lemma tubeIndexSet_univ (L : ι → ℕ) :
    tubeIndexSet (Set.univ : Set ι) L = {L} := by
  ext M
  simp only [mem_tubeIndexSet_iff, Set.mem_univ, forall_const, not_true_eq_false,
    IsEmpty.forall_iff, and_true, Set.mem_singleton_iff]
  exact ⟨fun h => funext fun i => h i, fun h i => congrFun h i⟩

/-! ## 4. The continuous logarithmic tube -/

/-- The continuous logarithmic tube `T_L`, defined exactly as the union of the
unit cells indexed by the finite discrete tube `𝕋_L`. -/
def logTube (D : Set ι) (L : ι → ℕ) : Set (ι → ℝ) :=
  ⋃ M ∈ tubeIndexSet D L, logCell M

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Every cell indexed by `𝕋_L` is contained in its logarithmic tube. -/
lemma logCell_subset_logTube {D : Set ι} {L M : ι → ℕ}
    (hM : M ∈ tubeIndexSet D L) : logCell M ⊆ logTube D L := by
  intro t ht
  exact Set.mem_iUnion₂.mpr ⟨M, hM, ht⟩

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The apex cell is contained in its logarithmic tube. -/
lemma apex_logCell_subset_logTube (D : Set ι) (L : ι → ℕ) :
    logCell L ⊆ logTube D L :=
  logCell_subset_logTube (self_mem_tubeIndexSet D L)

omit [Fintype ι] [DecidableEq ι] in
/-- When every coordinate is dotted, the logarithmic tube is just its apex
unit cell. -/
lemma logTube_univ (L : ι → ℕ) :
    logTube (Set.univ : Set ι) L = logCell L := by
  simp [logTube, tubeIndexSet_univ]

/-! ## 5. Completed maximal-scale/tube package -/

/-- A maximal dotted lattice scale bundled with its dotted set. -/
structure MaximalScale (E : StandardMultiNormMatrix ι) where
  D : Set ι
  L : ι → ℕ
  maximal : IsMaximalDottedScale E D L

/-- The finite discrete tube attached to a bundled maximal scale. -/
def MaximalScale.indices {E : StandardMultiNormMatrix ι}
    (A : MaximalScale E) : Set (ι → ℕ) :=
  tubeIndexSet A.D A.L

/-- The continuous logarithmic tube attached to a bundled maximal scale. -/
def MaximalScale.tube {E : StandardMultiNormMatrix ι}
    (A : MaximalScale E) : Set (ι → ℝ) :=
  logTube A.D A.L

/-- Capstone for the first dyadic layer: a maximal dotted scale belongs to its
canonical region and carries a finite downward tube with that scale as a
greatest element and with continuous realization equal to the union of its
unit logarithmic cells. -/
lemma maximalDottedScale_finiteTube_geometry
    (E : StandardMultiNormMatrix ι) (D : Set ι) (L : ι → ℕ)
    (hmax : IsMaximalDottedScale E D L) :
    toLogPoint L ∈ dottedRegion E D ∧
      (tubeIndexSet D L).Finite ∧
      (L ∈ tubeIndexSet D L ∧ ∀ M ∈ tubeIndexSet D L, M ≤ L) ∧
      logTube D L = ⋃ M ∈ tubeIndexSet D L, logCell M :=
  ⟨hmax.1, tubeIndexSet_finite D L, apex_isGreatest_tubeIndexSet D L, rfl⟩

end MultiNormDyadic

end Physlib.Mathematics.HarmonicAnalysis
