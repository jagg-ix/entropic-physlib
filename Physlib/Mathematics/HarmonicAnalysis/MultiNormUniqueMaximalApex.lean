/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormMaximalFloorCriterion

/-!
# Unique maximal apices for multi-norm dyadic tubes

This module proves the constructive lattice content of Lemma 3.7(a) in
Hejna--Nagel--Ricci. A lattice point in `Γ(D)` determines a maximal apex by
rounding every coordinate down from the dominant mark of its block. The
wall-robust floor theorem makes that apex independent of the chosen containing
marked cone and proves uniqueness.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormDyadic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open MultiNormMarkedPartition

/-! ## 1. Constructing an apex from a containing marked cone -/

/-- The candidate maximal apex obtained from the floor profile of `M` inside
the marked cone `S`. -/
def markedApex (E : StandardMultiNormMatrix ι)
    (S : MultiNormMarkedPartition ι) (M : ι → ℕ) : ι → ℕ :=
  fun i => floorCoordinate E S M i

omit [Fintype ι] [Nonempty ι] in
@[simp] lemma markedApex_eq_on_marks
    (E : StandardMultiNormMatrix ι) (S : MultiNormMarkedPartition ι)
    (M : ι → ℕ) {i : ι} (hi : i ∈ S.marks) :
    markedApex E S M i = M i :=
  floorCoordinate_eq_of_mem_marks E S M hi

/-- A lattice point in `S.cone E` lies coordinatewise below its constructed
apex. -/
lemma le_markedApex_of_mem_cone
    (E : StandardMultiNormMatrix ι) (S : MultiNormMarkedPartition ι)
    {M : ι → ℕ} (hM : toLogPoint M ∈ S.cone E) :
    M ≤ markedApex E S M := by
  intro i
  unfold markedApex floorCoordinate
  apply Nat.le_floor
  simpa [toLogPoint] using S.cone_withinBlock_le hM i

/-- The constructed apex remains in the same marked cone. -/
lemma markedApex_mem_cone
    (E : StandardMultiNormMatrix ι) (S : MultiNormMarkedPartition ι)
    {M : ι → ℕ} (hM : toLogPoint M ∈ S.cone E) :
    toLogPoint (markedApex E S M) ∈ S.cone E := by
  rw [S.mem_cone_iff_explicitCone E] at hM ⊢
  refine ⟨fun i => by simp [toLogPoint], ?_, ?_⟩
  · intro i
    have hnonneg : 0 ≤ (M (S.mark i) : ℝ) / E (S.mark i) i :=
      div_nonneg (by positivity) (E.entry_pos _ _).le
    calc
      toLogPoint (markedApex E S M) i
          = (⌊(M (S.mark i) : ℝ) / E (S.mark i) i⌋₊ : ℝ) := rfl
      _ ≤ (M (S.mark i) : ℝ) / E (S.mark i) i := Nat.floor_le hnonneg
      _ = toLogPoint (markedApex E S M) (S.mark i) / E (S.mark i) i := by
        rw [toLogPoint, markedApex_eq_on_marks E S M]
        exact ⟨i, rfl⟩
  · intro p q
    simpa [toLogPoint, markedApex_eq_on_marks E S M p.2,
      markedApex_eq_on_marks E S M q.2] using hM.2.2 p q

omit [Fintype ι] [Nonempty ι] in
/-- Membership in the strict dotted locus depends only on the dotted
coordinates. -/
lemma strictDottedLocus_congr
    (E : StandardMultiNormMatrix ι) (D : Set ι) {t u : ι → ℝ}
    (h : ∀ i ∈ D, t i = u i) :
    t ∈ strictDottedLocus E D ↔ u ∈ strictDottedLocus E D := by
  constructor <;> intro ht k hk
  · rw [← h k hk]
    refine ⟨(ht k hk).1, ?_⟩
    intro q hq hqk
    simpa [h q hq] using (ht k hk).2 q hq hqk
  · rw [h k hk]
    refine ⟨(ht k hk).1, ?_⟩
    intro q hq hqk
    simpa [h q hq] using (ht k hk).2 q hq hqk

/-- If `M` lies in `Γ(D)` and in a marked cone with marks `D`, its constructed
apex remains in `Γ(D)`. -/
lemma markedApex_mem_dottedRegion
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    (S : MultiNormMarkedPartition ι) (hmarks : S.marks = D)
    {M : ι → ℕ} (hMD : toLogPoint M ∈ dottedRegion E D)
    (hMS : toLogPoint M ∈ S.cone E) :
    toLogPoint (markedApex E S M) ∈ dottedRegion E D := by
  have hstrict : toLogPoint M ∈ strictDottedLocus E D :=
    (mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD _).1 hMD |>.2
  apply (mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD _).2
  refine ⟨⟨S, hmarks, markedApex_mem_cone E S hMS⟩, ?_⟩
  exact (strictDottedLocus_congr E D (fun i hi => by
    simp [toLogPoint, markedApex_eq_on_marks E S M (hmarks.symm ▸ hi)])).1 hstrict

/-! ## 2. Independence from the containing cone -/

/-- Two marked cones containing the same lattice point produce the same apex
when they have the same active marks. -/
lemma markedApex_eq_of_mem_cones
    (E : StandardMultiNormMatrix ι)
    (S T : MultiNormMarkedPartition ι) (_hmarks : S.marks = T.marks)
    {M : ι → ℕ} (hS : toLogPoint M ∈ S.cone E)
    (hT : toLogPoint M ∈ T.cone E) :
    markedApex E S M = markedApex E T M := by
  funext i
  have hST :
      (M (T.mark i) : ℝ) / E (T.mark i) i ≤
        (M (S.mark i) : ℝ) / E (S.mark i) i :=
    hS.2 i (T.mark i)
  have hTS :
      (M (S.mark i) : ℝ) / E (S.mark i) i ≤
        (M (T.mark i) : ℝ) / E (T.mark i) i :=
    hT.2 i (S.mark i)
  exact congrArg Nat.floor (le_antisymm hTS hST)

/-- The apex constructed from a containing cone has the robust floor profile
and is therefore maximal. -/
lemma markedApex_isMaximalDottedScale
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    (S : MultiNormMarkedPartition ι) (hmarks : S.marks = D)
    {M : ι → ℕ} (hMD : toLogPoint M ∈ dottedRegion E D)
    (hMS : toLogPoint M ∈ S.cone E) :
    IsMaximalDottedScale E D (markedApex E S M) := by
  have hAD := markedApex_mem_dottedRegion E hD S hmarks hMD hMS
  apply isMaximalDottedScale_of_hasMaximalFloorProfile E hD hAD
  intro T hTmarks hT i
  have hAS := markedApex_mem_cone E S hMS
  have hratio :
      (markedApex E S M (S.mark i) : ℝ) / E (S.mark i) i =
        (markedApex E S M (T.mark i) : ℝ) / E (T.mark i) i :=
    le_antisymm (hT.2 i (S.mark i)) (hAS.2 i (T.mark i))
  change floorCoordinate E S M i =
    floorCoordinate E T (markedApex E S M) i
  unfold floorCoordinate
  rw [← markedApex_eq_on_marks E S M
    (show S.mark i ∈ S.marks from ⟨i, rfl⟩)]
  exact congrArg Nat.floor hratio

/-! ## 3. Lowering inside a tube -/

/-- Lowering only undotted coordinates from an apex preserves membership in
a marked cone whose marks are precisely the dotted coordinates. -/
lemma mem_cone_of_mem_tubeIndexSet
    (E : StandardMultiNormMatrix ι) {D : Set ι}
    (S : MultiNormMarkedPartition ι) (hmarks : S.marks = D)
    {L M : ι → ℕ} (hL : toLogPoint L ∈ S.cone E)
    (hM : M ∈ tubeIndexSet D L) :
    toLogPoint M ∈ S.cone E := by
  rw [S.mem_cone_iff_explicitCone E] at hL ⊢
  refine ⟨fun i => by simp [toLogPoint], ?_, ?_⟩
  · intro i
    have hle : M i ≤ L i := le_apex_of_mem_tubeIndexSet hM i
    have hmarkD : S.mark i ∈ D :=
      hmarks ▸ (show S.mark i ∈ S.marks from ⟨i, rfl⟩)
    calc
      toLogPoint M i ≤ toLogPoint L i := by
        change (M i : ℝ) ≤ (L i : ℝ)
        exact_mod_cast hle
      _ ≤ toLogPoint L (S.mark i) / E (S.mark i) i := hL.2.1 i
      _ = toLogPoint M (S.mark i) / E (S.mark i) i := by
        change (L (S.mark i) : ℝ) / E (S.mark i) i =
          (M (S.mark i) : ℝ) / E (S.mark i) i
        rw [hM.1 (S.mark i) hmarkD]
  · intro p q
    have hpD : p.1 ∈ D := hmarks ▸ p.2
    have hqD : q.1 ∈ D := hmarks ▸ q.2
    simpa [toLogPoint, hM.1 p.1 hpD, hM.1 q.1 hqD] using hL.2.2 p q

/-- A maximal apex above `M`, expressed through any containing marked cone,
is the marked-cone floor construction applied directly to `M`. -/
lemma eq_markedApex_of_isMaximal_and_mem_tube
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    (T : MultiNormMarkedPartition ι) (hmarks : T.marks = D)
    {L M : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (hLT : toLogPoint L ∈ T.cone E) (hM : M ∈ tubeIndexSet D L) :
    L = markedApex E T M := by
  have hprofile := hasMaximalFloorProfile_of_isMaximalDottedScale E hD hmax
    T hmarks hLT
  funext i
  rw [hprofile i, markedApex, floorCoordinate, floorCoordinate]
  have hmarkD : T.mark i ∈ D :=
    hmarks ▸ (show T.mark i ∈ T.marks from ⟨i, rfl⟩)
  rw [hM.1 (T.mark i) hmarkD]

/-! ## 4. Unique maximal apex -/

/-- Lemma 3.7(a), lattice form: every scale in a nonempty canonical region
belongs to the discrete tube of a unique maximal scale in that region. -/
lemma existsUnique_maximalApex
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {M : ι → ℕ} (hMD : toLogPoint M ∈ dottedRegion E D) :
    ∃! L : ι → ℕ,
      IsMaximalDottedScale E D L ∧ M ∈ tubeIndexSet D L := by
  obtain ⟨⟨S, hmarks, hMS⟩, -⟩ :=
    (mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD _).1 hMD
  let A := markedApex E S M
  have hAmax : IsMaximalDottedScale E D A :=
    markedApex_isMaximalDottedScale E hD S hmarks hMD hMS
  have hMtube : M ∈ tubeIndexSet D A := by
    refine ⟨?_, ?_⟩
    · intro i hi
      exact (markedApex_eq_on_marks E S M (hmarks.symm ▸ hi)).symm
    · intro i _hi
      exact le_markedApex_of_mem_cone E S hMS i
  refine ⟨A, ⟨hAmax, hMtube⟩, ?_⟩
  intro L hL
  obtain ⟨⟨T, hTmarks, hLT⟩, -⟩ :=
    (mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD _).1 hL.1.1
  have hMT : toLogPoint M ∈ T.cone E :=
    mem_cone_of_mem_tubeIndexSet E T hTmarks hLT hL.2
  calc
    L = markedApex E T M :=
      eq_markedApex_of_isMaximal_and_mem_tube E hD T hTmarks hL.1 hLT hL.2
    _ = markedApex E S M :=
      (markedApex_eq_of_mem_cones E S T (hmarks.trans hTmarks.symm) hMS hMT).symm
    _ = A := rfl

/-- Capstone: within every nonempty canonical region, the finite discrete
tubes of maximal scales partition exactly the region's natural lattice
points. -/
lemma maximalApex_partitions_dottedRegion_lattice
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty) :
    ∀ M : ι → ℕ, toLogPoint M ∈ dottedRegion E D →
      ∃! L : ι → ℕ,
        IsMaximalDottedScale E D L ∧ M ∈ tubeIndexSet D L :=
  fun _ hM => existsUnique_maximalApex E hD hM

end MultiNormDyadic

end Physlib.Mathematics.HarmonicAnalysis
