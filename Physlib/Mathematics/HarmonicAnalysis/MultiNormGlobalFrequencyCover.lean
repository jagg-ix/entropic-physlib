/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormApexDensity
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTubeColoring
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff

/-!
# Global multi-norm frequency coverage, including the low block

The maximal-tube index used for overlap estimates deliberately contains only
nonempty dotted regions.  The paper's full index set also contains the unique
empty-region block `(D, L) = (∅, 0)`.  This module adjoins that block, proves
global logarithmic and frequency coverage, and packages the existing smooth
cutoffs over the completed index type.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormGlobalFrequencyCover

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
variable [∀ i, HasContDiffBump (V i)]

open MultiNormMarkedPartition MultiNormDyadic MultiNormFrequencyBlock
  MultiNormSmoothCutoff

/-! ## 1. The completed tube index -/

/-- The paper's full tube index: `none` is the unique low block
`(D,L) = (∅,0)` and `some A` is a nonempty-region maximal tube. -/
abbrev FullTubeIndex (E : StandardMultiNormMatrix ι) :=
  Option (MaximalTubeIndex E)

def fullDotted {E : StandardMultiNormMatrix ι} : FullTubeIndex E → Set ι
  | none => ∅
  | some A => A.dotted

def fullApex {E : StandardMultiNormMatrix ι} : FullTubeIndex E → (ι → ℕ)
  | none => 0
  | some A => A.apex

def fullTube {E : StandardMultiNormMatrix ι} (A : FullTubeIndex E) :
    Set (ι → ℝ) :=
  logTube (fullDotted A) (fullApex A)

def fullFrequencyBlock {E : StandardMultiNormMatrix ι}
    (A : FullTubeIndex E) : Set (∀ i, V i) :=
  {ξ | positiveLog2Norm ξ ∈ fullTube A}

def fullSmoothCutoff {E : StandardMultiNormMatrix ι}
    (A : FullTubeIndex E) (ξ : ∀ i, V i) : ℝ :=
  smoothBlockCutoff (fullDotted A) (fullApex A) ξ

/-! ## 2. Global logarithmic and frequency coverage -/

/-- Lemma 3.7(c), now including the empty-region low block: every
nonnegative logarithmic point belongs to a completed maximal tube. -/
lemma exists_fullTubeIndex_mem
    (E : StandardMultiNormMatrix ι) (t : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) :
    ∃ A : FullTubeIndex E, t ∈ fullTube A := by
  let M := nearestCellIndex t
  have htM : t ∈ logCell M := mem_logCell_nearestCellIndex ht
  by_cases hM : M = 0
  · refine ⟨none, ?_⟩
    change t ∈ logTube ∅ 0
    apply logCell_subset_logTube (self_mem_tubeIndexSet ∅ 0)
    simpa [M, hM] using htM
  · have hMnonneg : ∀ i, 0 ≤ toLogPoint M i := fun i => by simp [toLogPoint]
    let D := canonicalDottedSet E (toLogPoint M) hMnonneg
    have hD : D.Nonempty := canonicalDottedSet_nonempty E _ hMnonneg
    have hMlog : toLogPoint M ≠ 0 := by
      intro hzero
      apply hM
      funext i
      have hi := congrFun hzero i
      change (M i : ℝ) = 0 at hi
      exact Nat.cast_eq_zero.mp hi
    have hMD : toLogPoint M ∈ dottedRegion E D :=
      mem_dottedRegion_canonical E _ hMnonneg hMlog
    obtain ⟨L, hL, -⟩ := existsUnique_maximalApex E hD hMD
    let A : MaximalTubeIndex E :=
      ⟨D, hD, L, hL.1⟩
    refine ⟨some A, ?_⟩
    exact logCell_subset_logTube hL.2 htM

/-- Every frequency point belongs to a completed multi-norm block. -/
lemma exists_fullFrequencyBlock_mem
    (E : StandardMultiNormMatrix ι) (ξ : ∀ i, V i) :
    ∃ A : FullTubeIndex E, ξ ∈ fullFrequencyBlock A := by
  exact exists_fullTubeIndex_mem E (positiveLog2Norm ξ)
    (positiveLog2Norm_nonneg ξ)

/-! ## 3. A cutoff equal to one at every frequency point -/

lemma mem_coordinateDyadicShell_empty_zero_of_mem_fullFrequencyBlock
    (E : StandardMultiNormMatrix ι) {ξ : ∀ i, V i}
    (hξ : ξ ∈ fullFrequencyBlock (E := E) none) :
    ξ ∈ coordinateDyadicShell (V := V) ∅ 0 := by
  change positiveLog2Norm ξ ∈ logTube ∅ 0 at hξ
  rw [logTube_eq_logTubeBox, logTubeBox, Set.mem_pi] at hξ
  intro i
  have hi := hξ i (Set.mem_univ i)
  simp only [logTubeInterval, Set.mem_empty_iff_false, if_false,
    Set.mem_Icc] at hi
  refine ⟨?_, ?_⟩
  · simpa using (positiveLog2Norm_le_iff (ξ := ξ) (i := i) (by positivity)).1 hi.2
  · simp

/-- The completed cutoff attached to a containing block is exactly one. -/
lemma fullSmoothCutoff_eq_one_of_mem_fullFrequencyBlock
    (E : StandardMultiNormMatrix ι) (A : FullTubeIndex E)
    {ξ : ∀ i, V i} (hξ : ξ ∈ fullFrequencyBlock A) :
    fullSmoothCutoff A ξ = 1 := by
  cases A with
  | none =>
      apply smoothBlockCutoff_eq_one_of_mem_coordinateDyadicShell (V := V)
      exact mem_coordinateDyadicShell_empty_zero_of_mem_fullFrequencyBlock E hξ
  | some A =>
      apply smoothBlockCutoff_eq_one_of_mem_coordinateDyadicShell (V := V)
      exact (mem_frequencyBlock_iff_coordinateDyadicShell E
        A.dotted_nonempty A.maximal ξ).1 hξ

/-- First capstone: the completed tube family covers all frequency space and
at every point one of the already constructed smooth cutoffs equals one. -/
lemma fullFrequencyCover_and_cutoff_one
    (E : StandardMultiNormMatrix ι) (ξ : ∀ i, V i) :
    ∃ A : FullTubeIndex E,
      ξ ∈ fullFrequencyBlock A ∧ fullSmoothCutoff A ξ = 1 := by
  obtain ⟨A, hA⟩ := exists_fullFrequencyBlock_mem (V := V) E ξ
  exact ⟨A, hA,
    fullSmoothCutoff_eq_one_of_mem_fullFrequencyBlock (V := V) E A hA⟩

end MultiNormGlobalFrequencyCover

end Physlib.Mathematics.HarmonicAnalysis
