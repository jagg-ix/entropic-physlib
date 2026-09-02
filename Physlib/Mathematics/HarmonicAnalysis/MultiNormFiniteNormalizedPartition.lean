/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover

/-!
# Finite normalized smooth multi-norm partitions

This module performs the normalization step on any finite completed tube
family.  On the open set where the quadratic denominator is nonzero, the
symbols are `C∞`, nonnegative, and sum exactly to one.  If the finite family
contains a frequency block covering a point, denominator positivity follows
from the stronger fact that the corresponding unnormalized cutoff equals one.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped ContDiff

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormFiniteNormalizedPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
variable [∀ i, HasContDiffBump (V i)]

open MultiNormSmoothCutoff MultiNormGlobalFrequencyCover

/-! ## 1. Quadratic normalization energy -/

def finiteSmoothEnergy {E : StandardMultiNormMatrix ι}
    (I : Finset (FullTubeIndex E)) (ξ : ∀ i, V i) : ℝ :=
  ∑ A ∈ I, fullSmoothCutoff A ξ ^ 2

lemma fullSmoothCutoff_mem_Icc
    {E : StandardMultiNormMatrix ι} (A : FullTubeIndex E) (ξ : ∀ i, V i) :
    fullSmoothCutoff A ξ ∈ Set.Icc (0 : ℝ) 1 := by
  exact smoothBlockCutoff_mem_Icc (V := V) (fullDotted A) (fullApex A) ξ

lemma contDiff_fullSmoothCutoff
    {E : StandardMultiNormMatrix ι} (A : FullTubeIndex E) :
    ContDiff ℝ ∞ (fullSmoothCutoff (V := V) A) := by
  exact contDiff_smoothBlockCutoff (V := V) (fullDotted A) (fullApex A)

lemma contDiff_finiteSmoothEnergy
    {E : StandardMultiNormMatrix ι} (I : Finset (FullTubeIndex E)) :
    ContDiff ℝ ∞ (finiteSmoothEnergy (V := V) I) := by
  classical
  apply ContDiff.sum
  intro A hA
  exact (contDiff_fullSmoothCutoff (V := V) A).pow 2

lemma finiteSmoothEnergy_nonneg
    {E : StandardMultiNormMatrix ι} (I : Finset (FullTubeIndex E))
    (ξ : ∀ i, V i) :
    0 ≤ finiteSmoothEnergy I ξ := by
  exact Finset.sum_nonneg fun A _ => sq_nonneg (fullSmoothCutoff A ξ)

lemma finiteSmoothEnergy_pos_of_mem_fullFrequencyBlock
    (E : StandardMultiNormMatrix ι) {I : Finset (FullTubeIndex E)}
    {A : FullTubeIndex E} (hAI : A ∈ I) {ξ : ∀ i, V i}
    (hξ : ξ ∈ fullFrequencyBlock A) :
    0 < finiteSmoothEnergy I ξ := by
  have hAone : fullSmoothCutoff A ξ = 1 :=
    fullSmoothCutoff_eq_one_of_mem_fullFrequencyBlock (V := V) E A hξ
  have hterm : 0 < fullSmoothCutoff A ξ ^ 2 := by simp [hAone]
  exact hterm.trans_le (Finset.single_le_sum
    (fun B _ => sq_nonneg (fullSmoothCutoff B ξ)) hAI)

/-! ## 2. Normalized symbols -/

def normalizedSmoothSymbol {E : StandardMultiNormMatrix ι}
    (I : Finset (FullTubeIndex E)) (A : FullTubeIndex E)
    (ξ : ∀ i, V i) : ℝ :=
  fullSmoothCutoff A ξ ^ 2 / finiteSmoothEnergy I ξ

def normalizationDomain {E : StandardMultiNormMatrix ι}
    (I : Finset (FullTubeIndex E)) : Set (∀ i, V i) :=
  {ξ | finiteSmoothEnergy I ξ ≠ 0}

lemma contDiffOn_normalizedSmoothSymbol
    {E : StandardMultiNormMatrix ι} (I : Finset (FullTubeIndex E))
    (A : FullTubeIndex E) :
    ContDiffOn ℝ ∞ (normalizedSmoothSymbol (V := V) I A)
      (normalizationDomain (V := V) I) := by
  apply ContDiffOn.fun_div
  · exact (contDiff_fullSmoothCutoff (V := V) A).pow 2 |>.contDiffOn
  · exact (contDiff_finiteSmoothEnergy (V := V) I).contDiffOn
  · intro ξ hξ
    exact hξ

lemma normalizedSmoothSymbol_nonneg
    {E : StandardMultiNormMatrix ι} (I : Finset (FullTubeIndex E))
    (A : FullTubeIndex E) (ξ : ∀ i, V i) :
    0 ≤ normalizedSmoothSymbol I A ξ := by
  exact div_nonneg (sq_nonneg _) (finiteSmoothEnergy_nonneg I ξ)

lemma normalizedSmoothSymbol_le_one
    {E : StandardMultiNormMatrix ι} {I : Finset (FullTubeIndex E)}
    {A : FullTubeIndex E} (hAI : A ∈ I) {ξ : ∀ i, V i}
    (henergy : 0 < finiteSmoothEnergy I ξ) :
    normalizedSmoothSymbol I A ξ ≤ 1 := by
  rw [normalizedSmoothSymbol, div_le_one henergy]
  exact Finset.single_le_sum
    (fun B _ => sq_nonneg (fullSmoothCutoff B ξ)) hAI

lemma sum_normalizedSmoothSymbol_eq_one
    {E : StandardMultiNormMatrix ι} (I : Finset (FullTubeIndex E))
    {ξ : ∀ i, V i} (henergy : finiteSmoothEnergy I ξ ≠ 0) :
    ∑ A ∈ I, normalizedSmoothSymbol I A ξ = 1 := by
  simp_rw [normalizedSmoothSymbol]
  rw [← Finset.sum_div]
  exact div_self henergy

/-- Second capstone: a finite family covering `ξ` yields a positive smooth
normalization denominator, an exact partition of unity, and `[0,1]`-valued
normalized symbols at `ξ`. -/
lemma finiteNormalizedPartition_of_coversAt
    (E : StandardMultiNormMatrix ι) (I : Finset (FullTubeIndex E))
    (ξ : ∀ i, V i)
    (hcover : ∃ A ∈ I, ξ ∈ fullFrequencyBlock A) :
    0 < finiteSmoothEnergy I ξ ∧
    (∑ A ∈ I, normalizedSmoothSymbol I A ξ) = 1 ∧
    ∀ A ∈ I, normalizedSmoothSymbol I A ξ ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨A, hAI, hξA⟩ := hcover
  have henergy := finiteSmoothEnergy_pos_of_mem_fullFrequencyBlock
    (V := V) E hAI hξA
  refine ⟨henergy,
    sum_normalizedSmoothSymbol_eq_one (V := V) I henergy.ne', ?_⟩
  intro B hBI
  exact ⟨normalizedSmoothSymbol_nonneg (V := V) I B ξ,
    normalizedSmoothSymbol_le_one (V := V) hBI henergy⟩

end MultiNormFiniteNormalizedPartition

end Physlib.Mathematics.HarmonicAnalysis
