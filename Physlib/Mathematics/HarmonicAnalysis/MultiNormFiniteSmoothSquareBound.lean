/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring

/-!
# Finite square bounds for smooth multi-norm cutoffs

The smooth-support coloring gives a uniform pointwise overlap bound.  This
module turns that geometric statement into the finite square estimate needed
before constructing normalized Littlewood--Paley symbols and passing to an
infinite locally finite family.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormFiniteSmoothSquareBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
variable [∀ i, HasContDiffBump (V i)]

open MultiNormDyadic MultiNormSmoothCutoff MultiNormSmoothSupportColoring

/-! ## 1. The active finite subfamily -/

/-- Tubes in a finite family whose smooth cutoff is active at `ξ`. -/
def activeSmoothTubes {E : StandardMultiNormMatrix ι}
    (I : Finset (MaximalTubeIndex E)) (ξ : ∀ i, V i) :
    Finset (MaximalTubeIndex E) := by
  classical
  exact I.filter fun A => smoothBlockCutoff A.dotted A.apex ξ ≠ 0

lemma mem_activeSmoothTubes_iff
    {E : StandardMultiNormMatrix ι} {I : Finset (MaximalTubeIndex E)}
    {ξ : ∀ i, V i} {A : MaximalTubeIndex E} :
    A ∈ activeSmoothTubes (V := V) I ξ ↔
      A ∈ I ∧ smoothBlockCutoff A.dotted A.apex ξ ≠ 0 := by
  classical
  simp [activeSmoothTubes]

/-- At a fixed point, the smooth color is injective on active tubes. -/
lemma smoothTubeColor_injOn_activeSmoothTubes
    (E : StandardMultiNormMatrix ι) (I : Finset (MaximalTubeIndex E))
    (ξ : ∀ i, V i) :
    Set.InjOn (smoothTubeColor E)
      (activeSmoothTubes (V := V) I ξ : Set (MaximalTubeIndex E)) := by
  intro A hA B hB hcolor
  apply eq_of_smoothTubeColor_eq_of_support_inter (V := V) E hcolor
  exact ⟨ξ,
    (mem_activeSmoothTubes_iff (V := V)).1 hA |>.2,
    (mem_activeSmoothTubes_iff (V := V)).1 hB |>.2⟩

/-- Uniform pointwise overlap count for every finite tube family. -/
lemma card_activeSmoothTubes_le_colorCount
    (E : StandardMultiNormMatrix ι) (I : Finset (MaximalTubeIndex E))
    (ξ : ∀ i, V i) :
    (activeSmoothTubes (V := V) I ξ).card ≤
      Fintype.card (SmoothTubeColor E) := by
  classical
  apply Finset.card_le_card_of_injOn (smoothTubeColor E)
  · intro A hA
    exact Finset.mem_univ _
  · exact smoothTubeColor_injOn_activeSmoothTubes (V := V) E I ξ

/-! ## 2. The pointwise finite square estimate -/

lemma smoothBlockCutoff_sq_le_indicator
    {E : StandardMultiNormMatrix ι} (A : MaximalTubeIndex E)
    (ξ : ∀ i, V i) :
    smoothBlockCutoff A.dotted A.apex ξ ^ 2 ≤
      if smoothBlockCutoff A.dotted A.apex ξ ≠ 0 then (1 : ℝ) else 0 := by
  by_cases hzero : smoothBlockCutoff A.dotted A.apex ξ = 0
  · simp [hzero]
  · rw [if_pos hzero]
    have hrange := smoothBlockCutoff_mem_Icc (V := V) A.dotted A.apex ξ
    nlinarith [mul_nonneg hrange.1 (sub_nonneg.mpr hrange.2)]

/-- Third smooth-multiplier capstone: any finite family has a pointwise square
sum bounded solely by the cardinality of the constructed support coloring.
This is the finite, fully internal overlap estimate needed for normalization
of the paper's smooth Littlewood--Paley family. -/
lemma finiteSmoothMultiplierSquareBound
    (E : StandardMultiNormMatrix ι) (I : Finset (MaximalTubeIndex E))
    (ξ : ∀ i, V i) :
    (∑ A ∈ I, smoothBlockCutoff A.dotted A.apex ξ ^ 2) ≤
      (Fintype.card (SmoothTubeColor E) : ℝ) := by
  calc
    (∑ A ∈ I, smoothBlockCutoff A.dotted A.apex ξ ^ 2) ≤
        ∑ A ∈ I,
          if smoothBlockCutoff A.dotted A.apex ξ ≠ 0 then (1 : ℝ) else 0 :=
      Finset.sum_le_sum fun A _ => smoothBlockCutoff_sq_le_indicator (V := V) A ξ
    _ = ((activeSmoothTubes (V := V) I ξ).card : ℝ) := by
      classical
      rw [← Finset.sum_filter]
      simp [activeSmoothTubes]
    _ ≤ (Fintype.card (SmoothTubeColor E) : ℝ) := by
      exact_mod_cast card_activeSmoothTubes_le_colorCount (V := V) E I ξ

end MultiNormFiniteSmoothSquareBound

end Physlib.Mathematics.HarmonicAnalysis
