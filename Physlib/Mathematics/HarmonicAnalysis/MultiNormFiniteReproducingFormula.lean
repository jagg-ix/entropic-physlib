/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition

/-!
# Finite reproducing formulas for normalized multi-norm symbols

The normalized symbols from `MultiNormFiniteNormalizedPartition` now act as
an exact finite Fourier-side multiplier partition.  This module records the
reconstruction identity, the corresponding square-analysis identity, and
support subordination.  These statements isolate the algebraic core needed
before the later passage to locally finite infinite sums and distributions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormFiniteReproducingFormula

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
variable [∀ i, HasContDiffBump (V i)]

open MultiNormGlobalFrequencyCover MultiNormFiniteNormalizedPartition

/-! ## 1. Multiplier and square-analysis pieces -/

def normalizedMultiplierPiece {E : StandardMultiNormMatrix ι}
    (I : Finset (FullTubeIndex E)) (A : FullTubeIndex E)
    (f : (∀ i, V i) → ℝ) (ξ : ∀ i, V i) : ℝ :=
  normalizedSmoothSymbol I A ξ * f ξ

def normalizedAnalysisPiece {E : StandardMultiNormMatrix ι}
    (I : Finset (FullTubeIndex E)) (A : FullTubeIndex E)
    (f : (∀ i, V i) → ℝ) (ξ : ∀ i, V i) : ℝ :=
  Real.sqrt (normalizedSmoothSymbol I A ξ) * f ξ

/-! ## 2. Exact finite reconstruction -/

lemma sum_normalizedMultiplierPiece_eq
    {E : StandardMultiNormMatrix ι} (I : Finset (FullTubeIndex E))
    (f : (∀ i, V i) → ℝ) {ξ : ∀ i, V i}
    (henergy : finiteSmoothEnergy I ξ ≠ 0) :
    ∑ A ∈ I, normalizedMultiplierPiece I A f ξ = f ξ := by
  simp_rw [normalizedMultiplierPiece]
  rw [← Finset.sum_mul, sum_normalizedSmoothSymbol_eq_one (V := V) I henergy]
  simp

lemma sum_normalizedAnalysisPiece_sq_eq
    {E : StandardMultiNormMatrix ι} (I : Finset (FullTubeIndex E))
    (f : (∀ i, V i) → ℝ) {ξ : ∀ i, V i}
    (henergy : finiteSmoothEnergy I ξ ≠ 0) :
    ∑ A ∈ I, normalizedAnalysisPiece I A f ξ ^ 2 = f ξ ^ 2 := by
  calc
    (∑ A ∈ I, normalizedAnalysisPiece I A f ξ ^ 2) =
        ∑ A ∈ I, normalizedSmoothSymbol I A ξ * f ξ ^ 2 := by
      apply Finset.sum_congr rfl
      intro A hAI
      rw [normalizedAnalysisPiece, mul_pow,
        Real.sq_sqrt (normalizedSmoothSymbol_nonneg (V := V) I A ξ)]
    _ = (∑ A ∈ I, normalizedSmoothSymbol I A ξ) * f ξ ^ 2 := by
      rw [Finset.sum_mul]
    _ = f ξ ^ 2 := by
      rw [sum_normalizedSmoothSymbol_eq_one (V := V) I henergy]
      simp

/-! ## 3. Spectral support remains subordinate -/

lemma support_normalizedSmoothSymbol_subset
    {E : StandardMultiNormMatrix ι} (I : Finset (FullTubeIndex E))
    (A : FullTubeIndex E) :
    Function.support (normalizedSmoothSymbol (V := V) I A) ⊆
      Function.support (fullSmoothCutoff (V := V) A) := by
  intro ξ hnormalized
  intro hcutoff
  apply hnormalized
  simp [normalizedSmoothSymbol, hcutoff]

/-- Third capstone: at every point covered by a finite completed block family,
the normalized symbols give exact multiplier reconstruction, an exact
square-analysis identity, and retain support subordination to the original
smooth block cutoffs. -/
lemma finiteMultiNorm_reproducing_square_support
    (E : StandardMultiNormMatrix ι) (I : Finset (FullTubeIndex E))
    (f : (∀ i, V i) → ℝ) (ξ : ∀ i, V i)
    (hcover : ∃ A ∈ I, ξ ∈ fullFrequencyBlock A) :
    (∑ A ∈ I, normalizedMultiplierPiece I A f ξ) = f ξ ∧
    (∑ A ∈ I, normalizedAnalysisPiece I A f ξ ^ 2) = f ξ ^ 2 ∧
    ∀ A ∈ I,
      Function.support (normalizedSmoothSymbol (V := V) I A) ⊆
        Function.support (fullSmoothCutoff (V := V) A) := by
  obtain ⟨A, hAI, hξA⟩ := hcover
  have henergy : finiteSmoothEnergy I ξ ≠ 0 :=
    (finiteSmoothEnergy_pos_of_mem_fullFrequencyBlock
      (V := V) E hAI hξA).ne'
  exact ⟨sum_normalizedMultiplierPiece_eq (V := V) I f henergy,
    sum_normalizedAnalysisPiece_sq_eq (V := V) I f henergy,
    fun B _ => support_normalizedSmoothSymbol_subset (V := V) I B⟩

end MultiNormFiniteReproducingFormula

end Physlib.Mathematics.HarmonicAnalysis
