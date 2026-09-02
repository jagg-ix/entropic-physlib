/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalNormalizedPartition

/-!
# Global pointwise-finite multi-norm reproducing formulas

The native smooth partition from `MultiNormGlobalNormalizedPartition` gives
exact infinite multiplier reconstruction and an exact square-analysis
identity.  The sums are `finsum`s, with a canonical finite carrier at every
frequency point supplied by Mathlib's smooth partition API.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormGlobalReproducingFormula

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
variable [∀ i, HasContDiffBump (V i)]

open MultiNormGlobalFrequencyCover MultiNormGlobalNormalizedPartition

/-! ## 1. Global multiplier and square-analysis pieces -/

def globalNormalizedMultiplierPiece {E : StandardMultiNormMatrix ι}
    (A : FullTubeIndex E) (f : (∀ i, V i) → ℝ)
    (ξ : ∀ i, V i) : ℝ :=
  globalNormalizedSmoothSymbol A ξ * f ξ

def globalNormalizedAnalysisPiece {E : StandardMultiNormMatrix ι}
    (A : FullTubeIndex E) (f : (∀ i, V i) → ℝ)
    (ξ : ∀ i, V i) : ℝ :=
  Real.sqrt (globalNormalizedSmoothSymbol A ξ) * f ξ

/-! ## 2. Exact infinite identities -/

lemma finsum_globalNormalizedMultiplierPiece_eq
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℝ)
    (ξ : ∀ i, V i) :
    ∑ᶠ A : FullTubeIndex E,
      globalNormalizedMultiplierPiece A f ξ = f ξ := by
  simp_rw [globalNormalizedMultiplierPiece]
  rw [← finsum_mul,
    sum_globalNormalizedSmoothSymbol_eq_one (V := V) E ξ]
  simp

lemma finsum_globalNormalizedAnalysisPiece_sq_eq
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℝ)
    (ξ : ∀ i, V i) :
    ∑ᶠ A : FullTubeIndex E,
      globalNormalizedAnalysisPiece A f ξ ^ 2 = f ξ ^ 2 := by
  calc
    (∑ᶠ A : FullTubeIndex E,
        globalNormalizedAnalysisPiece A f ξ ^ 2) =
        ∑ᶠ A : FullTubeIndex E,
          globalNormalizedSmoothSymbol A ξ * f ξ ^ 2 := by
      apply finsum_congr
      intro A
      rw [globalNormalizedAnalysisPiece, mul_pow,
        Real.sq_sqrt
          (globalNormalizedSmoothSymbol_nonneg (V := V) A ξ)]
    _ = (∑ᶠ A : FullTubeIndex E,
        globalNormalizedSmoothSymbol A ξ) * f ξ ^ 2 := by
      rw [finsum_mul]
    _ = f ξ ^ 2 := by
      rw [sum_globalNormalizedSmoothSymbol_eq_one (V := V) E ξ]
      simp

/-! ## 3. Canonical finite carriers at each frequency -/

def globalSymbolFinsupport
    (E : StandardMultiNormMatrix ι) (ξ : ∀ i, V i) :
    Finset (FullTubeIndex E) :=
  (globalSmoothPartitionOfUnity (V := V) E).finsupport ξ

lemma mem_globalSymbolFinsupport_iff
    (E : StandardMultiNormMatrix ι) (ξ : ∀ i, V i)
    (A : FullTubeIndex E) :
    A ∈ globalSymbolFinsupport E ξ ↔
      globalNormalizedSmoothSymbol A ξ ≠ 0 := by
  exact (globalSmoothPartitionOfUnity (V := V) E).mem_finsupport
    (x₀ := ξ)

lemma sum_globalSymbolFinsupport_eq_one
    (E : StandardMultiNormMatrix ι) (ξ : ∀ i, V i) :
    ∑ A ∈ globalSymbolFinsupport E ξ,
      globalNormalizedSmoothSymbol A ξ = 1 := by
  exact (globalSmoothPartitionOfUnity (V := V) E).sum_finsupport ξ
    (Set.mem_univ ξ)

lemma sum_globalSymbolFinsupport_multiplier_eq
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℝ)
    (ξ : ∀ i, V i) :
    ∑ A ∈ globalSymbolFinsupport E ξ,
      globalNormalizedMultiplierPiece A f ξ = f ξ := by
  simp_rw [globalNormalizedMultiplierPiece]
  rw [← Finset.sum_mul, sum_globalSymbolFinsupport_eq_one (V := V) E ξ]
  simp

lemma sum_globalSymbolFinsupport_analysis_sq_eq
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℝ)
    (ξ : ∀ i, V i) :
    ∑ A ∈ globalSymbolFinsupport E ξ,
      globalNormalizedAnalysisPiece A f ξ ^ 2 = f ξ ^ 2 := by
  calc
    (∑ A ∈ globalSymbolFinsupport E ξ,
        globalNormalizedAnalysisPiece A f ξ ^ 2) =
        ∑ A ∈ globalSymbolFinsupport E ξ,
          globalNormalizedSmoothSymbol A ξ * f ξ ^ 2 := by
      apply Finset.sum_congr rfl
      intro A _
      rw [globalNormalizedAnalysisPiece, mul_pow,
        Real.sq_sqrt
          (globalNormalizedSmoothSymbol_nonneg (V := V) A ξ)]
    _ = (∑ A ∈ globalSymbolFinsupport E ξ,
        globalNormalizedSmoothSymbol A ξ) * f ξ ^ 2 := by
      rw [Finset.sum_mul]
    _ = f ξ ^ 2 := by
      rw [sum_globalSymbolFinsupport_eq_one (V := V) E ξ]
      simp

lemma support_globalNormalizedMultiplierPiece_subset
    {E : StandardMultiNormMatrix ι} (A : FullTubeIndex E)
    (f : (∀ i, V i) → ℝ) :
    Function.support (globalNormalizedMultiplierPiece A f) ⊆
      Function.support (fullSmoothCutoff (V := V) A) := by
  intro ξ hpiece
  apply support_globalNormalizedSmoothSymbol_subset (V := V) A
  intro hsymbol
  apply hpiece
  simp [globalNormalizedMultiplierPiece, hsymbol]

/-- Third global capstone: both infinite formulas are exact, each has the
canonical finite carrier furnished by the bundled smooth partition, and the
multiplier pieces remain subordinate to the original smooth tube supports. -/
lemma globalMultiNorm_reproducing_square_finiteSupport
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℝ)
    (ξ : ∀ i, V i) :
    (∑ᶠ A : FullTubeIndex E,
      globalNormalizedMultiplierPiece A f ξ) = f ξ ∧
    (∑ᶠ A : FullTubeIndex E,
      globalNormalizedAnalysisPiece A f ξ ^ 2) = f ξ ^ 2 ∧
    (∑ A ∈ globalSymbolFinsupport E ξ,
      globalNormalizedMultiplierPiece A f ξ) = f ξ ∧
    (∑ A ∈ globalSymbolFinsupport E ξ,
      globalNormalizedAnalysisPiece A f ξ ^ 2) = f ξ ^ 2 ∧
    ∀ A : FullTubeIndex E,
      Function.support (globalNormalizedMultiplierPiece (V := V) A f) ⊆
        Function.support (fullSmoothCutoff (V := V) A) := by
  exact ⟨finsum_globalNormalizedMultiplierPiece_eq (V := V) E f ξ,
    finsum_globalNormalizedAnalysisPiece_sq_eq (V := V) E f ξ,
    sum_globalSymbolFinsupport_multiplier_eq (V := V) E f ξ,
    sum_globalSymbolFinsupport_analysis_sq_eq (V := V) E f ξ,
    fun A => support_globalNormalizedMultiplierPiece_subset
      (V := V) A f⟩

end MultiNormGlobalReproducingFormula

end Physlib.Mathematics.HarmonicAnalysis
