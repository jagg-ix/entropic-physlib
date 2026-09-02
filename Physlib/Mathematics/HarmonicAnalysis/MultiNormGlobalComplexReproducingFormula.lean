/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula

/-!
# Complex global multi-norm reproducing formulas

The global smooth partition is lifted from real scalar data to complex Fourier
amplitudes.  This is the analytic interface needed by Schrödinger evolution and
decoherence functionals: the localized amplitudes reconstruct exactly, and their
Born weights resolve the pointwise modulus squared exactly.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormGlobalComplexReproducingFormula

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
variable [∀ i, HasContDiffBump (V i)]

open MultiNormGlobalFrequencyCover MultiNormGlobalNormalizedPartition
  MultiNormGlobalReproducingFormula

/-! ## A. Complex multiplier and analysis pieces -/

/-- The global normalized multiplier piece acting on a complex Fourier amplitude. -/
def globalNormalizedComplexMultiplierPiece {E : StandardMultiNormMatrix ι}
    (A : FullTubeIndex E) (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) : ℂ :=
  (globalNormalizedSmoothSymbol A ξ : ℂ) * f ξ

/-- The square-analysis branch amplitude, weighted by the square root of the
global normalized symbol. -/
def globalNormalizedComplexAnalysisPiece {E : StandardMultiNormMatrix ι}
    (A : FullTubeIndex E) (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) : ℂ :=
  (Real.sqrt (globalNormalizedSmoothSymbol A ξ) : ℂ) * f ξ

/-- Each complex square-analysis branch has Born weight equal to its normalized
symbol times the original Born weight. -/
lemma normSq_globalNormalizedComplexAnalysisPiece
    {E : StandardMultiNormMatrix ι} (A : FullTubeIndex E)
    (f : (∀ i, V i) → ℂ) (ξ : ∀ i, V i) :
    Complex.normSq (globalNormalizedComplexAnalysisPiece A f ξ) =
      globalNormalizedSmoothSymbol A ξ * Complex.normSq (f ξ) := by
  rw [globalNormalizedComplexAnalysisPiece, Complex.normSq_mul,
    Complex.normSq_ofReal,
    Real.mul_self_sqrt
      (globalNormalizedSmoothSymbol_nonneg (V := V) A ξ)]

/-! ## B. Canonical finite carrier -/

/-- The canonical finite carrier reconstructs a complex amplitude exactly. -/
lemma sum_globalSymbolFinsupport_complexMultiplier_eq
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) :
    ∑ A ∈ globalSymbolFinsupport E ξ,
      globalNormalizedComplexMultiplierPiece A f ξ = f ξ := by
  apply Complex.ext
  · simpa [globalNormalizedComplexMultiplierPiece,
      globalNormalizedMultiplierPiece, Complex.mul_re] using
      sum_globalSymbolFinsupport_multiplier_eq (V := V) E
        (fun η => (f η).re) ξ
  · simpa [globalNormalizedComplexMultiplierPiece,
      globalNormalizedMultiplierPiece, Complex.mul_im] using
      sum_globalSymbolFinsupport_multiplier_eq (V := V) E
        (fun η => (f η).im) ξ

/-- The canonical finite carrier resolves the complex Born weight exactly. -/
lemma sum_globalSymbolFinsupport_complexAnalysis_normSq_eq
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) :
    ∑ A ∈ globalSymbolFinsupport E ξ,
      Complex.normSq (globalNormalizedComplexAnalysisPiece A f ξ) =
        Complex.normSq (f ξ) := by
  simp_rw [normSq_globalNormalizedComplexAnalysisPiece (V := V)]
  rw [← Finset.sum_mul, sum_globalSymbolFinsupport_eq_one (V := V) E ξ]
  simp

/-! ## C. Exact locally finite formulas -/

/-- The support of the complex multiplier family at a point lies in the
canonical finite carrier. -/
lemma support_complexMultiplierAt_subset_globalSymbolFinsupport
    {E : StandardMultiNormMatrix ι} (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) :
    Function.support
        (fun A : FullTubeIndex E =>
          globalNormalizedComplexMultiplierPiece A f ξ) ⊆
      globalSymbolFinsupport E ξ := by
  intro A hA
  change A ∈ globalSymbolFinsupport E ξ
  rw [mem_globalSymbolFinsupport_iff (V := V)]
  intro hzero
  apply hA
  simp [globalNormalizedComplexMultiplierPiece, hzero]

/-- The support of the Born-weight family at a point lies in the canonical
finite carrier. -/
lemma support_complexAnalysisNormSqAt_subset_globalSymbolFinsupport
    {E : StandardMultiNormMatrix ι} (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) :
    Function.support
        (fun A : FullTubeIndex E =>
          Complex.normSq (globalNormalizedComplexAnalysisPiece A f ξ)) ⊆
      globalSymbolFinsupport E ξ := by
  intro A hA
  change A ∈ globalSymbolFinsupport E ξ
  rw [mem_globalSymbolFinsupport_iff (V := V)]
  intro hzero
  apply hA
  dsimp only
  rw [normSq_globalNormalizedComplexAnalysisPiece (V := V), hzero,
    zero_mul]

/-- The locally finite complex multiplier pieces reconstruct the Fourier
amplitude pointwise. -/
lemma finsum_globalNormalizedComplexMultiplierPiece_eq
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) :
    ∑ᶠ A : FullTubeIndex E,
      globalNormalizedComplexMultiplierPiece A f ξ = f ξ := by
  rw [finsum_eq_finsetSum_of_support_subset _
    (support_complexMultiplierAt_subset_globalSymbolFinsupport
      (V := V) f ξ)]
  exact sum_globalSymbolFinsupport_complexMultiplier_eq (V := V) E f ξ

/-- The Born weights of all locally finite analysis branches sum exactly to the
Born weight of the unlocalized complex amplitude. -/
lemma finsum_normSq_globalNormalizedComplexAnalysisPiece_eq
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) :
    ∑ᶠ A : FullTubeIndex E,
      Complex.normSq (globalNormalizedComplexAnalysisPiece A f ξ) =
        Complex.normSq (f ξ) := by
  rw [finsum_eq_finsetSum_of_support_subset _
    (support_complexAnalysisNormSqAt_subset_globalSymbolFinsupport
      (V := V) f ξ)]
  exact sum_globalSymbolFinsupport_complexAnalysis_normSq_eq
    (V := V) E f ξ

/-- The complex global partition simultaneously gives exact amplitude
reconstruction and exact Born-weight resolution, both as a `finsum` and on the
canonical finite carrier at each frequency. -/
lemma globalMultiNorm_complexReproducing_bornResolution
    (E : StandardMultiNormMatrix ι) (f : (∀ i, V i) → ℂ)
    (ξ : ∀ i, V i) :
    (∑ᶠ A : FullTubeIndex E,
      globalNormalizedComplexMultiplierPiece A f ξ) = f ξ ∧
    (∑ᶠ A : FullTubeIndex E,
      Complex.normSq (globalNormalizedComplexAnalysisPiece A f ξ)) =
        Complex.normSq (f ξ) ∧
    (∑ A ∈ globalSymbolFinsupport E ξ,
      globalNormalizedComplexMultiplierPiece A f ξ) = f ξ ∧
    (∑ A ∈ globalSymbolFinsupport E ξ,
      Complex.normSq (globalNormalizedComplexAnalysisPiece A f ξ)) =
        Complex.normSq (f ξ) := by
  exact ⟨finsum_globalNormalizedComplexMultiplierPiece_eq (V := V) E f ξ,
    finsum_normSq_globalNormalizedComplexAnalysisPiece_eq (V := V) E f ξ,
    sum_globalSymbolFinsupport_complexMultiplier_eq (V := V) E f ξ,
    sum_globalSymbolFinsupport_complexAnalysis_normSq_eq (V := V) E f ξ⟩

end MultiNormGlobalComplexReproducingFormula

end Physlib.Mathematics.HarmonicAnalysis
