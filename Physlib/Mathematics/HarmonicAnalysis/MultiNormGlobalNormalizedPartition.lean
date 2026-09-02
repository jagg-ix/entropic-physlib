/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalLocalFiniteness
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The global normalized smooth multi-norm partition

Local finiteness makes the quadratic normalization a genuine pointwise finite
sum.  This module proves positivity and smoothness of its denominator and
bundles the normalized symbols as Mathlib's `SmoothPartitionOfUnity`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped ContDiff Manifold

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormGlobalNormalizedPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
variable [∀ i, HasContDiffBump (V i)]

open MultiNormGlobalFrequencyCover MultiNormFiniteNormalizedPartition
  MultiNormGlobalLocalFiniteness

/-! ## 1. The locally finite normalization energy -/

def globalSmoothEnergy {E : StandardMultiNormMatrix ι}
    (ξ : ∀ i, V i) : ℝ :=
  ∑ᶠ A : FullTubeIndex E, fullSmoothCutoff A ξ ^ 2

lemma locallyFinite_fullSmoothSquares
    (E : StandardMultiNormMatrix ι) :
    LocallyFinite (fun A : FullTubeIndex E =>
      Function.support (fun ξ : (∀ i, V i) =>
        fullSmoothCutoff A ξ ^ 2)) := by
  exact (locallyFinite_fullSmoothSupports (V := V) E).subset fun A ξ hξ => by
    intro hzero
    simp [hzero] at hξ

lemma contDiff_globalSmoothEnergy
    (E : StandardMultiNormMatrix ι) :
    ContDiff ℝ ∞ (globalSmoothEnergy (V := V) (E := E)) := by
  rw [← contMDiff_iff_contDiff]
  change ContMDiff (modelWithCornersSelf ℝ (∀ i, V i))
    (modelWithCornersSelf ℝ ℝ) ∞
      (fun ξ => ∑ᶠ A : FullTubeIndex E, fullSmoothCutoff A ξ ^ 2)
  apply contMDiff_finsum
  · intro A
    rw [contMDiff_iff_contDiff]
    exact (contDiff_fullSmoothCutoff (V := V) A).pow 2
  · exact locallyFinite_fullSmoothSquares (V := V) E

lemma globalSmoothEnergy_nonneg
    {E : StandardMultiNormMatrix ι} (ξ : ∀ i, V i) :
    0 ≤ globalSmoothEnergy (E := E) ξ := by
  exact finsum_nonneg fun A => sq_nonneg (fullSmoothCutoff A ξ)

lemma globalSmoothEnergy_pos
    (E : StandardMultiNormMatrix ι) (ξ : ∀ i, V i) :
    0 < globalSmoothEnergy (E := E) ξ := by
  obtain ⟨A, hAone⟩ :=
    (globalSmoothCover_locallyFinite (V := V) E).2 ξ
  have hfinite : Function.HasFiniteSupport
      (fun B : FullTubeIndex E => fullSmoothCutoff B ξ ^ 2) :=
    (locallyFinite_fullSmoothSquares (V := V) E).point_finite ξ
  have hle := single_le_finsum A hfinite
    (fun B => sq_nonneg (fullSmoothCutoff B ξ))
  have hone : (1 : ℝ) ≤ globalSmoothEnergy (E := E) ξ := by
    simpa [globalSmoothEnergy, hAone] using hle
  exact zero_lt_one.trans_le hone

/-! ## 2. Global normalized symbols -/

def globalNormalizedSmoothSymbol {E : StandardMultiNormMatrix ι}
    (A : FullTubeIndex E) (ξ : ∀ i, V i) : ℝ :=
  fullSmoothCutoff A ξ ^ 2 / globalSmoothEnergy (E := E) ξ

lemma contDiff_globalNormalizedSmoothSymbol
    (E : StandardMultiNormMatrix ι) (A : FullTubeIndex E) :
    ContDiff ℝ ∞ (globalNormalizedSmoothSymbol (V := V) A) := by
  exact (contDiff_fullSmoothCutoff (V := V) A).pow 2 |>.div
    (contDiff_globalSmoothEnergy (V := V) E)
    (fun ξ => (globalSmoothEnergy_pos (V := V) E ξ).ne')

lemma globalNormalizedSmoothSymbol_nonneg
    {E : StandardMultiNormMatrix ι} (A : FullTubeIndex E)
    (ξ : ∀ i, V i) :
    0 ≤ globalNormalizedSmoothSymbol A ξ := by
  exact div_nonneg (sq_nonneg _)
    (globalSmoothEnergy_nonneg (V := V) ξ)

lemma sum_globalNormalizedSmoothSymbol_eq_one
    (E : StandardMultiNormMatrix ι) (ξ : ∀ i, V i) :
    ∑ᶠ A : FullTubeIndex E, globalNormalizedSmoothSymbol A ξ = 1 := by
  simp_rw [globalNormalizedSmoothSymbol, div_eq_mul_inv]
  rw [← finsum_mul, ← globalSmoothEnergy]
  exact mul_inv_cancel₀ (globalSmoothEnergy_pos (V := V) E ξ).ne'

lemma support_globalNormalizedSmoothSymbol_subset
    {E : StandardMultiNormMatrix ι} (A : FullTubeIndex E) :
    Function.support (globalNormalizedSmoothSymbol (V := V) A) ⊆
      Function.support (fullSmoothCutoff (V := V) A) := by
  intro ξ hnormalized hcutoff
  apply hnormalized
  simp [globalNormalizedSmoothSymbol, hcutoff]

lemma locallyFinite_globalNormalizedSmoothSupports
    (E : StandardMultiNormMatrix ι) :
    LocallyFinite (fun A : FullTubeIndex E =>
      Function.support (globalNormalizedSmoothSymbol (V := V) A)) :=
  (locallyFinite_fullSmoothSupports (V := V) E).subset
    (support_globalNormalizedSmoothSymbol_subset (V := V))

/-! ## 3. The bundled smooth partition of unity -/

def globalSmoothPartitionOfUnity
    (E : StandardMultiNormMatrix ι) :
    SmoothPartitionOfUnity (FullTubeIndex E)
      (modelWithCornersSelf ℝ (∀ i, V i)) (∀ i, V i) Set.univ where
  toFun := fun A =>
    ⟨globalNormalizedSmoothSymbol (V := V) A,
      contMDiff_iff_contDiff.mpr
        (contDiff_globalNormalizedSmoothSymbol (V := V) E A)⟩
  locallyFinite' := locallyFinite_globalNormalizedSmoothSupports (V := V) E
  nonneg' := globalNormalizedSmoothSymbol_nonneg (V := V)
  sum_eq_one' := fun ξ _ =>
    sum_globalNormalizedSmoothSymbol_eq_one (V := V) E ξ
  sum_le_one' := fun ξ =>
    (sum_globalNormalizedSmoothSymbol_eq_one (V := V) E ξ).le

/-- Second global capstone: the completed multi-norm cutoff family produces a
native Mathlib smooth partition of unity on the entire frequency space. -/
lemma globalSmoothPartitionOfUnity_spec
    (E : StandardMultiNormMatrix ι) :
    (∀ ξ : (∀ i, V i),
      ∑ᶠ A : FullTubeIndex E,
        globalSmoothPartitionOfUnity (V := V) E A ξ = 1) ∧
    LocallyFinite (fun A : FullTubeIndex E =>
      Function.support (globalSmoothPartitionOfUnity (V := V) E A)) := by
  exact ⟨fun ξ =>
    (globalSmoothPartitionOfUnity (V := V) E).sum_eq_one (Set.mem_univ ξ),
    (globalSmoothPartitionOfUnity (V := V) E).locallyFinite⟩

end MultiNormGlobalNormalizedPartition

end Physlib.Mathematics.HarmonicAnalysis
