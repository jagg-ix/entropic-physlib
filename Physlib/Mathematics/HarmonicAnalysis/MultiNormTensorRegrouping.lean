/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Regrouping full tensor indices by the paper's maximal tubes

This module connects Proposition 4.3 to the already formalized Section 3
lattice geometry.  It proves that the completed maximal tubes form a genuine
partition of `ℕ^n`, then supplies finite and infinite fiberwise regrouping
lemmas for tensor kernels and tempered distributions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped BigOperators SchwartzMap Topology

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormTensorRegrouping

open MultiNormMarkedPartition MultiNormDyadic MultiNormGlobalFrequencyCover
  MultiNormTensorCalderon

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-! ## A. The paper's full index fibers -/

/-- The raw multi-index fiber grouped under one completed maximal-tube index.
The `none` index is the paper's unique low block and contains only zero. -/
def paperTubeIndexSet {E : StandardMultiNormMatrix ι}
    (A : FullTubeIndex E) : Set (ι → ℕ) :=
  match A with
  | none => {0}
  | some T => tubeIndexSet T.dotted T.apex

lemma paperTubeIndexSet_finite {E : StandardMultiNormMatrix ι}
    (A : FullTubeIndex E) : (paperTubeIndexSet A).Finite := by
  cases A with
  | none => simp [paperTubeIndexSet]
  | some A => exact tubeIndexSet_finite A.dotted A.apex

/-- The finite raw-index set belonging to a paper tube. -/
def paperTubeIndexFinset {E : StandardMultiNormMatrix ι}
    (A : FullTubeIndex E) : Finset (ι → ℕ) :=
  (paperTubeIndexSet_finite A).toFinset

@[simp]
lemma mem_paperTubeIndexFinset_iff {E : StandardMultiNormMatrix ι}
    {A : FullTubeIndex E} {K : ι → ℕ} :
    K ∈ paperTubeIndexFinset A ↔ K ∈ paperTubeIndexSet A := by
  simp [paperTubeIndexFinset]

/-! ## B. Existence and uniqueness of the grouping index -/

/-- The completed maximal tubes partition the entire natural multi-index
lattice, including the zero index through the distinguished low block. -/
lemma existsUnique_paperTubeIndex
    (E : StandardMultiNormMatrix ι) (K : ι → ℕ) :
    ∃! A : FullTubeIndex E, K ∈ paperTubeIndexSet A := by
  by_cases hzero : K = 0
  · subst K
    refine ⟨none, by simp [paperTubeIndexSet], ?_⟩
    intro A hA
    cases A with
    | none => rfl
    | some A =>
        exfalso
        have hregion : toLogPoint (0 : ι → ℕ) ∈ dottedRegion E A.dotted :=
          mem_dottedRegion_of_mem_maximalTube E A.dotted_nonempty
            A.maximal hA
        have hD : A.dotted = ∅ :=
          dottedRegion_index_unique E _ hregion (by
            have hlogzero : toLogPoint (0 : ι → ℕ) = (0 : ι → ℝ) := by
              funext i
              simp [toLogPoint]
            rw [hlogzero]
            exact zero_mem_dottedRegion_empty E)
        exact Set.not_nonempty_empty (hD ▸ A.dotted_nonempty)
  · have hnonneg : ∀ i, 0 ≤ toLogPoint K i := fun i => by simp [toLogPoint]
    let D := canonicalDottedSet E (toLogPoint K) hnonneg
    have hD : D.Nonempty := canonicalDottedSet_nonempty E _ hnonneg
    have hKlog : toLogPoint K ≠ 0 := by
      intro h
      apply hzero
      funext i
      have hi := congrFun h i
      change (K i : ℝ) = 0 at hi
      exact Nat.cast_eq_zero.mp hi
    have hKD : toLogPoint K ∈ dottedRegion E D :=
      mem_dottedRegion_canonical E _ hnonneg hKlog
    obtain ⟨L, hL, hLunique⟩ := existsUnique_maximalApex E hD hKD
    let A : MaximalTubeIndex E := ⟨D, hD, L, hL.1⟩
    refine ⟨some A, hL.2, ?_⟩
    intro B hKB
    cases B with
    | none =>
        have : K = 0 := by simpa [paperTubeIndexSet] using hKB
        exact (hzero this).elim
    | some B =>
        have hKBD : toLogPoint K ∈ dottedRegion E B.dotted :=
          mem_dottedRegion_of_mem_maximalTube E B.dotted_nonempty
            B.maximal hKB
        have hDB : B.dotted = D :=
          dottedRegion_index_unique E _ hKBD hKD
        have hBmax : IsMaximalDottedScale E D B.apex := hDB ▸ B.maximal
        have hKB' : K ∈ tubeIndexSet D B.apex := hDB ▸ hKB
        have hBL : B.apex = L :=
          (hLunique B.apex ⟨hBmax, hKB'⟩).trans
            (hLunique L hL).symm
        apply congrArg some
        exact MaximalTubeIndex.ext hDB hBL

/-- The canonical paper tube assigned to a raw full tensor index. -/
def paperTubeIndexOfScale (E : StandardMultiNormMatrix ι)
    (K : ι → ℕ) : FullTubeIndex E :=
  Classical.choose (existsUnique_paperTubeIndex E K)

lemma mem_paperTubeIndexOfScale
    (E : StandardMultiNormMatrix ι) (K : ι → ℕ) :
    K ∈ paperTubeIndexSet (paperTubeIndexOfScale E K) :=
  (Classical.choose_spec (existsUnique_paperTubeIndex E K)).1

lemma paperTubeIndexOfScale_eq_iff
    (E : StandardMultiNormMatrix ι) (K : ι → ℕ) (A : FullTubeIndex E) :
    paperTubeIndexOfScale E K = A ↔ K ∈ paperTubeIndexSet A := by
  constructor
  · rintro rfl
    exact mem_paperTubeIndexOfScale E K
  · intro hA
    exact ((Classical.choose_spec (existsUnique_paperTubeIndex E K)).2 A hA).symm

lemma preimage_paperTubeIndexOfScale_singleton
    (E : StandardMultiNormMatrix ι) (T : FullTubeIndex E) :
    (paperTubeIndexOfScale E) ⁻¹' {T} = paperTubeIndexSet T := by
  ext K
  simp [paperTubeIndexOfScale_eq_iff]

lemma preimage_paperTubeIndexOfScale_finite
    (E : StandardMultiNormMatrix ι) (T : FullTubeIndex E) :
    ((paperTubeIndexOfScale E) ⁻¹' {T}).Finite := by
  rw [preimage_paperTubeIndexOfScale_singleton]
  exact paperTubeIndexSet_finite T

noncomputable instance paperTubeIndexFiberFintype
    (E : StandardMultiNormMatrix ι) (T : FullTubeIndex E) :
    Fintype {K // paperTubeIndexOfScale E K = T} := by
  apply Set.Finite.fintype
  apply (paperTubeIndexSet_finite T).subset
  intro K hK
  exact (paperTubeIndexOfScale_eq_iff E K T).1 hK

noncomputable instance paperTubeIndexPreimageFintype
    (E : StandardMultiNormMatrix ι) (T : FullTubeIndex E) :
    Fintype ((paperTubeIndexOfScale E) ⁻¹' {T}) :=
  (preimage_paperTubeIndexOfScale_finite E T).fintype

/-! ## C. Finite and infinite regrouping -/

open Classical in
/-- Any finite sum over raw tensor indices can be regrouped exactly by the
paper's completed maximal-tube index. -/
lemma sum_regroup_by_paperTubes
    (E : StandardMultiNormMatrix ι) {A : Type*} [AddCommMonoid A]
    (S : Finset (ι → ℕ)) (f : (ι → ℕ) → A) :
    ∑ K ∈ S, f K =
      ∑ T ∈ S.image (paperTubeIndexOfScale E),
        ∑ K ∈ S with paperTubeIndexOfScale E K = T, f K := by
  classical
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun K hK => Finset.mem_image.mpr ⟨K, hK, rfl⟩) f

open Classical in
/-- Fiber membership in the finite regrouping is exactly membership in the
paper's finite tube set. -/
lemma filter_paperTubeIndexOfScale_eq
    (E : StandardMultiNormMatrix ι) (S : Finset (ι → ℕ))
    (T : FullTubeIndex E) :
    S.filter (fun K => paperTubeIndexOfScale E K = T) =
      S ∩ paperTubeIndexFinset T := by
  classical
  ext K
  simp [paperTubeIndexOfScale_eq_iff]

/-- Infinite unconditional sums may be regrouped by the exact paper tubes.
This is the abstract distribution-valued step needed by Proposition 4.3(a). -/
lemma hasSum_regroup_by_paperTubes
    (E : StandardMultiNormMatrix ι)
    {A : Type*} [AddCommGroup A] [UniformSpace A] [IsUniformAddGroup A]
    [CompleteSpace A] [T2Space A] {f : (ι → ℕ) → A} {a : A}
    (hf : HasSum f a) :
    HasSum (fun T : FullTubeIndex E =>
      ∑' K : (paperTubeIndexOfScale E) ⁻¹' {T}, f K) a :=
  hf.tsum_fiberwise (paperTubeIndexOfScale E)

/-- Because every paper tube is finite, the regrouping theorem also applies
in regular topological additive monoids that are not complete.  This is the
form used for Mathlib's tempered-distribution topology. -/
lemma hasSum_regroup_by_finite_paperTubes
    (E : StandardMultiNormMatrix ι)
    {A : Type*} [AddCommMonoid A] [TopologicalSpace A] [ContinuousAdd A]
    [RegularSpace A] {f : (ι → ℕ) → A} {a : A} (hf : HasSum f a) :
    HasSum (fun T : FullTubeIndex E =>
      ∑ K : (paperTubeIndexOfScale E) ⁻¹' {T}, f K) a := by
  let e := Equiv.sigmaFiberEquiv (paperTubeIndexOfScale E)
  apply (e.hasSum_iff.mpr hf).sigma
  intro T
  exact hasSum_fintype _

/-! ## D. Distribution-valued tensor regrouping -/

/-- One full-index dual tensor kernel embedded in the product-space tempered
distributions. -/
def fullTensorDualDetailDistribution {n d m : ℕ} [Nonempty (Fin n)]
    (φ : Fin n → ContDiffBump
      (0 : MultiNormDualCalderon.CoordinateSpace d))
    [(volume : Measure
      (Fin n → MultiNormDualCalderon.CoordinateSpace d)).HasTemperateGrowth]
    (D : ∀ i, MultiNormDualCalderon.DualCalderonFamily (φ i) m)
    (K : Fin n → ℕ) :
    𝓢'(Fin n → MultiNormDualCalderon.CoordinateSpace d, ℂ) :=
  SchwartzMap.toTemperedDistributionCLM
    (Fin n → MultiNormDualCalderon.CoordinateSpace d) ℂ volume
    (fullTensorDualDetailKernel φ D K)

/-- The Proposition 4.3 distribution attached to one paper tube, defined as
the unconditional sum of the raw full-index distributions in its fiber.  The
fiber is finite by `paperTubeIndexSet_finite`. -/
def paperGroupedDualDetailDistribution {n d m : ℕ}
    [Nonempty (Fin n)]
    (E : StandardMultiNormMatrix (Fin n))
    (φ : Fin n → ContDiffBump
      (0 : MultiNormDualCalderon.CoordinateSpace d))
    [(volume : Measure
      (Fin n → MultiNormDualCalderon.CoordinateSpace d)).HasTemperateGrowth]
    (D : ∀ i, MultiNormDualCalderon.DualCalderonFamily (φ i) m)
    (T : FullTubeIndex E) :
    𝓢'(Fin n → MultiNormDualCalderon.CoordinateSpace d, ℂ) :=
  ∑ K : (paperTubeIndexOfScale E) ⁻¹' {T},
    fullTensorDualDetailDistribution φ D K

/-- Proposition 4.3(a), exact regrouping step: once the raw `ℕ^n` tensor
series has the Dirac distribution as its unconditional sum, regrouping it by
the paper's actual completed maximal-tube index preserves that sum. -/
lemma hasSum_paperGroupedDualDetailDistribution_delta {n d m : ℕ}
    [Nonempty (Fin n)]
    (E : StandardMultiNormMatrix (Fin n))
    (φ : Fin n → ContDiffBump
      (0 : MultiNormDualCalderon.CoordinateSpace d))
    [(volume : Measure
      (Fin n → MultiNormDualCalderon.CoordinateSpace d)).HasTemperateGrowth]
    (D : ∀ i, MultiNormDualCalderon.DualCalderonFamily (φ i) m)
    (hraw : HasSum (fullTensorDualDetailDistribution φ D)
      (TemperedDistribution.delta
        (0 : Fin n → MultiNormDualCalderon.CoordinateSpace d))) :
    HasSum (paperGroupedDualDetailDistribution E φ D)
      (TemperedDistribution.delta
        (0 : Fin n → MultiNormDualCalderon.CoordinateSpace d)) :=
  hasSum_regroup_by_finite_paperTubes E hraw

open Classical in
/-- Capstone: the existing Section 3 maximal-tube partition supplies both
the exact finite regrouping and the infinite unconditional regrouping used by
the tensor-product Calderon construction. -/
lemma fullTensorIndex_paperTube_partition_and_regrouping
    (E : StandardMultiNormMatrix ι)
    {A : Type*} [AddCommGroup A] [UniformSpace A] [IsUniformAddGroup A]
    [CompleteSpace A] [T2Space A] (S : Finset (ι → ℕ))
    (f : (ι → ℕ) → A) {a : A} (hf : HasSum f a) :
    (∀ K, ∃! T : FullTubeIndex E, K ∈ paperTubeIndexSet T) ∧
    (∑ K ∈ S, f K =
      ∑ T ∈ S.image (paperTubeIndexOfScale E),
        ∑ K ∈ S with paperTubeIndexOfScale E K = T, f K) ∧
    HasSum (fun T : FullTubeIndex E =>
      ∑' K : (paperTubeIndexOfScale E) ⁻¹' {T}, f K) a :=
  by
    classical
    exact ⟨existsUnique_paperTubeIndex E,
      sum_regroup_by_paperTubes E S f,
      hasSum_regroup_by_paperTubes E hf⟩

end MultiNormTensorRegrouping

end Physlib.Mathematics.HarmonicAnalysis
