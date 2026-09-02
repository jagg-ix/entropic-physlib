/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSupport
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovCancellation

/-!
# Quantitative estimates for the constructed Rychkov family

This module closes the remaining analytic clauses of Lemma 4.2 for the
concrete Rychkov polynomials.  It proves paper-faithful normalization before
external dyadic dilation, arbitrary positive-level moment cancellation, and
one uniform explicit physical-space carrier for both dual families.  The
resulting `DualCalderonFamily` is constructed without external premises.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap Topology

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormRychkovEstimates

open MultiNormDualCalderon MultiNormMomentDerivative MultiNormRychkovCancellation
  MultiNormRychkovDual MultiNormRychkovLimit MultiNormRychkovSupport
  MultiNormSchwartzKernel MultiNormTemperedCalderon

/-! ## A. The unscaled paper templates -/

lemma inv_dyadicExpansion_smul_dyadicExpansion_smul {d ell : ℕ}
    (ξ : CoordinateSpace d) :
    (dyadicExpansion ell)⁻¹ • (dyadicExpansion ell • ξ) = ξ := by
  rw [smul_smul]
  simp [(dyadicExpansion_pos ell).ne']

lemma inv_dyadicExpansion_smul_dyadicExpansion_succ_smul {d ell : ℕ}
    (ξ : CoordinateSpace d) :
    (dyadicExpansion ell)⁻¹ • (dyadicExpansion (ell + 1) • ξ) =
      dyadicExpansion 1 • ξ := by
  rw [smul_smul]
  congr 1
  simp [dyadicExpansion, pow_succ]

/-- Undoing the external dilation of the original approximation family
recovers the constant bump template used by this repository's specialization
of the paper. -/
lemma unscaled_complexDyadicApproximationKernel_eq {d ell : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) :
    unscaledDyadicFamily (complexDyadicApproximationKernel φ) ell =
      complexDyadicApproximationKernel φ 0 := by
  apply (FourierTransform.fourierCLE ℂ
    𝓢(CoordinateSpace d, ℂ)).injective
  change 𝓕 (paperDyadicUndilation
    (complexDyadicApproximationKernel φ ell) ell) =
      𝓕 (complexDyadicApproximationKernel φ 0)
  rw [fourier_paperDyadicUndilation]
  ext ξ
  change 𝓕 (complexDyadicApproximationKernel φ ell)
    (dyadicExpansion ell • ξ) =
      𝓕 (complexDyadicApproximationKernel φ 0) ξ
  rw [fourier_complexDyadicApproximationKernel_apply,
    inv_dyadicExpansion_smul_dyadicExpansion_smul]

/-- The constructed tilded approximation family is likewise one unscaled
template followed by the paper's external dyadic dilation. -/
lemma unscaled_rychkovDualApproximation_eq {d M ell : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) :
    unscaledDyadicFamily (rychkovDualApproximation φ M) ell =
      rychkovDualApproximation φ M 0 := by
  apply (FourierTransform.fourierCLE ℂ
    𝓢(CoordinateSpace d, ℂ)).injective
  change 𝓕 (paperDyadicUndilation
    (rychkovDualApproximation φ M ell) ell) =
      𝓕 (rychkovDualApproximation φ M 0)
  rw [fourier_paperDyadicUndilation, fourier_rychkovDualApproximation,
    fourier_rychkovDualApproximation]
  ext ξ
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, approximationFrequencyFactor_apply]
  rw [dyadicExpansionCLE_apply]
  rw [fourier_complexDyadicApproximationKernel_apply,
    inv_dyadicExpansion_smul_dyadicExpansion_smul]

/-- All positive tilded detail levels have the same unscaled template. -/
lemma unscaled_rychkovDualDetail_succ_eq {d M ell : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) :
    unscaledDyadicFamily (rychkovDualDetail φ M) (ell + 1) =
      unscaledDyadicFamily (rychkovDualDetail φ M) 1 := by
  apply (FourierTransform.fourierCLE ℂ
    𝓢(CoordinateSpace d, ℂ)).injective
  change 𝓕 (paperDyadicUndilation
    (rychkovDualDetail φ M (ell + 1)) (ell + 1)) =
      𝓕 (paperDyadicUndilation (rychkovDualDetail φ M 1) 1)
  rw [fourier_paperDyadicUndilation, fourier_paperDyadicUndilation,
    fourier_rychkovDualDetail_succ, fourier_rychkovDualDetail_succ]
  ext ξ
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, detailFrequencyFactor_apply]
  simp only [dyadicExpansionCLE_apply]
  rw [fourier_complexDyadicApproximationKernel_apply φ ell,
    fourier_complexDyadicApproximationKernel_apply φ (ell + 1),
    fourier_complexDyadicApproximationKernel_apply φ 1,
    inv_dyadicExpansion_smul_dyadicExpansion_succ_smul,
    inv_dyadicExpansion_smul_dyadicExpansion_smul,
    inv_dyadicExpansion_smul_dyadicExpansion_smul]

/-! ## B. Relative normalization from the fixed reference template -/

lemma complexDyadicApproximationKernel_zero_ne {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) :
    complexDyadicApproximationKernel φ 0 ≠ 0 := by
  intro hzero
  have hmass := fourier_complexDyadicApproximationKernel_zero φ 0
  rw [hzero] at hmass
  simp at hmass

lemma seminorm_zero_zero_pos_of_ne_zero {d : ℕ}
    (f : 𝓢(CoordinateSpace d, ℂ)) (hf : f ≠ 0) :
    0 < SchwartzMap.seminorm ℂ 0 0 f := by
  refine lt_of_le_of_ne (by positivity) ?_
  intro h
  apply hf
  ext x
  apply norm_eq_zero.mp
  have hx : ‖f x‖ ≤ 0 := by
    simpa [h.symm] using SchwartzMap.norm_le_seminorm ℂ f x
  exact le_antisymm hx (norm_nonneg _)

lemma normalizedRelative_constant {d : ℕ}
    (reference candidate : 𝓢(CoordinateSpace d, ℂ))
    (href : reference ≠ 0) :
    NormalizedRelative (fun _ => reference) (fun _ => candidate) := by
  intro k n
  let r := SchwartzMap.seminorm ℂ 0 0 reference
  let p := SchwartzMap.seminorm ℂ k n candidate
  have hr : 0 < r := seminorm_zero_zero_pos_of_ne_zero reference href
  refine ⟨p / r, div_nonneg (by positivity) hr.le, 0, 0, ?_⟩
  intro ell
  change p ≤ p / r * r
  rw [div_mul_cancel₀ p hr.ne']

lemma normalizedRelative_zero_succ_constant {d : ℕ}
    (reference zeroTemplate positiveTemplate :
      𝓢(CoordinateSpace d, ℂ)) (href : reference ≠ 0) :
    NormalizedRelative (fun _ => reference)
      (fun ell => match ell with
        | 0 => zeroTemplate
        | _ + 1 => positiveTemplate) := by
  intro k n
  let r := SchwartzMap.seminorm ℂ 0 0 reference
  let p₀ := SchwartzMap.seminorm ℂ k n zeroTemplate
  let p₁ := SchwartzMap.seminorm ℂ k n positiveTemplate
  let p := max p₀ p₁
  have hr : 0 < r := seminorm_zero_zero_pos_of_ne_zero reference href
  refine ⟨p / r, div_nonneg (by positivity) hr.le, 0, 0, ?_⟩
  intro ell
  have hp : p / r * r = p := div_mul_cancel₀ p hr.ne'
  rw [hp]
  cases ell with
  | zero => exact le_max_left _ _
  | succ ell => exact le_max_right _ _

/-- Lemma 4.2(a), first family: the unscaled tilded approximation templates
are normalized relative to the original unscaled approximation templates. -/
lemma rychkovDualApproximation_normalizedRelative {d M : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) :
    NormalizedRelative
      (unscaledDyadicFamily (complexDyadicApproximationKernel φ))
      (unscaledDyadicFamily (rychkovDualApproximation φ M)) := by
  rw [show unscaledDyadicFamily (complexDyadicApproximationKernel φ) =
      (fun _ => complexDyadicApproximationKernel φ 0) by
        funext ell
        exact unscaled_complexDyadicApproximationKernel_eq φ,
    show unscaledDyadicFamily (rychkovDualApproximation φ M) =
      (fun _ => rychkovDualApproximation φ M 0) by
        funext ell
        exact unscaled_rychkovDualApproximation_eq φ]
  exact normalizedRelative_constant _ _
    (complexDyadicApproximationKernel_zero_ne φ)

/-- The whole tilded detail family has one level-zero template and one common
positive-level template after the external dilation is removed. -/
lemma unscaled_rychkovDualDetail_eq_zero_succ {d M : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) :
    unscaledDyadicFamily (rychkovDualDetail φ M) =
      (fun ell => match ell with
        | 0 => rychkovDualApproximation φ M 0
        | _ + 1 => unscaledDyadicFamily (rychkovDualDetail φ M) 1) := by
  funext ell
  cases ell with
  | zero =>
      change paperDyadicUndilation (rychkovDualDetail φ M 0) 0 =
        rychkovDualApproximation φ M 0
      rw [rychkovDualDetail_zero]
      exact unscaled_rychkovDualApproximation_eq φ
  | succ ell => exact unscaled_rychkovDualDetail_succ_eq φ

/-- Lemma 4.2(a), second family: the unscaled tilded detail templates are
normalized relative to the same original approximation family—not relative
to the already-scaled detail kernels. -/
lemma rychkovDualDetail_normalizedRelative {d M : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) :
    NormalizedRelative
      (unscaledDyadicFamily (complexDyadicApproximationKernel φ))
      (unscaledDyadicFamily (rychkovDualDetail φ M)) := by
  rw [show unscaledDyadicFamily (complexDyadicApproximationKernel φ) =
      (fun _ => complexDyadicApproximationKernel φ 0) by
        funext ell
        exact unscaled_complexDyadicApproximationKernel_eq φ,
    unscaled_rychkovDualDetail_eq_zero_succ φ]
  exact normalizedRelative_zero_succ_constant _ _ _
    (complexDyadicApproximationKernel_zero_ne φ)

/-- Compatibility package for the two normalization clauses.  Both fields
are now filled by `constructedRychkovNormalizationCertificate`. -/
structure RychkovNormalizationCertificate {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (m : ℕ) where
  normalized_approximation :
    NormalizedRelative
      (unscaledDyadicFamily (complexDyadicApproximationKernel φ))
      (unscaledDyadicFamily (rychkovDualApproximation φ (m + 1)))
  normalized_detail :
    NormalizedRelative
      (unscaledDyadicFamily (complexDyadicApproximationKernel φ))
      (unscaledDyadicFamily (rychkovDualDetail φ (m + 1)))

/-- Upgrade the two normalization estimates to the previous analytic
certificate.  Cancellation and both spatial support fields are theorems. -/
def RychkovNormalizationCertificate.toAnalyticCertificate {d m : ℕ}
    {φ : ContDiffBump (0 : CoordinateSpace d)}
    (C : RychkovNormalizationCertificate φ m) :
    MultiNormRychkovLimit.RychkovAnalyticCertificate φ m where
  spatialCarrier := fun _ => rychkovSpatialCarrier φ (m + 1)
  normalized_approximation := C.normalized_approximation
  normalized_detail := C.normalized_detail
  cancellation := fun ell hell =>
    rychkovDualDetail_hasCancellationOrder (m := m) (ell := ell) φ hell
  spatial_approximation_support :=
    rychkovDualApproximation_tsupport_subset_spatialCarrier φ (m + 1)
  spatial_detail_support :=
    rychkovDualDetail_tsupport_subset_spatialCarrier φ (m + 1)

/-- Package the constructed family using only the two remaining normalization
estimates. -/
def RychkovNormalizationCertificate.toDualCalderonFamily {d m : ℕ}
    {φ : ContDiffBump (0 : CoordinateSpace d)}
    (C : RychkovNormalizationCertificate φ m) : DualCalderonFamily φ m :=
  C.toAnalyticCertificate.toDualCalderonFamily

/-- The formerly external normalization certificate is now constructed for
the explicit Rychkov family. -/
def constructedRychkovNormalizationCertificate {d m : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) :
    RychkovNormalizationCertificate φ m where
  normalized_approximation :=
    rychkovDualApproximation_normalizedRelative φ
  normalized_detail := rychkovDualDetail_normalizedRelative φ

/-- Fully constructed Lemma 4.2 family: no analytic certificate remains to be
supplied by downstream clients. -/
def constructedRychkovDualCalderonFamily {d m : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) :
    DualCalderonFamily φ m :=
  (constructedRychkovNormalizationCertificate φ).toDualCalderonFamily

/-- Paper-faithful normalization and the generic scaling bridge are exposed
together for downstream tensor-product constructions. -/
lemma constructedRychkovDual_normalization_scaling {d m : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) :
    NormalizedRelative
      (unscaledDyadicFamily (complexDyadicApproximationKernel φ))
      (unscaledDyadicFamily (rychkovDualApproximation φ (m + 1))) ∧
    NormalizedRelative
      (unscaledDyadicFamily (complexDyadicApproximationKernel φ))
      (unscaledDyadicFamily (rychkovDualDetail φ (m + 1))) ∧
    (∀ ell, paperDyadicDilation
      (unscaledDyadicFamily (rychkovDualApproximation φ (m + 1)) ell) ell =
        rychkovDualApproximation φ (m + 1) ell) ∧
    (∀ ell, paperDyadicDilation
      (unscaledDyadicFamily (rychkovDualDetail φ (m + 1)) ell) ell =
        rychkovDualDetail φ (m + 1) ell) := by
  exact ⟨rychkovDualApproximation_normalizedRelative φ,
    rychkovDualDetail_normalizedRelative φ,
    paperDyadicDilation_unscaledDyadicFamily _,
    paperDyadicDilation_unscaledDyadicFamily _⟩

/-- The three newly unconditional clauses, exposed without any certificate. -/
lemma constructedRychkovDual_cancellation_uniformSpatialSupport {d m : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) :
    (∀ ell : ℕ, 0 < ell →
      HasCancellationOrder (rychkovDualDetail φ (m + 1) ell) m) ∧
    (∀ ell, tsupport (rychkovDualApproximation φ (m + 1) ell) ⊆
      rychkovSpatialCarrier φ (m + 1)) ∧
    (∀ ell, tsupport (rychkovDualDetail φ (m + 1) ell) ⊆
      rychkovSpatialCarrier φ (m + 1)) := by
  exact ⟨fun ell hell =>
      rychkovDualDetail_hasCancellationOrder (m := m) (ell := ell) φ hell,
    rychkovDualApproximation_tsupport_subset_spatialCarrier φ (m + 1),
    rychkovDualDetail_tsupport_subset_spatialCarrier φ (m + 1)⟩

end MultiNormRychkovEstimates

end Physlib.Mathematics.HarmonicAnalysis
