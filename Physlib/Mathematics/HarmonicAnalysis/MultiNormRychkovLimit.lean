/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The analytic limit of the constructed Rychkov kernels

This module closes the analytic premise left by the finite construction in
`MultiNormRychkovDual`.  The normalized dyadic kernel has Fourier transform
converging pointwise to one.  The finite Rychkov polynomial is uniformly
bounded, so dominated convergence on the Fourier side proves that the final
approximation, and hence the complete detail series, converges to `δ₀`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Convolution FourierTransform SchwartzMap Topology

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormRychkovLimit

open MultiNormDualCalderon MultiNormMomentDerivative MultiNormRychkovDual
  MultiNormSchwartzKernel MultiNormTemperedCalderon

/-! ## A. Fourier scaling and normalization -/

lemma fourier_complexDyadicApproximationKernel_apply {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (n : ℕ)
    (ξ : CoordinateSpace d) :
    𝓕 (complexDyadicApproximationKernel φ n) ξ =
      𝓕 (complexDyadicApproximationKernel φ 0)
        ((dyadicExpansion n)⁻¹ • ξ) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    Real.fourier_eq, Real.fourier_eq]
  simp_rw [complexDyadicApproximationKernel_apply]
  let c := dyadicExpansion n
  have hc : 0 < c := dyadicExpansion_pos n
  have hchange := Measure.integral_comp_smul_of_nonneg volume
    (fun y : CoordinateSpace d =>
      𝐞 (-inner ℝ y (c⁻¹ • ξ)) •
        ((complexDyadicApproximationKernel φ 0 y) : ℂ)) c (hR := hc.le)
  have hc0 : c ≠ 0 := hc.ne'
  calc
    _ = (c ^ Module.finrank ℝ (CoordinateSpace d) : ℂ) *
        ∫ x, 𝐞 (-inner ℝ x ξ) •
          ((complexDyadicApproximationKernel φ 0 (c • x)) : ℂ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp [c, complexDyadicApproximationKernel_apply, dyadicExpansion,
        Circle.smul_def]
      ring
    _ = (c ^ Module.finrank ℝ (CoordinateSpace d) : ℂ) *
        ∫ x, 𝐞 (-inner ℝ (c • x) (c⁻¹ • ξ)) •
          ((complexDyadicApproximationKernel φ 0 (c • x)) : ℂ) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      simp [inner_smul_left, inner_smul_right, hc0]
    _ = _ := by
      rw [hchange]
      simp [c, hc0]

lemma tendsto_inv_dyadic_smul_zero {d : ℕ}
    (ξ : CoordinateSpace d) :
    Tendsto (fun n : ℕ => (dyadicExpansion n)⁻¹ • ξ) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => dyadicExpansion n) atTop atTop := by
    simpa [dyadicExpansion] using
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  simpa using (tendsto_inv_atTop_zero.comp hpow).smul_const ξ

lemma fourier_complexDyadicApproximationKernel_zero {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (n : ℕ) :
    𝓕 (complexDyadicApproximationKernel φ n) 0 = 1 := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  simp only [inner_zero_right, neg_zero]
  change ∫ v, ((Real.fourierChar 0 : Circle) : ℂ) •
    complexDyadicApproximationKernel φ n v = 1
  rw [AddChar.map_zero_eq_one]
  simp only [Circle.coe_one]
  simp only [one_smul]
  rw [complexDyadicApproximationKernel]
  simp only [SchwartzMap.postcompCLM_apply]
  change ∫ x, Complex.ofReal (dyadicApproximationKernel φ n x) = 1
  have h := Complex.ofRealCLM.integral_comp_comm
    (μ := volume) (dyadicApproximationKernel φ n).integrable
  calc
    _ = Complex.ofRealCLM
        (∫ x, dyadicApproximationKernel φ n x) := h
    _ = 1 := by
      rw [integral_dyadicApproximationKernel φ n]
      rfl

lemma tendsto_fourier_complexDyadicApproximationKernel_one {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d))
    (ξ : CoordinateSpace d) :
    Tendsto (fun n => 𝓕 (complexDyadicApproximationKernel φ n) ξ)
      atTop (𝓝 1) := by
  rw [show (fun n => 𝓕 (complexDyadicApproximationKernel φ n) ξ) =
      (fun n => 𝓕 (complexDyadicApproximationKernel φ 0)
        ((dyadicExpansion n)⁻¹ • ξ)) by
    funext n
    exact fourier_complexDyadicApproximationKernel_apply φ n ξ]
  have h := (𝓕 (complexDyadicApproximationKernel φ 0)).continuous.continuousAt.tendsto.comp
    (tendsto_inv_dyadic_smul_zero ξ)
  rw [fourier_complexDyadicApproximationKernel_zero] at h
  exact h

lemma norm_fourier_complexDyadicApproximationKernel_le_one {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (n : ℕ)
    (ξ : CoordinateSpace d) :
    ‖𝓕 (complexDyadicApproximationKernel φ n) ξ‖ ≤ 1 := by
  refine (SchwartzMap.norm_fourier_apply_le_toLp_one
    (complexDyadicApproximationKernel φ n) ξ).trans_eq ?_
  rw [SchwartzMap.norm_toLp_one]
  calc
    ∫ x, ‖complexDyadicApproximationKernel φ n x‖ =
        ∫ x, dyadicApproximationKernel φ n x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [complexDyadicApproximationKernel]
      simp only [SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply,
        Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg (pow_nonneg (dyadicExpansion_pos n).le _)
        (φ.nonneg_normed _)
    _ = 1 := integral_dyadicApproximationKernel φ n

/-! ## B. The Rychkov multiplier limit -/

lemma tendsto_fourier_dualApproximationConvolution_rychkov_one {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M : ℕ) (hM : 0 < M)
    (ξ : CoordinateSpace d) :
    Tendsto (fun n => 𝓕 (dualApproximationConvolution φ
      (rychkovDualApproximation φ M) n) ξ) atTop (𝓝 1) := by
  let p : ℂ → ℂ := fun z => z * approximationFactor M z
  have hp : Continuous p := by
    unfold p approximationFactor
    fun_prop
  have h := hp.continuousAt.tendsto.comp
    (tendsto_fourier_complexDyadicApproximationKernel_one φ ξ)
  have hM0 : M ≠ 0 := Nat.ne_of_gt hM
  rw [show p 1 = 1 by simp [p, mul_approximationFactor, hM0]] at h
  convert h using 1
  funext n
  exact fourier_dualApproximationConvolution_rychkov_apply φ M n ξ

lemma norm_fourier_dualApproximationConvolution_rychkov_le {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M n : ℕ)
    (ξ : CoordinateSpace d) :
    ‖𝓕 (dualApproximationConvolution φ
      (rychkovDualApproximation φ M) n) ξ‖ ≤ 1 + 2 ^ M := by
  rw [fourier_dualApproximationConvolution_rychkov_apply,
    mul_approximationFactor]
  let z := 𝓕 (complexDyadicApproximationKernel φ n) ξ
  have hz : ‖z‖ ≤ 1 :=
    norm_fourier_complexDyadicApproximationKernel_le_one φ n ξ
  calc
    ‖1 - (1 - z ^ 2) ^ M‖ ≤ ‖(1 : ℂ)‖ + ‖(1 - z ^ 2) ^ M‖ :=
      norm_sub_le _ _
    _ = 1 + ‖1 - z ^ 2‖ ^ M := by simp [norm_pow]
    _ ≤ 1 + 2 ^ M := by
      gcongr
      calc
        ‖1 - z ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2‖ := norm_sub_le _ _
        _ ≤ 2 := by
          rw [norm_one, norm_pow]
          nlinarith [mul_self_le_mul_self (norm_nonneg z) hz]

lemma integral_fourierInv_eq_eval_zero {d : ℕ}
    (g : 𝓢(CoordinateSpace d, ℂ)) :
    ∫ ξ, 𝓕⁻ g ξ = g 0 := by
  have heq : 𝓕 (𝓕⁻ g) = g := FourierTransform.fourier_fourierInv_eq g
  have h := congrArg (fun f : 𝓢(CoordinateSpace d, ℂ) =>
    f (0 : CoordinateSpace d)) heq
  rw [SchwartzMap.fourier_coe, Real.fourier_eq] at h
  simp only [inner_zero_right, neg_zero] at h
  change (∫ v, ((Real.fourierChar 0 : Circle) : ℂ) • 𝓕⁻ g v) = g 0 at h
  rw [AddChar.map_zero_eq_one] at h
  simpa only [Circle.coe_one, one_smul] using h

/-! ## C. Unconditional distributional Calderón limits -/

/-- The constructed final Rychkov approximation converges to `δ₀`; no
external analytic limit certificate is required. -/
lemma tendsto_rychkovDualApproximation_delta {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M : ℕ) (hM : 0 < M) :
    Tendsto (dualApproximationDistribution φ
      (rychkovDualApproximation φ M)) atTop
      (𝓝 (TemperedDistribution.delta (0 : CoordinateSpace d))) := by
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.2
  intro g
  let K : ℕ → 𝓢(CoordinateSpace d, ℂ) := fun n =>
    dualApproximationConvolution φ (rychkovDualApproximation φ M) n
  let h : 𝓢(CoordinateSpace d, ℂ) := 𝓕⁻ g
  have hpair (n : ℕ) :
      ∫ x, g x * K n x = ∫ ξ, 𝓕 (K n) ξ * h ξ := by
    calc
      _ = ∫ x, K n x * g x := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = ∫ x, K n x * 𝓕 h x := by
        rw [show 𝓕 h = g by simp [h]]
      _ = _ := (SchwartzMap.integral_fourier_mul_eq (K n) h).symm
  change Tendsto (fun n => ∫ x, g x * K n x) atTop (𝓝 (g 0))
  rw [show (fun n => ∫ x, g x * K n x) =
      (fun n => ∫ ξ, 𝓕 (K n) ξ * h ξ) by
    funext n
    exact hpair n]
  have hdom : Tendsto (fun n => ∫ ξ, 𝓕 (K n) ξ * h ξ) atTop
      (𝓝 (∫ ξ, h ξ)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun ξ => (1 + 2 ^ M) * ‖h ξ‖)
    · exact Filter.Eventually.of_forall fun n =>
        ((𝓕 (K n)).continuous.mul h.continuous).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun n =>
        Filter.Eventually.of_forall fun ξ => by
          rw [norm_mul]
          gcongr
          exact norm_fourier_dualApproximationConvolution_rychkov_le φ M n ξ
    · exact h.integrable.norm.const_mul (1 + 2 ^ M)
    · exact Filter.Eventually.of_forall fun ξ => by
        simpa using
          (tendsto_fourier_dualApproximationConvolution_rychkov_one
            φ M hM ξ).mul_const (h ξ)
  rw [integral_fourierInv_eq_eval_zero g] at hdom
  exact hdom

/-- The full constructed detail series converges to `δ₀` as a consequence
of the exact finite telescope and the now-proved final approximation limit. -/
lemma tendsto_rychkovDualCalderon_delta {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M : ℕ) (hM : 0 < M) :
    Tendsto (dualCalderonPartialDistribution φ
      (rychkovDualDetail φ M)) atTop
      (𝓝 (TemperedDistribution.delta (0 : CoordinateSpace d))) :=
  tendsto_rychkovDualCalderon_of_approximation φ M
    (tendsto_rychkovDualApproximation_delta φ M hM)

/-! ## D. Intermediate analytic packaging -/

/-- Intermediate compatibility package for the analytic clauses.  The
downstream estimates module now constructs every field for the explicit
Rychkov family; the finite identity and both distributional limits are
already theorems here. -/
structure RychkovAnalyticCertificate {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (m : ℕ) where
  spatialCarrier : ℕ → Set (CoordinateSpace d)
  normalized_approximation :
    NormalizedRelative
      (unscaledDyadicFamily (complexDyadicApproximationKernel φ))
      (unscaledDyadicFamily (rychkovDualApproximation φ (m + 1)))
  normalized_detail :
    NormalizedRelative
      (unscaledDyadicFamily (complexDyadicApproximationKernel φ))
      (unscaledDyadicFamily (rychkovDualDetail φ (m + 1)))
  cancellation : ∀ ell : ℕ, 0 < ell →
    HasCancellationOrder (rychkovDualDetail φ (m + 1) ell) m
  spatial_approximation_support : ∀ ell,
    tsupport (rychkovDualApproximation φ (m + 1) ell) ⊆ spatialCarrier ell
  spatial_detail_support : ∀ ell,
    tsupport (rychkovDualDetail φ (m + 1) ell) ⊆ spatialCarrier ell

/-- Package the constructed kernels and all proved identities as the
repository's existing `DualCalderonFamily`. -/
def RychkovAnalyticCertificate.toDualCalderonFamily {d m : ℕ}
    {φ : ContDiffBump (0 : CoordinateSpace d)}
    (C : RychkovAnalyticCertificate φ m) : DualCalderonFamily φ m where
  dualApproximation := rychkovDualApproximation φ (m + 1)
  dualDetail := rychkovDualDetail φ (m + 1)
  fourierApproximationCarrier := rychkovFourierApproximationCarrier φ
  fourierDetailCarrier := rychkovFourierDetailCarrier φ
  spatialCarrier := C.spatialCarrier
  normalized_approximation := C.normalized_approximation
  normalized_detail := C.normalized_detail
  detail_zero := rychkovDualDetail_zero φ (m + 1)
  cancellation := C.cancellation
  fourier_approximation_support :=
    fourier_rychkovDualApproximation_support φ (m + 1)
  fourier_detail_support := fourier_rychkovDualDetail_support φ (m + 1)
  spatial_approximation_support := C.spatial_approximation_support
  spatial_detail_support := C.spatial_detail_support
  partial_kernel_identity := rychkov_partial_kernel_identity φ (m + 1)
  full_identity := tendsto_rychkovDualCalderon_delta φ (m + 1) (Nat.succ_pos m)

/-- Capstone for the constructive part of Lemma 4.2: the finite and full
Calderón identities are proved for the explicit inverse-Fourier kernels. -/
lemma constructedRychkovDualCalderon_partial_full {d m : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d))
    (_C : RychkovAnalyticCertificate φ m) :
    (∀ N, (∑ ell ∈ Finset.range (N + 1),
      dualDetailConvolution φ (rychkovDualDetail φ (m + 1)) ell) =
        dualApproximationConvolution φ
          (rychkovDualApproximation φ (m + 1)) N) ∧
    Tendsto (dualCalderonPartialDistribution φ
      (rychkovDualDetail φ (m + 1))) atTop
      (𝓝 (TemperedDistribution.delta (0 : CoordinateSpace d))) :=
  ⟨rychkov_partial_kernel_identity φ (m + 1),
    tendsto_rychkovDualCalderon_delta φ (m + 1) (Nat.succ_pos m)⟩

end MultiNormRychkovLimit

/-! ## E. Source-compatible names for the original construction module -/

namespace MultiNormRychkovDual

open Filter MultiNormDualCalderon MultiNormTemperedCalderon
open scoped BigOperators Topology

/-- Compatibility name for the reduced certificate, whose limit field has
been eliminated. -/
abbrev RychkovAnalyticCertificate {d : ℕ}
    (φ : ContDiffBump (0 : MultiNormDualCalderon.CoordinateSpace d))
    (m : ℕ) := MultiNormRychkovLimit.RychkovAnalyticCertificate φ m

/-- Compatibility wrapper for clients of the earlier module namespace. -/
def RychkovAnalyticCertificate.toDualCalderonFamily {d m : ℕ}
    {φ : ContDiffBump (0 : MultiNormDualCalderon.CoordinateSpace d)}
    (C : RychkovAnalyticCertificate φ m) :
    MultiNormDualCalderon.DualCalderonFamily φ m :=
  MultiNormRychkovLimit.RychkovAnalyticCertificate.toDualCalderonFamily C

/-- Compatibility wrapper for the constructive Lemma 4.2 capstone. -/
lemma constructedRychkovDualCalderon_partial_full {d m : ℕ}
    (φ : ContDiffBump (0 : MultiNormDualCalderon.CoordinateSpace d))
    (C : RychkovAnalyticCertificate φ m) :
    (∀ N, (∑ ell ∈ Finset.range (N + 1),
      dualDetailConvolution φ (rychkovDualDetail φ (m + 1)) ell) =
        dualApproximationConvolution φ
          (rychkovDualApproximation φ (m + 1)) N) ∧
    Tendsto (dualCalderonPartialDistribution φ
      (rychkovDualDetail φ (m + 1))) atTop
      (𝓝 (TemperedDistribution.delta
        (0 : MultiNormDualCalderon.CoordinateSpace d))) :=
  MultiNormRychkovLimit.constructedRychkovDualCalderon_partial_full φ C

end MultiNormRychkovDual

end Physlib.Mathematics.HarmonicAnalysis
