/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon
public import Mathlib.Algebra.Ring.GeomSum

/-!
# The finite Rychkov dual-kernel construction

This module formalizes the finite polynomial identities in equations (4.2)
and (4.3) of Hejna--Nagel--Ricci.  It constructs the tilded Schwartz kernels
with Mathlib's Fourier equivalence and temperate-growth multiplier API, and
proves the finite Calderon identity without introducing a second Fourier or
convolution implementation.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Convolution FourierTransform SchwartzMap Topology

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormRychkovDual

open MultiNormDualCalderon MultiNormMomentDerivative MultiNormSchwartzKernel
  MultiNormTemperedCalderon

/-! ## A. The polynomial identity behind the construction -/

/-- The truncated factor multiplying the low-frequency Fourier kernel in
Rychkov's construction. -/
def approximationFactor {R : Type*} [CommRing R] (M : ℕ) (ν : R) : R :=
  ν * ∑ k ∈ Finset.range M, (1 - ν ^ 2) ^ k

/-- The truncated factor multiplying a consecutive Fourier difference. -/
def detailFactor {R : Type*} [CommRing R]
    (M : ℕ) (previous current : R) : R :=
  (current + previous) *
    ∑ k ∈ Finset.range M,
      (1 - previous ^ 2) ^ k * (1 - current ^ 2) ^ (M - 1 - k)

/-- Multiplying the approximation factor by its original kernel leaves the
order-`M` residual appearing in equation (4.3). -/
lemma mul_approximationFactor {R : Type*} [CommRing R]
    (M : ℕ) (ν : R) :
    ν * approximationFactor M ν = 1 - (1 - ν ^ 2) ^ M := by
  rw [approximationFactor, ← mul_assoc, ← pow_two]
  calc
    ν ^ 2 * ∑ k ∈ Finset.range M, (1 - ν ^ 2) ^ k =
        (∑ k ∈ Finset.range M, (1 - ν ^ 2) ^ k) *
          (1 - (1 - ν ^ 2)) := by ring
    _ = 1 - (1 - ν ^ 2) ^ M := geom_sum_mul_neg (1 - ν ^ 2) M

/-- A consecutive difference times its dual factor is the difference of the
two order-`M` residuals. -/
lemma sub_mul_detailFactor {R : Type*} [CommRing R]
    (M : ℕ) (previous current : R) :
    (current - previous) * detailFactor M previous current =
      (1 - previous ^ 2) ^ M - (1 - current ^ 2) ^ M := by
  rw [detailFactor]
  have hdiff :
      (current - previous) * (current + previous) =
        (1 - previous ^ 2) - (1 - current ^ 2) := by ring
  rw [← mul_assoc]
  calc
    (current - previous) * (current + previous) *
        ∑ k ∈ Finset.range M,
          (1 - previous ^ 2) ^ k * (1 - current ^ 2) ^ (M - 1 - k) =
      ((1 - previous ^ 2) - (1 - current ^ 2)) *
        ∑ k ∈ Finset.range M,
          (1 - previous ^ 2) ^ k * (1 - current ^ 2) ^ (M - 1 - k) := by
        rw [hdiff]
    _ = (1 - previous ^ 2) ^ M - (1 - current ^ 2) ^ M :=
      (Commute.all (1 - previous ^ 2) (1 - current ^ 2)).mul_geom_sum₂ M

/-- The level-zero term and positive consecutive differences used in the
finite Rychkov telescope. -/
def rychkovProductTerm {R : Type*} [CommRing R]
    (M : ℕ) (ν : ℕ → R) : ℕ → R
  | 0 => ν 0 * approximationFactor M (ν 0)
  | ell + 1 => (ν (ell + 1) - ν ell) * detailFactor M (ν ell) (ν (ell + 1))

/-- Equation (4.3), finite form: the Rychkov products telescope exactly to
the low-frequency product at the last level. -/
lemma sum_rychkovProductTerm {R : Type*} [CommRing R]
    (M : ℕ) (ν : ℕ → R) (N : ℕ) :
    ∑ ell ∈ Finset.range (N + 1), rychkovProductTerm M ν ell =
      ν N * approximationFactor M (ν N) := by
  induction N with
  | zero => simp [rychkovProductTerm]
  | succ N ih =>
      rw [show N + 1 + 1 = (N + 1) + 1 by omega,
        Finset.sum_range_succ, ih]
      rw [rychkovProductTerm, sub_mul_detailFactor, mul_approximationFactor,
        mul_approximationFactor]
      ring

/-! ## B. Bundled Schwartz Fourier factors -/

/-- The pointwise truncated geometric multiplier. -/
def approximationMultiplier {d : ℕ}
    (M : ℕ) (ν : 𝓢(CoordinateSpace d, ℂ)) : CoordinateSpace d → ℂ :=
  fun ξ => ∑ k ∈ Finset.range M, (1 - ν ξ ^ 2) ^ k

lemma approximationMultiplier_hasTemperateGrowth {d : ℕ}
    (M : ℕ) (ν : 𝓢(CoordinateSpace d, ℂ)) :
    (approximationMultiplier M ν).HasTemperateGrowth := by
  unfold approximationMultiplier
  fun_prop

/-- The pointwise two-residual multiplier. -/
def detailMultiplier {d : ℕ} (M : ℕ)
    (previous current : 𝓢(CoordinateSpace d, ℂ)) : CoordinateSpace d → ℂ :=
  fun ξ => ∑ k ∈ Finset.range M,
    (1 - previous ξ ^ 2) ^ k *
      (1 - current ξ ^ 2) ^ (M - 1 - k)

lemma detailMultiplier_hasTemperateGrowth {d : ℕ} (M : ℕ)
    (previous current : 𝓢(CoordinateSpace d, ℂ)) :
    (detailMultiplier M previous current).HasTemperateGrowth := by
  unfold detailMultiplier
  fun_prop

/-- The bundled Fourier-side approximation factor from equation (4.2). -/
def approximationFrequencyFactor {d : ℕ} (M : ℕ)
    (ν : 𝓢(CoordinateSpace d, ℂ)) : 𝓢(CoordinateSpace d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (approximationMultiplier M ν) ν

@[simp]
lemma approximationFrequencyFactor_apply {d : ℕ} (M : ℕ)
    (ν : 𝓢(CoordinateSpace d, ℂ)) (ξ : CoordinateSpace d) :
    approximationFrequencyFactor M ν ξ = approximationFactor M (ν ξ) := by
  rw [approximationFrequencyFactor,
    SchwartzMap.smulLeftCLM_apply_apply
      (approximationMultiplier_hasTemperateGrowth M ν)]
  simp [approximationMultiplier, approximationFactor, smul_eq_mul, mul_comm]

/-- The bundled Fourier-side detail factor from equation (4.2). -/
def detailFrequencyFactor {d : ℕ} (M : ℕ)
    (previous current : 𝓢(CoordinateSpace d, ℂ)) :
    𝓢(CoordinateSpace d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (detailMultiplier M previous current)
    (current + previous)

@[simp]
lemma detailFrequencyFactor_apply {d : ℕ} (M : ℕ)
    (previous current : 𝓢(CoordinateSpace d, ℂ)) (ξ : CoordinateSpace d) :
    detailFrequencyFactor M previous current ξ =
      detailFactor M (previous ξ) (current ξ) := by
  rw [detailFrequencyFactor,
    SchwartzMap.smulLeftCLM_apply_apply
      (detailMultiplier_hasTemperateGrowth M previous current)]
  simp [detailMultiplier, detailFactor, smul_eq_mul, mul_comm]

/-! ## C. Constructed tilded dyadic families -/

/-- The constructed tilded low-frequency kernel at level `ell`. -/
def rychkovDualApproximation {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    𝓢(CoordinateSpace d, ℂ) :=
  𝓕⁻ (approximationFrequencyFactor M
    (𝓕 (complexDyadicApproximationKernel φ ell)))

/-- The constructed tilded detail kernel.  Level zero agrees definitionally
with the tilded low-frequency kernel. -/
def rychkovDualDetail {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M : ℕ) :
    ℕ → 𝓢(CoordinateSpace d, ℂ)
  | 0 => rychkovDualApproximation φ M 0
  | ell + 1 => 𝓕⁻ (detailFrequencyFactor M
      (𝓕 (complexDyadicApproximationKernel φ ell))
      (𝓕 (complexDyadicApproximationKernel φ (ell + 1))))

@[simp]
lemma rychkovDualDetail_zero {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M : ℕ) :
    rychkovDualDetail φ M 0 = rychkovDualApproximation φ M 0 := rfl

@[simp]
lemma fourier_rychkovDualApproximation {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    𝓕 (rychkovDualApproximation φ M ell) =
      approximationFrequencyFactor M
        (𝓕 (complexDyadicApproximationKernel φ ell)) := by
  simp [rychkovDualApproximation]

@[simp]
lemma fourier_rychkovDualDetail_succ {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    𝓕 (rychkovDualDetail φ M (ell + 1)) =
      detailFrequencyFactor M
        (𝓕 (complexDyadicApproximationKernel φ ell))
        (𝓕 (complexDyadicApproximationKernel φ (ell + 1))) := by
  simp [rychkovDualDetail]

/-! ## D. The actual finite convolutional Calderon identity -/

lemma complexDyadicDetailKernel_zero {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) :
    complexDyadicDetailKernel φ 0 = complexDyadicApproximationKernel φ 0 := by
  simp [complexDyadicDetailKernel, complexDyadicApproximationKernel]

lemma complexDyadicDetailKernel_succ {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (ell : ℕ) :
    complexDyadicDetailKernel φ (ell + 1) =
      complexDyadicApproximationKernel φ (ell + 1) -
        complexDyadicApproximationKernel φ ell := by
  simp [complexDyadicDetailKernel, complexDyadicApproximationKernel]

/-- Each Fourier-transformed convolution term is exactly the corresponding
term of the abstract Rychkov polynomial telescope. -/
lemma fourier_dualDetailConvolution_rychkov_apply {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ)
    (ξ : CoordinateSpace d) :
    𝓕 (dualDetailConvolution φ (rychkovDualDetail φ M) ell) ξ =
      rychkovProductTerm M
        (fun j => 𝓕 (complexDyadicApproximationKernel φ j) ξ) ell := by
  cases ell with
  | zero =>
      rw [dualDetailConvolution, SchwartzMap.fourier_convolution,
        SchwartzMap.pairing_apply_apply, complexDyadicDetailKernel_zero,
        rychkovDualDetail_zero, fourier_rychkovDualApproximation]
      simp [rychkovProductTerm, approximationFrequencyFactor_apply]
  | succ ell =>
      rw [dualDetailConvolution, SchwartzMap.fourier_convolution,
        SchwartzMap.pairing_apply_apply, complexDyadicDetailKernel_succ,
        fourier_rychkovDualDetail_succ]
      simp only [sub_eq_add_neg, FourierTransform.fourier_add,
        FourierTransform.fourier_neg]
      simp [rychkovProductTerm, detailFrequencyFactor_apply]
      ring

/-- The Fourier transform of the constructed low-frequency convolution is
the final approximation product in the abstract telescope. -/
lemma fourier_dualApproximationConvolution_rychkov_apply {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ)
    (ξ : CoordinateSpace d) :
    𝓕 (dualApproximationConvolution φ
      (rychkovDualApproximation φ M) ell) ξ =
      𝓕 (complexDyadicApproximationKernel φ ell) ξ *
        approximationFactor M
          (𝓕 (complexDyadicApproximationKernel φ ell) ξ) := by
  rw [dualApproximationConvolution, SchwartzMap.fourier_convolution,
    SchwartzMap.pairing_apply_apply, fourier_rychkovDualApproximation]
  simp [approximationFrequencyFactor_apply]

/-- Lemma 4.2(d) for the constructed tilded family: every finite sum of
detail/dual-detail convolutions is exactly the final approximation/dual-
approximation convolution. -/
lemma rychkov_partial_kernel_identity {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M N : ℕ) :
    (∑ ell ∈ Finset.range (N + 1),
      dualDetailConvolution φ (rychkovDualDetail φ M) ell) =
      dualApproximationConvolution φ (rychkovDualApproximation φ M) N := by
  apply (FourierTransform.fourierCLE ℂ
    𝓢(CoordinateSpace d, ℂ)).injective
  ext ξ
  simp only [FourierTransform.fourierCLE_apply, map_sum, sum_apply]
  rw [show (∑ x ∈ Finset.range (N + 1),
      𝓕 (dualDetailConvolution φ (rychkovDualDetail φ M) x) ξ) =
      ∑ x ∈ Finset.range (N + 1), rychkovProductTerm M
        (fun j => 𝓕 (complexDyadicApproximationKernel φ j) ξ) x by
        apply Finset.sum_congr rfl
        intro ell _
        exact fourier_dualDetailConvolution_rychkov_apply φ M ell ξ]
  rw [sum_rychkovProductTerm, fourier_dualApproximationConvolution_rychkov_apply]

/-! ## E. Fourier support and the distributional limit bridge -/

/-- The canonical Fourier carrier of a constructed tilded approximation is
the Fourier support of the original approximation kernel. -/
def rychkovFourierApproximationCarrier {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (ell : ℕ) :
    Set (CoordinateSpace d) :=
  tsupport (SchwartzMap.fourierTransformCLM ℂ
    (complexDyadicApproximationKernel φ ell))

/-- The level-zero carrier is the original low-frequency support.  A positive
detail level is carried by the union of the two adjacent approximation
supports occurring in equation (4.2). -/
def rychkovFourierDetailCarrier {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) :
    ℕ → Set (CoordinateSpace d)
  | 0 => rychkovFourierApproximationCarrier φ 0
  | ell + 1 => rychkovFourierApproximationCarrier φ ell ∪
      rychkovFourierApproximationCarrier φ (ell + 1)

/-- Equation (4.2) cannot enlarge the Fourier support of an approximation:
the constructed factor is a pointwise multiple of the original Fourier
kernel. -/
lemma fourier_rychkovDualApproximation_support {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    tsupport (SchwartzMap.fourierTransformCLM ℂ
      (rychkovDualApproximation φ M ell)) ⊆
      rychkovFourierApproximationCarrier φ ell := by
  rw [show SchwartzMap.fourierTransformCLM ℂ
      (rychkovDualApproximation φ M ell) =
        approximationFrequencyFactor M
          (SchwartzMap.fourierTransformCLM ℂ
            (complexDyadicApproximationKernel φ ell)) from
      fourier_rychkovDualApproximation φ M ell,
    approximationFrequencyFactor]
  let ν := SchwartzMap.fourierTransformCLM ℂ
    (complexDyadicApproximationKernel φ ell)
  have hfun : ⇑(SchwartzMap.smulLeftCLM ℂ
      (approximationMultiplier M ν) ν) =
      fun ξ => approximationMultiplier M ν ξ • ν ξ := by
    funext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (approximationMultiplier_hasTemperateGrowth M ν)]
  rw [hfun]
  exact tsupport_smul_subset_right
    (fun ξ => approximationMultiplier M ν ξ) (fun ξ => ν ξ)

/-- Every positive constructed detail is Fourier-supported in the union of
the two adjacent original approximation supports. -/
lemma fourier_rychkovDualDetail_succ_support {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    tsupport (SchwartzMap.fourierTransformCLM ℂ
      (rychkovDualDetail φ M (ell + 1))) ⊆
      rychkovFourierDetailCarrier φ (ell + 1) := by
  rw [show SchwartzMap.fourierTransformCLM ℂ
      (rychkovDualDetail φ M (ell + 1)) =
        detailFrequencyFactor M
          (SchwartzMap.fourierTransformCLM ℂ
            (complexDyadicApproximationKernel φ ell))
          (SchwartzMap.fourierTransformCLM ℂ
            (complexDyadicApproximationKernel φ (ell + 1))) from
      fourier_rychkovDualDetail_succ φ M ell,
    detailFrequencyFactor]
  let previous := SchwartzMap.fourierTransformCLM ℂ
    (complexDyadicApproximationKernel φ ell)
  let current := SchwartzMap.fourierTransformCLM ℂ
    (complexDyadicApproximationKernel φ (ell + 1))
  have hfun : ⇑(SchwartzMap.smulLeftCLM ℂ
      (detailMultiplier M previous current) (current + previous)) =
      fun ξ => detailMultiplier M previous current ξ •
        (current ξ + previous ξ) := by
    funext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (detailMultiplier_hasTemperateGrowth M previous current)]
    rfl
  rw [hfun]
  exact (tsupport_smul_subset_right
      (fun ξ => detailMultiplier M previous current ξ)
      (fun ξ => current ξ + previous ξ)).trans
    ((tsupport_add current previous).trans
      (Set.union_comm _ _ ▸ Set.Subset.rfl))

/-- Fourier support for every constructed detail level, including the
definitionally low-frequency level zero. -/
lemma fourier_rychkovDualDetail_support {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M ell : ℕ) :
    tsupport (SchwartzMap.fourierTransformCLM ℂ
      (rychkovDualDetail φ M ell)) ⊆
      rychkovFourierDetailCarrier φ ell := by
  cases ell with
  | zero =>
      simpa [rychkovFourierDetailCarrier,
        rychkovFourierApproximationCarrier] using
        fourier_rychkovDualApproximation_support φ M 0
  | succ ell => exact fourier_rychkovDualDetail_succ_support φ M ell

/-- The proved kernel identity descends to the repository's canonical
tempered-distribution embedding. -/
lemma dualCalderonPartialDistribution_rychkov_eq_approximation {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M N : ℕ) :
    dualCalderonPartialDistribution φ (rychkovDualDetail φ M) N =
      dualApproximationDistribution φ
        (rychkovDualApproximation φ M) N := by
  simpa [dualCalderonPartialDistribution, dualDetailDistribution,
    dualApproximationDistribution, map_sum] using congrArg
      (SchwartzMap.toTemperedDistributionCLM
        (CoordinateSpace d) ℂ volume)
      (rychkov_partial_kernel_identity φ M N)

/-- Therefore the full constructed Calderon limit needs only the analytic
limit of the final approximation term; the detail-series limit is not an
independent premise. -/
lemma tendsto_rychkovDualCalderon_of_approximation {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (M : ℕ)
    (happrox : Tendsto (dualApproximationDistribution φ
      (rychkovDualApproximation φ M)) atTop
      (𝓝 (TemperedDistribution.delta (0 : CoordinateSpace d)))) :
    Tendsto (dualCalderonPartialDistribution φ
      (rychkovDualDetail φ M)) atTop
      (𝓝 (TemperedDistribution.delta (0 : CoordinateSpace d))) :=
  happrox.congr' (Filter.Eventually.of_forall fun N =>
    (dualCalderonPartialDistribution_rychkov_eq_approximation φ M N).symm)

end MultiNormRychkovDual

end Physlib.Mathematics.HarmonicAnalysis
