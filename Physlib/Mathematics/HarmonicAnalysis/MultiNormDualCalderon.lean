/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon
public import Mathlib.Analysis.Fourier.Convolution
meta import Zil

/-!
# Certified dual Calderon families

This module gives the exact analytic interface of Lemma 4.2.  A certificate
contains the tilded Schwartz families, arbitrary cancellation, normalization,
Fourier/spatial support control, every finite partial identity, and convergence
of the full convolution series to the Dirac tempered distribution.  Downstream
multi-norm constructions consume this package without restating those analytic
hypotheses.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Convolution FourierTransform SchwartzMap Topology

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormDualCalderon

open MultiNormMomentDerivative MultiNormSchwartzKernel
  MultiNormTemperedCalderon

abbrev CoordinateSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The paper's "normalized relative to" estimate, expressed directly using
Mathlib's defining Schwartz seminorms. -/
def NormalizedRelative {d : ℕ}
    (reference candidate : ℕ → 𝓢(CoordinateSpace d, ℂ)) : Prop :=
  ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ k' n' : ℕ, ∀ ell : ℕ,
    SchwartzMap.seminorm ℂ k n (candidate ell) ≤
      C * SchwartzMap.seminorm ℂ k' n' (reference ell)

/-! ## Paper-level dyadic templates

The families in Lemma 4.2 are normalized *before* the external dilation
`f ↦ f^{(-ell)}` is applied.  The repository's concrete Calderón kernels are
stored after that dilation, so we expose the Fourier-conjugate dilation and
its inverse explicitly and use `unscaledDyadicFamily` at the certificate
boundary. -/

/-- The mass-preserving dyadic dilation, expressed natively by conjugating
frequency contraction with the Schwartz Fourier equivalence. -/
def paperDyadicDilation {d : ℕ}
    (f : 𝓢(CoordinateSpace d, ℂ)) (ell : ℕ) :
    𝓢(CoordinateSpace d, ℂ) :=
  𝓕⁻ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (dyadicExpansionCLE ell).symm (𝓕 f))

/-- Remove the external level-`ell` dyadic dilation. -/
def paperDyadicUndilation {d : ℕ}
    (f : 𝓢(CoordinateSpace d, ℂ)) (ell : ℕ) :
    𝓢(CoordinateSpace d, ℂ) :=
  𝓕⁻ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (dyadicExpansionCLE ell) (𝓕 f))

@[simp]
lemma fourier_paperDyadicDilation {d : ℕ}
    (f : 𝓢(CoordinateSpace d, ℂ)) (ell : ℕ) :
    𝓕 (paperDyadicDilation f ell) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (dyadicExpansionCLE ell).symm (𝓕 f) := by
  simp [paperDyadicDilation]

@[simp]
lemma fourier_paperDyadicUndilation {d : ℕ}
    (f : 𝓢(CoordinateSpace d, ℂ)) (ell : ℕ) :
    𝓕 (paperDyadicUndilation f ell) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (dyadicExpansionCLE ell) (𝓕 f) := by
  simp [paperDyadicUndilation]

@[simp]
lemma paperDyadicDilation_undilation {d : ℕ}
    (f : 𝓢(CoordinateSpace d, ℂ)) (ell : ℕ) :
    paperDyadicDilation (paperDyadicUndilation f ell) ell = f := by
  apply (FourierTransform.fourierCLE ℂ
    𝓢(CoordinateSpace d, ℂ)).injective
  change 𝓕 (paperDyadicDilation (paperDyadicUndilation f ell) ell) = 𝓕 f
  rw [fourier_paperDyadicDilation, fourier_paperDyadicUndilation]
  ext ξ
  change (𝓕 f) (dyadicExpansionCLE ell
    ((dyadicExpansionCLE ell).symm ξ)) = (𝓕 f) ξ
  rw [ContinuousLinearEquiv.apply_symm_apply]

@[simp]
lemma paperDyadicUndilation_dilation {d : ℕ}
    (f : 𝓢(CoordinateSpace d, ℂ)) (ell : ℕ) :
    paperDyadicUndilation (paperDyadicDilation f ell) ell = f := by
  apply (FourierTransform.fourierCLE ℂ
    𝓢(CoordinateSpace d, ℂ)).injective
  change 𝓕 (paperDyadicUndilation (paperDyadicDilation f ell) ell) = 𝓕 f
  rw [fourier_paperDyadicUndilation, fourier_paperDyadicDilation]
  ext ξ
  change (𝓕 f) ((dyadicExpansionCLE ell).symm
    (dyadicExpansionCLE ell ξ)) = (𝓕 f) ξ
  rw [ContinuousLinearEquiv.symm_apply_apply]

/-- Recover the paper's unscaled template family from the repository's
already-dilated kernels. -/
def unscaledDyadicFamily {d : ℕ}
    (family : ℕ → 𝓢(CoordinateSpace d, ℂ)) :
    ℕ → 𝓢(CoordinateSpace d, ℂ) :=
  fun ell => paperDyadicUndilation (family ell) ell

lemma paperDyadicDilation_unscaledDyadicFamily {d : ℕ}
    (family : ℕ → 𝓢(CoordinateSpace d, ℂ)) (ell : ℕ) :
    paperDyadicDilation (unscaledDyadicFamily family ell) ell = family ell :=
  paperDyadicDilation_undilation (family ell) ell

/-- Convolution of an original detail kernel with its certified dual. -/
def dualDetailConvolution {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d))
    (dualDetail : ℕ → 𝓢(CoordinateSpace d, ℂ)) (ell : ℕ) :
    𝓢(CoordinateSpace d, ℂ) :=
  SchwartzMap.convolution (.mul ℂ ℂ)
    (complexDyadicDetailKernel φ ell) (dualDetail ell)

/-- Convolution of an original approximate-identity kernel with its dual. -/
def dualApproximationConvolution {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d))
    (dualApproximation : ℕ → 𝓢(CoordinateSpace d, ℂ)) (ell : ℕ) :
    𝓢(CoordinateSpace d, ℂ) :=
  SchwartzMap.convolution (.mul ℂ ℂ)
    (complexDyadicApproximationKernel φ ell) (dualApproximation ell)

/-- Canonical embedding of a dual detail convolution into tempered
distributions. -/
def dualDetailDistribution {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d))
    (dualDetail : ℕ → 𝓢(CoordinateSpace d, ℂ)) (ell : ℕ) :
    𝓢'(CoordinateSpace d, ℂ) :=
  SchwartzMap.toTemperedDistributionCLM (CoordinateSpace d) ℂ volume
    (dualDetailConvolution φ dualDetail ell)

/-- Finite convolutional Calderon partial sum through level `N`. -/
def dualCalderonPartialDistribution {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d))
    (dualDetail : ℕ → 𝓢(CoordinateSpace d, ℂ)) (N : ℕ) :
    𝓢'(CoordinateSpace d, ℂ) :=
  ∑ ell ∈ Finset.range (N + 1), dualDetailDistribution φ dualDetail ell

/-- The low-frequency convolution at level `N`, embedded in tempered
distributions. -/
def dualApproximationDistribution {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d))
    (dualApproximation : ℕ → 𝓢(CoordinateSpace d, ℂ)) (N : ℕ) :
    𝓢'(CoordinateSpace d, ℂ) :=
  SchwartzMap.toTemperedDistributionCLM (CoordinateSpace d) ℂ volume
    (dualApproximationConvolution φ dualApproximation N)

/-- Exact proof object for all clauses of the tilded-family construction in
Lemma 4.2.  The carrier sets make both Fourier and spatial support statements
explicit rather than conflating them. -/
structure DualCalderonFamily {d : ℕ}
    (φ : ContDiffBump (0 : CoordinateSpace d)) (m : ℕ) where
  dualApproximation : ℕ → 𝓢(CoordinateSpace d, ℂ)
  dualDetail : ℕ → 𝓢(CoordinateSpace d, ℂ)
  fourierApproximationCarrier : ℕ → Set (CoordinateSpace d)
  fourierDetailCarrier : ℕ → Set (CoordinateSpace d)
  spatialCarrier : ℕ → Set (CoordinateSpace d)
  normalized_approximation :
    NormalizedRelative
      (unscaledDyadicFamily (complexDyadicApproximationKernel φ))
      (unscaledDyadicFamily dualApproximation)
  normalized_detail :
    NormalizedRelative
      (unscaledDyadicFamily (complexDyadicApproximationKernel φ))
      (unscaledDyadicFamily dualDetail)
  detail_zero : dualDetail 0 = dualApproximation 0
  cancellation : ∀ ell : ℕ, 0 < ell → HasCancellationOrder (dualDetail ell) m
  fourier_approximation_support : ∀ ell,
    tsupport (SchwartzMap.fourierTransformCLM ℂ (dualApproximation ell)) ⊆
      fourierApproximationCarrier ell
  fourier_detail_support : ∀ ell,
    tsupport (SchwartzMap.fourierTransformCLM ℂ (dualDetail ell)) ⊆
      fourierDetailCarrier ell
  spatial_approximation_support : ∀ ell,
    tsupport (dualApproximation ell) ⊆ spatialCarrier ell
  spatial_detail_support : ∀ ell,
    tsupport (dualDetail ell) ⊆ spatialCarrier ell
  partial_kernel_identity : ∀ N,
    (∑ ell ∈ Finset.range (N + 1),
      dualDetailConvolution φ dualDetail ell) =
      dualApproximationConvolution φ dualApproximation N
  full_identity :
    Tendsto (dualCalderonPartialDistribution φ dualDetail) atTop
      (𝓝 (TemperedDistribution.delta (0 : CoordinateSpace d)))

/-- The certified Schwartz-kernel partial identity descends through Mathlib's
canonical embedding to the corresponding tempered-distribution identity. -/
lemma DualCalderonFamily.partial_identity
    {d m : ℕ} {φ : ContDiffBump (0 : CoordinateSpace d)}
    (D : DualCalderonFamily φ m) (N : ℕ) :
    dualCalderonPartialDistribution φ D.dualDetail N =
      dualApproximationDistribution φ D.dualApproximation N := by
  simpa [dualCalderonPartialDistribution, dualDetailDistribution,
    dualApproximationDistribution, map_sum] using congrArg
      (SchwartzMap.toTemperedDistributionCLM (CoordinateSpace d) ℂ volume)
      (D.partial_kernel_identity N)

/-- Lemma 4.2 capstone: one certificate exposes arbitrary cancellation,
support control, every partial Calderon identity, and the full distributional
identity through the actual bundled convolution and tempered-distribution APIs. -/
lemma dualCalderon_arbitraryCancellation_support_partial_full
    {d m : ℕ} (φ : ContDiffBump (0 : CoordinateSpace d))
    (D : DualCalderonFamily φ m) :
    (∀ ell : ℕ, 0 < ell → HasCancellationOrder (D.dualDetail ell) m) ∧
    (∀ ell, tsupport (SchwartzMap.fourierTransformCLM ℂ
      (D.dualApproximation ell)) ⊆
      D.fourierApproximationCarrier ell) ∧
    (∀ ell, tsupport (SchwartzMap.fourierTransformCLM ℂ
      (D.dualDetail ell)) ⊆ D.fourierDetailCarrier ell) ∧
    (∀ ell, tsupport (D.dualApproximation ell) ⊆ D.spatialCarrier ell) ∧
    (∀ ell, tsupport (D.dualDetail ell) ⊆ D.spatialCarrier ell) ∧
    (∀ N, dualCalderonPartialDistribution φ D.dualDetail N =
      dualApproximationDistribution φ D.dualApproximation N) ∧
    Tendsto (dualCalderonPartialDistribution φ D.dualDetail) atTop
      (𝓝 (TemperedDistribution.delta (0 : CoordinateSpace d))) := by
  exact ⟨D.cancellation, D.fourier_approximation_support,
    D.fourier_detail_support, D.spatial_approximation_support,
    D.spatial_detail_support, D.partial_identity, D.full_identity⟩

end MultiNormDualCalderon

end Physlib.Mathematics.HarmonicAnalysis

/- ZIL-BEGIN -/

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualCalderon_arbitraryCancellation_support_partial_full where
  formalizes @ "claim:the-dual-calderon-certificate-exposes-arbitrary-cancellation-support-containment-partial-identities-and-full-convergence-to-dirac",
  supported_by @ "paper:calderon-reproducing-formula-dual-family-certificate"

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.DualCalderonFamily.partial_identity where
  formalizes @ "claim:the-certified-dual-schwartz-kernel-partial-identity-descends-to-tempered-distributions-at-each-cutoff"

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.paperDyadicDilation_undilation where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:the-mass-preserving-dyadic-dilation-and-undilation-are-mutually-inverse-certifying-the-unscaled-template-correspondence"

zil_file_contract physlib.multiNormDualCalderon where
  promises "The dual Calderon family certificate: the mass-preserving dyadic dilation and undilation (Fourier-conjugated frequency contraction) are mutually inverse, recovering the paper's unscaled template family; the DualCalderonFamily structure bundles normalization, arbitrary-order cancellation, four support-containment statements, every finite partial identity, and full convergence of the dual convolution series to the Dirac tempered distribution; and one certificate exposes all of these together (Lemma 4.2 capstone)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.DualCalderonFamily",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.paperDyadicDilation",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualDetailConvolution"]
  forbids_substitutes ["a bare existence of a dual family, the certificate carries the explicit normalization and support data the multi-norm consumers need"]
  witnessed_by [Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.dualCalderon_arbitraryCancellation_support_partial_full,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.DualCalderonFamily.partial_identity,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.paperDyadicDilation_undilation,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon.paperDyadicUndilation_dilation]

/- ZIL-END -/
