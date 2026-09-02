/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula
public import Mathlib.Analysis.Fourier.Convolution
meta import Zil

/-!
# Physical-space Calderon reconstruction

The distributional detail kernels are applied to Schwartz amplitudes through
Mathlib's bundled Schwartz convolution.  Finite reconstructions telescope to
convolution with the last approximate identity and converge pointwise to the
original amplitude.  A Fourier-side adapter identifies such convolution
pieces with the repository's existing global complex multi-norm multipliers.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ContDiff Convolution FourierTransform SchwartzMap Topology

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormPhysicalCalderon

open MultiNormSchwartzKernel MultiNormTemperedCalderon
open MultiNormGlobalFrequencyCover MultiNormGlobalNormalizedPartition
  MultiNormGlobalComplexReproducingFormula

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## A. Bundled physical-space convolution pieces -/

/-- Convolution of one Section 4 detail kernel with a Schwartz amplitude. -/
def dyadicCalderonConvolutionPiece
    (φ : ContDiffBump (0 : E)) (n : ℕ) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.convolution (.mul ℂ ℂ) (complexDyadicDetailKernel φ n) f

/-- The finite physical-space Calderon reconstruction through level `N`. -/
def dyadicCalderonPartialReconstruction
    (φ : ContDiffBump (0 : E)) (N : ℕ) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  ∑ n ∈ Finset.range (N + 1), dyadicCalderonConvolutionPiece φ n f

/-- Finite physical-space reconstruction telescopes to convolution with the
last approximate-identity kernel. -/
lemma dyadicCalderonPartialReconstruction_eq
    (φ : ContDiffBump (0 : E)) (N : ℕ) (f : 𝓢(E, ℂ)) :
    dyadicCalderonPartialReconstruction φ N f =
      SchwartzMap.convolution (.mul ℂ ℂ)
        (complexDyadicApproximationKernel φ N) f := by
  simpa [dyadicCalderonPartialReconstruction,
    dyadicCalderonConvolutionPiece, map_sum] using congrArg
      (fun K : 𝓢(E, ℂ) => SchwartzMap.convolution (.mul ℂ ℂ) K f)
      (sum_range_complexDyadicDetailKernel φ N)

/-! ## B. Pointwise Calderon reconstruction -/

/-- Convolution with the dyadic approximate identity converges at every point
of a Schwartz amplitude. -/
lemma tendsto_dyadicApproximationConvolution_apply
    (φ : ContDiffBump (0 : E)) (f : 𝓢(E, ℂ)) (x : E) :
    Tendsto
      (fun N => SchwartzMap.convolution (.mul ℂ ℂ)
        (complexDyadicApproximationKernel φ N) f x)
      atTop (𝓝 (f x)) := by
  let g : E → ℂ := fun y => f (x - y)
  have hgInt : Integrable g volume := by
    simpa [g, sub_eq_add_neg] using (f.integrable.comp_add_left x).comp_neg
  have hgCont : ContinuousAt g 0 := by
    dsimp [g]
    fun_prop
  have hpeak := tendsto_integral_comp_smul_smul_of_integrable
    (μ := volume) (φ := φ.normed volume)
    φ.nonneg_normed φ.integral_normed
    (normalizedBump_peak_decay φ) hgInt hgCont
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hdyadic := hpeak.comp hpow
  simp_rw [SchwartzMap.convolution_apply]
  change Tendsto
    (fun N => ∫ y,
      (complexDyadicApproximationKernel φ N y) * f (x - y))
    atTop (𝓝 (f x))
  simp_rw [complexDyadicApproximationKernel_apply]
  convert hdyadic using 1
  · funext N
    apply integral_congr_ae
    filter_upwards with y
    simp [dyadicExpansion, g]
  · simp [g]

/-- The Section 4 physical partial sums reconstruct every Schwartz amplitude
pointwise. -/
lemma dyadicCalderonPartialReconstruction_tendsto_apply
    (φ : ContDiffBump (0 : E)) (f : 𝓢(E, ℂ)) (x : E) :
    Tendsto (fun N => dyadicCalderonPartialReconstruction φ N f x)
      atTop (𝓝 (f x)) := by
  exact (tendsto_dyadicApproximationConvolution_apply φ f x).congr'
    (Filter.Eventually.of_forall fun N => by
      exact congrArg (fun h : 𝓢(E, ℂ) => h x)
        (dyadicCalderonPartialReconstruction_eq φ N f).symm)

/-! ## C. Adapter to the existing multi-norm multiplier layer -/

/-- Fourier transform turns each physical Section 4 convolution piece into
pointwise multiplication of the already bundled Schwartz transforms. -/
lemma fourier_dyadicCalderonConvolutionPiece_apply
    (φ : ContDiffBump (0 : E)) (n : ℕ) (f : 𝓢(E, ℂ)) (ξ : E) :
    𝓕 (dyadicCalderonConvolutionPiece φ n f) ξ =
      𝓕 (complexDyadicDetailKernel φ n) ξ * 𝓕 f ξ := by
  rw [dyadicCalderonConvolutionPiece, SchwartzMap.fourier_convolution]
  rfl

/-- If a Section 4 Schwartz kernel realizes one existing normalized multi-norm
symbol in Fourier space, its physical convolution realizes exactly the
repository's `globalNormalizedComplexMultiplierPiece`; no second multiplier
definition is introduced. -/
lemma fourier_convolution_eq_globalNormalizedComplexMultiplierPiece
    {M : StandardMultiNormMatrix Unit} (A : FullTubeIndex M)
    (φ : ContDiffBump (0 : E)) (n : ℕ)
    (f : 𝓢(E, ℂ)) (ξ : E)
    (hkernel : 𝓕 (complexDyadicDetailKernel φ n) ξ =
      (globalNormalizedSmoothSymbol
        (V := fun _ : Unit => E) A (fun _ => ξ) : ℂ)) :
    𝓕 (dyadicCalderonConvolutionPiece φ n f) ξ =
      globalNormalizedComplexMultiplierPiece
        (V := fun _ : Unit => E) A (fun η => 𝓕 f (η ())) (fun _ => ξ) := by
  rw [fourier_dyadicCalderonConvolutionPiece_apply, hkernel]
  rfl

/-- Third Section 4 capstone: physical convolution partial sums reconstruct
Schwartz amplitudes pointwise, Fourier transform converts every piece to a
multiplier, and kernels realizing existing normalized symbols reuse the exact
global multi-norm multiplier API. -/
lemma physicalCalderon_reconstruction_multiNormMultiplier_bridge
    {M : StandardMultiNormMatrix Unit} (A : FullTubeIndex M)
    (φ : ContDiffBump (0 : E)) (n : ℕ)
    (f : 𝓢(E, ℂ)) (x ξ : E)
    (hkernel : 𝓕 (complexDyadicDetailKernel φ n) ξ =
      (globalNormalizedSmoothSymbol
        (V := fun _ : Unit => E) A (fun _ => ξ) : ℂ)) :
    Tendsto (fun N => dyadicCalderonPartialReconstruction φ N f x)
        atTop (𝓝 (f x)) ∧
    𝓕 (dyadicCalderonConvolutionPiece φ n f) ξ =
      globalNormalizedComplexMultiplierPiece
        (V := fun _ : Unit => E) A (fun η => 𝓕 f (η ())) (fun _ => ξ) := by
  exact ⟨dyadicCalderonPartialReconstruction_tendsto_apply φ f x,
    fourier_convolution_eq_globalNormalizedComplexMultiplierPiece
      A φ n f ξ hkernel⟩

end MultiNormPhysicalCalderon

end Physlib.Mathematics.HarmonicAnalysis

/- ZIL-BEGIN -/

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.physicalCalderon_reconstruction_multiNormMultiplier_bridge where
  formalizes @ "claim:the-physical-space-calderon-reconstruction-conjoins-pointwise-reconstruction-with-reuse-of-the-existing-global-multi-norm-multiplier",
  requires @ "claim:the-physical-partial-sums-reconstruct-every-schwartz-amplitude-pointwise",
  supported_by @ "paper:multi-norm-physical-calderon-reconstruction"

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.dyadicCalderonPartialReconstruction_tendsto_apply where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  supported_by @ "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.tendsto_dyadicApproximationConvolution_apply",
  formalizes @ "claim:the-physical-partial-sums-reconstruct-every-schwartz-amplitude-pointwise"

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.fourier_convolution_eq_globalNormalizedComplexMultiplierPiece where
  formalizes @ "claim:each-physical-convolution-piece-equals-the-existing-global-normalized-complex-multiplier-no-new-multiplier-introduced"

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.tendsto_dyadicApproximationConvolution_apply where
  supported_by @ "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.normalizedBump_peak_decay",
  formalizes @ "claim:convolution-with-the-dyadic-approximate-identity-converges-pointwise-to-the-amplitude-at-every-point"

zil_file_contract physlib.multiNormPhysicalCalderon where
  promises "The physical-space Calderon reconstruction: each convolution piece is the detail kernel convolved with a Schwartz amplitude, the finite reconstruction telescopes to convolution with the last approximation kernel and reconstructs every amplitude pointwise, the Fourier transform sends each piece to multiplication that equals the repository's existing global normalized complex multiplier (no new multiplier introduced), and the Section-4 capstone conjoins pointwise reconstruction with reuse of the existing multi-norm multiplier layer."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.dyadicCalderonConvolutionPiece",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.dyadicCalderonPartialReconstruction"]
  forbids_substitutes ["any new Fourier multiplier, the existing globalNormalizedComplexMultiplierPiece is reused via the Fourier-side adapter"]
  witnessed_by [Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.physicalCalderon_reconstruction_multiNormMultiplier_bridge,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.dyadicCalderonPartialReconstruction_tendsto_apply,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.fourier_convolution_eq_globalNormalizedComplexMultiplierPiece,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.tendsto_dyadicApproximationConvolution_apply]

/- ZIL-END -/
