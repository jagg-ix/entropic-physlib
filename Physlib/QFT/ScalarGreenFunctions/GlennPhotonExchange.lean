/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.Continuum
public import Physlib.QFT.ScalarGreenFunctions.DysonWick
public import Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess

/-!
# Vacuum-photon exchange nonlinearities in harmonic systems

This file formalizes the structural core of

R. Glenn, K. Bennett, K. E. Dorfman, and S. Mukamel,
*Photon-exchange induces optical nonlinearities in harmonic systems*,
J. Phys. B **48** (2015) 065401.

The paper distinguishes two photon-exchange processes.  Consecutive exchange
is retained by the reduced quantum master equation and leaves a harmonic
system's response linear.  Interrupted exchange occurs only in the full
time-ordered expansion and can produce a third-order optical response.  The
first finite contribution analyzed in the paper is fourth order in the vacuum
field: its four field insertions are reduced by Wick's theorem and its
frequency-space expression is a double convolution.

The formalization reuses three existing layers:

* `dysonOrder_smul_wicks_theorem` for the complete contraction expansion;
* `MeasureTheory.integral` for the product-measure frequency convolution;
* complex linear maps for the response retained by a linear QME.
* Junker's Wigner--Dunkl `|z|^{2ν}` Chapman--Kolmogorov kernel and its
  reflecting/absorbing Feynman--Kac channels for a concrete path-integral
  realization of consecutive versus interrupted propagation.

The vacuum-selection facts specific to the electromagnetic model are visible
fields of `GlennPhotonExchangeData`: the second-order and balanced fourth-order
kernels vanish almost everywhere, while the interrupted fourth-order kernel is
integrable and has nonzero integral.  Thus the Lean result is conditional on
those paper-specific analytic/operator inputs.  It does not claim to construct
the dipole Hamiltonian, evaluate the numerical susceptibility of a material,
or prove convergence of Glenn et al.'s kernel without the stated integrability
premise.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open FieldSpecification
open MeasureTheory
open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess

/-! ## A. A response diagnostic separating linear and cubic behavior -/

/-- The third forward finite difference of an optical response along a field
amplitude.  It vanishes for a linear response and detects a homogeneous cubic
response with coefficient `3! = 6`. -/
def opticalThirdDifference (response : ℂ → ℂ) (field : ℂ) : ℂ :=
  response (3 * field) - 3 * response (2 * field) +
    3 * response field - response 0

/-- A response retained by a complex-linear harmonic QME has no cubic
finite-difference signal.  This is the exact algebraic content of the paper's
statement that consecutive exchange keeps the oscillator equations linear. -/
lemma linearQMEResponse_thirdDifference_eq_zero
    (response : ℂ →ₗ[ℂ] ℂ) (field : ℂ) :
    opticalThirdDifference response field = 0 := by
  have hthree : response (3 * field) = 3 * response field := by
    simpa only [smul_eq_mul] using response.map_smul (3 : ℂ) field
  have htwo : response (2 * field) = 2 * response field := by
    simpa only [smul_eq_mul] using response.map_smul (2 : ℂ) field
  rw [opticalThirdDifference, hthree, htwo, map_zero]
  ring

/-- A scalar third-order susceptibility acting on one complex field mode. -/
def cubicOpticalResponse (susceptibility field : ℂ) : ℂ :=
  susceptibility * field ^ 3

/-- The third finite difference of a cubic response is `3!` times the response. -/
lemma cubicOpticalResponse_thirdDifference
    (susceptibility field : ℂ) :
    opticalThirdDifference (cubicOpticalResponse susceptibility) field =
      6 * cubicOpticalResponse susceptibility field := by
  simp [opticalThirdDifference, cubicOpticalResponse]
  ring

/-- A nonzero susceptibility probed by a nonzero field has a nonzero cubic
finite-difference signal, so it cannot be represented by the linear QME
response of `linearQMEResponse_thirdDifference_eq_zero`. -/
lemma cubicOpticalResponse_thirdDifference_ne_zero
    (susceptibility field : ℂ)
    (hsusceptibility : susceptibility ≠ 0) (hfield : field ≠ 0) :
    opticalThirdDifference (cubicOpticalResponse susceptibility) field ≠ 0 := by
  rw [cubicOpticalResponse_thirdDifference]
  exact mul_ne_zero (by norm_num)
    (mul_ne_zero hsusceptibility (pow_ne_zero 3 hfield))

/-! ## B. Fourth vacuum order uses the complete Wick expansion -/

/-- The fourth vacuum-field Dyson coefficient expands over every Wick
contraction of the four field insertions.  This is the repository's complete
Wick theorem specialized to the order used in Glenn et al., rather than a new
or paper-specific contraction calculus. -/
lemma fourthVacuumOrder_dysonWickExpansion
    {𝓕 : FieldSpecification} (hbar : ℝ)
    (φ₁ φ₂ φ₃ φ₄ : 𝓕.FieldOp) :
    (((-Complex.I) / (hbar : ℂ)) ^ 4 / ((4 : ℕ).factorial : ℂ)) •
        WickAlgebra.timeOrder
          (WickAlgebra.ofFieldOpList [φ₁, φ₂, φ₃, φ₄]) =
      ∑ φsΛ : WickContraction 4,
        (((-Complex.I) / (hbar : ℂ)) ^ 4 / ((4 : ℕ).factorial : ℂ)) •
          WickContraction.wickTerm (φs := [φ₁, φ₂, φ₃, φ₄]) φsΛ := by
  simpa using
    (dysonOrder_smul_wicks_theorem (𝓕 := 𝓕) hbar 4
      [φ₁, φ₂, φ₃, φ₄])

/-! ## C. The two-process double-frequency convolution -/

/-- The pair of vacuum-mode frequencies integrated in the fourth-order
photon-exchange response. -/
abbrev GlennFrequencyPair := ℝ × ℝ

/-- A complex response kernel on the two exchanged vacuum frequencies. -/
abbrev GlennFrequencyKernel := GlennFrequencyPair → ℂ

/-- Product-measure form of the double frequency integral in Glenn et al.
Eq. (18).  Fubini rearrangements require separate integrability hypotheses;
the definition itself fixes only the Bochner integral over `ℝ × ℝ`. -/
def doubleFrequencyConvolution (kernel : GlennFrequencyKernel) : ℂ :=
  ∫ frequencies, kernel frequencies

/-- Sum the consecutive/sequential exchange kernel and the interrupted
exchange kernel before carrying out the double frequency convolution. -/
def glennTwoProcessConvolution
    (sequential interrupted : GlennFrequencyKernel) : ℂ :=
  doubleFrequencyConvolution (fun frequencies =>
    sequential frequencies + interrupted frequencies)

/-- Integrability lets the full two-process frequency convolution split
exactly into its sequential and interrupted contributions. -/
lemma glennTwoProcessConvolution_eq_sum
    (sequential interrupted : GlennFrequencyKernel)
    (hsequential : Integrable sequential)
    (hinterrupted : Integrable interrupted) :
    glennTwoProcessConvolution sequential interrupted =
      doubleFrequencyConvolution sequential +
        doubleFrequencyConvolution interrupted := by
  exact integral_add hsequential hinterrupted

/-- An almost-everywhere vanishing frequency kernel has zero double
convolution. -/
lemma doubleFrequencyConvolution_eq_zero_of_ae_zero
    (kernel : GlennFrequencyKernel)
    (hzero : kernel =ᵐ[volume] 0) :
    doubleFrequencyConvolution kernel = 0 := by
  unfold doubleFrequencyConvolution
  calc
    (∫ frequencies, kernel frequencies) =
        ∫ _ : GlennFrequencyPair, (0 : ℂ) := integral_congr_ae hzero
    _ = 0 := by simp

/-- If the sequential contribution vanishes by the relevant vacuum selection
rule, the two-process response is exactly the interrupted exchange response. -/
lemma glennTwoProcessConvolution_eq_interrupted
    (sequential interrupted : GlennFrequencyKernel)
    (hsequentialZero : sequential =ᵐ[volume] 0)
    (hinterrupted : Integrable interrupted) :
    glennTwoProcessConvolution sequential interrupted =
      doubleFrequencyConvolution interrupted := by
  have hsequential : Integrable sequential :=
    (MeasureTheory.integrable_zero GlennFrequencyPair ℂ volume).congr
      hsequentialZero.symm
  rw [glennTwoProcessConvolution_eq_sum sequential interrupted
    hsequential hinterrupted]
  rw [doubleFrequencyConvolution_eq_zero_of_ae_zero sequential
    hsequentialZero, zero_add]

/-! ## D. Wigner--Dunkl realization of the two convolution processes -/

/-- A factorized two-frequency kernel assembled from one frequency amplitude.
This is the product-kernel specialization of Glenn's double convolution; it is
used below for the two Wigner--Dunkl parity channels. -/
def factorizedFrequencyKernel (amplitude : ℝ → ℂ) :
    GlennFrequencyKernel :=
  fun frequencies => amplitude frequencies.1 * amplitude frequencies.2

/-- The product-measure double convolution of a factorized kernel is the
product of its two one-frequency integrals. -/
lemma doubleFrequencyConvolution_factorized
    (amplitude : ℝ → ℂ) :
    doubleFrequencyConvolution (factorizedFrequencyKernel amplitude) =
      (∫ ω, amplitude ω) * ∫ ω, amplitude ω := by
  rw [doubleFrequencyConvolution, Measure.volume_eq_prod]
  simpa [factorizedFrequencyKernel] using
    (MeasureTheory.integral_prod_mul (μ := volume) (ν := volume)
      amplitude amplitude)

/-- The reflecting (even/Neumann) Wigner--Dunkl Feynman--Kac frequency
amplitude from Junker Eq. 78. -/
noncomputable def dunklReflectingFrequencyAmplitude
    (Brefl : FeynmanKacModel ℝ) (β : ℝ)
    (observable : ℝ → ℝ → ℝ) (τ x : ℝ) (ω : ℝ) : ℂ :=
  (feynman_kac_propagator Brefl β (observable ω) τ x : ℝ)

/-- The absorbing (odd/Dirichlet) Wigner--Dunkl Feynman--Kac frequency
amplitude, including the `x*y` parity factor of Junker Eq. 78. -/
noncomputable def dunklAbsorbingFrequencyAmplitude
    (Babs : FeynmanKacModel ℝ) (β : ℝ)
    (observable : ℝ → ℝ → ℝ) (τ x y : ℝ) (ω : ℝ) : ℂ :=
  ((x * y * feynman_kac_propagator Babs β (observable ω) τ x : ℝ) : ℂ)

/-- The full Euclidean Wigner--Dunkl frequency amplitude is exactly the sum
of its reflecting and absorbing Bessel-process channels (Junker Eqs. 77--78). -/
lemma dunklEuclideanFrequencyAmplitude_eq_channels
    (Brefl Babs : FeynmanKacModel ℝ) (β : ℝ)
    (observable : ℝ → ℝ → ℝ) (τ x y ω : ℝ) :
    ((dunklEuclideanFK Brefl Babs β (observable ω) τ x y : ℝ) : ℂ) =
      dunklReflectingFrequencyAmplitude Brefl β observable τ x ω +
        dunklAbsorbingFrequencyAmplitude Babs β observable τ x y ω := by
  simp [dunklEuclideanFK, dunklReflectingFrequencyAmplitude,
    dunklAbsorbingFrequencyAmplitude]

/-- **Wigner--Dunkl parity resolution of Glenn's double convolution.**
If the reflecting and absorbing one-frequency amplitudes are integrable, the
factorized two-photon kernel has four exact Bessel-process channels:
reflecting--reflecting, reflecting--absorbing, absorbing--reflecting, and
absorbing--absorbing.  This is the direct bridge from Junker Eqs. 77--78 to
the two-frequency convolution in Glenn et al. Eq. 18. -/
lemma dunklParityDoubleConvolution_eq_four_channels
    (reflecting absorbing : ℝ → ℂ)
    (hreflecting : Integrable reflecting)
    (habsorbing : Integrable absorbing) :
    doubleFrequencyConvolution
        (factorizedFrequencyKernel (fun ω =>
          reflecting ω + absorbing ω)) =
      (∫ ω, reflecting ω) * (∫ ω, reflecting ω) +
      (∫ ω, reflecting ω) * (∫ ω, absorbing ω) +
      (∫ ω, absorbing ω) * (∫ ω, reflecting ω) +
      (∫ ω, absorbing ω) * (∫ ω, absorbing ω) := by
  rw [doubleFrequencyConvolution_factorized,
    integral_add hreflecting habsorbing]
  ring

/-- The paper's actual Euclidean Wigner--Dunkl FK amplitudes instantiate the
four-channel Glenn decomposition.  Integrability of the two frequency
amplitudes remains explicit; it is the analytic spectral input required by
the product-measure Bochner integral. -/
lemma dunklEuclideanFK_doubleConvolution_eq_four_channels
    (Brefl Babs : FeynmanKacModel ℝ) (β : ℝ)
    (observable : ℝ → ℝ → ℝ) (τ x y : ℝ)
    (hreflecting : Integrable
      (dunklReflectingFrequencyAmplitude Brefl β observable τ x))
    (habsorbing : Integrable
      (dunklAbsorbingFrequencyAmplitude Babs β observable τ x y)) :
    doubleFrequencyConvolution
        (factorizedFrequencyKernel (fun ω =>
          ((dunklEuclideanFK Brefl Babs β (observable ω) τ x y : ℝ) : ℂ))) =
      (∫ ω, dunklReflectingFrequencyAmplitude Brefl β observable τ x ω) *
          (∫ ω, dunklReflectingFrequencyAmplitude Brefl β observable τ x ω) +
      (∫ ω, dunklReflectingFrequencyAmplitude Brefl β observable τ x ω) *
          (∫ ω, dunklAbsorbingFrequencyAmplitude Babs β observable τ x y ω) +
      (∫ ω, dunklAbsorbingFrequencyAmplitude Babs β observable τ x y ω) *
          (∫ ω, dunklReflectingFrequencyAmplitude Brefl β observable τ x ω) +
      (∫ ω, dunklAbsorbingFrequencyAmplitude Babs β observable τ x y ω) *
          (∫ ω, dunklAbsorbingFrequencyAmplitude Babs β observable τ x y ω) := by
  have hfun :
      (fun ω =>
        ((dunklEuclideanFK Brefl Babs β (observable ω) τ x y : ℝ) : ℂ)) =
      (fun ω =>
        dunklReflectingFrequencyAmplitude Brefl β observable τ x ω +
          dunklAbsorbingFrequencyAmplitude Babs β observable τ x y ω) := by
    funext ω
    exact dunklEuclideanFrequencyAmplitude_eq_channels
      Brefl Babs β observable τ x y ω
  rw [hfun]
  exact dunklParityDoubleConvolution_eq_four_channels
    _ _ hreflecting habsorbing

/-- Turn a Wigner--Dunkl kernel with a frequency-dependent intermediate
insertion into Glenn's two-frequency kernel: each exchanged frequency probes
one interrupted kernel composition. -/
noncomputable def dunklInterruptedGlennKernel {ν : ℝ}
    (S : DunklKernelSemigroup ν) (insertion : ℝ → ℝ → ℂ)
    (t₂ t₁ x y : ℝ) : GlennFrequencyKernel :=
  factorizedFrequencyKernel
    (fun ω => S.interruptedKernel (insertion ω) t₂ t₁ x y)

/-- The corresponding consecutive Wigner--Dunkl realization, with each
frequency weighted by an external spectral profile. -/
noncomputable def dunklSequentialGlennKernel {ν : ℝ}
    (S : DunklKernelSemigroup ν) (profile : ℝ → ℂ)
    (t₂ t₁ x y : ℝ) : GlennFrequencyKernel :=
  factorizedFrequencyKernel
    (fun ω => profile ω * S.kernel (t₂ + t₁) x y)

/-- With a scalar spectral profile multiplying the identity insertion, the
interrupted Wigner--Dunkl kernel collapses pointwise to the consecutive
semigroup kernel.  Hence a genuine Glenn interrupted process requires a
non-scalar intermediate insertion; time slicing alone cannot create it. -/
lemma dunklInterruptedGlennKernel_scalar_eq_sequential {ν : ℝ}
    (S : DunklKernelSemigroup ν) (profile : ℝ → ℂ)
    (t₂ t₁ x y : ℝ) (ht₂ : 0 < t₂) (ht₁ : 0 < t₁) :
    dunklInterruptedGlennKernel S
        (fun ω _ => profile ω) t₂ t₁ x y =
      dunklSequentialGlennKernel S profile t₂ t₁ x y := by
  funext frequencies
  simp only [dunklInterruptedGlennKernel, dunklSequentialGlennKernel,
    factorizedFrequencyKernel]
  have hcollapse (ω : ℝ) :
      S.interruptedKernel (fun _ => profile ω) t₂ t₁ x y =
        profile ω * S.kernel (t₂ + t₁) x y := by
    unfold DunklKernelSemigroup.interruptedKernel
    rw [show
      (fun z =>
        ((dunklSpatialWeight ν z : ℝ) : ℂ) *
            S.kernel t₂ x z * profile ω * S.kernel t₁ z y) =
        (fun z =>
          profile ω * (((dunklSpatialWeight ν z : ℝ) : ℂ) *
            S.kernel t₂ x z * S.kernel t₁ z y)) by
          funext z; ring]
    rw [MeasureTheory.integral_const_mul]
    change profile ω *
        dunklWeightedKernelComposition ν (S.kernel t₂) (S.kernel t₁) x y =
      profile ω * S.kernel (t₂ + t₁) x y
    rw [S.sequentialKernel_eq_total t₂ t₁ x y ht₂ ht₁]
  rw [hcollapse frequencies.1, hcollapse frequencies.2]

/-- Consequently the two double-frequency convolutions agree for scalar
insertions.  This is the precise kernel statement behind Glenn's distinction:
consecutive propagation is already included by the semigroup, while an
operator-valued interruption is extra physics. -/
lemma dunklScalarInsertionConvolution_eq_sequential {ν : ℝ}
    (S : DunklKernelSemigroup ν) (profile : ℝ → ℂ)
    (t₂ t₁ x y : ℝ) (ht₂ : 0 < t₂) (ht₁ : 0 < t₁) :
    doubleFrequencyConvolution
        (dunklInterruptedGlennKernel S
          (fun ω _ => profile ω) t₂ t₁ x y) =
      doubleFrequencyConvolution
        (dunklSequentialGlennKernel S profile t₂ t₁ x y) := by
  rw [dunklInterruptedGlennKernel_scalar_eq_sequential
    S profile t₂ t₁ x y ht₂ ht₁]

/-- The scalar-insertion collapse is realized concretely by the explicit
positive-time Wiener kernel, rather than by an externally supplied abstract
semigroup.  This is the `ν = 0` Wigner--Dunkl/Glenn bridge. -/
lemma freeWienerInterruptedGlennKernel_scalar_eq_sequential
    (profile : ℝ → ℂ) (t₂ t₁ x y : ℝ)
    (ht₂ : 0 < t₂) (ht₁ : 0 < t₁) :
    dunklInterruptedGlennKernel freeWienerDunklSemigroup
        (fun ω _ => profile ω) t₂ t₁ x y =
      dunklSequentialGlennKernel freeWienerDunklSemigroup
        profile t₂ t₁ x y :=
  dunklInterruptedGlennKernel_scalar_eq_sequential
    freeWienerDunklSemigroup profile t₂ t₁ x y ht₂ ht₁

/-- Consequently, Glenn's two-frequency convolution also collapses for a
scalar insertion in the concrete free Wiener realization.  A nontrivial
interrupted exchange must therefore be carried by a genuinely
position-dependent intermediate operator. -/
lemma freeWienerScalarInsertionConvolution_eq_sequential
    (profile : ℝ → ℂ) (t₂ t₁ x y : ℝ)
    (ht₂ : 0 < t₂) (ht₁ : 0 < t₁) :
    doubleFrequencyConvolution
        (dunklInterruptedGlennKernel freeWienerDunklSemigroup
          (fun ω _ => profile ω) t₂ t₁ x y) =
      doubleFrequencyConvolution
        (dunklSequentialGlennKernel freeWienerDunklSemigroup
          profile t₂ t₁ x y) :=
  dunklScalarInsertionConvolution_eq_sequential
    freeWienerDunklSemigroup profile t₂ t₁ x y ht₂ ht₁

/-! ## E. Glenn's vacuum-selection data and the first finite response -/

/-- Analytic and vacuum-selection data for the two perturbative orders isolated
by Glenn et al.  The balanced fourth-order kernel is the contribution with two
vacuum interactions on each oscillator; the interrupted kernel is the `3+1`
assignment.  Their vanishing/nonvanishing properties are inputs from the
paper's electromagnetic field correlations, not consequences of abstract
Bochner integration. -/
structure GlennPhotonExchangeData where
  /-- Second-order vacuum-exchange kernel. -/
  secondVacuumOrder : GlennFrequencyKernel
  /-- Balanced fourth-order (`2+2`) vacuum-exchange kernel. -/
  balancedFourthOrder : GlennFrequencyKernel
  /-- Interrupted fourth-order (`3+1`) vacuum-exchange kernel. -/
  interruptedFourthOrder : GlennFrequencyKernel
  /-- The second-order vacuum correlation vanishes almost everywhere. -/
  secondVacuumOrder_ae_zero : secondVacuumOrder =ᵐ[volume] 0
  /-- The balanced `2+2` fourth-order vacuum correlation vanishes almost
  everywhere under the bosonic-vacuum/heterodyne selection rule. -/
  balancedFourthOrder_ae_zero : balancedFourthOrder =ᵐ[volume] 0
  /-- The interrupted fourth-order kernel is Bochner integrable. -/
  interruptedFourthOrder_integrable : Integrable interruptedFourthOrder
  /-- The integrated interrupted exchange is finite and nonzero. -/
  interruptedFourthOrder_nonzero :
    doubleFrequencyConvolution interruptedFourthOrder ≠ 0

namespace GlennPhotonExchangeData

/-- Integrated second-order vacuum correction. -/
def secondOrderResponse (data : GlennPhotonExchangeData) : ℂ :=
  doubleFrequencyConvolution data.secondVacuumOrder

/-- Integrated fourth-order response, with the balanced and interrupted
processes retained until the vacuum selection rule is applied. -/
def fourthOrderResponse (data : GlennPhotonExchangeData) : ℂ :=
  glennTwoProcessConvolution data.balancedFourthOrder
    data.interruptedFourthOrder

/-- The second-order vacuum correction vanishes. -/
lemma secondOrderResponse_eq_zero (data : GlennPhotonExchangeData) :
    data.secondOrderResponse = 0 :=
  doubleFrequencyConvolution_eq_zero_of_ae_zero
    data.secondVacuumOrder data.secondVacuumOrder_ae_zero

/-- The fourth-order response reduces exactly to the interrupted `3+1`
process after the balanced `2+2` vacuum correlation vanishes. -/
lemma fourthOrderResponse_eq_interrupted (data : GlennPhotonExchangeData) :
    data.fourthOrderResponse =
      doubleFrequencyConvolution data.interruptedFourthOrder :=
  glennTwoProcessConvolution_eq_interrupted
    data.balancedFourthOrder data.interruptedFourthOrder
    data.balancedFourthOrder_ae_zero
    data.interruptedFourthOrder_integrable

/-- The surviving fourth-order interrupted response is nonzero. -/
lemma fourthOrderResponse_ne_zero (data : GlennPhotonExchangeData) :
    data.fourthOrderResponse ≠ 0 := by
  rw [data.fourthOrderResponse_eq_interrupted]
  exact data.interruptedFourthOrder_nonzero

/-- Among the two vacuum orders analyzed here, the second-order correction
vanishes while the fourth-order interrupted exchange is finite and nonzero. -/
theorem firstFiniteResponse_is_interruptedFourthOrder
    (data : GlennPhotonExchangeData) :
    data.secondOrderResponse = 0 ∧
      data.fourthOrderResponse =
        doubleFrequencyConvolution data.interruptedFourthOrder ∧
      data.fourthOrderResponse ≠ 0 :=
  ⟨data.secondOrderResponse_eq_zero,
    data.fourthOrderResponse_eq_interrupted,
    data.fourthOrderResponse_ne_zero⟩

/-- The surviving interrupted fourth-order susceptibility yields a nonzero
third finite-difference response for every nonzero external field.  Combined
with `linearQMEResponse_thirdDifference_eq_zero`, this is the precise formal
separation between the full time-ordered response and the linear QME sector. -/
theorem interruptedFourthOrder_hasNonzeroCubicDifference
    (data : GlennPhotonExchangeData) (field : ℂ) (hfield : field ≠ 0) :
    opticalThirdDifference
        (cubicOpticalResponse data.fourthOrderResponse) field ≠ 0 :=
  cubicOpticalResponse_thirdDifference_ne_zero
    data.fourthOrderResponse field data.fourthOrderResponse_ne_zero hfield

end GlennPhotonExchangeData

end Physlib.QFT.ScalarGreenFunctions

end
