/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.SpaceAndTime.Space.Norm.Basic
public import Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Fourier.Convolution
meta import Zil

/-!
# The Newtonian convolution potential of a mass density (Schrödinger–Poisson)

The static gravitational potential sourced by a mass density `ρ` on `ℝ³` is the Newtonian volume
integral

  `φ_ρ(x) = ∫ ρ(y)/‖x − y‖ dy = (1/‖·‖) ⋆ ρ`,

the unique `𝒟^{1,2}` solution of the Poisson equation `−Δφ = 4πρ` (Chen–Tang, *Ground state solutions
of Schrödinger–Poisson systems with variable potential and convolution nonlinearity*, J. Math. Anal.
Appl. 2019, eq. (1.5), established there via Lax–Milgram). This is the continuum source generalizing
the point-mass fundamental solution `Space.distLaplacian_fundamentalSolution_norm_zpow`
(`Δ(1/‖x‖) = −4π·δ`) and the discrete finite-source superpositions, and it is the potential appearing
in the entropic-time Schrödinger–Poisson development
(`ComplexEinstein.EinsteinSchrodingerNonrelLimit`, `schrodingerPoissonChargeDensity`).

This module builds that potential and its immediate structural content:

* `newtonianConvolutionPotential ρ x = ∫ y, ρ y / ‖x − y‖` — the potential (Chen–Tang eq. (1.5));
* `newtonianConvolutionPotential_eq_convolution` — it is the Mathlib Bochner convolution
  `(1/‖·‖) ⋆ ρ`, exactly the second form in eq. (1.5);
* linearity in the source (`_add`, `_smul`);
* `newtonianSelfEnergy ρ = ∫ φ_ρ·ρ = ∬ ρ(x)ρ(y)/‖x − y‖` — the gravitational self-interaction energy,
  the convolution term of the Chen–Tang energy functional (1.10).
* `temperedConvolutionSchwartz` — a genuine convolution of a complex tempered distribution with
  a Schwartz density;
* `temperedConvolutionSchwartz_laplacian` — the distributional Laplacian commutes with that
  convolution;
* `temperedFundamentalSolution_convolution` — a fundamental solution convoluted with a Schwartz
  density solves the corresponding continuum distributional source equation.
* `complexifyRealDistribution3_laplacian` — the canonical scalar extension intertwines the
  repository's real distributional Laplacian with Mathlib's complex tempered one;
* `newtonKernelTempered3_laplacian` and `newtonTemperedPotential3_laplacian` — the existing
  `1/‖x‖` theorem supplies the full continuum Poisson equation;
* `inferenceNewtonTemperedPotential_laplacian` — the same equation with
  `G = ħcσ₀⁴`, without a primitive Newton-constant parameter.
* `newtonTemperedPotential3_poisson_and_energy_unique` — the same charted
  Schwartz source simultaneously has the distributional Poisson solution and
  a unique continuum `Ḣ¹₀` energy solution.

This module carries the potential as the Newtonian integral / convolution and its algebraic
self-energy identity. The complex Schwartz/tempered layer carries the proved real Newton
fundamental distribution into the continuum source mechanism. The Euclidean Fourier adapter proves
that every charted Schwartz source belongs to `Ḣ⁻¹(ℝ³)` and hence has a unique zero-boundary
`Ḣ¹` solution. Full inhomogeneous `H¹` regularity remains conditional on the separately exposed
infrared `L²` criterion; it is false for a generic nonzero-mass Newton tail.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000

open MeasureTheory
open Physlib
open scoped Convolution Space SchwartzMap Laplacian

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential

open Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization

/-- The three-dimensional Newtonian kernel `1/‖x‖`. -/
noncomputable def newtonKernel3 (x : Space 3) : ℝ := ‖x‖⁻¹

/-- **The Newtonian convolution potential** of a mass density `ρ` (Chen–Tang eq. (1.5)):
`φ_ρ(x) = ∫ ρ(y)/‖x − y‖ dy`. -/
noncomputable def newtonianConvolutionPotential (ρ : Space 3 → ℝ) (x : Space 3) : ℝ :=
  ∫ y, ρ y / ‖x - y‖

/-- **[The potential is the Newtonian Bochner convolution]** `φ_ρ = (1/‖·‖) ⋆ ρ`, the second form of
Chen–Tang eq. (1.5), reusing Mathlib's `MeasureTheory.convolution`. -/
@[zil_level physical_theorem]
theorem newtonianConvolutionPotential_eq_convolution (ρ : Space 3 → ℝ) (x : Space 3) :
    newtonianConvolutionPotential ρ x = (newtonKernel3 ⋆ ρ) x := by
  rw [newtonianConvolutionPotential, convolution_def,
    ← integral_sub_left_eq_self (fun y : Space 3 => ρ y / ‖x - y‖) volume x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [newtonKernel3, ContinuousLinearMap.lsmul_apply, smul_eq_mul, sub_sub_cancel]
  ring

/-- The Newtonian convolution potential is additive in the source density. -/
@[zil_level physical_theorem]
theorem newtonianConvolutionPotential_add (ρ σ : Space 3 → ℝ) (x : Space 3)
    (hρ : Integrable (fun y => ρ y / ‖x - y‖)) (hσ : Integrable (fun y => σ y / ‖x - y‖)) :
    newtonianConvolutionPotential (ρ + σ) x =
      newtonianConvolutionPotential ρ x + newtonianConvolutionPotential σ x := by
  unfold newtonianConvolutionPotential
  rw [← integral_add hρ hσ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply]
  ring

/-- The Newtonian convolution potential is homogeneous in the source density. -/
@[zil_level physical_theorem]
theorem newtonianConvolutionPotential_smul (c : ℝ) (ρ : Space 3 → ℝ) (x : Space 3) :
    newtonianConvolutionPotential (c • ρ) x = c • newtonianConvolutionPotential ρ x := by
  unfold newtonianConvolutionPotential
  rw [smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Spatial dilation of a mass density: `(dilateDensity t ρ) x = ρ (t • x)`. -/
def dilateDensity (t : ℝ) (ρ : Space 3 → ℝ) : Space 3 → ℝ := fun x => ρ (t • x)

/-- **[The potential scales as |t|⁻² under spatial dilation]** `φ_{ρ(t·)}(x) = |t|⁻²·φ_ρ(t·x)`, the
Newton-kernel homogeneity behind the Chen–Tang dilation scaling. The additive-Haar change of
variables (`integral_comp_smul`) needs no integrability hypothesis. -/
@[zil_level physical_theorem]
theorem newtonianConvolutionPotential_dilateDensity (t : ℝ) (ht : t ≠ 0) (ρ : Space 3 → ℝ)
    (x : Space 3) :
    newtonianConvolutionPotential (dilateDensity t ρ) x =
      (|t| ^ 2)⁻¹ * newtonianConvolutionPotential ρ (t • x) := by
  have ht' : |t| ≠ 0 := abs_ne_zero.mpr ht
  rw [newtonianConvolutionPotential]
  simp only [dilateDensity]
  rw [show (fun y : Space 3 => ρ (t • y) / ‖x - y‖)
        = (fun y : Space 3 => (fun w : Space 3 => ρ w / ‖x - t⁻¹ • w‖) (t • y)) from by
      funext y; simp only [smul_smul, inv_mul_cancel₀ ht, one_smul]]
  rw [Measure.integral_comp_smul volume (fun w : Space 3 => ρ w / ‖x - t⁻¹ • w‖) t,
    Space.finrank_eq_dim]
  have hw : ∀ w : Space 3, ρ w / ‖x - t⁻¹ • w‖ = |t| * (ρ w / ‖t • x - w‖) := fun w => by
    rw [show x - t⁻¹ • w = t⁻¹ • (t • x - w) from by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ ht, one_smul],
      norm_smul, Real.norm_eq_abs, abs_inv, div_mul_eq_div_div, div_inv_eq_mul, mul_comm,
      mul_div_assoc]
  simp_rw [hw]
  rw [integral_const_mul, newtonianConvolutionPotential, smul_eq_mul, abs_inv, abs_pow,
    ← mul_assoc]
  congr 1
  rw [pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ ht', mul_one]

/-- **The gravitational self-interaction energy** of a density `ρ`: `∫ φ_ρ·ρ`, the convolution term of
the Chen–Tang energy functional (1.10). -/
noncomputable def newtonianSelfEnergy (ρ : Space 3 → ℝ) : ℝ :=
  ∫ x, newtonianConvolutionPotential ρ x * ρ x

/-- **[The self-energy is the Newtonian double integral]**
`∫ φ_ρ·ρ = ∬ ρ(x)ρ(y)/‖x − y‖` — the pairwise gravitational binding energy of the density. -/
@[zil_level physical_theorem]
theorem newtonianSelfEnergy_eq_doubleIntegral (ρ : Space 3 → ℝ) :
    newtonianSelfEnergy ρ = ∫ x, ∫ y, ρ x * ρ y / ‖x - y‖ := by
  unfold newtonianSelfEnergy newtonianConvolutionPotential
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  ring

/-- **[The gravitational self-energy is quadratic in the source]** `E[c·ρ] = c²·E[ρ]`: scaling the
mass density by `c` scales the self-interaction energy by `c²`, since the potential is linear in the
source. -/
@[zil_level physical_theorem]
theorem newtonianSelfEnergy_smul (c : ℝ) (ρ : Space 3 → ℝ) :
    newtonianSelfEnergy (c • ρ) = c ^ 2 * newtonianSelfEnergy ρ := by
  unfold newtonianSelfEnergy
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [newtonianConvolutionPotential_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **[The gravitational self-energy scales as |t|⁻⁵ under spatial dilation]**
`E[ρ(t·)] = |t|⁻⁵·E[ρ]` — the Newton/Coulomb self-energy scaling exponent underlying the Chen–Tang
Nehari–Pohozaev manifold analysis (two `d = 3` additive-Haar changes of variables against the
degree-`−1` kernel). No integrability hypotheses are needed. -/
@[zil_level physical_theorem]
theorem newtonianSelfEnergy_dilateDensity (t : ℝ) (ht : t ≠ 0) (ρ : Space 3 → ℝ) :
    newtonianSelfEnergy (dilateDensity t ρ) = (|t| ^ 5)⁻¹ * newtonianSelfEnergy ρ := by
  have ht' : |t| ≠ 0 := abs_ne_zero.mpr ht
  rw [newtonianSelfEnergy]
  have key : ∀ x : Space 3,
      newtonianConvolutionPotential (dilateDensity t ρ) x * dilateDensity t ρ x
        = (|t| ^ 2)⁻¹ * (fun u : Space 3 => newtonianConvolutionPotential ρ u * ρ u) (t • x) :=
    fun x => by
      rw [newtonianConvolutionPotential_dilateDensity t ht ρ x]
      simp only [dilateDensity]
      ring
  simp_rw [key]
  rw [integral_const_mul,
    Measure.integral_comp_smul volume (fun u : Space 3 => newtonianConvolutionPotential ρ u * ρ u) t,
    Space.finrank_eq_dim, smul_eq_mul, abs_inv, abs_pow, ← mul_assoc, newtonianSelfEnergy]
  congr 1
  rw [← mul_inv, ← pow_add]

/-- The **Schrödinger–Poisson gravitational self-interaction energy** `¼∫φ_ρ·ρ` — the convolution
term of the Chen–Tang energy functional (1.10). -/
noncomputable def schrodingerPoissonGravitationalEnergy (ρ : Space 3 → ℝ) : ℝ :=
  (1 / 4) * newtonianSelfEnergy ρ

/-- **[The Schrödinger–Poisson gravitational energy is the ¼ Newtonian double integral]** — the
convolution term of the Chen–Tang energy functional (1.10) in explicit pairwise form. -/
@[zil_level physical_theorem]
theorem schrodingerPoissonGravitationalEnergy_eq_doubleIntegral (ρ : Space 3 → ℝ) :
    schrodingerPoissonGravitationalEnergy ρ =
      (1 / 4) * ∫ x, ∫ y, ρ x * ρ y / ‖x - y‖ := by
  rw [schrodingerPoissonGravitationalEnergy, newtonianSelfEnergy_eq_doubleIntegral]

/-- **[The Schrödinger–Poisson gravitational energy is quadratic in the source]** `E[c·ρ] = c²·E[ρ]`,
the scaling underlying the Chen–Tang Nehari–Pohozaev manifold analysis. -/
@[zil_level physical_theorem]
theorem schrodingerPoissonGravitationalEnergy_smul (c : ℝ) (ρ : Space 3 → ℝ) :
    schrodingerPoissonGravitationalEnergy (c • ρ) =
      c ^ 2 * schrodingerPoissonGravitationalEnergy ρ := by
  rw [schrodingerPoissonGravitationalEnergy, schrodingerPoissonGravitationalEnergy,
    newtonianSelfEnergy_smul]
  ring

/-! ## Continuum distributional convolution on Schwartz data -/

/-- The Laplacian commutes with convolution in the right Schwartz argument.  This is proved on the
actual Schwartz carrier through the Fourier-multiplier realization of the Laplacian, rather than
postulated as a distributional-convolution rule. -/
@[zil_level physical_theorem]
theorem schwartzLaplacian_convolution_right
    (f g : 𝓢(Space 3, ℂ)) :
    Δ (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g) =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f (Δ g) := by
  rw [SchwartzMap.laplacian_eq_fourierMultiplierCLM,
    SchwartzMap.laplacian_eq_fourierMultiplierCLM]
  apply_fun FourierTransform.fourier
  case inj =>
    intro a b hab
    calc
      a = FourierTransformInv.fourierInv (FourierTransform.fourier a) :=
        (FourierTransform.fourierInv_fourier_eq a).symm
      _ = FourierTransformInv.fourierInv (FourierTransform.fourier b) := congrArg _ hab
      _ = b := FourierTransform.fourierInv_fourier_eq b
  ext x
  simp [SchwartzMap.fourierMultiplierCLM_apply,
    SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop),
    SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp [SchwartzMap.pairing_apply_apply]
  ring

/-- Reflection of a complex Schwartz density, `ρ̌(x) = ρ(-x)`. -/
noncomputable def reflectSchwartz3 (f : 𝓢(Space 3, ℂ)) : 𝓢(Space 3, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := Space 3)) f

/-- Convolution of a complex tempered distribution `T` with a Schwartz density `f`.
It is the standard dual definition
`(T ⋆ f)(η) = T(f̌ ⋆ η)`, implemented by precomposition with the continuous Schwartz
convolution operator. -/
noncomputable def temperedConvolutionSchwartz
    (T : 𝓢'(Space 3, ℂ)) (f : 𝓢(Space 3, ℂ)) : 𝓢'(Space 3, ℂ) :=
  PointwiseConvergenceCLM.precomp ℂ
    (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (reflectSchwartz3 f)) T

/-- **[Distributional derivatives commute with continuum convolution]**
`Δ(T ⋆ f) = (ΔT) ⋆ f` for every complex tempered distribution and Schwartz density. -/
@[zil_level physical_theorem]
theorem temperedConvolutionSchwartz_laplacian
    (T : 𝓢'(Space 3, ℂ)) (f : 𝓢(Space 3, ℂ)) :
    Δ (temperedConvolutionSchwartz T f) =
      temperedConvolutionSchwartz (Δ T) f := by
  ext η
  rw [TemperedDistribution.laplacian_apply_apply]
  change T (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (reflectSchwartz3 f) (Δ η)) =
    (Δ T) (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (reflectSchwartz3 f) η)
  rw [TemperedDistribution.laplacian_apply_apply]
  congr 1
  exact (schwartzLaplacian_convolution_right (reflectSchwartz3 f) η).symm

/-- Dirac convolution is exactly the regular continuum density pairing:
`(δ₀ ⋆ f)(η) = ∫ f(x)η(x) dx`. -/
@[zil_level physical_theorem]
theorem delta_temperedConvolutionSchwartz_apply
    (f η : 𝓢(Space 3, ℂ)) :
    temperedConvolutionSchwartz (TemperedDistribution.delta 0) f η =
      ∫ x, f x * η x := by
  change SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (reflectSchwartz3 f) η 0 = _
  rw [SchwartzMap.convolution_apply, MeasureTheory.convolution_def,
    ← MeasureTheory.integral_neg_eq_self]
  congr 1
  funext x
  simp [reflectSchwartz3]

/-- **[A fundamental solution yields the full continuum source]**
If `T` satisfies `ΔT = c·δ₀`, then its convolution with every Schwartz density satisfies
`Δ(T⋆f) = c·(δ₀⋆f)`, whose action is the ordinary density integral by
`delta_temperedConvolutionSchwartz_apply`. -/
@[zil_level physical_theorem]
theorem temperedFundamentalSolution_convolution
    (T : 𝓢'(Space 3, ℂ)) (f : 𝓢(Space 3, ℂ)) (c : ℂ)
    (hT : Δ T = c • TemperedDistribution.delta 0) :
    Δ (temperedConvolutionSchwartz T f) =
      c • temperedConvolutionSchwartz (TemperedDistribution.delta 0) f := by
  rw [temperedConvolutionSchwartz_laplacian, hT]
  rfl

/-! ## Scalar extension of the proved real Newton kernel -/

/-- Real-part projection from complex to real Schwartz test functions. -/
noncomputable def realPartSchwartz3 :
    𝓢(Space 3, ℂ) →L[ℝ] 𝓢(Space 3, ℝ) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM

/-- Imaginary-part projection from complex to real Schwartz test functions. -/
noncomputable def imaginaryPartSchwartz3 :
    𝓢(Space 3, ℂ) →L[ℝ] 𝓢(Space 3, ℝ) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.imCLM

/-- The complex-linear extension of a real Physlib distribution to complex Schwartz tests. -/
noncomputable def complexifyRealDistribution3CLM
    (T : (Space 3) →d[ℝ] ℝ) : 𝓢(Space 3, ℂ) →L[ℂ] ℂ where
  toFun f :=
    (T (realPartSchwartz3 f) : ℂ) +
      Complex.I * (T (imaginaryPartSchwartz3 f) : ℂ)
  map_add' f g := by
    simp [map_add]
    ring
  map_smul' z f := by
    have hRe :
        realPartSchwartz3 (z • f) =
          z.re • realPartSchwartz3 f - z.im • imaginaryPartSchwartz3 f := by
      ext x
      simp [realPartSchwartz3, imaginaryPartSchwartz3, Complex.mul_re]
    have hIm :
        imaginaryPartSchwartz3 (z • f) =
          z.im • realPartSchwartz3 f + z.re • imaginaryPartSchwartz3 f := by
      ext x
      simp [realPartSchwartz3, imaginaryPartSchwartz3, Complex.mul_im]
      ring
    simp only [RingHom.id_apply]
    rw [hRe, hIm]
    simp [map_sub, map_add, map_smul, smul_eq_mul]
    apply Complex.ext <;> simp <;> ring
  cont := by
    fun_prop

/-- Scalar extension of a real Physlib distribution to Mathlib's complex tempered carrier. -/
noncomputable def complexifyRealDistribution3
    (T : (Space 3) →d[ℝ] ℝ) : 𝓢'(Space 3, ℂ) :=
  ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _
    (complexifyRealDistribution3CLM T)

@[simp]
lemma complexifyRealDistribution3_apply
    (T : (Space 3) →d[ℝ] ℝ) (f : 𝓢(Space 3, ℂ)) :
    complexifyRealDistribution3 T f =
      (T (realPartSchwartz3 f) : ℂ) +
        Complex.I * (T (imaginaryPartSchwartz3 f) : ℂ) :=
  rfl

/-- Scalar extension transports the real Dirac distribution to Mathlib's complex Dirac
distribution, rather than introducing an unrelated point-source carrier. -/
@[zil_level physical_theorem]
theorem complexifyRealDistribution3_dirac :
    complexifyRealDistribution3
        (Physlib.Distribution.diracDelta ℝ (0 : Space 3)) =
      TemperedDistribution.delta 0 := by
  ext f
  simp [complexifyRealDistribution3_apply, realPartSchwartz3, imaginaryPartSchwartz3]
  rw [mul_comm]
  exact Complex.re_add_im (f 0)

/-- Scalar extension commutes with multiplication by a real coefficient. -/
lemma complexifyRealDistribution3_smul
    (c : ℝ) (T : (Space 3) →d[ℝ] ℝ) :
    complexifyRealDistribution3 (c • T) =
      (c : ℂ) • complexifyRealDistribution3 T := by
  ext f
  simp [complexifyRealDistribution3_apply, smul_eq_mul]
  apply Complex.ext <;> simp

/-- Physlib's real distributional Laplacian acts by the ordinary Laplacian on real Schwartz
test functions. This is the integration-by-parts sign cancellation for two derivatives. -/
lemma realDistLaplacian_apply
    (T : (Space 3) →d[ℝ] ℝ) (f : 𝓢(Space 3, ℝ)) :
    (Δᵈ T) f = T (Δ f) := by
  rw [Space.distLaplacian]
  change Space.distDiv (Space.distGrad T) f = _
  rw [Space.distDiv_apply_eq_sum_distDeriv]
  simp_rw [Space.distDeriv_apply, Physlib.Distribution.fderivD_apply]
  rw [SchwartzMap.laplacian_eq_sum Space.basis, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change
    - ((∇ᵈ T) (LineDeriv.lineDerivOp (Space.basis i) f)).ofLp i =
      T (LineDeriv.lineDerivOp (Space.basis i)
        (LineDeriv.lineDerivOp (Space.basis i) f))
  rw [Space.distGrad_apply]
  change
    - (∂ᵈ[i] T) (LineDeriv.lineDerivOp (Space.basis i) f) =
      T (LineDeriv.lineDerivOp (Space.basis i)
        (LineDeriv.lineDerivOp (Space.basis i) f))
  rw [Space.distDeriv_apply, Physlib.Distribution.fderivD_apply]
  simp only [neg_neg]
  rfl

lemma realPartSchwartz3_lineDeriv
    (v : Space 3) (f : 𝓢(Space 3, ℂ)) :
    realPartSchwartz3 (LineDeriv.lineDerivOp v f) =
      LineDeriv.lineDerivOp v (realPartSchwartz3 f) := by
  ext x
  simp only [realPartSchwartz3, SchwartzMap.postcompCLM_apply,
    Complex.reCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have h :=
    (Complex.reCLM.hasFDerivAt.comp x (f.hasFDerivAt x))
  exact (congrArg (fun L : Space 3 →L[ℝ] ℝ => L v) h.fderiv).symm

lemma realPartSchwartz3_laplacian (f : 𝓢(Space 3, ℂ)) :
    realPartSchwartz3 (Δ f) =
      (Δ (realPartSchwartz3 f) : 𝓢(Space 3, ℝ)) := by
  rw [SchwartzMap.laplacian_eq_sum Space.basis,
    SchwartzMap.laplacian_eq_sum Space.basis]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [realPartSchwartz3_lineDeriv, realPartSchwartz3_lineDeriv]

lemma imaginaryPartSchwartz3_lineDeriv
    (v : Space 3) (f : 𝓢(Space 3, ℂ)) :
    imaginaryPartSchwartz3 (LineDeriv.lineDerivOp v f) =
      LineDeriv.lineDerivOp v (imaginaryPartSchwartz3 f) := by
  ext x
  simp only [imaginaryPartSchwartz3, SchwartzMap.postcompCLM_apply,
    Complex.imCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have h :=
    (Complex.imCLM.hasFDerivAt.comp x (f.hasFDerivAt x))
  exact (congrArg (fun L : Space 3 →L[ℝ] ℝ => L v) h.fderiv).symm

lemma imaginaryPartSchwartz3_laplacian (f : 𝓢(Space 3, ℂ)) :
    imaginaryPartSchwartz3 (Δ f) =
      (Δ (imaginaryPartSchwartz3 f) : 𝓢(Space 3, ℝ)) := by
  rw [SchwartzMap.laplacian_eq_sum Space.basis,
    SchwartzMap.laplacian_eq_sum Space.basis]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [imaginaryPartSchwartz3_lineDeriv, imaginaryPartSchwartz3_lineDeriv]

/-- **[Real-to-complex distribution compatibility]** Scalar extension intertwines Physlib's real
distributional Laplacian with Mathlib's complex tempered-distribution Laplacian. -/
@[zil_level physical_theorem]
theorem complexifyRealDistribution3_laplacian
    (T : (Space 3) →d[ℝ] ℝ) :
    complexifyRealDistribution3 (Δᵈ T) =
      Δ (complexifyRealDistribution3 T) := by
  ext f
  rw [TemperedDistribution.laplacian_apply_apply]
  simp only [complexifyRealDistribution3_apply, realDistLaplacian_apply]
  rw [realPartSchwartz3_laplacian, imaginaryPartSchwartz3_laplacian]

/-- The existing real distribution `1/‖x‖`, transported to the complex tempered carrier. -/
noncomputable def newtonKernelTempered3 : 𝓢'(Space 3, ℂ) :=
  complexifyRealDistribution3 <|
    Space.distOfFunction
      (fun x : Space 3 => ‖x‖ ^ (- ((3 : ℤ) - 2)))
      (Space.IsDistBounded.pow _ (by omega))

/-- **[The transported Newton kernel is a fundamental solution]**
`Δ(1/‖x‖) = -4πδ₀` on the complex tempered carrier, derived from the existing real Physlib
fundamental-solution theorem through the proved scalar extension. -/
@[zil_level physical_theorem]
theorem newtonKernelTempered3_laplacian :
    Δ newtonKernelTempered3 =
      (-4 * Real.pi : ℂ) • TemperedDistribution.delta 0 := by
  have hReal :
      Δᵈ (Space.distOfFunction
        (fun x : Space 3 => ‖x‖ ^ (- ((3 : ℤ) - 2)))
        (Space.IsDistBounded.pow _ (by omega))) =
        (-4 * Real.pi) •
          Physlib.Distribution.diracDelta ℝ (0 : Space 3) := by
    have h :=
      (Space.distLaplacian_fundamentalSolution_norm_zpow (d := 3))
    rw [Space.volume_metricBall_three_real] at h
    convert h using 1 <;> ring
  have h := congrArg complexifyRealDistribution3 hReal
  rw [complexifyRealDistribution3_laplacian,
    complexifyRealDistribution3_smul,
    complexifyRealDistribution3_dirac] at h
  simpa [newtonKernelTempered3] using h

/-- The full continuum Newton potential of a complex Schwartz density on the tempered carrier. -/
noncomputable def newtonTemperedPotential3
    (f : 𝓢(Space 3, ℂ)) : 𝓢'(Space 3, ℂ) :=
  temperedConvolutionSchwartz newtonKernelTempered3 f

/-- **[Continuum distributional Poisson equation]**
`Δ(K⋆f) = -4π(δ₀⋆f)` for every complex Schwartz density. The right-hand side acts as
`-4π∫fη` on every test function. -/
@[zil_level physical_theorem]
theorem newtonTemperedPotential3_laplacian (f : 𝓢(Space 3, ℂ)) :
    Δ (newtonTemperedPotential3 f) =
      (-4 * Real.pi : ℂ) •
        temperedConvolutionSchwartz (TemperedDistribution.delta 0) f := by
  exact temperedFundamentalSolution_convolution
    newtonKernelTempered3 f (-4 * Real.pi) newtonKernelTempered3_laplacian

/-! ## The same source on the continuum Sobolev-energy carrier -/

/-- The standard zero-origin linear chart from Mathlib's Euclidean
three-space to Physlib's affine `Space 3`.  It is assembled from the existing
coordinate equivalences rather than introducing a second spatial model. -/
noncomputable def euclideanToSpaceThree :
    EuclideanSpace ℝ (Fin 3) ≃L[ℝ] Space 3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).trans (Space.equivPi 3).symm

/-- A Physlib Schwartz density pulled back through the standard linear chart.
Continuous-linear-equivalence composition preserves the Schwartz class. -/
noncomputable def spaceSchwartzToEuclideanThree
    (f : 𝓢(Space 3, ℂ)) :
    𝓢(EuclideanSpace ℝ (Fin 3), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ euclideanToSpaceThree f

@[simp]
lemma spaceSchwartzToEuclideanThree_apply
    (f : 𝓢(Space 3, ℂ)) (x : EuclideanSpace ℝ (Fin 3)) :
    spaceSchwartzToEuclideanThree f x = f (euclideanToSpaceThree x) :=
  rfl

/-- The charted density as an actual `Ḣ⁻¹(ℝ³)` source.  Membership is proved
by the inverse-frequency integrability theorem, not supplied by the caller. -/
noncomputable def newtonSchwartzDotHMinusOneThree
    (f : 𝓢(Space 3, ℂ)) : FourierDotHMinusOneThree :=
  schwartzSourceDotHMinusOne (spaceSchwartzToEuclideanThree f)

/-- **Distributional Poisson plus zero-boundary energy well-posedness.**
For the same Schwartz density, the existing tempered convolution solves the
distributional equation, while its Euclidean-chart source has one and only one
continuum `Ḣ¹₀` weak solution. -/
@[zil_level physical_theorem]
theorem newtonTemperedPotential3_poisson_and_energy_unique
    (f : 𝓢(Space 3, ℂ)) :
    Δ (newtonTemperedPotential3 f) =
        (-4 * Real.pi : ℂ) •
          temperedConvolutionSchwartz (TemperedDistribution.delta 0) f ∧
      ∃! energyDerivative : FourierDotHOneThree,
        IsFourierDotHOneWeakSolution
          (newtonSchwartzDotHMinusOneThree f) energyDerivative := by
  exact ⟨newtonTemperedPotential3_laplacian f,
    existsUnique_fourierDotHOneWeakSolution
      (newtonSchwartzDotHMinusOneThree f)⟩

/-- The unique energy derivative is explicitly the inverse-frequency Fourier
profile of the charted source. -/
lemma newtonSchwartz_energySolution_eq
    (f : 𝓢(Space 3, ℂ)) :
    fourierDotHOnePoissonSolution
        (newtonSchwartzDotHMinusOneThree f) =
      schwartzSourceEnergyVector
        (spaceSchwartzToEuclideanThree f) :=
  fourierDotHOnePoissonSolution_schwartzSource
    (spaceSchwartzToEuclideanThree f)

/-- Precise full-`H¹` boundary for the charted Newton solution.  The
homogeneous energy part is automatic; the only remaining condition is
infrared `L²` integrability of `ρ̂/|ξ|²`. -/
lemma newtonSchwartz_besselOne_memLp_iff
    (f : 𝓢(Space 3, ℂ)) :
    MemLp (fun ξ =>
        (besselPotentialWeight 1 ξ : ℂ) *
          schwartzNewtonFourierPotential
            (spaceSchwartzToEuclideanThree f) ξ) 2 ↔
      MemLp (schwartzNewtonFourierPotential
        (spaceSchwartzToEuclideanThree f)) 2 :=
  schwartzNewtonFourierPotential_besselOne_memLp_iff
    (spaceSchwartzToEuclideanThree f)

/-- Newton's potential with the inference-scale coupling `G = ħcσ₀⁴`, without a primitive
Newton-constant parameter. -/
noncomputable def inferenceNewtonTemperedPotential
    (ħ c σ₀ : ℝ) (f : 𝓢(Space 3, ℂ)) : 𝓢'(Space 3, ℂ) :=
  (-(ħ * c * σ₀ ^ 4) : ℂ) • newtonTemperedPotential3 f

/-- **[The `G = ħcσ₀⁴` continuum Poisson equation]**
The inferred Newton potential solves
`ΔΦ = 4π(ħcσ₀⁴)ρ` distributionally for every complex Schwartz source. -/
@[zil_level physical_theorem]
theorem inferenceNewtonTemperedPotential_laplacian
    (ħ c σ₀ : ℝ) (f : 𝓢(Space 3, ℂ)) :
    Δ (inferenceNewtonTemperedPotential ħ c σ₀ f) =
      (4 * Real.pi * (ħ * c * σ₀ ^ 4) : ℂ) •
        temperedConvolutionSchwartz (TemperedDistribution.delta 0) f := by
  rw [inferenceNewtonTemperedPotential,
    ← TemperedDistribution.laplacianCLM_apply, map_smul,
    TemperedDistribution.laplacianCLM_apply,
    newtonTemperedPotential3_laplacian, smul_smul]
  congr 1
  push_cast
  ring

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianConvolutionPotential_eq_convolution where
  formalizes @ "claim:the-newtonian-convolution-potential-of-a-mass-density-defined-as-the-volume-integral-of-rho-y-over-norm-x-minus-y-equals-the-bochner-convolution-of-the-newton-kernel-one-over-norm-x-with-rho-chen-tang-2019-equation-one-point-five",
  supported_by @ "paper:chen-tang-2019-ground-state-solutions-of-schrodinger-poisson-systems-with-variable-potential-and-convolution-nonlinearity-jmaa-equation-1-5",
  supported_by @ "lean:MeasureTheory.convolution_def"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianSelfEnergy_eq_doubleIntegral where
  formalizes @ "claim:the-gravitational-self-interaction-energy-integral-of-the-newtonian-convolution-potential-times-the-density-equals-the-newtonian-double-integral-of-rho-x-rho-y-over-norm-x-minus-y-the-convolution-term-of-the-chen-tang-energy-functional"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.schwartzLaplacian_convolution_right where
  formalizes @ "claim:on-complex-schwartz-space-the-laplacian-of-a-convolution-equals-convolution-with-the-laplacian-in-the-right-argument",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:SchwartzMap.laplacian_eq_fourierMultiplierCLM",
  supported_by @ "lean:SchwartzMap.fourier_convolution",
  caveat @ "an-exact-fourier-multiplier-identity-on-the-schwartz-carrier-not-a-physical-field-equation"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.temperedConvolutionSchwartz_laplacian where
  formalizes @ "claim:the-distributional-laplacian-commutes-with-the-genuine-convolution-of-a-complex-tempered-distribution-and-a-schwartz-density",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.schwartzLaplacian_convolution_right",
  caveat @ "an-exact-operator-identity-on-the-complex-tempered-carrier-not-by-itself-a-choice-of-physical-fundamental-solution"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.delta_temperedConvolutionSchwartz_apply where
  supported_by @ "lean:CPTPMap.funext",
  supported_by @ "lean:HasVarAdjDerivAt.mul",
  formalizes @ "claim:convolving-the-dirac-delta-with-a-schwartz-density-acts-on-every-test-function-as-the-ordinary-continuum-density-integral",
  epistemic_status @ "consistency-identity",
  caveat @ "this-identifies-the-source-action-exactly-and-does-not-assert-positivity-normalization-or-a-specific-physical-density"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.temperedFundamentalSolution_convolution where
  formalizes @ "claim:any-tempered-fundamental-solution-with-laplacian-c-times-dirac-produces-by-convolution-the-full-continuum-distributional-source-c-times-the-density",
  epistemic_status @ "consistency-identity",
  requires @ "assumption:the-selected-complex-tempered-kernel-is-a-fundamental-solution-with-laplacian-c-times-dirac",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.temperedConvolutionSchwartz_laplacian",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.delta_temperedConvolutionSchwartz_apply",
  caveat @ "this-generic-distributional-identity-holds-exactly-by-rewrite-given-the-mathematical-fundamental-solution-hypothesis-delta-t-equals-c-dirac-a-precondition-not-an-empirical-ansatz-which-the-newton-kernel-instantiation-below-discharges"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.complexifyRealDistribution3_dirac where
  formalizes @ "claim:the-canonical-complex-linear-extension-of-the-real-physlib-dirac-distribution-is-exactly-the-mathlib-complex-tempered-dirac-distribution",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Distribution.diracDelta_apply",
  caveat @ "a-carrier-compatibility-theorem-not-a-physical-source-postulate"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.complexifyRealDistribution3_laplacian where
  formalizes @ "claim:canonical-real-to-complex-scalar-extension-of-distributions-intertwines-the-physlib-real-distributional-laplacian-and-the-mathlib-complex-tempered-laplacian",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.realDistLaplacian_apply",
  caveat @ "an-exact-intertwining-identity-on-schwartz-test-functions"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonKernelTempered3_laplacian where
  formalizes @ "claim:the-existing-real-physlib-one-over-norm-fundamental-distribution-transported-to-the-complex-tempered-carrier-has-laplacian-minus-four-pi-times-dirac",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Space.distLaplacian_fundamentalSolution_norm_zpow",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.complexifyRealDistribution3_laplacian",
  caveat @ "this-is-the-exact-three-dimensional-fundamental-solution-normalization-not-a-boundary-condition-or-uniqueness-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonTemperedPotential3_laplacian where
  formalizes @ "claim:convolving-the-proved-three-dimensional-newton-fundamental-distribution-with-every-complex-schwartz-density-solves-the-full-continuum-distributional-poisson-equation",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-existing-real-physlib-one-over-norm-fundamental-distribution-transported-to-the-complex-tempered-carrier-has-laplacian-minus-four-pi-times-dirac",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.temperedFundamentalSolution_convolution",
  caveat @ "schwartz-source-and-tempered-distribution-solution-theorem-it-does-not-claim-h-one-regularity-or-uniqueness-under-boundary-conditions"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonTemperedPotential3_poisson_and_energy_unique where
  formalizes @ "claim:every-complex-schwartz-density-on-three-space-simultaneously-generates-the-proved-tempered-distributional-newton-potential-and-a-unique-zero-boundary-homogeneous-h-one-weak-energy-solution",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonTemperedPotential3_laplacian",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.inverseNormSchwartzThree_memLp_two",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.existsUnique_fourierDotHOneWeakSolution",
  caveat @ "the-distributional-and-energy-solutions-are-linked-to-the-same-source-through-the-standard-linear-chart-the-theorem-does-not-identify-the-two-carrier-representatives-pointwise-and-full-inhomogeneous-h-one-still-requires-the-explicit-infrared-l-two-condition"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.inferenceNewtonTemperedPotential_laplacian where
  formalizes @ "claim:with-the-model-identification-newton-G-equals-hbar-times-c-times-sigma-zero-to-the-fourth-the-continuum-tempered-newton-potential-solves-laplacian-phi-equals-four-pi-times-hbar-c-sigma-zero-four-times-the-density",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-inference-scale-identification-G-equals-hbar-c-sigma-zero-to-the-fourth",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonTemperedPotential3_laplacian",
  caveat @ "derives-the-continuum-poisson-law-conditionally-on-the-inference-scale-identification-and-does-not-fit-sigma-zero-to-the-measured-newton-constant"

zil_file_contract physlib.newtonianConvolutionPotential where
  promises "The static Newtonian convolution potential of a mass density on R^3 (Schrodinger-Poisson / Choquard source). newtonianConvolutionPotential rho x = integral of rho(y)/norm(x-y) dy is the Newtonian volume integral (Chen-Tang J. Math. Anal. Appl. 2019 equation 1.5), and newtonianConvolutionPotential_eq_convolution proves it equals the Mathlib Bochner convolution (1/norm) star rho (the second form of eq 1.5), reusing MeasureTheory.convolution. The potential is additive and homogeneous in the source. newtonianSelfEnergy rho is the gravitational self-interaction energy and equals the Newtonian density double integral, the convolution term of Chen-Tang equation 1.10. The continuum distributional layer is constructed on genuine complex Schwartz and tempered-distribution carriers. Canonical scalar extension transports the existing real Physlib Dirac and distributional Laplacian to Mathlib's complex tempered carrier; therefore the repository's already-proved real one-over-norm fundamental solution becomes newtonKernelTempered3 with Laplacian minus four pi Dirac. Convolution then proves the full continuum Poisson equation for every complex Schwartz density. The same charted Schwartz source is proved to lie in homogeneous H-minus-one because its inverse-frequency square singularity is locally integrable in dimension three, yielding a unique zero-boundary homogeneous H-one weak solution. inferenceNewtonTemperedPotential_laplacian supplies the G-free coefficient four pi hbar c sigma-zero-four. Honest: the latter coefficient is conditional on the model identification G equals hbar c sigma-zero-four; full inhomogeneous H-one regularity requires the explicit infrared L-two condition and derivation of the scale identification remains separate."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:MeasureTheory.convolution",
    "lean:MeasureTheory.convolution_def",
    "lean:SchwartzMap.laplacian_eq_fourierMultiplierCLM",
    "lean:SchwartzMap.fourier_convolution",
    "lean:TemperedDistribution.laplacian_apply_apply",
    "lean:Space.distLaplacian_fundamentalSolution_norm_zpow"]
  forbids_substitutes ["a point-mass or finite-sum source, whereas this is the continuum convolution potential of a general density rho",
    "the discrete fundamental solution alone, whereas this is the Newtonian volume integral over the continuum source"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianConvolutionPotential_eq_convolution,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianConvolutionPotential_add,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianConvolutionPotential_smul,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianSelfEnergy_eq_doubleIntegral,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianConvolutionPotential_dilateDensity,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianSelfEnergy_dilateDensity,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonianSelfEnergy_smul,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.schrodingerPoissonGravitationalEnergy_eq_doubleIntegral,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.schrodingerPoissonGravitationalEnergy_smul,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.schwartzLaplacian_convolution_right,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.temperedConvolutionSchwartz_laplacian,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.delta_temperedConvolutionSchwartz_apply,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.temperedFundamentalSolution_convolution,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.complexifyRealDistribution3_dirac,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.complexifyRealDistribution3_laplacian,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonKernelTempered3_laplacian,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonTemperedPotential3_laplacian,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonTemperedPotential3_poisson_and_energy_unique,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.inferenceNewtonTemperedPotential_laplacian]

/- ZIL-END -/
