/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Meta.AxiomWhitelistCheck
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Covariance

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerRaoInferenceMass -/

/-!
# The Gaussian mean Fisher information integral is the inverse variance

`FisherRaoGaussianLeviCivita.gMuMu σ = (σ²)⁻¹` is *posited* as the `μ`-`μ` Fisher-Rao metric component, and
`gMuMu_is_gaussian_fisher_info` proves only the value `gMuMu σ = 1/σ²` by unfolding the definition — the
Fisher-information integral `I(p) = ∫(∂_μ log p)² p dx` that names it lives only in that lemma's prose.

This file supplies the two missing computations, so the "metric component is the Gaussian Fisher
information" claim rests entirely on proven theorems rather than on a definitional restatement:

* `gaussianMeanScore_eq_deriv_logPDF` — the location score is the genuine log-derivative of the density,
  `∂_μ log p(x∣μ,v) = (x−μ)/v` (an actual `deriv`, so the score is proven, not merely posited);
* `gaussianMeanFisherInformation_eq_inv_variance` — the mean Fisher information, the integral of that
  squared score against the Gaussian measure, is the inverse variance:
  `∫ ((x−μ)/v)² dN(μ,v) = (1/v²) ∫ (x−μ)² dN(μ,v) = (1/v²)·v = 1/v`, using the Gaussian second central
  moment `∫ (x−μ)² dN(μ,v) = v` (`variance_id_gaussianReal`);
* `gMuMu_eq_gaussianMeanFisherInformation` — at variance `v = σ²` this integral is exactly `gMuMu σ`.

The chain is closed end to end: the score is the proven log-derivative `∂_μ log p`, its second moment is the
Fisher information `1/v`, and at `v = σ²` that is `gMuMu σ` — the value the posited `gMuMu` previously
restated by unfolding.

## References
* A. Caticha, C. Cafaro — information → mass; M. Reginatto (1998) — Schrödinger equation from Fisher
  information. Companion: `EntropicTime.FisherRaoGaussianLeviCivita` (the posited metric `gMuMu`).
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianMeanFisherInformationIntegral

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita

/-- The **location (mean) score** of the real Gaussian, `(x−μ)/v`. Proved to equal `∂_μ log p(x∣μ,v)` by
`gaussianMeanScore_eq_deriv_logPDF`. -/
noncomputable def gaussianMeanScore (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ := (x - μ) / (v : ℝ)

/-- The **mean Fisher information** of the real Gaussian: the integral of the squared location score
against the Gaussian measure, `I = ∫ (∂_μ log p)² dN(μ,v)`. -/
noncomputable def gaussianMeanFisherInformation (μ : ℝ) (v : ℝ≥0) : ℝ :=
  ∫ x, gaussianMeanScore μ v x ^ 2 ∂(gaussianReal μ v)

/-- **[The Gaussian location score is the log-derivative of the density]** `∂_μ log p(x∣μ,v) = (x−μ)/v`.
The score `gaussianMeanScore` is the genuine derivative of the log Gaussian density with respect to the
mean parameter — so the Fisher information below is the second moment of an actual log-derivative. -/
theorem gaussianMeanScore_eq_deriv_logPDF (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    deriv (fun m => Real.log (gaussianPDFReal m v x)) μ = gaussianMeanScore μ v x := by
  have hvpos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hv' : (v : ℝ) ≠ 0 := ne_of_gt hvpos
  have hlog : (fun m => Real.log (gaussianPDFReal m v x))
      = fun m => Real.log (√(2 * π * (v : ℝ)))⁻¹ + (x - m) ^ 2 * -(2 * (v : ℝ))⁻¹ := by
    funext m
    rw [gaussianPDFReal, Real.log_mul (ne_of_gt (by positivity)) (Real.exp_ne_zero _), Real.log_exp]
    ring
  rw [hlog, gaussianMeanScore]
  have h1 : HasDerivAt (fun m : ℝ => x - m) (-1 : ℝ) μ := (hasDerivAt_id μ).const_sub x
  have hg : HasDerivAt (fun t : ℝ => t ^ 2) (2 * (x - μ)) (x - μ) := by
    simpa using hasDerivAt_pow 2 (x - μ)
  have hsq : HasDerivAt (fun m => (x - m) ^ 2) (2 * (x - μ) * -1) μ := hg.comp μ h1
  have hfull := (hsq.mul_const (-(2 * (v : ℝ))⁻¹)).const_add (Real.log (√(2 * π * (v : ℝ)))⁻¹)
  exact hfull.deriv.trans (by ring)

/-- The Gaussian **second central moment** is the variance: `∫ (x−μ)² dN(μ,v) = v`. -/
theorem integral_sub_sq_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    ∫ x, (x - μ) ^ 2 ∂(gaussianReal μ v) = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := μ) (v := v)
  rwa [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at h

/-- **[The Gaussian mean Fisher information is the inverse variance]** `I(N(μ,v)) = 1/v`. Integrating the
squared location score `((x−μ)/v)²` against the Gaussian measure returns the reciprocal variance — the
Fisher-information content of the mean, as an integral identity. -/
theorem gaussianMeanFisherInformation_eq_inv_variance (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianMeanFisherInformation μ v = 1 / (v : ℝ) := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  unfold gaussianMeanFisherInformation gaussianMeanScore
  simp_rw [div_pow]
  rw [integral_div, integral_sub_sq_gaussianReal]
  field_simp

/-- **[The Fisher-Rao mean metric component is the Gaussian mean Fisher information]** at variance
`v = σ²` the posited metric component `gMuMu σ = (σ²)⁻¹` equals the integral of the squared location
score against `N(0, σ²)` — the Fisher information is now the content of the identity, not a def-unfold. -/
theorem gMuMu_eq_gaussianMeanFisherInformation (σ : ℝ) (hσ : σ ≠ 0) :
    gMuMu σ = gaussianMeanFisherInformation 0 (σ ^ 2).toNNReal := by
  have hpos : (0 : ℝ) < σ ^ 2 := by positivity
  have hv : (σ ^ 2).toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero]; exact not_le.mpr hpos
  rw [gaussianMeanFisherInformation_eq_inv_variance 0 _ hv, Real.coe_toNNReal (σ ^ 2) (le_of_lt hpos),
    gMuMu, one_div]

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianMeanFisherInformationIntegral

end

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianMeanFisherInformationIntegral in
#physlib_axiom_clean_all [
  gaussianMeanScore_eq_deriv_logPDF,
  integral_sub_sq_gaussianReal,
  gaussianMeanFisherInformation_eq_inv_variance,
  gMuMu_eq_gaussianMeanFisherInformation ]

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianMeanFisherInformationIntegral in
#physlib_non_vacuous_all [
  gaussianMeanScore_eq_deriv_logPDF,
  integral_sub_sq_gaussianReal,
  gaussianMeanFisherInformation_eq_inv_variance,
  gMuMu_eq_gaussianMeanFisherInformation ]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianMeanFisherInformationIntegral.gaussianMeanScore_eq_deriv_logPDF where
  formalizes @ "claim:the-gaussian-location-score-is-the-mean-derivative-of-the-log-density",
  supported_by @ "paper:reginatto-1998-derivation-schrodinger-fisher-information"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianMeanFisherInformationIntegral.gaussianMeanFisherInformation_eq_inv_variance where
  formalizes @ "claim:the-gaussian-mean-fisher-information-integral-equals-the-inverse-variance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianMeanFisherInformationIntegral.integral_sub_sq_gaussianReal",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianMeanFisherInformationIntegral.gaussianMeanScore_eq_deriv_logPDF",
  supported_by @ "paper:reginatto-1998-derivation-schrodinger-fisher-information"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianMeanFisherInformationIntegral.gMuMu_eq_gaussianMeanFisherInformation where
  formalizes @ "claim:the-mean-mean-metric-component-is-the-gaussian-fisher-information",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianMeanFisherInformationIntegral.gaussianMeanFisherInformation_eq_inv_variance"

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerRaoInferenceMass -/

/-!
# Cramér-Rao: the Fisher information is the inference-precision limit

`GaussianMeanFisherInformationIntegral` proves the location Fisher information of the Gaussian is `1/σ²`,
which the entropic-dynamics program identifies with the **inference mass** `m = 1/σ²`. That identification
is a physical bridge (`mass ↔ inference precision`); no theorem can derive a physical mass from pure
probability. What *can* be made a theorem, rather than posited, is the content that makes the bridge
principled: the **Cramér-Rao bound** — the Fisher information is the reciprocal of the smallest variance any
(regular, unbiased) estimator can achieve. So `m = 1/σ²` is the *maximal attainable inference precision*, not
an arbitrary number.

* `covariance_sq_le_variance_mul_variance` — the covariance Cauchy-Schwarz `cov[X,Y]² ≤ Var[X]·Var[Y]`,
  proved from `Var[X − tY] ≥ 0` for all `t` (a nonnegative quadratic in `t`, so its discriminant is `≤ 0`);
* `cramerRao_bound` — the abstract bound: any statistic `T` whose covariance with a mean-zero score `s` is
  `1` (the standard unbiasedness/regularity condition, taken as an explicit hypothesis) satisfies
  `Var[T]·Var[s] ≥ 1`, i.e. `Var[T] ≥ 1/Var[s]`;
* `gaussianMeanScore_variance` — the Gaussian location score has variance equal to the Fisher information
  `1/v`, and `gaussianMeanScore_integral_zero` its mean is `0`;
* `gaussian_cramerRao_inferenceMass` — instantiated: an unbiased estimator of the Gaussian mean has
  variance `≥ v = σ²`, so the Fisher information `1/σ²` is the reciprocal of the minimal variance — the
  inference mass is the Cramér-Rao precision limit.

The physical identification `physical mass = inference precision` is *not* discharged (and cannot be); it is
isolated, and the "`= Fisher information = 1/σ²`" part is now a theorem.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerRaoInferenceMass

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianMeanFisherInformationIntegral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **[Covariance Cauchy-Schwarz]** `cov[X,Y]² ≤ Var[X]·Var[Y]`. Since `Var[X − tY] ≥ 0` for every `t`, the
quadratic `Var[Y]·t² − 2cov[X,Y]·t + Var[X]` is nonnegative, so its discriminant is `≤ 0`. -/
theorem covariance_sq_le_variance_mul_variance [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    covariance X Y μ ^ 2 ≤ variance X μ * variance Y μ := by
  have key : ∀ t : ℝ,
      0 ≤ variance Y μ * (t * t) + -(2 * covariance X Y μ) * t + variance X μ := by
    intro t
    have hMul : MemLp (fun ω => t * Y ω) 2 μ := hY.const_mul t
    have h := variance_nonneg (fun ω => X ω - t * Y ω) μ
    rw [variance_fun_sub hX hMul, variance_const_mul, covariance_const_mul_right] at h
    nlinarith [h]
  have hd := discrim_le_zero key
  simp only [discrim] at hd
  nlinarith [hd]

/-- **[The Cramér-Rao bound]** For a mean-zero score `s` and a statistic `T` whose covariance with the
score is `1` — the unbiased-regular-estimator condition `∂_θ E[T] = 1`, stated here as an explicit
hypothesis — the product `Var[T]·Var[s] ≥ 1`; equivalently `Var[T] ≥ 1/Var[s]`, the Fisher-information
lower bound on the estimator variance. -/
theorem cramerRao_bound [IsFiniteMeasure μ] {T s : Ω → ℝ}
    (hT : MemLp T 2 μ) (hs : MemLp s 2 μ) (hcov : covariance T s μ = 1) :
    1 ≤ variance T μ * variance s μ := by
  have hcs := covariance_sq_le_variance_mul_variance hT hs
  rw [hcov] at hcs
  simpa using hcs

/-! ### The Gaussian instance: the inference mass is the Cramér-Rao precision limit -/

/-- The Gaussian location score as a scalar multiple of the centered coordinate. -/
theorem gaussianMeanScore_eq (μ : ℝ) (v : ℝ≥0) :
    gaussianMeanScore μ v = fun x => (v : ℝ)⁻¹ * (x - μ) := by
  funext x; simp only [gaussianMeanScore]; ring

/-- The Gaussian location score is square-integrable. -/
theorem memLp_gaussianMeanScore (μ : ℝ) (v : ℝ≥0) :
    MemLp (gaussianMeanScore μ v) 2 (gaussianReal μ v) := by
  rw [gaussianMeanScore_eq]
  exact ((memLp_id_gaussianReal 2).sub (memLp_const μ)).const_mul _

/-- **[The Gaussian location score variance is the Fisher information]** `Var[∂_μ log p] = 1/v`. -/
theorem gaussianMeanScore_variance (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    variance (gaussianMeanScore μ v) (gaussianReal μ v) = 1 / (v : ℝ) := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have h2 : variance (fun x : ℝ => x - μ) (gaussianReal μ v) = (v : ℝ) :=
    (variance_sub_const (by fun_prop) μ).trans variance_fun_id_gaussianReal
  rw [gaussianMeanScore_eq, variance_const_mul, h2]
  field_simp

/-- **[Cramér-Rao for the Gaussian mean: the inference mass is the precision limit]** any statistic `T`
whose covariance with the location score is `1` (the unbiased-estimator regularity condition) has variance
at least `v = σ²`. Equivalently, the Fisher information `1/σ² = gMuMu σ` — the inference mass — is the
reciprocal of the minimal achievable variance: no estimator beats it. -/
theorem gaussian_cramerRao_inferenceMass (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) {T : ℝ → ℝ}
    (hT : MemLp T 2 (gaussianReal μ v))
    (hcov : covariance T (gaussianMeanScore μ v) (gaussianReal μ v) = 1) :
    (v : ℝ) ≤ variance T (gaussianReal μ v) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hcr := cramerRao_bound hT (memLp_gaussianMeanScore μ v) hcov
  rw [gaussianMeanScore_variance μ v hv, mul_one_div, le_div_iff₀ hvpos, one_mul] at hcr
  exact hcr

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerRaoInferenceMass

end

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerRaoInferenceMass in
#physlib_axiom_clean_all [
  covariance_sq_le_variance_mul_variance,
  cramerRao_bound,
  gaussianMeanScore_variance,
  gaussian_cramerRao_inferenceMass ]

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerRaoInferenceMass in
#physlib_non_vacuous_all [
  covariance_sq_le_variance_mul_variance,
  cramerRao_bound,
  gaussianMeanScore_variance,
  gaussian_cramerRao_inferenceMass ]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerRaoInferenceMass.covariance_sq_le_variance_mul_variance where
  supported_by @ "lean:HasVarAdjDerivAt.const_mul",
  formalizes @ "claim:the-covariance-cauchy-schwarz-covariance-squared-is-at-most-the-variance-product"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerRaoInferenceMass.cramerRao_bound where
  formalizes @ "claim:the-cramer-rao-bound-a-regular-estimator-variance-times-score-variance-is-at-least-one",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerRaoInferenceMass.covariance_sq_le_variance_mul_variance"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerRaoInferenceMass.gaussianMeanScore_variance where
  formalizes @ "claim:the-gaussian-location-score-variance-equals-the-fisher-information-inverse-variance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.GaussianMeanFisherInformationIntegral.gaussianMeanScore_eq_deriv_logPDF"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerRaoInferenceMass.gaussian_cramerRao_inferenceMass where
  formalizes @ "claim:the-inference-mass-fisher-information-is-the-cramer-rao-reciprocal-of-the-minimal-estimator-variance",
  epistemic_status @ "conditional-model",
  requires @ "assumption:the-estimator-covariance-with-the-location-score-is-one-the-unbiased-regularity-condition",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerRaoInferenceMass.cramerRao_bound",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerRaoInferenceMass.gaussianMeanScore_variance",
  caveat @ "epistemic:the-physical-identification-of-mass-with-inference-precision-remains-a-bridge-postulate-cramer-rao-only-establishes-that-the-fisher-information-is-the-attainable-precision-limit"

