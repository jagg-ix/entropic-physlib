/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.MeasureTheory.Integral.PeakFunction
meta import Zil

/-!
# Distributional Calderon identity for dyadic Schwartz kernels

The finite telescoping identity from `MultiNormSchwartzKernel` is embedded in
the native space of tempered distributions.  The normalized dyadic kernels
converge pointwise on Schwartz test functions to the Dirac delta, so their
detail partial sums give an actual distributional Calderon formula.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ContDiff SchwartzMap Topology

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormTemperedCalderon

open MultiNormSchwartzKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## A. Complex kernels and their tempered distributions -/

/-- Complexification of a real dyadic approximate-identity kernel. -/
def complexDyadicApproximationKernel
    (φ : ContDiffBump (0 : E)) (n : ℕ) : 𝓢(E, ℂ) :=
  (dyadicApproximationKernel φ n).postcompCLM Complex.ofRealCLM

@[simp]
lemma complexDyadicApproximationKernel_apply
    (φ : ContDiffBump (0 : E)) (n : ℕ) (x : E) :
    complexDyadicApproximationKernel φ n x =
      dyadicExpansion n ^ Module.finrank ℝ E *
        φ.normed volume (dyadicExpansion n • x) := by
  simp [complexDyadicApproximationKernel,
    dyadicApproximationKernel_apply, SchwartzMap.postcompCLM_apply]

/-- Complexification of one cancelling detail kernel. -/
def complexDyadicDetailKernel
    (φ : ContDiffBump (0 : E)) (n : ℕ) : 𝓢(E, ℂ) :=
  (dyadicDetailKernel φ n).postcompCLM Complex.ofRealCLM

/-- The approximate-identity kernel embedded in tempered distributions. -/
def dyadicApproximationDistribution
    (φ : ContDiffBump (0 : E)) (n : ℕ) : 𝓢'(E, ℂ) :=
  SchwartzMap.toTemperedDistributionCLM E ℂ volume
    (complexDyadicApproximationKernel φ n)

/-- One cancelling detail kernel embedded in tempered distributions. -/
def dyadicDetailDistribution
    (φ : ContDiffBump (0 : E)) (n : ℕ) : 𝓢'(E, ℂ) :=
  SchwartzMap.toTemperedDistributionCLM E ℂ volume
    (complexDyadicDetailKernel φ n)

/-! ## B. Finite distributional partial sums -/

lemma sum_range_complexDyadicDetailKernel
    (φ : ContDiffBump (0 : E)) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), complexDyadicDetailKernel φ n) =
      complexDyadicApproximationKernel φ N := by
  simpa [complexDyadicDetailKernel, complexDyadicApproximationKernel,
    map_sum] using congrArg
    (fun f : 𝓢(E, ℝ) => f.postcompCLM Complex.ofRealCLM)
    (sum_range_dyadicDetailKernel φ N)

/-- Every finite sum of embedded detail kernels is exactly the final embedded
approximate identity, before taking a distributional limit. -/
lemma sum_range_dyadicDetailDistribution
    (φ : ContDiffBump (0 : E)) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), dyadicDetailDistribution φ n) =
      dyadicApproximationDistribution φ N := by
  simpa [dyadicDetailDistribution, dyadicApproximationDistribution,
    map_sum] using congrArg
      (SchwartzMap.toTemperedDistributionCLM E ℂ volume)
      (sum_range_complexDyadicDetailKernel φ N)

/-! ## C. Convergence to the Dirac distribution -/

lemma normalizedBump_peak_decay (φ : ContDiffBump (0 : E)) :
    Tendsto
      (fun x : E => ‖x‖ ^ Module.finrank ℝ E * φ.normed volume x)
      (Bornology.cobounded E) (𝓝 0) := by
  rw [Metric.cobounded_eq_cocompact]
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [
    (φ.hasCompactSupport_normed (μ := volume)).compl_mem_cocompact
  ] with x hx
  have hxSupport : x ∉ Function.support (φ.normed volume) := by
    intro hx'
    exact hx (subset_closure hx')
  have hzero : φ.normed volume x = 0 := by
    simpa [Function.mem_support] using hxSupport
  simp [hzero]

/-- The normalized dyadic Schwartz kernels converge to `δ₀` in Mathlib's
pointwise topology on tempered distributions. -/
lemma tendsto_dyadicApproximationDistribution_delta
    (φ : ContDiffBump (0 : E)) :
    Tendsto (dyadicApproximationDistribution φ) atTop
      (𝓝 (TemperedDistribution.delta (0 : E))) := by
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.2
  intro g
  have hpeak := tendsto_integral_comp_smul_smul_of_integrable
    (μ := volume) (φ := φ.normed volume)
    φ.nonneg_normed φ.integral_normed
    (normalizedBump_peak_decay φ) g.integrable g.continuous.continuousAt
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hdyadic := hpeak.comp hpow
  change Tendsto
    (fun n => ∫ x, g x *
      (complexDyadicApproximationKernel φ n x)) atTop (𝓝 (g 0))
  simp_rw [complexDyadicApproximationKernel_apply]
  convert hdyadic using 1
  funext n
  apply integral_congr_ae
  filter_upwards with x
  simp [dyadicExpansion, mul_comm]

/-- Second Section 4 capstone: the exact finite detail sums converge to the
Dirac tempered distribution, which is the distributional Calderon identity
`δ₀ = Σ ψ_n`. -/
lemma dyadicDetailDistribution_tendsto_delta
    (φ : ContDiffBump (0 : E)) :
    Tendsto
      (fun N => ∑ n ∈ Finset.range (N + 1), dyadicDetailDistribution φ n)
      atTop (𝓝 (TemperedDistribution.delta (0 : E))) := by
  exact (tendsto_dyadicApproximationDistribution_delta φ).congr'
    (Filter.Eventually.of_forall fun N =>
      (sum_range_dyadicDetailDistribution φ N).symm)

end MultiNormTemperedCalderon

end Physlib.Mathematics.HarmonicAnalysis

/- ZIL-BEGIN -/

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.dyadicDetailDistribution_tendsto_delta where
  formalizes @ "claim:the-distributional-calderon-resolution-the-dyadic-detail-partial-sums-converge-to-the-dirac-distribution",
  requires @ "claim:the-normalized-dyadic-approximate-identities-converge-to-the-dirac-distribution-in-the-tempered-topology",
  supported_by @ "paper:calderon-reproducing-formula-tempered-distributions"

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.tendsto_dyadicApproximationDistribution_delta where
  supported_by @ "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.normalizedBump_peak_decay",
  formalizes @ "claim:the-normalized-dyadic-approximate-identities-converge-to-the-dirac-distribution-in-the-tempered-topology"

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.sum_range_dyadicDetailDistribution where
  formalizes @ "claim:the-finite-dyadic-detail-partial-sum-telescopes-exactly-to-the-approximation-distribution-at-each-cutoff"

zil attach Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.normalizedBump_peak_decay where
  supported_by @ "lean:ProbDistribution.normalized",
  formalizes @ "claim:the-normalized-bump-peak-decays-along-the-cobounded-filter-the-decay-estimate-driving-peak-to-delta-convergence"

zil_file_contract physlib.multiNormTemperedCalderon where
  promises "The tempered-distribution Calderon resolution of the identity: the complexified dyadic approximation and detail kernels embed into tempered distributions, the finite detail partial sums telescope exactly to the approximation distribution at each cutoff, the normalized approximate identities converge to the Dirac distribution (via the peak-function estimate), and hence the distributional Calderon identity delta_0 = sum of detail pieces holds in the pointwise topology on S'. This is the base carrier of the multi-norm Calderon dyadic-ladder arc."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.complexDyadicApproximationKernel",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.complexDyadicDetailKernel",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.dyadicDetailDistribution"]
  forbids_substitutes ["any Lp operator-norm convergence, the resolution here is in the pointwise tempered-distribution topology only"]
  witnessed_by [Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.dyadicDetailDistribution_tendsto_delta,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.tendsto_dyadicApproximationDistribution_delta,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.sum_range_dyadicDetailDistribution,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.normalizedBump_peak_decay]

/- ZIL-END -/
