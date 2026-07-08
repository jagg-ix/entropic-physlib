/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.PathIntegral.MeasureModel
public import Physlib.QuantumMechanics.Schrodinger.SpectralDynamics
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Measure-theoretic complex path-integral expectations

This file extends `Physlib.QFT.PathIntegral.MeasureModel` with the
standard expectation-level operations for an entropically damped complex
path-integral model:

* the complex partition functional `Z = ∫ weight dμ`;
* unnormalised and normalised observable expectations;
* source-coupled partitions and connected generating functionals;
* finite-dimensional approximation by dominated convergence.

The construction is deliberately placed in the shared QFT path-integral
layer so QED, Chern-Simons/Wilson-loop, ABJM/Fermi-gas, matrix-model,
and curved-background files can use the same canonical model.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Complex Filter
open scoped Topology

namespace Physlib.QFT.PathIntegral

open Physlib.QuantumMechanics.Schrodinger.SpectralDynamics

namespace MeasurePathIntegralModel

variable {α : Type*} [MeasurableSpace α] (m : MeasurePathIntegralModel α)

/-! ## Basic measurable factors and finite-measure bounds -/

/-- The oscillatory phase is measurable. -/
theorem measurable_phase : Measurable m.phase := by
  unfold phase actionReScaled
  exact Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp (m.measurable_actionRe.div_const m.hbar)).mul_const Complex.I)

/-- Alias for the damping identity in `MeasureModel`, expressed using `m.damping`. -/
theorem norm_weight_eq_damping (x : α) :
    ‖m.weight x‖ = m.damping x := by
  rw [m.weight_norm_is_damping]
  rfl

/-- The path weight is uniformly bounded by one. -/
theorem norm_weight_le_one (x : α) : ‖m.weight x‖ ≤ 1 :=
  m.weight_bochner_bounded x

/-- Under a finite reference measure, the complex path weight is integrable. -/
theorem integrable_weight_of_isFiniteMeasure [IsFiniteMeasure m.μ] :
    Integrable m.weight m.μ := by
  refine Integrable.mono' (integrable_const (μ := m.μ) (1 : ℝ))
    m.measurable_weight.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall m.norm_weight_le_one

/-- Under a finite reference measure, the real damping profile is integrable. -/
theorem integrable_damping_of_isFiniteMeasure [IsFiniteMeasure m.μ] :
    Integrable m.damping m.μ := by
  refine Integrable.mono' (integrable_const (μ := m.μ) (1 : ℝ))
    m.measurable_damping.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  have hnonneg : 0 ≤ m.damping x := (m.damping_pos x).le
  calc
    ‖m.damping x‖ = m.damping x := by rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ ≤ 1 := by simpa [m.norm_weight_eq_damping x] using m.norm_weight_le_one x

/-! ## Partition functions and observable expectations -/

/-- Complex partition functional `Z = ∫ weight dμ`. -/
def partition : ℂ :=
  ∫ x, m.weight x ∂m.μ

/-- Unnormalised observable expectation `⟪O⟫ = ∫ weight * O dμ`. -/
def unnormalizedExpectation (O : α → ℂ) : ℂ :=
  ∫ x, m.weight x * O x ∂m.μ

/-- Normalised expectation `E[O] = ⟪O⟫ / Z`. -/
def normalizedExpectation (O : α → ℂ) : ℂ :=
  m.unnormalizedExpectation O / m.partition

/-- Finite-measure a priori bound on the complex partition functional. -/
theorem norm_partition_le_measure_univ_toReal [IsFiniteMeasure m.μ] :
    ‖m.partition‖ ≤ (m.μ Set.univ).toReal := by
  unfold partition
  have hnorm_int : Integrable (fun x => ‖m.weight x‖) m.μ :=
    m.integrable_weight_of_isFiniteMeasure.norm
  have hconst_int : Integrable (fun _x : α => (1 : ℝ)) m.μ :=
    integrable_const 1
  calc
    ‖∫ x, m.weight x ∂m.μ‖ ≤ ∫ x, ‖m.weight x‖ ∂m.μ := by
      exact norm_integral_le_integral_norm (f := fun x => m.weight x)
    _ ≤ ∫ _x, (1 : ℝ) ∂m.μ := by
      refine integral_mono_ae hnorm_int hconst_int ?_
      exact Filter.Eventually.of_forall m.norm_weight_le_one
    _ = (m.μ Set.univ).toReal := by
      simp [Measure.real_def]

/-- Bounded observables are integrable against the complex path weight on finite measure spaces. -/
theorem integrable_weight_mul_of_bound [IsFiniteMeasure m.μ] (O : α → ℂ)
    (hO_meas : AEStronglyMeasurable O m.μ)
    {C : ℝ} (hO_bound : ∀ᵐ x ∂m.μ, ‖O x‖ ≤ C) :
    Integrable (fun x => m.weight x * O x) m.μ := by
  refine Integrable.mono' (integrable_const (μ := m.μ) C)
    (m.measurable_weight.aestronglyMeasurable.mul hO_meas) ?_
  filter_upwards [Filter.Eventually.of_forall m.norm_weight_le_one, hO_bound] with x hxW hxO
  have hmul :
      ‖m.weight x‖ * ‖O x‖ ≤ ‖O x‖ := by
    calc
      ‖m.weight x‖ * ‖O x‖ ≤ 1 * ‖O x‖ :=
        mul_le_mul_of_nonneg_right hxW (norm_nonneg (O x))
      _ = ‖O x‖ := by simp
  calc
    ‖m.weight x * O x‖ = ‖m.weight x‖ * ‖O x‖ := by simp
    _ ≤ ‖O x‖ := hmul
    _ ≤ C := hxO

/-- A named wrapper for bounded-observable integrability. -/
theorem unnormalizedExpectation_integrable_of_bound [IsFiniteMeasure m.μ] (O : α → ℂ)
    (hO_meas : AEStronglyMeasurable O m.μ)
    {C : ℝ} (hO_bound : ∀ᵐ x ∂m.μ, ‖O x‖ ≤ C) :
    Integrable (fun x => m.weight x * O x) m.μ :=
  m.integrable_weight_mul_of_bound O hO_meas hO_bound

/-- Algebraic normalisation identity when `Z ≠ 0`. -/
theorem normalizedExpectation_mul_partition (O : α → ℂ) (hZ : m.partition ≠ 0) :
    m.normalizedExpectation O * m.partition = m.unnormalizedExpectation O := by
  unfold normalizedExpectation
  field_simp [hZ]

/-- Additivity of unnormalised expectations for integrable observables. -/
theorem unnormalizedExpectation_add (O1 O2 : α → ℂ)
    (h1 : Integrable (fun x => m.weight x * O1 x) m.μ)
    (h2 : Integrable (fun x => m.weight x * O2 x) m.μ) :
    m.unnormalizedExpectation (fun x => O1 x + O2 x) =
      m.unnormalizedExpectation O1 + m.unnormalizedExpectation O2 := by
  unfold unnormalizedExpectation
  calc
    ∫ x, m.weight x * (O1 x + O2 x) ∂m.μ
      = ∫ x, (m.weight x * O1 x) + (m.weight x * O2 x) ∂m.μ := by
          congr with x
          simp [mul_add]
    _ = (∫ x, m.weight x * O1 x ∂m.μ) + (∫ x, m.weight x * O2 x ∂m.μ) :=
          integral_add h1 h2

/-- Scalar multiplication pulls out of an unnormalised expectation. -/
theorem unnormalizedExpectation_const_mul (c : ℂ) (O : α → ℂ) :
    m.unnormalizedExpectation (fun x => c * O x) =
      c * m.unnormalizedExpectation O := by
  unfold unnormalizedExpectation
  calc
    ∫ x, m.weight x * (c * O x) ∂m.μ
      = ∫ x, c * (m.weight x * O x) ∂m.μ := by
          congr with x
          simp [mul_assoc, mul_comm]
    _ = c * ∫ x, m.weight x * O x ∂m.μ := by
          simpa using integral_const_mul c (fun x => m.weight x * O x)

/-! ## Sources, connected functionals, and correlations -/

/-- Source-coupled weight `weight * exp(J)`. -/
def sourceCoupledWeight (J : α → ℂ) (x : α) : ℂ :=
  m.weight x * Complex.exp (J x)

/-- Source-coupled partition functional `Z[J]`. -/
def sourceCoupledPartition (J : α → ℂ) : ℂ :=
  ∫ x, m.sourceCoupledWeight J x ∂m.μ

/-- Source-coupled unnormalised expectation `⟪O⟫_J`. -/
def sourceCoupledUnnormalizedExpectation (J O : α → ℂ) : ℂ :=
  ∫ x, m.sourceCoupledWeight J x * O x ∂m.μ

/-- Source-coupled normalised expectation `E_J[O]`. -/
def sourceCoupledExpectation (J O : α → ℂ) : ℂ :=
  m.sourceCoupledUnnormalizedExpectation J O / m.sourceCoupledPartition J

/-- Connected generating functional `W[J] = log Z[J]`. -/
def connectedGeneratingFunctional (J : α → ℂ) : ℂ :=
  Complex.log (m.sourceCoupledPartition J)

/-- Compatibility at zero source: `Z[0] = Z`. -/
theorem sourceCoupledPartition_zero :
    m.sourceCoupledPartition (fun _ => (0 : ℂ)) = m.partition := by
  unfold sourceCoupledPartition sourceCoupledWeight partition
  congr with x
  simp

/-- Compatibility at zero source: source-coupled expectation reduces to base expectation. -/
theorem sourceCoupledExpectation_zero (O : α → ℂ) :
    m.sourceCoupledExpectation (fun _ => (0 : ℂ)) O = m.normalizedExpectation O := by
  unfold sourceCoupledExpectation normalizedExpectation
  rw [m.sourceCoupledPartition_zero]
  unfold sourceCoupledUnnormalizedExpectation unnormalizedExpectation sourceCoupledWeight
  simp

/-- Source-coupled partition is an unnormalised expectation of `exp(J)`. -/
theorem sourceCoupledPartition_eq_unnormalizedExpectation_exp (J : α → ℂ) :
    m.sourceCoupledPartition J =
      m.unnormalizedExpectation (fun x => Complex.exp (J x)) := by
  rfl

/-- Product observable for an `n`-point function. -/
def nPointObservable (n : ℕ) (obs : Fin n → α → ℂ) : α → ℂ :=
  fun x => ∏ i : Fin n, obs i x

/-- `n`-point correlation as the normalised expectation of a product observable. -/
def nPointCorrelation (n : ℕ) (obs : Fin n → α → ℂ) : ℂ :=
  m.normalizedExpectation (nPointObservable n obs)

/-- One-point function. -/
def onePointCorrelation (O : α → ℂ) : ℂ :=
  m.nPointCorrelation 1 (fun _ => O)

/-- Two-point function. -/
def twoPointCorrelation (O1 O2 : α → ℂ) : ℂ :=
  m.nPointCorrelation 2 (fun i => if (i : ℕ) = 0 then O1 else O2)

/-- At zero source, the connected generating functional is `log Z`. -/
theorem connectedGeneratingFunctional_zero :
    m.connectedGeneratingFunctional (fun _ => (0 : ℂ)) = Complex.log m.partition := by
  unfold connectedGeneratingFunctional
  rw [m.sourceCoupledPartition_zero]

/-! ## Finite-dimensional approximation -/

/-- Finite-dimensional approximation data for a dominated-convergence passage. -/
structure FiniteDimApproximation where
  approx : ℕ → α → ℂ
  limit : α → ℂ
  bound : α → ℝ
  approx_aestronglyMeasurable : ∀ n, AEStronglyMeasurable (approx n) m.μ
  bound_integrable : Integrable bound m.μ
  dominated : ∀ n, ∀ᵐ x ∂m.μ, ‖m.weight x * approx n x‖ ≤ bound x
  pointwise_tendsto :
    ∀ᵐ x ∂m.μ, Tendsto (fun n => m.weight x * approx n x) atTop
      (𝓝 (m.weight x * limit x))

/-- Dominated-convergence transfer for finite-dimensional approximants. -/
theorem finiteDimApproximation_tendsto (A : m.FiniteDimApproximation) :
    Tendsto (fun n => m.unnormalizedExpectation (A.approx n)) atTop
      (𝓝 (m.unnormalizedExpectation A.limit)) := by
  unfold unnormalizedExpectation
  exact MeasureTheory.tendsto_integral_of_dominated_convergence A.bound
    (fun n => m.measurable_weight.aestronglyMeasurable.mul (A.approx_aestronglyMeasurable n))
    A.bound_integrable A.dominated A.pointwise_tendsto

end MeasurePathIntegralModel

/-! ## Small canonical anchors -/

/-- The zero-action one-point model, a finite vacuum-sector path integral. -/
def gaussian0DModel (hbar : ℝ) (hbar_pos : 0 < hbar) :
    MeasurePathIntegralModel Unit where
  μ := Measure.count
  hbar := hbar
  hbar_pos := hbar_pos
  actionRe := fun _ => 0
  actionIm := fun _ => 0
  measurable_actionRe := measurable_const
  measurable_actionIm := measurable_const
  actionIm_nonneg := fun _ => le_refl 0

/-- The zero-action one-point model has unit path weight. -/
theorem gaussian0DModel_weight_eq_one (hbar : ℝ) (hbar_pos : 0 < hbar) (x : Unit) :
    (gaussian0DModel hbar hbar_pos).weight x = 1 := by
  simp [gaussian0DModel, MeasurePathIntegralModel.weight,
    MeasurePathIntegralModel.actionReScaled, MeasurePathIntegralModel.actionImScaled, zero_div]

/-- A finite heat-kernel model with Euclidean action `S_I(k) = λ(k) * t`. -/
def heatKernelModel (n : ℕ) (eigenvalue : Fin n → ℝ)
    (eigenvalue_nonneg : ∀ k, 0 ≤ eigenvalue k)
    (t : ℝ) (ht : 0 < t)
    (hbar : ℝ) (hbar_pos : 0 < hbar) :
    MeasurePathIntegralModel (Fin n) where
  μ := Measure.count
  hbar := hbar
  hbar_pos := hbar_pos
  actionRe := fun _ => 0
  actionIm := fun k => eigenvalue k * t
  measurable_actionRe := measurable_const
  measurable_actionIm := (measurable_of_finite eigenvalue).mul_const t
  actionIm_nonneg := fun k => mul_nonneg (eigenvalue_nonneg k) (le_of_lt ht)

/-- Heat-kernel weights satisfy the damping bound modewise. -/
theorem heatKernelModel_weight_le_one (n : ℕ) (eigenvalue : Fin n → ℝ)
    (eigenvalue_nonneg : ∀ k, 0 ≤ eigenvalue k)
    (t : ℝ) (ht : 0 < t) (hbar : ℝ) (hbar_pos : 0 < hbar) (k : Fin n) :
    ‖(heatKernelModel n eigenvalue eigenvalue_nonneg t ht hbar hbar_pos).weight k‖ ≤ 1 :=
  (heatKernelModel n eigenvalue eigenvalue_nonneg t ht hbar hbar_pos).norm_weight_le_one k

/-- The finite heat-kernel damping of a mode is the Wick-rotated spectral phase
with potential `λ/ℏ`. -/
theorem heatKernelModel_weight_eq_wickRotatedSpectralPhase
    (n : ℕ) (eigenvalue : Fin n → ℝ)
    (eigenvalue_nonneg : ∀ k, 0 ≤ eigenvalue k)
    (t : ℝ) (ht : 0 < t) (hbar : ℝ) (hbar_pos : 0 < hbar) (k : Fin n) :
    (heatKernelModel n eigenvalue eigenvalue_nonneg t ht hbar hbar_pos).weight k =
      Physlib.QuantumMechanics.NonHermitian.WickRotation.reversiblePhaseC
        (eigenvalue k) hbar (-Complex.I * (t : ℂ)) := by
  rw [wickRotatedSpectralPhase_eq_feynmanKacWeight]
  have hRe :
      ∀ x : Fin n, (heatKernelModel n eigenvalue eigenvalue_nonneg t ht hbar hbar_pos).actionRe x = 0 :=
    fun _ => rfl
  rw [(heatKernelModel n eigenvalue eigenvalue_nonneg t ht hbar hbar_pos).weight_eq_damping_of_actionRe_zero
    hRe k]
  unfold heatKernelModel MeasurePathIntegralModel.damping MeasurePathIntegralModel.actionImScaled
    feynman_kac_weight
  simp
  congr 1
  ring_nf

/-- Finite heat-kernel spectral coefficients preserve total Born weight in the
Lorentzian spectral-dynamics phase evolution. -/
theorem heatKernelModel_lorentzianSpectralEvolution_total_probability
    (n : ℕ) (eigenvalue : Fin n → ℝ) (hbar t : ℝ) (c : Fin n → ℂ) :
    (∑ k, ‖finiteSpectralEvolution eigenvalue hbar t c k‖ ^ 2) =
      ∑ k, ‖c k‖ ^ 2 := by
  simpa using finiteSpectralEvolution_total_probability eigenvalue hbar t c

end Physlib.QFT.PathIntegral

end
