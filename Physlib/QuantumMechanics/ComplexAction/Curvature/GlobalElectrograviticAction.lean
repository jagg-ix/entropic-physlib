/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalEinsteinHilbertAction
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow
public import Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics
public import Physlib.Thermodynamics.ModularErasureCost
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Operator.NormedSpace
meta import Zil

/-!
# Global electrogravitic action

This file has two deliberately separated layers.

The legacy adapter `CanonicalIntegratedElectrograviticActionData` accepts a
certified density and identifies its integrated derivative with the existing
coupled variation. It remains useful for arbitrary continuum models, but it
is not a microscopic construction.

The constructed layer does not use that adapter. It defines the nonlinear
microscopic density
`(Psi + (q - S1 - S2)^2 / 2) rho + beta^-1 rho log rho`, integrates it, and
derives both probability and BCJ-energy variations from the formula. For a
normalized probability, energy-coordinate stationarity is equivalent to the
BCJ split; the constructed Gibbs density is stationary under mass-preserving
variations. An explicit metric-built Einstein--Maxwell potential supplies
`Psi` from `R[g]` and `F_ab F^ab`, and is gauge invariant.

All differentiation-under-the-integral hypotheses remain explicit. The new
construction proves the probability and BCJ-coordinate variations; it does
not identify those two results with a full Fréchet variation in the metric
and gauge-field carriers.

The Maxwell completion below keeps four analytic layers explicit. It
constructs the atlas-independent manifold action from the canonical
Lorentzian measure, differentiates the nonlinear coordinate density under a
locally Lipschitz dominated integral to obtain the integrated stress-energy
pairing, derives the canonical action as a summable gluing of chart actions,
and removes the explicit gauge boundary current by the genuine box divergence
theorem. Chartwise differentiability under a summable derivative bound now
lifts to a directional derivative of the actual canonical manifold action.
No statement calls this one-parameter result a full field-space Fréchet
derivative.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Bundle Module MeasureTheory Set Filter
open scoped Manifold Topology

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations

universe u v

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.PTTensorDynamics
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein
open Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics
open Physlib.Thermodynamics.ModularErasureCost
open Physlib.Mathematics.LovelockRund
open Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalEinsteinHilbertAction
open PseudoRiemannianMetric

/-- A continuum action density with a uniformly dominated Fréchet derivative
may be differentiated under the integral sign. -/
@[zil_level bridge_theorem]
theorem globalAction_hasFDerivAt_of_dominated
    {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MeasurableSpace X]
    (μ : Measure X) (F : P → X → ℝ)
    (F' : P → X → P →L[ℝ] ℝ) (bound : X → ℝ)
    (s : Set P) (p₀ : P)
    (hs : s ∈ 𝓝 p₀)
    (hFmeas : ∀ᶠ p in 𝓝 p₀, AEStronglyMeasurable (F p) μ)
    (hFint : Integrable (F p₀) μ)
    (hF'meas : AEStronglyMeasurable (F' p₀) μ)
    (hbound : ∀ᵐ x ∂μ, ∀ p ∈ s, ‖F' p x‖ ≤ bound x)
    (hboundInt : Integrable bound μ)
    (hpointwise : ∀ᵐ x ∂μ, ∀ p ∈ s,
      HasFDerivAt (fun q => F q x) (F' p x) p) :
    HasFDerivAt (fun p => ∫ x, F p x ∂μ)
      (∫ x, F' p₀ x ∂μ) p₀ :=
  hasFDerivAt_integral_of_dominated_of_fderiv_le
    hs hFmeas hFint hF'meas hbound hboundInt hpointwise

variable {n : WithTop ℕ∞}
variable {E M : Type v} {P : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [TopologicalSpace M] [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M]
variable [IsManifold 𝓘(ℝ, E) (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x)]
variable [T2Space M] [SigmaCompactSpace M]
variable [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Analytic data for one nonlinear continuum electrogravitic action,
integrated against the measure constructed from the pseudo-Riemannian metric.
The load-bearing final field identifies the integrated density derivative
with the repo's coupled Einstein--Maxwell--entropic first variation after a
surjective realization of continuum variations. -/
structure CanonicalIntegratedElectrograviticActionData
    (P : Type u) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (metric : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ mI c S1 S2 : ℝ) (k A : Fin 4 → ℝ) where
  density : P → M → ℝ
  densityDerivative : P → M → P →L[ℝ] ℝ
  bound : M → ℝ
  neighborhood : Set P
  background : P
  neighborhood_mem : neighborhood ∈ 𝓝 background
  density_measurable : ∀ᶠ p in 𝓝 background,
    AEStronglyMeasurable (density p)
      (PseudoRiemannianMetric.lorentzianVolumeMeasure metric)
  density_integrable : Integrable (density background)
    (PseudoRiemannianMetric.lorentzianVolumeMeasure metric)
  derivative_measurable : AEStronglyMeasurable
    (densityDerivative background)
      (PseudoRiemannianMetric.lorentzianVolumeMeasure metric)
  derivative_bound :
    ∀ᵐ x ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure metric),
      ∀ p ∈ neighborhood, ‖densityDerivative p x‖ ≤ bound x
  bound_integrable : Integrable bound
    (PseudoRiemannianMetric.lorentzianVolumeMeasure metric)
  pointwise_hasFDerivAt :
    ∀ᵐ x ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure metric),
      ∀ p ∈ neighborhood,
        HasFDerivAt (fun q => density q x) (densityDerivative p x) p
  realizeVariation : P →ₗ[ℝ] CoupledElectrograviticVariationSpace
  realizeVariation_surjective : Function.Surjective realizeVariation
  integratedDerivative_apply : ∀ p,
    (∫ x, densityDerivative background x
      ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure metric)) p =
      coupledElectrograviticFirstVariation
        Ric scalarR g gInv Λ S κ mI c S1 S2 k A
        (coupledVariationOfSpace (realizeVariation p))

namespace CanonicalIntegratedElectrograviticActionData

variable
    {metric : PseudoRiemannianMetric E E M n 𝓘(ℝ, E)}
    {Ric : FourTensor} {scalarR : ℝ} {g gInv Λ S : FourTensor}
    {κ mI c S1 S2 : ℝ} {k A : Fin 4 → ℝ}

/-- The actual nonlinear continuum action represented by the certified local
density and the canonical metric measure. -/
def action
    (D : CanonicalIntegratedElectrograviticActionData
      P metric Ric scalarR g gInv Λ S κ mI c S1 S2 k A) : P → ℝ :=
  fun p => ∫ x, D.density p x
    ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure metric)

/-- The certified continuum action has the integral of its pointwise
derivative as a genuine Fréchet derivative. -/
@[zil_level physical_theorem]
theorem hasFDerivAt
    (D : CanonicalIntegratedElectrograviticActionData
      P metric Ric scalarR g gInv Λ S κ mI c S1 S2 k A) :
    HasFDerivAt D.action
      (∫ x, D.densityDerivative D.background x
        ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure metric))
      D.background := by
  exact globalAction_hasFDerivAt_of_dominated
    (PseudoRiemannianMetric.lorentzianVolumeMeasure metric)
    D.density D.densityDerivative D.bound D.neighborhood D.background
    D.neighborhood_mem D.density_measurable D.density_integrable
    D.derivative_measurable D.derivative_bound D.bound_integrable
    D.pointwise_hasFDerivAt

/-- Stationarity of the actual integrated action at its background. -/
def IsStationary
    (D : CanonicalIntegratedElectrograviticActionData
      P metric Ric scalarR g gInv Λ S κ mI c S1 S2 k A) : Prop :=
  fderiv ℝ D.action D.background = 0

/-- Stationarity of the canonical-measure continuum action forces all
metric, gauge, and entropic first variations to vanish. -/
@[zil_level physical_theorem]
theorem stationary_implies_coupled
    (D : CanonicalIntegratedElectrograviticActionData
      P metric Ric scalarR g gInv Λ S κ mI c S1 S2 k A)
    (hstationary : D.IsStationary) :
    IsCoupledElectrograviticStationary
      Ric scalarR g gInv Λ S κ mI c S1 S2 k A := by
  have hzero :
      (∫ x, D.densityDerivative D.background x
        ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure metric)) = 0 := by
    rw [← D.hasFDerivAt.fderiv]
    exact hstationary
  intro variation
  let variationSpace : CoupledElectrograviticVariationSpace :=
    ((variation.metricReal, variation.metricImag),
      (variation.gauge, variation.entropic))
  obtain ⟨p, hp⟩ := D.realizeVariation_surjective variationSpace
  have hpzero := congrArg (fun L : P →L[ℝ] ℝ => L p) hzero
  rw [D.integratedDerivative_apply p] at hpzero
  simpa [variationSpace, hp, coupledVariationOfSpace] using hpzero

/-- A stationary nonlinear action integrated against the metric-built
Lorentzian measure yields the repo's complete metric-built
Einstein--Maxwell--entropic equation and its Levi-Civita/Bianchi geometry. -/
@[zil_level physical_theorem]
theorem derive_metricBuilt_electrogravitic_field_equation
    (gField gInvField : FourMetricField) (x : FourCoordinate)
    (ΛField SField : FourTensor)
    (κField mRField mIField cField S1Field S2Field : ℝ)
    (kField AField : Fin 4 → ℝ)
    (hκ : κField ≠ 0) (hGeom : IsFourMetricPair gField gInvField)
    (D : CanonicalIntegratedElectrograviticActionData P metric
      (metricBuiltRicciAt gField gInvField x)
      (metricBuiltScalarAt gField gInvField x)
      (gField x) (gInvField x) ΛField SField κField
      mIField cField S1Field S2Field kField AField)
    (hstationary : D.IsStationary) :
    ElectroGravitationalFieldEquation
        (metricBuiltRicciAt gField gInvField x)
        (metricBuiltScalarAt gField gInvField x)
        (gField x) ΛField
        (maxwellStressEnergy (gField x) (gInvField x)
          (faraday kField AField))
        SField κField mRField mIField cField S1Field S2Field kField AField
      ∧ AreInverseMetrics (gField x) (gInvField x)
      ∧ (∀ ν, maxwellOp (faraday kField AField) kField ν = 0)
      ∧ (∀ lam μ ν,
        kField lam * faraday kField AField μ ν
          + kField μ * faraday kField AField ν lam
          + kField ν * faraday kField AField lam μ = 0)
      ∧ IsTorsionFree (metricBuiltConnectionField gField gInvField x)
      ∧ IsMetricCompatible
        (metricBuiltConnectionField gField gInvField x)
        (metricFirstJet (frechetCoordinatePartial (ι := Fin 4)) gField x)
        (gField x)
      ∧ FirstBianchi (metricBuiltRiemannAt gField gInvField x) := by
  exact
    derive_metricBuilt_electrogravitic_field_equation_from_coupled_stationarity
      gField gInvField x ΛField SField κField mRField mIField cField
      S1Field S2Field kField AField hκ hGeom
      (D.stationary_implies_coupled hstationary)

end CanonicalIntegratedElectrograviticActionData

/-! ## A. Constructed microscopic entropic--BCJ action -/

section ConstructedMicroscopicAction

variable {X : Type*}

/-- The BCJ energy-coordinate mismatch `q - (S₁ + S₂)`. At the physical
coordinate `q = mI * c ^ 2`, its zero set is the entropic BCJ split. -/
def bcjEnergyMismatch (q S1 S2 : ℝ) : ℝ := q - (S1 + S2)

/-- The potential obtained by adding the quadratic BCJ mismatch penalty to
the microscopic drift potential. -/
def entropicBCJEffectivePotential (Psi q S1 S2 : ℝ) : ℝ :=
  Psi + (1 / 2 : ℝ) * bcjEnergyMismatch q S1 S2 ^ 2

/-- The explicit microscopic effective density
`(Psi + (q - S₁ - S₂)²/2) rho + beta⁻¹ rho log rho`.
Unlike `CanonicalIntegratedElectrograviticActionData.density`, this density
is a definition rather than a field of a certificate structure. -/
noncomputable def entropicBCJEffectiveDensity
    (Psi beta rho q S1 S2 : ℝ) : ℝ :=
  freeEnergyDensity (entropicBCJEffectivePotential Psi q S1 S2) beta rho

/-- The continuum effective action constructed by integrating the explicit
microscopic entropic--BCJ density. -/
noncomputable def entropicBCJEffectiveAction
    [MeasurableSpace X] (mu : Measure X) (Psi rho : X → ℝ)
    (beta q S1 S2 : ℝ) : ℝ :=
  ∫ x, entropicBCJEffectiveDensity (Psi x) beta (rho x) q S1 S2 ∂mu

/-- An affine probability-density variation `rho + t eta`. -/
def affineProbabilityPath (rho eta : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  rho x + t * eta x

/-- The explicitly computed local first-variation density along an affine
probability path. -/
noncomputable def entropicBCJProbabilityVariationDensity
    (Psi rho eta : X → ℝ) (beta q S1 S2 t : ℝ) (x : X) : ℝ :=
  freeEnergyVariation (entropicBCJEffectivePotential (Psi x) q S1 S2)
      beta (affineProbabilityPath rho eta t x) * eta x

/-- The derivative of the constructed microscopic density along an affine
probability variation is its free-energy first variation times the
variation. No derivative density is supplied as model data. -/
lemma entropicBCJEffectiveDensity_affineProbabilityPath_hasDerivAt
    (Psi rho eta : X → ℝ) (beta q S1 S2 t : ℝ) (x : X)
    (hne : affineProbabilityPath rho eta t x ≠ 0) :
    HasDerivAt
      (fun u => entropicBCJEffectiveDensity (Psi x) beta
        (affineProbabilityPath rho eta u x) q S1 S2)
      (entropicBCJProbabilityVariationDensity
        Psi rho eta beta q S1 S2 t x) t := by
  have hpath :
      HasDerivAt (fun u => affineProbabilityPath rho eta u x) (eta x) t := by
    simpa only [affineProbabilityPath, id_eq, one_mul] using
      ((hasDerivAt_id t).mul_const (eta x)).const_add (rho x)
  exact
    (freeEnergyDensity_hasDerivAt_rho
      (entropicBCJEffectivePotential (Psi x) q S1 S2)
      beta (affineProbabilityPath rho eta t x) hne).comp t hpath

/-- The constructed continuum action differentiates to the integral of the
explicitly computed microscopic first variation under standard dominated
differentiation hypotheses. The hypotheses concern only measurability,
integrability, domination, and positivity of the varied probability. -/
@[zil_level physical_theorem]
lemma entropicBCJEffectiveAction_affineProbabilityPath_hasDerivAt
    [MeasurableSpace X]
    (mu : Measure X) (Psi rho eta : X → ℝ) (beta q S1 S2 : ℝ)
    (bound : X → ℝ) (s : Set ℝ) (t0 : ℝ)
    (hs : s ∈ 𝓝 t0)
    (hFmeas : ∀ᶠ t in 𝓝 t0,
      AEStronglyMeasurable
        (fun x => entropicBCJEffectiveDensity (Psi x) beta
          (affineProbabilityPath rho eta t x) q S1 S2) mu)
    (hFint : Integrable
      (fun x => entropicBCJEffectiveDensity (Psi x) beta
        (affineProbabilityPath rho eta t0 x) q S1 S2) mu)
    (hDmeas : AEStronglyMeasurable
      (entropicBCJProbabilityVariationDensity
        Psi rho eta beta q S1 S2 t0) mu)
    (hbound : ∀ᵐ x ∂mu, ∀ t ∈ s,
      ‖entropicBCJProbabilityVariationDensity
        Psi rho eta beta q S1 S2 t x‖ ≤ bound x)
    (hboundInt : Integrable bound mu)
    (hpositive : ∀ᵐ x ∂mu, ∀ t ∈ s,
      affineProbabilityPath rho eta t x ≠ 0) :
    Integrable (entropicBCJProbabilityVariationDensity
        Psi rho eta beta q S1 S2 t0) mu ∧
      HasDerivAt
        (fun t => entropicBCJEffectiveAction mu Psi
          (affineProbabilityPath rho eta t) beta q S1 S2)
        (∫ x, entropicBCJProbabilityVariationDensity
          Psi rho eta beta q S1 S2 t0 x ∂mu) t0 := by
  apply
    Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalEinsteinHilbertAction.globalAction_hasDerivAt_of_dominated
      mu
    (fun t x => entropicBCJEffectiveDensity (Psi x) beta
      (affineProbabilityPath rho eta t x) q S1 S2)
    (entropicBCJProbabilityVariationDensity
      Psi rho eta beta q S1 S2)
    bound s t0 hs hFmeas hFint hDmeas hbound hboundInt
  filter_upwards [hpositive] with x hx t ht
  exact entropicBCJEffectiveDensity_affineProbabilityPath_hasDerivAt
    Psi rho eta beta q S1 S2 t x (hx t ht)

/-- Splitting off the explicitly constructed BCJ penalty leaves the ordinary
microscopic free-energy action plus the probability mass times the squared
energy mismatch. -/
lemma entropicBCJEffectiveAction_eq_freeEnergy_add_penalty
    [MeasurableSpace X] (mu : Measure X) (Psi rho : X → ℝ)
    (beta q S1 S2 : ℝ)
    (hfree : Integrable (fun x => freeEnergyDensity (Psi x) beta (rho x)) mu)
    (hrho : Integrable rho mu) :
    entropicBCJEffectiveAction mu Psi rho beta q S1 S2 =
      (∫ x, freeEnergyDensity (Psi x) beta (rho x) ∂mu) +
        (1 / 2 : ℝ) * bcjEnergyMismatch q S1 S2 ^ 2 * ∫ x, rho x ∂mu := by
  rw [entropicBCJEffectiveAction]
  have hdensity :
      (fun x => entropicBCJEffectiveDensity (Psi x) beta (rho x) q S1 S2) =
        fun x => freeEnergyDensity (Psi x) beta (rho x) +
          ((1 / 2 : ℝ) * bcjEnergyMismatch q S1 S2 ^ 2) * rho x := by
    funext x
    simp only [entropicBCJEffectiveDensity, entropicBCJEffectivePotential,
      freeEnergyDensity]
    ring
  rw [hdensity, integral_add hfree (hrho.const_mul _), integral_const_mul]

/-- The energy-coordinate derivative of the constructed continuum action is
the BCJ mismatch times total probability mass. It is derived from the action
formula, not identified by a certificate. -/
@[zil_level physical_theorem]
lemma entropicBCJEffectiveAction_energyCoordinate_hasDerivAt
    [MeasurableSpace X] (mu : Measure X) (Psi rho : X → ℝ)
    (beta q S1 S2 : ℝ)
    (hfree : Integrable (fun x => freeEnergyDensity (Psi x) beta (rho x)) mu)
    (hrho : Integrable rho mu) :
    HasDerivAt
      (fun r => entropicBCJEffectiveAction mu Psi rho beta r S1 S2)
      (bcjEnergyMismatch q S1 S2 * ∫ x, rho x ∂mu) q := by
  have heq :
      (fun r => entropicBCJEffectiveAction mu Psi rho beta r S1 S2) =
        fun r => (∫ x, freeEnergyDensity (Psi x) beta (rho x) ∂mu) +
          (1 / 2 : ℝ) * bcjEnergyMismatch r S1 S2 ^ 2 * ∫ x, rho x ∂mu := by
    funext r
    exact entropicBCJEffectiveAction_eq_freeEnergy_add_penalty
      mu Psi rho beta r S1 S2 hfree hrho
  rw [heq]
  have hmismatch :
      HasDerivAt (fun r => bcjEnergyMismatch r S1 S2) 1 q := by
    simpa [bcjEnergyMismatch] using (hasDerivAt_id q).sub_const (S1 + S2)
  have hpenaltyRaw :=
    ((hmismatch.pow 2).const_mul (1 / 2 : ℝ)).mul_const
      (∫ x, rho x ∂mu)
  have hpenalty :
      HasDerivAt
        (fun y => (1 / 2 : ℝ) *
          ((fun r => bcjEnergyMismatch r S1 S2) ^ 2) y * ∫ x, rho x ∂mu)
        (bcjEnergyMismatch q S1 S2 * ∫ x, rho x ∂mu) q :=
    hpenaltyRaw.congr_deriv (by norm_num; ring_nf; simp)
  change HasDerivAt
    (fun r => (1 / 2 : ℝ) * bcjEnergyMismatch r S1 S2 ^ 2 *
      ∫ x, rho x ∂mu)
    (bcjEnergyMismatch q S1 S2 * ∫ x, rho x ∂mu) q at hpenalty
  change HasDerivAt
    ((fun _ : ℝ => ∫ x, freeEnergyDensity (Psi x) beta (rho x) ∂mu) +
      fun r => (1 / 2 : ℝ) * bcjEnergyMismatch r S1 S2 ^ 2 *
        ∫ x, rho x ∂mu)
    (bcjEnergyMismatch q S1 S2 * ∫ x, rho x ∂mu) q
  have hsum : HasDerivAt
      ((fun _ : ℝ => ∫ x, freeEnergyDensity (Psi x) beta (rho x) ∂mu) +
        fun r => (1 / 2 : ℝ) * bcjEnergyMismatch r S1 S2 ^ 2 *
          ∫ x, rho x ∂mu)
      (bcjEnergyMismatch q S1 S2 * ∫ x, rho x ∂mu) q := by
    simpa only [zero_add] using
      (hasDerivAt_const q
        (∫ x, freeEnergyDensity (Psi x) beta (rho x) ∂mu)).add hpenalty
  exact hsum

/-- For a normalized microscopic probability, stationarity in the constructed
energy coordinate is equivalent to the BCJ split. -/
@[zil_level physical_theorem]
lemma entropicBCJEffectiveAction_energyCoordinate_stationary_iff
    [MeasurableSpace X] (mu : Measure X) (Psi rho : X → ℝ)
    (beta q S1 S2 : ℝ)
    (hfree : Integrable (fun x => freeEnergyDensity (Psi x) beta (rho x)) mu)
    (hrho : Integrable rho mu) (hnormalized : ∫ x, rho x ∂mu = 1) :
    HasDerivAt
        (fun r => entropicBCJEffectiveAction mu Psi rho beta r S1 S2) 0 q ↔
      q = S1 + S2 := by
  have hderived := entropicBCJEffectiveAction_energyCoordinate_hasDerivAt
    mu Psi rho beta q S1 S2 hfree hrho
  constructor
  · intro hstationary
    have hzero := hderived.unique hstationary
    rw [hnormalized, mul_one] at hzero
    exact sub_eq_zero.mp hzero
  · intro hsplit
    convert hderived using 1
    rw [hnormalized, mul_one, bcjEnergyMismatch, hsplit, sub_self]

/-- At `q = mI * c²`, stationarity of the constructed continuum action is
equivalent to the repository's BCJ entropic stationarity interface. -/
@[zil_level physical_theorem]
lemma entropicBCJEffectiveAction_stationary_iff_bcjEntropicStationary
    [MeasurableSpace X] (mu : Measure X) (Psi rho : X → ℝ)
    (beta mI c S1 S2 : ℝ)
    (hfree : Integrable (fun x => freeEnergyDensity (Psi x) beta (rho x)) mu)
    (hrho : Integrable rho mu) (hnormalized : ∫ x, rho x ∂mu = 1) :
    HasDerivAt
        (fun r => entropicBCJEffectiveAction mu Psi rho beta r S1 S2) 0
        (mI * c ^ 2) ↔
      IsBCJEntropicStationary mI c S1 S2 := by
  rw [entropicBCJEffectiveAction_energyCoordinate_stationary_iff
    mu Psi rho beta (mI * c ^ 2) S1 S2 hfree hrho hnormalized]
  exact (bcjEntropicStationary_iff mI c S1 S2).symm

/-! ## B. Explicit metric-built Einstein--Maxwell potential -/

/-- The coordinate Einstein--Maxwell potential used by the microscopic
effective action: `R[g]/(2 kappa) - F_ab F^ab/4`. Both curvature and Faraday
tensor are constructed by existing repository definitions from the metric
and gauge-potential fields. -/
noncomputable def metricBuiltEinsteinMaxwellPotential
    (g gInv : FourMetricField) (kappa : ℝ)
    (k A : FourCoordinate → Fin 4 → ℝ) (x : FourCoordinate) : ℝ :=
  (1 / (2 * kappa)) * metricBuiltScalarAt g gInv x -
    (1 / 4 : ℝ) * maxwellInvariant (gInv x) (faraday (k x) (A x))

/-- The explicit metric-built Einstein--Maxwell potential is invariant under
the pointwise Fourier gauge shift `A -> A + chi k`. -/
lemma metricBuiltEinsteinMaxwellPotential_gauge_invariant
    (g gInv : FourMetricField) (kappa : ℝ)
    (k A : FourCoordinate → Fin 4 → ℝ) (chi : FourCoordinate → ℝ) :
    metricBuiltEinsteinMaxwellPotential g gInv kappa k
        (fun x mu => A x mu + chi x * k x mu) =
      metricBuiltEinsteinMaxwellPotential g gInv kappa k A := by
  funext x
  unfold metricBuiltEinsteinMaxwellPotential
  rw [faraday_gauge_invariant (k x) (A x) (chi x)]

/-- The microscopic Einstein--Maxwell--BCJ action obtained without a supplied
global density: its local potential is metric-built and its nonlinear
information term is `beta⁻¹ rho log rho`. -/
noncomputable def metricBuiltEntropicBCJEffectiveAction
    (mu : Measure FourCoordinate) (g gInv : FourMetricField) (kappa : ℝ)
    (k A : FourCoordinate → Fin 4 → ℝ) (rho : FourCoordinate → ℝ)
    (beta q S1 S2 : ℝ) : ℝ :=
  entropicBCJEffectiveAction mu
    (metricBuiltEinsteinMaxwellPotential g gInv kappa k A)
    rho beta q S1 S2

/-- Gauge invariance of the constructed microscopic
Einstein--Maxwell--BCJ action. -/
@[zil_level bridge_theorem]
lemma metricBuiltEntropicBCJEffectiveAction_gauge_invariant
    (mu : Measure FourCoordinate) (g gInv : FourMetricField) (kappa : ℝ)
    (k A : FourCoordinate → Fin 4 → ℝ) (rho : FourCoordinate → ℝ)
    (beta q S1 S2 : ℝ) (chi : FourCoordinate → ℝ) :
    metricBuiltEntropicBCJEffectiveAction mu g gInv kappa k
        (fun x mu => A x mu + chi x * k x mu) rho beta q S1 S2 =
      metricBuiltEntropicBCJEffectiveAction mu g gInv kappa k A
        rho beta q S1 S2 := by
  rw [metricBuiltEntropicBCJEffectiveAction,
    metricBuiltEntropicBCJEffectiveAction,
    metricBuiltEinsteinMaxwellPotential_gauge_invariant]

/-- The Gibbs probability constructed from the full microscopic potential,
including the BCJ mismatch penalty. -/
noncomputable def entropicBCJGibbsDensity
    (Psi : X → ℝ) (beta q S1 S2 Z : ℝ) (x : X) : ℝ :=
  Real.exp (-(beta * entropicBCJEffectivePotential (Psi x) q S1 S2)) / Z

/-- At the constructed Gibbs density, the local probability first variation
is spatially constant. -/
lemma entropicBCJGibbs_probabilityVariation_constant
    (Psi eta : X → ℝ) (beta q S1 S2 Z : ℝ) (x : X)
    (hbeta : beta ≠ 0) (hZ : 0 < Z) :
    entropicBCJProbabilityVariationDensity Psi
        (entropicBCJGibbsDensity Psi beta q S1 S2 Z) eta
        beta q S1 S2 0 x =
      (1 / beta) * (1 - Real.log Z) * eta x := by
  simp only [entropicBCJProbabilityVariationDensity, affineProbabilityPath,
    zero_mul, add_zero, entropicBCJGibbsDensity]
  rw [gibbs_variation_constant
    (entropicBCJEffectivePotential (Psi x) q S1 S2) beta Z hbeta hZ]

/-- The constructed Gibbs density is stationary under every dominated affine
probability variation of zero total mass. The zero derivative follows from
the density formula and normalization constraint; it is not supplied as a
global stationarity certificate. -/
@[zil_level physical_theorem]
lemma entropicBCJGibbs_hasDerivAt_zero_of_mass_preserving
    [MeasurableSpace X]
    (mu : Measure X) (Psi eta : X → ℝ) (beta q S1 S2 Z : ℝ)
    (bound : X → ℝ) (s : Set ℝ)
    (hbeta : beta ≠ 0) (hZ : 0 < Z) (hs : s ∈ 𝓝 0)
    (hFmeas : ∀ᶠ t in 𝓝 0,
      AEStronglyMeasurable
        (fun x => entropicBCJEffectiveDensity (Psi x) beta
          (affineProbabilityPath
            (entropicBCJGibbsDensity Psi beta q S1 S2 Z) eta t x)
          q S1 S2) mu)
    (hFint : Integrable
      (fun x => entropicBCJEffectiveDensity (Psi x) beta
        (entropicBCJGibbsDensity Psi beta q S1 S2 Z x) q S1 S2) mu)
    (hDmeas : AEStronglyMeasurable
      (entropicBCJProbabilityVariationDensity Psi
        (entropicBCJGibbsDensity Psi beta q S1 S2 Z) eta
        beta q S1 S2 0) mu)
    (hbound : ∀ᵐ x ∂mu, ∀ t ∈ s,
      ‖entropicBCJProbabilityVariationDensity Psi
        (entropicBCJGibbsDensity Psi beta q S1 S2 Z) eta
        beta q S1 S2 t x‖ ≤ bound x)
    (hboundInt : Integrable bound mu)
    (hpositive : ∀ᵐ x ∂mu, ∀ t ∈ s,
      affineProbabilityPath
        (entropicBCJGibbsDensity Psi beta q S1 S2 Z) eta t x ≠ 0)
    (hmass : ∫ x, eta x ∂mu = 0) :
    HasDerivAt
      (fun t => entropicBCJEffectiveAction mu Psi
        (affineProbabilityPath
          (entropicBCJGibbsDensity Psi beta q S1 S2 Z) eta t)
        beta q S1 S2) 0 0 := by
  have hFint0 : Integrable
      (fun x => entropicBCJEffectiveDensity (Psi x) beta
        (affineProbabilityPath
          (entropicBCJGibbsDensity Psi beta q S1 S2 Z) eta 0 x)
        q S1 S2) mu := by
    simpa [affineProbabilityPath] using hFint
  have hglobal :=
    (entropicBCJEffectiveAction_affineProbabilityPath_hasDerivAt
      mu Psi (entropicBCJGibbsDensity Psi beta q S1 S2 Z) eta
      beta q S1 S2 bound s 0 hs hFmeas hFint0 hDmeas hbound
      hboundInt hpositive).2
  have hderivative :
      (∫ x, entropicBCJProbabilityVariationDensity Psi
        (entropicBCJGibbsDensity Psi beta q S1 S2 Z) eta
        beta q S1 S2 0 x ∂mu) = 0 := by
    calc
      _ = ∫ x, ((1 / beta) * (1 - Real.log Z)) * eta x ∂mu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x =>
          entropicBCJGibbs_probabilityVariation_constant
            Psi eta beta q S1 S2 Z x hbeta hZ
      _ = ((1 / beta) * (1 - Real.log Z)) * ∫ x, eta x ∂mu :=
        by rw [integral_const_mul]
      _ = 0 := by rw [hmass, mul_zero]
  rw [hderivative] at hglobal
  exact hglobal

/-! ## C. Constructed stationarity and local Clausius equalities -/

/-- Stationarity of the constructed normalized action at `q = mI c²`
produces the BCJ entropic split, while the same information-theoretic layer
has the exact coarse-graining and local-screen Clausius equalities. -/
@[zil_level physical_theorem]
lemma constructedAction_stationarity_bcj_and_localClausius
    [MeasurableSpace X]
    (mu : Measure X) (Psi rho : X → ℝ) (beta mI c S1 S2 : ℝ)
    (hfree : Integrable (fun x => freeEnergyDensity (Psi x) beta (rho x)) mu)
    (hrho : Integrable rho mu) (hnormalized : ∫ x, rho x ∂mu = 1)
    (hstationary : HasDerivAt
      (fun r => entropicBCJEffectiveAction mu Psi rho beta r S1 S2) 0
      (mI * c ^ 2))
    (step : Physlib.Thermodynamics.BoltzmannHTheorem.CoarseGrainingStep)
    (T : ℝ) (hT : 0 ≤ T) (acceleration dArea G : ℝ) :
    IsBCJEntropicStationary mI c S1 S2
      ∧ Physlib.Thermodynamics.Landauer.landauerEnergyForBits T
          (step.tauEnt / Real.log 2) = Constants.kB * T * step.tauEnt
      ∧ 0 ≤ Constants.kB * T * step.tauEnt
      ∧ screenEnergyFlux acceleration dArea G =
          Physlib.QuantumMechanics.ComplexAction.Lorentz.JacobsonUnruhRindlerClock.unruhTemperature
            acceleration * entropyDifferential dArea G := by
  have hbcj :=
    (entropicBCJEffectiveAction_stationary_iff_bcjEntropicStationary
      mu Psi rho beta mI c S1 S2 hfree hrho hnormalized).mp hstationary
  have hclausius := coarseGraining_clausius_heat step T hT
  exact ⟨hbcj, hclausius.1, hclausius.2,
    screen_first_law acceleration dArea G⟩

end ConstructedMicroscopicAction

/-! ## D. Constructed Maxwell gauge-variation interface -/

/-- The constructed Fourier Maxwell action realizes the coupled module's
post-integration-by-parts electromagnetic first variation, with the exact
normalization fixed by the formal-adjoint identity. -/
lemma maxwellFourierAction_line_hasDerivAt_electromagneticFirstVariation
    (k A α : Fin 4 → ℝ) :
    HasDerivAt
      (fun t : ℝ => maxwellFourierAction k (fun i => A i + t * α i))
      (-2 * electromagneticFirstVariation k A α) 0 := by
  refine (maxwellFourierAction_line_hasDerivAt k A α).congr_deriv ?_
  rw [maxwell_variational A k α]
  rfl

/-- Stationarity of the constructed Fourier Maxwell action is equivalent
to the electromagnetic stationarity interface used by the coupled action. -/
@[zil_level bridge_theorem]
lemma maxwellFourierAction_stationary_iff_electromagneticStationary
    (k A : Fin 4 → ℝ) :
    (∀ α : Fin 4 → ℝ,
      deriv (fun t : ℝ => maxwellFourierAction k
        (fun i => A i + t * α i)) 0 = 0) ↔
      IsElectromagneticStationary k A := by
  constructor
  · intro h α
    have hα := h α
    rw [(maxwellFourierAction_line_hasDerivAt_electromagneticFirstVariation
      k A α).deriv] at hα
    linarith
  · intro h α
    rw [(maxwellFourierAction_line_hasDerivAt_electromagneticFirstVariation
      k A α).deriv, h α, mul_zero]

/-! ## E. Canonical manifold Maxwell action -/

/-- The scalar Maxwell Lagrangian integrated against the metric volume
measure, without a second coordinate density factor. -/
noncomputable def maxwellScalarLagrangian
    (gInv F : FourTensor) : ℝ :=
  -(1 / 4 : ℝ) * maxwellInvariant gInv F

/-- The coordinate Maxwell density is exactly the scalar Lagrangian times
the Lorentzian coordinate-volume density. -/
lemma maxwellMetricDensity_eq_volume_mul_scalarLagrangian
    (g gInv F : FourTensor) :
    maxwellMetricDensity g gInv F =
      lorentzianVolumeDensity g * maxwellScalarLagrangian gInv F := by
  unfold maxwellMetricDensity maxwellScalarLagrangian
  ring

/-- The canonical pulled-back chart metric as a four-dimensional matrix. -/
def fourDimensionalChartMetricMatrix
    (hdim : Module.finrank ℝ E = 4)
    (metric : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (a : M) (y : (chartAt E a).target) : FourTensor :=
  chartMetricMatrix (finCongr hdim) metric a y

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M] [T2Space M] [SigmaCompactSpace M] in
/-- On the Lorentzian branch, the canonical geometric chart density is the
usual four-dimensional coordinate density of its reindexed metric matrix. -/
lemma chartMetricDensity_eq_lorentzianVolumeDensity_fourDimensional
    (hdim : Module.finrank ℝ E = 4)
    (metric : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (a : M) (y : (chartAt E a).target)
    (hLorentz : Matrix.det
      (fourDimensionalChartMetricMatrix hdim metric a y) < 0) :
    chartMetricDensity metric a y =
      lorentzianVolumeDensity
        (fourDimensionalChartMetricMatrix hdim metric a y) := by
  rw [chartMetricDensity_eq_absoluteDeterminantDensity_chartMetricMatrix
    (finCongr hdim)]
  exact (lorentzianVolumeDensity_eq_absoluteDeterminantDensity
    _ hLorentz).symm

/-- The Maxwell action on a smooth manifold, integrated against the
canonical Lorentzian measure constructed from the pseudo-Riemannian metric. -/
noncomputable def canonicalMaxwellAction
    (metric : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (gInv F : M → FourTensor) : ℝ :=
  ∫ x, maxwellScalarLagrangian (gInv x) (F x)
    ∂(PseudoRiemannianMetric.lorentzianVolumeMeasure metric)

/-- One weighted coordinate-chart contribution to the canonical Maxwell
action. The chart inverse pulls back only the scalar Lagrangian; the metric
density and partition weight are already carried by the constructed chart
measure. -/
noncomputable def canonicalMaxwellChartAction
    (metric : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (gInv F : M → FourTensor) (a : M) : ℝ :=
  ∫ y, maxwellScalarLagrangian
      (gInv (PseudoRiemannianMetric.chartInverse (E := E) a y))
      (F (PseudoRiemannianMetric.chartInverse (E := E) a y))
    ∂(PseudoRiemannianMetric.chartWeightedMeasure metric
      (PseudoRiemannianMetric.canonicalChartPartition (E := E) (M := M)) a)

/-- The fixed partition-weighted Euclidean reference measure for one
canonical Maxwell chart. The varying determinant density is not included. -/
noncomputable def canonicalMaxwellChartCoordinateMeasure (a : M) :
    Measure ((chartAt E a).target) :=
  chartPartitionMeasure
    (canonicalChartPartition (E := E) (M := M)) a

/-- In four dimensions, a canonical chart action is exactly the explicit
Maxwell coordinate density integrated against the partition-weighted
Euclidean chart measure. This derives the local density representation from
the metric-built chart measure and determinant reindexing. -/
lemma canonicalMaxwellChartAction_eq_integral_metricDensity
    (hdim : Module.finrank ℝ E = 4)
    (metric : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (manifoldGInv manifoldF : M → FourTensor) (a : M)
    (gInv F : (chartAt E a).target → FourTensor)
    (hmetricMeas : Measurable fun y : (chartAt E a).target ↦
      ENNReal.ofReal (chartMetricDensity metric a y))
    (hLorentz : ∀ y, Matrix.det
      (fourDimensionalChartMetricMatrix hdim metric a y) < 0)
    (hGInv : ∀ y, manifoldGInv (chartInverse (E := E) a y) = gInv y)
    (hF : ∀ y, manifoldF (chartInverse (E := E) a y) = F y) :
    canonicalMaxwellChartAction metric manifoldGInv manifoldF a =
      ∫ y, maxwellMetricDensity
          (fourDimensionalChartMetricMatrix hdim metric a y)
          (gInv y) (F y)
        ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a) := by
  unfold canonicalMaxwellChartAction
    canonicalMaxwellChartCoordinateMeasure
  rw [chartWeightedMeasure_eq_chartPartitionMeasure_withDensity
    metric (canonicalChartPartition (E := E) (M := M)) a hmetricMeas]
  rw [integral_withDensity_eq_integral_toReal_smul hmetricMeas]
  · apply integral_congr_ae
    filter_upwards [] with y
    rw [ENNReal.toReal_ofReal (chartMetricDensity_nonneg metric a y),
      hGInv y, hF y,
      chartMetricDensity_eq_lorentzianVolumeDensity_fourDimensional
        hdim metric a y (hLorentz y),
      maxwellMetricDensity_eq_volume_mul_scalarLagrangian]
    rfl
  · exact Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top

/-- The canonical manifold Maxwell action is exactly the summable atlas
gluing of its weighted chart contributions. -/
lemma canonicalMaxwellAction_eq_tsum_chartAction
    (metric : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (gInv F : M → FourTensor)
    (hint : Integrable
      (fun x ↦ maxwellScalarLagrangian (gInv x) (F x))
      (PseudoRiemannianMetric.lorentzianVolumeMeasure metric)) :
    canonicalMaxwellAction metric gInv F =
      ∑' a : M, canonicalMaxwellChartAction metric gInv F a := by
  exact PseudoRiemannianMetric.integral_lorentzianVolumeMeasure_eq_tsum_chartWeightedMeasure
      metric (fun x ↦ maxwellScalarLagrangian (gInv x) (F x)) hint

/-- The canonical Maxwell action along a path of genuine manifold metrics
and inverse-metric representatives. -/
noncomputable def canonicalMaxwellActionPath
    (metricPath : ℝ → PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (gInvPath : ℝ → M → FourTensor) (F : M → FourTensor)
    (t : ℝ) : ℝ :=
  canonicalMaxwellAction (metricPath t) (gInvPath t) F

/-- One chart contribution along the same genuine manifold-metric path. -/
noncomputable def canonicalMaxwellChartActionPath
    (metricPath : ℝ → PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (gInvPath : ℝ → M → FourTensor) (F : M → FourTensor)
    (a : M) (t : ℝ) : ℝ :=
  canonicalMaxwellChartAction (metricPath t) (gInvPath t) F a

/-- Chartwise differentiability with a summable derivative bound lifts to
the derivative of the actual canonical manifold Maxwell action. The action
representation used in the proof is derived from the constructed measure
at every nearby metric, rather than supplied as a global density
certificate. -/
@[zil_level physical_theorem]
lemma canonicalMaxwellActionPath_hasDerivAt_of_chart_sum
    (metricPath : ℝ → PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (gInvPath : ℝ → M → FourTensor) (F : M → FourTensor)
    (chartDerivative : M → ℝ → ℝ) (bound : M → ℝ)
    (s : Set ℝ)
    (hs : IsOpen s) (hconnected : IsPreconnected s) (hzero : 0 ∈ s)
    (hintegrable : ∀ t ∈ s, Integrable
      (fun x ↦ maxwellScalarLagrangian (gInvPath t x) (F x))
      (PseudoRiemannianMetric.lorentzianVolumeMeasure (metricPath t)))
    (hchart : ∀ a t, t ∈ s → HasDerivAt
      (canonicalMaxwellChartActionPath metricPath gInvPath F a)
      (chartDerivative a t) t)
    (hderivBound : ∀ a t, t ∈ s →
      ‖chartDerivative a t‖ ≤ bound a)
    (hbound : Summable bound)
    (haction : Summable (fun a ↦
      canonicalMaxwellChartActionPath metricPath gInvPath F a 0)) :
    HasDerivAt
      (canonicalMaxwellActionPath metricPath gInvPath F)
      (∑' a : M, chartDerivative a 0) 0 := by
  have hsum := hasDerivAt_tsum_of_isPreconnected
    hbound hs hconnected hchart hderivBound hzero haction hzero
  apply hsum.congr_of_eventuallyEq
  filter_upwards [hs.eventually_mem hzero] with t ht
  simpa [canonicalMaxwellActionPath, canonicalMaxwellChartActionPath] using
    canonicalMaxwellAction_eq_tsum_chartAction
      (metricPath t) (gInvPath t) F (hintegrable t ht)

/-! ## E.1. Compact-manifold finite chart reduction -/

/-- On a compact manifold, local finiteness of the canonical partition
reduces the Maxwell atlas sum to the finite set of nonempty chart weights. -/
lemma canonicalMaxwellAction_eq_sum_activeCharts
    [CompactSpace M]
    (metric : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (gInv F : M → FourTensor)
    (hint : Integrable
      (fun x ↦ maxwellScalarLagrangian (gInv x) (F x))
      (PseudoRiemannianMetric.lorentzianVolumeMeasure metric)) :
    canonicalMaxwellAction metric gInv F =
      ∑ a ∈ canonicalActiveCharts
        (E := E) (M := M), canonicalMaxwellChartAction metric gInv F a := by
  rw [canonicalMaxwellAction_eq_tsum_chartAction metric gInv F hint]
  apply tsum_eq_sum
  intro a ha
  unfold canonicalMaxwellChartAction
  rw [chartWeightedMeasure_eq_zero_of_not_mem_canonicalActiveCharts metric a ha]
  simp

/-- On a compact manifold, derivatives of the finitely many active chart
actions at the background metric lift directly to a derivative of the actual
canonical Maxwell action. Unlike infinite-series differentiation, no
neighborhood-wide derivative bound is needed. -/
@[zil_level physical_theorem]
lemma canonicalMaxwellActionPath_hasDerivAt_of_compact_chart_sum
    [CompactSpace M]
    (metricPath : ℝ → PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (gInvPath : ℝ → M → FourTensor) (F : M → FourTensor)
    (chartDerivative : M → ℝ)
    (hintegrable : ∀ᶠ t in 𝓝 (0 : ℝ), Integrable
      (fun x ↦ maxwellScalarLagrangian (gInvPath t x) (F x))
      (PseudoRiemannianMetric.lorentzianVolumeMeasure (metricPath t)))
    (hchart : ∀ a ∈ canonicalActiveCharts
      (E := E) (M := M), HasDerivAt
        (canonicalMaxwellChartActionPath metricPath gInvPath F a)
        (chartDerivative a) 0) :
    HasDerivAt
      (canonicalMaxwellActionPath metricPath gInvPath F)
      (∑ a ∈ canonicalActiveCharts
        (E := E) (M := M), chartDerivative a) 0 := by
  have hsum := HasDerivAt.fun_sum hchart
  apply hsum.congr_of_eventuallyEq
  filter_upwards [hintegrable] with t ht
  simpa [canonicalMaxwellActionPath, canonicalMaxwellChartActionPath] using
    canonicalMaxwellAction_eq_sum_activeCharts
      (metricPath t) (gInvPath t) F ht

/-! ## F. Integrated Maxwell metric variation -/

/-- The nonlinear coordinate-density Maxwell action along the covariant
metric line and its constructed inverse-metric direction. -/
noncomputable def integratedMaxwellMetricDensityPath
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (g gInv h F : X → FourTensor) (t : ℝ) : ℝ :=
  ∫ x, maxwellMetricDensity
      (g x + t • h x)
      (gInv x + t • inverseMetricVariation (gInv x) (h x))
      (F x) ∂μ

/-- Pointwise chart-metric, inverse-metric, and field-strength
identifications derive the local coordinate-density representation along an
affine four-dimensional metric path. No action or density equality is
supplied as a premise. -/
lemma canonicalMaxwellChartActionPath_eventuallyEq_integratedMetricDensityPath
    (hdim : Module.finrank ℝ E = 4)
    (metricPath : ℝ → PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (manifoldGInvPath : ℝ → M → FourTensor)
    (manifoldF : M → FourTensor) (a : M)
    (g gInv h F : (chartAt E a).target → FourTensor)
    (s : Set ℝ) (hs : s ∈ 𝓝 (0 : ℝ))
    (hmetric : ∀ t ∈ s, ∀ y,
      fourDimensionalChartMetricMatrix hdim (metricPath t) a y =
        g y + t • h y)
    (hmetricMeas : ∀ t ∈ s, Measurable fun y : (chartAt E a).target ↦
      ENNReal.ofReal (chartMetricDensity (metricPath t) a y))
    (hLorentz : ∀ (t : ℝ), t ∈ s →
      ∀ y, Matrix.det (g y + t • h y) < 0)
    (hGInv : ∀ t ∈ s, ∀ y,
      manifoldGInvPath t (chartInverse (E := E) a y) =
        gInv y + t • inverseMetricVariation (gInv y) (h y))
    (hF : ∀ y, manifoldF (chartInverse (E := E) a y) = F y) :
    canonicalMaxwellChartActionPath metricPath manifoldGInvPath manifoldF a
      =ᶠ[𝓝 (0 : ℝ)]
      integratedMaxwellMetricDensityPath
        (canonicalMaxwellChartCoordinateMeasure (E := E) a)
        g gInv h F := by
  filter_upwards [hs] with t ht
  unfold canonicalMaxwellChartActionPath
    integratedMaxwellMetricDensityPath
  rw [canonicalMaxwellChartAction_eq_integral_metricDensity
    hdim (metricPath t) (manifoldGInvPath t) manifoldF a
    (fun y ↦ gInv y + t • inverseMetricVariation (gInv y) (h y)) F
    (hmetricMeas t ht)
    (fun y ↦ by rw [hmetric t ht y]; exact hLorentz t ht y)
    (hGInv t ht) hF]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦ by
    change maxwellMetricDensity
      (fourDimensionalChartMetricMatrix hdim (metricPath t) a y)
      (gInv y + t • inverseMetricVariation (gInv y) (h y)) (F y) =
      maxwellMetricDensity (g y + t • h y)
        (gInv y + t • inverseMetricVariation (gInv y) (h y)) (F y)
    rw [hmetric t ht y]

/-- The pointwise stress-energy pairing that is the covariant metric
derivative of the Maxwell coordinate density. -/
noncomputable def maxwellMetricStressVariationDensity
    {X : Type*} (g gInv h F : X → FourTensor) (x : X) : ℝ :=
  lorentzianVolumeDensity (g x) / 2 *
    tensorPairing (maxwellStressEnergy (g x) (gInv x) (F x))
      (inverseMetricVariation (gInv x) (h x))

/-- A locally Lipschitz dominated Maxwell density path may be differentiated
under the integral. The derivative is constructed pointwise from the
Maxwell stress tensor rather than supplied as a density certificate. -/
@[zil_level physical_theorem]
lemma integratedMaxwellMetricDensityPath_hasDerivAt_stressEnergy
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (g gInv h F : X → FourTensor)
    (bound : X → ℝ) (s : Set ℝ)
    (hs : s ∈ 𝓝 (0 : ℝ))
    (hmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable
      (fun x ↦ maxwellMetricDensity
        (g x + t • h x)
        (gInv x + t • inverseMetricVariation (gInv x) (h x))
        (F x)) μ)
    (hint : Integrable
      (fun x ↦ maxwellMetricDensity (g x) (gInv x) (F x)) μ)
    (hderivMeas : AEStronglyMeasurable
      (maxwellMetricStressVariationDensity g gInv h F) μ)
    (hlipschitz : ∀ᵐ x ∂μ,
      LipschitzOnWith (Real.nnabs (bound x))
        (fun t ↦ maxwellMetricDensity
          (g x + t • h x)
          (gInv x + t • inverseMetricVariation (gInv x) (h x))
          (F x)) s)
    (hbound : Integrable bound μ)
    (hInv : ∀ᵐ x ∂μ, g x * gInv x = 1)
    (hLorentz : ∀ᵐ x ∂μ, Matrix.det (g x) < 0)
    (hgInv : ∀ᵐ x ∂μ, ∀ i j, gInv x i j = gInv x j i)
    (hh : ∀ᵐ x ∂μ, ∀ i j, h x i j = h x j i)
    (hF : ∀ᵐ x ∂μ, ∀ i j, F x i j = -F x j i) :
    HasDerivAt
      (integratedMaxwellMetricDensityPath μ g gInv h F)
      (∫ x, maxwellMetricStressVariationDensity g gInv h F x ∂μ) 0 := by
  apply (hasDerivAt_integral_of_dominated_loc_of_lip
    hs hmeas ?_ hderivMeas hlipschitz hbound ?_).2
  · simpa [integratedMaxwellMetricDensityPath] using hint
  · filter_upwards [hInv, hLorentz, hgInv, hh, hF] with x
      hxInv hxLorentz hxgInv hxh hxF
    exact maxwellMetricDensity_covariantLine_hasDerivAt_stressEnergy
      (g x) (gInv x) (h x) (F x)
      hxInv hxLorentz hxgInv hxh hxF

omit [MeasurableSpace M] [BorelSpace M] in
/-- If one canonical chart action is represented by the explicit nonlinear
coordinate Maxwell density, its derivative is the integrated Maxwell stress
pairing. The premise is a local coordinate-representation equality, not a
global density or derivative certificate. -/
@[zil_level physical_theorem]
lemma canonicalMaxwellChartActionPath_hasDerivAt_stressEnergy
    (metricPath : ℝ → PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (manifoldGInvPath : ℝ → M → FourTensor)
    (manifoldF : M → FourTensor) (a : M)
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (g gInv h F : X → FourTensor)
    (bound : X → ℝ) (s : Set ℝ)
    (hrepresent :
      canonicalMaxwellChartActionPath
        metricPath manifoldGInvPath manifoldF a =
      integratedMaxwellMetricDensityPath mu g gInv h F)
    (hs : s ∈ 𝓝 (0 : ℝ))
    (hmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable
      (fun x ↦ maxwellMetricDensity
        (g x + t • h x)
        (gInv x + t • inverseMetricVariation (gInv x) (h x))
        (F x)) mu)
    (hint : Integrable
      (fun x ↦ maxwellMetricDensity (g x) (gInv x) (F x)) mu)
    (hderivMeas : AEStronglyMeasurable
      (maxwellMetricStressVariationDensity g gInv h F) mu)
    (hlipschitz : ∀ᵐ x ∂mu,
      LipschitzOnWith (Real.nnabs (bound x))
        (fun t ↦ maxwellMetricDensity
          (g x + t • h x)
          (gInv x + t • inverseMetricVariation (gInv x) (h x))
          (F x)) s)
    (hbound : Integrable bound mu)
    (hInv : ∀ᵐ x ∂mu, g x * gInv x = 1)
    (hLorentz : ∀ᵐ x ∂mu, Matrix.det (g x) < 0)
    (hgInv : ∀ᵐ x ∂mu, ∀ i j, gInv x i j = gInv x j i)
    (hh : ∀ᵐ x ∂mu, ∀ i j, h x i j = h x j i)
    (hF : ∀ᵐ x ∂mu, ∀ i j, F x i j = -F x j i) :
    HasDerivAt
      (canonicalMaxwellChartActionPath
        metricPath manifoldGInvPath manifoldF a)
      (∫ x, maxwellMetricStressVariationDensity g gInv h F x ∂mu) 0 := by
  rw [hrepresent]
  exact integratedMaxwellMetricDensityPath_hasDerivAt_stressEnergy
    mu g gInv h F bound s hs hmeas hint hderivMeas hlipschitz hbound
    hInv hLorentz hgInv hh hF

/-- The canonical Maxwell chart derivative is the integrated stress-energy
pairing when the actual reindexed chart metric follows the stated affine
four-dimensional path. The coordinate action representation is derived by
`canonicalMaxwellChartActionPath_eventuallyEq_integratedMetricDensityPath`;
it is not an assumption of this result. -/
@[zil_level physical_theorem]
lemma canonicalMaxwellChartActionPath_hasDerivAt_stressEnergy_of_fourDimensionalChart
    (hdim : Module.finrank ℝ E = 4)
    (metricPath : ℝ → PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (manifoldGInvPath : ℝ → M → FourTensor)
    (manifoldF : M → FourTensor) (a : M)
    (g gInv h F : (chartAt E a).target → FourTensor)
    (bound : (chartAt E a).target → ℝ) (s : Set ℝ)
    (hmetric : ∀ t ∈ s, ∀ y,
      fourDimensionalChartMetricMatrix hdim (metricPath t) a y =
        g y + t • h y)
    (hmetricMeas : ∀ t ∈ s, Measurable fun y : (chartAt E a).target ↦
      ENNReal.ofReal (chartMetricDensity (metricPath t) a y))
    (hpathLorentz : ∀ (t : ℝ), t ∈ s →
      ∀ y, Matrix.det (g y + t • h y) < 0)
    (hGInvPath : ∀ t ∈ s, ∀ y,
      manifoldGInvPath t (chartInverse (E := E) a y) =
        gInv y + t • inverseMetricVariation (gInv y) (h y))
    (hField : ∀ y, manifoldF (chartInverse (E := E) a y) = F y)
    (hs : s ∈ 𝓝 (0 : ℝ))
    (hmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable
      (fun x ↦ maxwellMetricDensity
        (g x + t • h x)
        (gInv x + t • inverseMetricVariation (gInv x) (h x))
        (F x)) (canonicalMaxwellChartCoordinateMeasure (E := E) a))
    (hint : Integrable
      (fun x ↦ maxwellMetricDensity (g x) (gInv x) (F x))
      (canonicalMaxwellChartCoordinateMeasure (E := E) a))
    (hderivMeas : AEStronglyMeasurable
      (maxwellMetricStressVariationDensity g gInv h F)
      (canonicalMaxwellChartCoordinateMeasure (E := E) a))
    (hlipschitz : ∀ᵐ x
      ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a),
      LipschitzOnWith (Real.nnabs (bound x))
        (fun t ↦ maxwellMetricDensity
          (g x + t • h x)
          (gInv x + t • inverseMetricVariation (gInv x) (h x))
          (F x)) s)
    (hbound : Integrable bound
      (canonicalMaxwellChartCoordinateMeasure (E := E) a))
    (hInv : ∀ᵐ x ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a),
      g x * gInv x = 1)
    (hLorentz : ∀ᵐ x ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a),
      Matrix.det (g x) < 0)
    (hgInv : ∀ᵐ x ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a),
      ∀ i j, gInv x i j = gInv x j i)
    (hh : ∀ᵐ x ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a),
      ∀ i j, h x i j = h x j i)
    (hF : ∀ᵐ x ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a),
      ∀ i j, F x i j = -F x j i) :
    HasDerivAt
      (canonicalMaxwellChartActionPath
        metricPath manifoldGInvPath manifoldF a)
      (∫ x, maxwellMetricStressVariationDensity g gInv h F x
        ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a)) 0 := by
  have hstress := integratedMaxwellMetricDensityPath_hasDerivAt_stressEnergy
    (canonicalMaxwellChartCoordinateMeasure (E := E) a)
    g gInv h F bound s hs hmeas hint hderivMeas hlipschitz hbound
    hInv hLorentz hgInv hh hF
  apply hstress.congr_of_eventuallyEq
  exact canonicalMaxwellChartActionPath_eventuallyEq_integratedMetricDensityPath
    hdim metricPath manifoldGInvPath manifoldF a g gInv h F s hs
    hmetric hmetricMeas hpathLorentz hGInvPath hField

/-! ## G. Maxwell gauge boundary control -/

/-- The bulk Maxwell gauge variation `-2 αν ∂μFμν` in the
normalization of the constructed quadratic Fourier action. -/
noncomputable def maxwellGaugeBulkVariation
    {n : ℕ} (α maxwellDiv : BoxPoint n → Fin 4 → ℝ) :
    BoxPoint n → ℝ :=
  fun x ↦ -2 * ∑ ν, α x ν * maxwellDiv x ν

/-- The Maxwell integration-by-parts boundary current `2 αν Fμν`. -/
noncomputable def maxwellGaugeBoundaryCurrent
    (α : BoxPoint 3 → Fin 4 → ℝ)
    (F : BoxPoint 3 → FourTensor) : BoxPoint 3 → BoxVector 3 ℝ :=
  fun x μ ↦ 2 * ∑ ν, α x ν * F x μ ν

/-- The Maxwell gauge first-variation density after the product rule:
the Euler--Lagrange bulk term plus the divergence of its explicit boundary
current. -/
noncomputable def maxwellGaugeFirstVariationDensity
    (α maxwellDiv : BoxPoint 3 → Fin 4 → ℝ)
    (boundaryDerivative :
      BoxPoint 3 → BoxPoint 3 →L[ℝ] BoxVector 3 ℝ) :
    BoxPoint 3 → ℝ :=
  fun x ↦ maxwellGaugeBulkVariation α maxwellDiv x +
    boxDivergence boundaryDerivative x

/-- Genuine Stokes control of the Maxwell gauge variation. If the oriented
flux of the explicit Maxwell boundary current vanishes, its integrated
divergence drops out and only the source-free Maxwell bulk pairing remains. -/
@[zil_level physical_theorem]
lemma integratedMaxwellGaugeVariation_eq_bulk_of_boundary
    (a b : BoxPoint 3) (hle : a ≤ b)
    (α maxwellDiv : BoxPoint 3 → Fin 4 → ℝ)
    (F : BoxPoint 3 → FourTensor)
    (boundaryDerivative :
      BoxPoint 3 → BoxPoint 3 →L[ℝ] BoxVector 3 ℝ)
    (singular : Set (BoxPoint 3))
    (hsingular : singular.Countable)
    (hcontinuous : ContinuousOn
      (maxwellGaugeBoundaryCurrent α F) (Icc a b))
    (hderiv : ∀ x ∈
      (Set.pi Set.univ fun i ↦ Ioo (a i) (b i)) \ singular,
        HasFDerivAt (maxwellGaugeBoundaryCurrent α F)
          (boundaryDerivative x) x)
    (hbulk : IntegrableOn
      (maxwellGaugeBulkVariation α maxwellDiv) (Icc a b))
    (hdiv : IntegrableOn
      (boxDivergence boundaryDerivative) (Icc a b))
    (hboundary :
      (∑ i : Fin 4,
        ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            maxwellGaugeBoundaryCurrent α F
              (i.insertNth (b i) x) i) -
          ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            maxwellGaugeBoundaryCurrent α F
              (i.insertNth (a i) x) i)) = 0) :
    (∫ x in Icc a b,
      maxwellGaugeFirstVariationDensity
        α maxwellDiv boundaryDerivative x) =
      ∫ x in Icc a b, maxwellGaugeBulkVariation α maxwellDiv x := by
  rw [show maxwellGaugeFirstVariationDensity
      α maxwellDiv boundaryDerivative =
      fun x ↦ maxwellGaugeBulkVariation α maxwellDiv x +
        boxDivergence boundaryDerivative x from rfl]
  rw [MeasureTheory.integral_add hbulk hdiv,
    integral_boxDivergence_eq_zero_of_boundary
      a b hle (maxwellGaugeBoundaryCurrent α F)
      boundaryDerivative singular hsingular hcontinuous hderiv hdiv
      hboundary,
    add_zero]

/-! ## H. Canonical Einstein--Maxwell action path -/

/-- The coupled action path formed from the canonical Einstein--Hilbert and
Maxwell manifold actions, with their physical normalizations kept explicit. -/
noncomputable def canonicalEinsteinMaxwellActionPath
    [CompleteSpace E] [IsManifold 𝓘(ℝ, E) 2 M]
    (metricPath : ℝ → PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (RicSharpPath : ∀ (_ : ℝ) (x : M),
      TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x)
    (gInvPath : ℝ → M → FourTensor) (F : M → FourTensor)
    (einsteinCoefficient maxwellCoefficient t : ℝ) : ℝ :=
  einsteinCoefficient *
      canonicalEinsteinHilbertAction (metricPath t) (RicSharpPath t) +
    maxwellCoefficient * canonicalMaxwellActionPath metricPath gInvPath F t

omit [BorelSpace M] in
/-- The derivative of the coupled canonical action is the normalized sum of
the separately established Einstein and Maxwell derivatives. In particular,
the Einstein premise may be discharged after Palatini/GHY boundary control,
while the Maxwell premise may be discharged by atlas chart summation. -/
@[zil_level physical_theorem]
lemma canonicalEinsteinMaxwellActionPath_hasDerivAt
    [CompleteSpace E] [IsManifold 𝓘(ℝ, E) 2 M]
    (metricPath : ℝ → PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (RicSharpPath : ∀ (_ : ℝ) (x : M),
      TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x)
    (gInvPath : ℝ → M → FourTensor) (F : M → FourTensor)
    (einsteinCoefficient maxwellCoefficient
      einsteinDerivative maxwellDerivative : ℝ)
    (hEinstein : HasDerivAt
      (fun t ↦ canonicalEinsteinHilbertAction
        (metricPath t) (RicSharpPath t))
      einsteinDerivative 0)
    (hMaxwell : HasDerivAt
      (canonicalMaxwellActionPath metricPath gInvPath F)
      maxwellDerivative 0) :
    HasDerivAt
      (canonicalEinsteinMaxwellActionPath metricPath RicSharpPath
        gInvPath F einsteinCoefficient maxwellCoefficient)
      (einsteinCoefficient * einsteinDerivative +
        maxwellCoefficient * maxwellDerivative) 0 := by
  exact (hEinstein.const_mul einsteinCoefficient).add
    (hMaxwell.const_mul maxwellCoefficient)

omit [BorelSpace M] in
/-- If the boundary-controlled Einstein derivative and atlas-controlled
Maxwell derivative cancel with their action normalizations, the canonical
Einstein--Maxwell action is stationary. -/
lemma canonicalEinsteinMaxwellActionPath_stationary
    [CompleteSpace E] [IsManifold 𝓘(ℝ, E) 2 M]
    (metricPath : ℝ → PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (RicSharpPath : ∀ (_ : ℝ) (x : M),
      TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x)
    (gInvPath : ℝ → M → FourTensor) (F : M → FourTensor)
    (einsteinCoefficient maxwellCoefficient
      einsteinDerivative maxwellDerivative : ℝ)
    (hEinstein : HasDerivAt
      (fun t ↦ canonicalEinsteinHilbertAction
        (metricPath t) (RicSharpPath t))
      einsteinDerivative 0)
    (hMaxwell : HasDerivAt
      (canonicalMaxwellActionPath metricPath gInvPath F)
      maxwellDerivative 0)
    (hcancel : einsteinCoefficient * einsteinDerivative +
      maxwellCoefficient * maxwellDerivative = 0) :
    HasDerivAt
      (canonicalEinsteinMaxwellActionPath metricPath RicSharpPath
        gInvPath F einsteinCoefficient maxwellCoefficient) 0 0 := by
  simpa [hcancel] using
    canonicalEinsteinMaxwellActionPath_hasDerivAt
      metricPath RicSharpPath gInvPath F
      einsteinCoefficient maxwellCoefficient
      einsteinDerivative maxwellDerivative hEinstein hMaxwell

/- ZIL-BEGIN -/

zil attach
    PseudoRiemannianMetric.chartMetricDensity_eq_absoluteDeterminantDensity_chartMetricMatrix where
  formalizes @ "claim:chart-metric-density-is-invariant-under-coordinate-reindexing",
  epistemic_status @ "consistency-identity",
  supported_by @ "mathlib:Matrix.det_reindex_self"

zil attach
    PseudoRiemannianMetric.chartWeightedMeasure_eq_chartPartitionMeasure_withDensity where
  formalizes @ "claim:weighted-chart-measure-factors-through-metric-density",
  epistemic_status @ "consistency-identity",
  supported_by @ "mathlib:MeasureTheory.withDensity_mul",
  caveat @ "premise:the-chart-metric-density-is-measurable"

zil attach
    canonicalMaxwellChartActionPath_eventuallyEq_integratedMetricDensityPath where
  formalizes @ "claim:local-canonical-maxwell-action-has-coordinate-density-representation",
  supported_by @ "claim:weighted-chart-measure-factors-through-metric-density",
  supported_by @ "lean:chartMetricDensity_eq_lorentzianVolumeDensity_fourDimensional",
  caveat @ "premise:the-pointwise-coordinate-identifications-hold-near-the-background",
  caveat @ "scope:the-representation-is-chart-local-not-a-global-density-certificate"

zil attach
    canonicalMaxwellChartActionPath_hasDerivAt_stressEnergy_of_fourDimensionalChart where
  formalizes @ "claim:local-chart-maxwell-stress-variation",
  supported_by @ "claim:local-canonical-maxwell-action-has-coordinate-density-representation",
  supported_by @ "lean:integratedMaxwellMetricDensityPath_hasDerivAt_stressEnergy",
  caveat @ "premise:the-explicit-local-analytic-and-algebraic-hypotheses-hold"

zil attach PseudoRiemannianMetric.integral_lorentzianVolumeMeasure_eq_tsum_chartWeightedMeasure where
  formalizes @ "claim:integration-against-the-canonical-pseudo-riemannian-measure-is-exactly-the-summable-gluing-of-the-coordinate-chart-integrals-that-construct-that-measure",
  epistemic_status @ "consistency-identity",
  supported_by @ "mathlib:MeasureTheory.integral_sum_measure",
  supported_by @ "mathlib:MeasureTheory.integral_map",
  caveat @ "premise:the-manifold-field-is-bochner-integrable-against-the-canonical-measure"

zil attach canonicalMaxwellAction_eq_tsum_chartAction where
  formalizes @ "claim:the-canonical-maxwell-manifold-action-is-exactly-the-tsum-of-its-weighted-chart-contributions",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:PseudoRiemannianMetric.integral_lorentzianVolumeMeasure_eq_tsum_chartWeightedMeasure",
  caveat @ "premise:the-scalar-maxwell-lagrangian-is-integrable-against-the-canonical-metric-measure"

zil attach canonicalMaxwellActionPath_hasDerivAt_of_chart_sum where
  formalizes @ "claim:locally-differentiable-chart-maxwell-actions-with-a-summable-uniform-derivative-bound-differentiate-the-actual-canonical-manifold-maxwell-action",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.canonicalMaxwellAction_eq_tsum_chartAction",
  supported_by @ "mathlib:hasDerivAt_tsum_of_isPreconnected",
  caveat @ "premise:nearby-canonical-actions-are-integrable-and-chart-derivatives-have-a-summable-uniform-bound",
  caveat @ "scope:one-parameter-directional-derivative-not-a-full-field-space-frechet-derivative"

zil attach canonicalMaxwellActionPath_hasDerivAt_of_compact_chart_sum where
  formalizes @ "claim:on-a-compact-manifold-local-finiteness-reduces-the-canonical-maxwell-atlas-to-finitely-many-active-charts-whose-background-derivatives-sum-to-the-actual-manifold-action-derivative",
  supported_by @ "lean:PseudoRiemannianMetric.chartWeightedMeasure_eq_zero_of_not_mem_canonicalActiveCharts",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.canonicalMaxwellAction_eq_sum_activeCharts",
  supported_by @ "mathlib:HasDerivAt.fun_sum",
  caveat @ "premise:the-manifold-is-compact-nearby-actions-are-integrable-and-each-finitely-active-chart-action-is-differentiable-at-the-background"

zil attach canonicalMaxwellChartActionPath_hasDerivAt_stressEnergy where
  formalizes @ "claim:a-canonical-chart-action-locally-represented-by-the-explicit-nonlinear-coordinate-maxwell-density-has-derivative-equal-to-the-integrated-maxwell-stress-pairing",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.integratedMaxwellMetricDensityPath_hasDerivAt_stressEnergy",
  caveat @ "premise:the-local-coordinate-representation-equality-and-the-explicit-dominated-lipschitz-invertibility-signature-and-symmetry-hypotheses-hold",
  caveat @ "scope:the-representation-premise-is-chart-local-and-does-not-supply-a-global-density-or-derivative-certificate"

zil attach canonicalEinsteinMaxwellActionPath_hasDerivAt where
  formalizes @ "claim:the-canonical-einstein-maxwell-action-derivative-is-the-normalized-sum-of-its-separately-established-einstein-and-maxwell-derivatives",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalEinsteinHilbertAction.canonicalEinsteinHilbertActionPath_hasDerivAt_of_dominated",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.canonicalMaxwellActionPath_hasDerivAt_of_chart_sum",
  caveat @ "premise:the-two-sector-derivatives-have-been-established-for-the-same-metric-path-and-the-action-normalizations-are-explicit"

zil attach maxwellMetricDensity_eq_volume_mul_scalarLagrangian where
  formalizes @ "claim:the-explicit-coordinate-maxwell-density-is-the-scalar-maxwell-lagrangian-times-the-constructed-lorentzian-coordinate-volume-density",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.maxwellMetricDensity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.lorentzianVolumeDensity",
  caveat @ "scope:coordinate-density-identity-the-atlas-independent-action-integrates-the-scalar-lagrangian-against-the-canonical-metric-measure"

zil attach integratedMaxwellMetricDensityPath_hasDerivAt_stressEnergy where
  formalizes @ "claim:a-locally-lipschitz-dominated-integral-of-the-explicit-nonlinear-maxwell-coordinate-density-has-directional-derivative-equal-to-the-integral-of-the-volume-weighted-maxwell-stress-energy-pairing",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.maxwellMetricDensity_covariantLine_hasDerivAt_stressEnergy",
  supported_by @ "mathlib:hasDerivAt_integral_of_dominated_loc_of_lip",
  caveat @ "premise:measurability-integrability-local-lipschitz-domination-invertibility-lorentz-signature-and-symmetry-hold-almost-everywhere",
  caveat @ "scope:integrated-coordinate-density-variation-not-yet-the-chart-glued-frechet-derivative-of-the-varying-canonical-manifold-measure"

zil attach integratedMaxwellGaugeVariation_eq_bulk_of_boundary where
  formalizes @ "claim:on-a-four-dimensional-coordinate-box-the-genuine-divergence-theorem-removes-the-explicit-maxwell-gauge-boundary-current-when-its-total-oriented-boundary-flux-vanishes",
  supported_by @ "lean:Physlib.Mathematics.LovelockRund.integral_boxDivergence_eq_zero_of_boundary",
  caveat @ "premise:continuity-frechet-differentiability-integrability-and-zero-oriented-boundary-flux-of-the-explicit-current-two-alpha-nu-f-mu-nu-are-explicit",
  caveat @ "scope:coordinate-box-stokes-control-not-a-global-de-rham-stokes-theorem-on-an-arbitrary-manifold-with-boundary"

zil attach maxwellFourierAction_stationary_iff_electromagneticStationary where
  formalizes @ "claim:stationarity-of-the-explicit-quadratic-fourier-maxwell-action-is-equivalent-to-the-electromagnetic-first-variation-interface-used-by-the-coupled-electrogravitic-action",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.maxwellFourierAction_line_hasDerivAt",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.maxwell_variational",
  caveat @ "scope:exact-single-fourier-mode-gauge-potential-directional-derivative-not-the-spacetime-integrated-gauge-field-frechet-derivative-or-boundary-domain"

zil attach entropicBCJEffectiveAction_affineProbabilityPath_hasDerivAt where
  formalizes @ "claim:the-explicit-microscopic-entropic-bcj-density-differentiates-under-the-continuum-integral-without-a-supplied-density-derivative-certificate",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow.freeEnergyDensity_hasDerivAt_rho",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalEinsteinHilbertAction.globalAction_hasDerivAt_of_dominated",
  caveat @ "premise:the-explicit-measurability-integrability-domination-and-nonzero-probability-hypotheses-are-analytic-not-action-density-certificates"

zil attach entropicBCJEffectiveAction_stationary_iff_bcjEntropicStationary where
  formalizes @ "claim:for-a-normalized-microscopic-probability-stationarity-of-the-constructed-energy-coordinate-action-is-equivalent-to-the-entropic-bcj-split",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.entropicBCJEffectiveAction_energyCoordinate_hasDerivAt",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.bcjEntropicStationary_iff",
  caveat @ "scope:the-varied-coordinate-is-q-equal-to-mI-times-c-squared-and-the-probability-is-normalized"

zil attach entropicBCJGibbs_hasDerivAt_zero_of_mass_preserving where
  formalizes @ "claim:the-gibbs-density-constructed-from-the-entropic-bcj-effective-potential-is-stationary-under-dominated-zero-mass-probability-variations",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow.gibbs_variation_constant",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.entropicBCJEffectiveAction_affineProbabilityPath_hasDerivAt",
  caveat @ "premise:beta-is-nonzero-the-partition-function-is-positive-and-the-dominated-variation-hypotheses-hold"

zil attach metricBuiltEntropicBCJEffectiveAction_gauge_invariant where
  formalizes @ "claim:the-explicit-metric-built-einstein-maxwell-entropic-bcj-effective-action-is-invariant-under-pointwise-fourier-gauge-shifts",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday.faraday_gauge_invariant",
  caveat @ "scope:coordinate-fourier-mode-gauge-invariance-not-yet-a-full-gauge-field-frechet-variation-theorem"

zil attach constructedAction_stationarity_bcj_and_localClausius where
  formalizes @ "claim:stationarity-of-the-constructed-normalized-energy-coordinate-action-yields-the-bcj-split-alongside-the-exact-information-erasure-and-timelike-screen-clausius-equalities",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.entropicBCJEffectiveAction_stationary_iff_bcjEntropicStationary",
  supported_by @ "lean:Physlib.Thermodynamics.ModularErasureCost.coarseGraining_clausius_heat",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics.screen_first_law",
  caveat @ "claim:joint-operational-capstone-not-an-identification-of-the-kl-heat-with-the-screen-flux-without-an-additional-calibration"

zil_file_contract physlib.constructedEntropicBCJEffectiveAction where
  promises "An explicit nonlinear microscopic density consisting of a drift potential, a quadratic BCJ energy mismatch, and beta-inverse rho log rho is integrated directly. Its probability and energy-coordinate derivatives are computed from the formula. Normalized energy-coordinate stationarity is equivalent to the BCJ split, the constructed Gibbs probability is stationary under dominated mass-preserving variations, and a metric-built Einstein-Maxwell specialization is gauge invariant. Existing coarse-graining and local-screen Clausius equalities are carried with the stationarity result."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow.freeEnergyDensity",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.metricBuiltScalarAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.maxwellInvariant",
    "lean:Physlib.Thermodynamics.ModularErasureCost.coarseGraining_clausius_heat",
    "lean:Physlib.QuantumMechanics.ComplexAction.GaussCodazzi.ScreenThermodynamics.screen_first_law"
  ]
  forbids_substitutes [
    "supplying-the-global-action-density-as-a-structure-field",
    "supplying-the-integrated-derivative-identification-as-a-structure-field",
    "calling-probability-and-energy-coordinate-stationarity-a-full-metric-and-gauge-frechet-variation",
    "identifying-information-erasure-heat-with-screen-flux-without-a-calibration"
  ]
  witnessed_by [
    entropicBCJEffectiveAction_affineProbabilityPath_hasDerivAt,
    entropicBCJEffectiveAction_stationary_iff_bcjEntropicStationary,
    entropicBCJGibbs_hasDerivAt_zero_of_mass_preserving,
    metricBuiltEntropicBCJEffectiveAction_gauge_invariant,
    constructedAction_stationarity_bcj_and_localClausius
  ]

#zil_formalization_lint physlib.constructedEntropicBCJEffectiveAction

namespace CanonicalIntegratedElectrograviticActionData

zil attach globalAction_hasFDerivAt_of_dominated where
  formalizes @ "claim:a-uniformly-dominated-pointwise-frechet-derivative-passes-through-the-continuum-action-integral",
  epistemic_status @ "consistency-identity",
  supported_by @ "mathlib:hasFDerivAt_integral_of_dominated_of_fderiv_le",
  caveat @ "premise:measurability-integrability-a-common-derivative-bound-and-pointwise-frechet-differentiability-are-explicit"

zil attach CanonicalIntegratedElectrograviticActionData.hasFDerivAt where
  formalizes @ "claim:the-nonlinear-electrogravitic-action-integrated-against-the-metric-built-lorentzian-measure-has-the-integral-of-its-local-density-derivative-as-its-frechet-derivative",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:PseudoRiemannianMetric.lorentzianVolumeMeasure",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.globalAction_hasFDerivAt_of_dominated",
  caveat @ "premise:the-interacting-density-and-its-dominated-pointwise-derivative-certificate-are-model-data"

zil attach CanonicalIntegratedElectrograviticActionData.stationary_implies_coupled where
  formalizes @ "claim:stationarity-of-the-canonical-measure-continuum-action-forces-the-metric-maxwell-and-entropic-first-variation-sectors-to-vanish",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.CanonicalIntegratedElectrograviticActionData.hasFDerivAt",
  caveat @ "premise:the-continuum-variation-realization-is-surjective-and-the-integrated-density-derivative-is-identified-with-the-existing-coupled-first-variation"

zil attach
    CanonicalIntegratedElectrograviticActionData.derive_metricBuilt_electrogravitic_field_equation where
  formalizes @ "claim:a-stationary-nonlinear-action-integrated-against-the-metric-built-lorentzian-measure-yields-the-metric-built-complex-einstein-maxwell-entropic-equations-with-levi-civita-and-first-bianchi-certificates",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.CanonicalIntegratedElectrograviticActionData.stationary_implies_coupled",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_metricBuilt_electrogravitic_field_equation_from_coupled_stationarity",
  caveat @ "scope:the-global-integration-and-full-frechet-variation-are-proved-the-density-realization-remains-explicit-model-data-and-the-final-coordinate-field-carrier-is-the-repository-four-dimensional-metric-built-sector"

zil_file_contract physlib.globalElectrograviticCanonicalAction where
  promises "A nonlinear continuum action density is integrated against the pseudo-Riemannian metric's Lorentzian measure. Under explicit dominated Fréchet hypotheses its derivative passes through the integral. A surjective continuum variation realization and exact integrated-derivative identification make stationarity imply simultaneous metric, Maxwell, and entropic stationarity, hence the metric-built complex Einstein-Maxwell-entropic equations, inverse metric, homogeneous and source-free Maxwell equations, Levi-Civita compatibility, torsion freedom, and first Bianchi."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:PseudoRiemannianMetric.lorentzianVolumeMeasure",
    "lean:hasFDerivAt_integral_of_dominated_of_fderiv_le",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.coupledElectrograviticFirstVariation",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_metricBuilt_electrogravitic_field_equation_from_coupled_stationarity"
  ]
  forbids_substitutes [
    "calling-a-one-parameter-directional-derivative-the-full-coupled-frechet-variation",
    "dropping-dominated-differentiation-hypotheses-when-moving-the-variation-through-the-integral",
    "omitting-gauge-or-entropic-directions-from-the-continuum-variation-carrier",
    "claiming-that-the-action-density-is-derived-when-it-is-supplied-as-explicit-model-data"
  ]
  witnessed_by [
    globalAction_hasFDerivAt_of_dominated,
    CanonicalIntegratedElectrograviticActionData.hasFDerivAt,
    CanonicalIntegratedElectrograviticActionData.stationary_implies_coupled,
    CanonicalIntegratedElectrograviticActionData.derive_metricBuilt_electrogravitic_field_equation
  ]

#zil_formalization_lint physlib.globalElectrograviticCanonicalAction

/- ZIL-END -/

end CanonicalIntegratedElectrograviticActionData

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
