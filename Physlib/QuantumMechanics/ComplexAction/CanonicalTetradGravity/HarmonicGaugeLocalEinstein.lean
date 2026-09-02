/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.WaldMaximalDevelopment
public import Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
meta import Zil

/-!
# Harmonic-gauge local Einstein evolution and fixed-Cauchy uniqueness

This module closes the precise local-uniqueness seam between the continuum
ADM evolution and the Wald maximal-development layer.

First, `harmonicGaugeSourceAt` is the actual contracted Christoffel field

`H^ρ = g^{μν} Γ^ρ_{μν}`.

The continuum gauge residual lives in the same completed `Ḣ⁻¹` carrier as
the ADM Hamiltonian and momentum residuals.  Its Fréchet derivative along
the ADM vector field is required to equal a bounded homogeneous subsidiary
operator applied to the residual.  The existing ODE uniqueness theorem then
proves that zero harmonic-gauge data remain zero.  Combining this with the
existing constrained ADM trajectory gives local existence, Einstein/ADM
constraint propagation, harmonic-gauge propagation, and Cauchy uniqueness
on the common interval.

Finally, two such solutions with the same Cauchy datum are presented in one
common harmonic slab.  Their chart transition is the identity because the
phase trajectories agree.  Consequently it preserves the realized metric,
the Cauchy embedding, causality, and the Einstein predicate, and therefore
produces the repository's actual `FixedCauchyEquiv` together with a
metric-preservation theorem.

## Honest analytic boundary

The current ADM phase carrier is the completed continuum `Ḣ¹` carrier.
In three spatial dimensions `H¹` is not a multiplication algebra, so this
file does not pretend to derive the locally Lipschitz reduced Einstein
vector field from raw quadratic Christoffel terms at that regularity.
The `ConcreteADMGFreeCauchyData` Lipschitz premise and the differentiated
harmonic subsidiary identity remain explicit analytic inputs.  Replacing
them by a quasilinear Sobolev theorem requires a higher regularity carrier
and the corresponding Moser/product estimates.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity

namespace HarmonicGaugeLocalEinstein

open ADMConstraintPropagation
open WaldMaximalDevelopment
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence

/-! ## A. The geometric harmonic-gauge source -/

/-- The contracted Christoffel gauge source
`H^ρ = g^{μν} Γ^ρ_{μν}` at one coordinate point.  Harmonic (wave)
coordinates are exactly the vanishing of this function. -/
def harmonicGaugeSourceAt {ι : Type*} [Fintype ι]
    (gInv : Matrix ι ι ℝ) (Γ : ι → Matrix ι ι ℝ) (ρ : ι) : ℝ :=
  ∑ μ, ∑ ν, gInv μ ν * (Γ ρ) μ ν

/-- Harmonic gauge at a chart point is vanishing of every contracted
Christoffel component. -/
def IsHarmonicGaugeAt {ι : Type*} [Fintype ι]
    (gInv : Matrix ι ι ℝ) (Γ : ι → Matrix ι ι ℝ) : Prop :=
  ∀ ρ, harmonicGaugeSourceAt gInv Γ ρ = 0

@[simp]
lemma harmonicGaugeSourceAt_zero_connection {ι : Type*} [Fintype ι]
    (gInv : Matrix ι ι ℝ) (ρ : ι) :
    harmonicGaugeSourceAt gInv (fun _ => 0) ρ = 0 := by
  simp [harmonicGaugeSourceAt]

lemma isHarmonicGaugeAt_zero_connection {ι : Type*} [Fintype ι]
    (gInv : Matrix ι ι ℝ) :
    IsHarmonicGaugeAt gInv (fun _ => 0) := by
  intro ρ
  exact harmonicGaugeSourceAt_zero_connection gInv ρ

/-- The concrete metric-built harmonic source.  This definition connects the
gauge condition directly to the existing Levi-Civita construction rather
than introducing a second connection. -/
def metricHarmonicGaugeSourceAt {ι : Type*} [Fintype ι]
    (gInv : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) (ρ : ι) : ℝ :=
  harmonicGaugeSourceAt gInv (christoffelFromMetric gInv dg) ρ

/-! ## B. Distributional harmonic-gauge propagation on the ADM carrier -/

/-- The four weak harmonic-coordinate residuals use the already completed
`Ḣ⁻¹` ADM residual carrier: one temporal and three spatial components. -/
abbrev HarmonicGaugeWeakResidual : Type :=
  ADMWeakConstraintResidual

/-- Concrete harmonic-gauge data extending the existing continuum ADM
Cauchy problem.  The gauge map itself is the weak contracted-Christoffel
field; the two derivative fields state its genuine Fréchet subsidiary
equation, not trajectory-level propagation as an axiom. -/
structure HarmonicGaugeADMCauchyData
    (ħ c σ₀ : ℝ) (initialState : ADMMetricMomentumMatterPhaseSpace)
    extends ConcreteADMGFreeCauchyData ħ c σ₀ initialState where
  /-- Distributional contracted-Christoffel field on the ADM phase space. -/
  harmonicGaugeResidual :
    ADMMetricMomentumMatterPhaseSpace → HarmonicGaugeWeakResidual
  /-- Fréchet derivative of the weak harmonic-gauge map. -/
  harmonicGaugeResidualDerivative :
    ADMMetricMomentumMatterPhaseSpace →
      ADMMetricMomentumMatterPhaseSpace →L[ℝ] HarmonicGaugeWeakResidual
  /-- The displayed derivative is the actual Fréchet derivative. -/
  harmonicGaugeResidual_hasFDerivAt :
    ∀ state,
      HasFDerivAt harmonicGaugeResidual
        (harmonicGaugeResidualDerivative state) state
  /-- Homogeneous wave/subsidiary generator for the gauge source. -/
  harmonicGaugePropagation :
    HarmonicGaugeWeakResidual →L[ℝ] HarmonicGaugeWeakResidual
  /-- Contracted Bianchi plus the reduced equations identify the derivative
  along the ADM vector field with the homogeneous subsidiary system. -/
  harmonicGaugeResidualDerivative_vectorField :
    ∀ state,
      harmonicGaugeResidualDerivative state (toConcreteADMGFreeCauchyData.vectorField state) =
        harmonicGaugePropagation (harmonicGaugeResidual state)
  /-- The Cauchy data obey the harmonic constraint. -/
  initial_harmonicGauge : harmonicGaugeResidual initialState = 0

namespace HarmonicGaugeADMCauchyData

variable {ħ c σ₀ : ℝ}
  {initialState : ADMMetricMomentumMatterPhaseSpace}

/-- Harmonic gauge on the continuum phase carrier. -/
def InHarmonicGauge
    (D : HarmonicGaugeADMCauchyData ħ c σ₀ initialState)
    (state : ADMMetricMomentumMatterPhaseSpace) : Prop :=
  D.harmonicGaugeResidual state = 0

/-- The harmonic subsidiary evolution along an ADM trajectory follows from
the Fréchet chain rule. -/
@[zil_level bridge_theorem]
theorem harmonicGaugeResidual_hasDerivAt_along
    (D : HarmonicGaugeADMCauchyData ħ c σ₀ initialState)
    (trajectory : ℝ → ADMMetricMomentumMatterPhaseSpace) (t : ℝ)
    (hevolution :
      HasDerivAt trajectory
        (D.toConcreteADMGFreeCauchyData.vectorField (trajectory t)) t) :
    HasDerivAt (D.harmonicGaugeResidual ∘ trajectory)
      (D.harmonicGaugePropagation
        (D.harmonicGaugeResidual (trajectory t))) t := by
  have hchain :=
    (D.harmonicGaugeResidual_hasFDerivAt (trajectory t)).comp_hasDerivAt
      t hevolution
  rw [D.harmonicGaugeResidualDerivative_vectorField] at hchain
  exact hchain

/-- Zero harmonic gauge propagates throughout a local ADM evolution.  This
reuses the existing completed-residual subsidiary theorem. -/
@[zil_level physical_theorem]
theorem harmonicGauge_propagates
    (D : HarmonicGaugeADMCauchyData ħ c σ₀ initialState)
    (trajectory : ℝ → ADMMetricMomentumMatterPhaseSpace)
    (ε : ℝ) (hε : 0 < ε)
    (hzero : trajectory 0 = initialState)
    (hevolution : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt trajectory
        (D.toConcreteADMGFreeCauchyData.vectorField (trajectory t)) t) :
    ∀ t ∈ Set.Ioo (-ε) ε, D.InHarmonicGauge (trajectory t) := by
  apply zero_of_linear_constraint_evolution D.harmonicGaugePropagation
    (D.harmonicGaugeResidual ∘ trajectory) ε hε
  · change D.harmonicGaugeResidual (trajectory 0) = 0
    rw [hzero]
    exact D.initial_harmonicGauge
  · intro t ht
    exact D.harmonicGaugeResidual_hasDerivAt_along trajectory t
      (hevolution t ht)

/-- **Harmonic-gauge local Einstein well-posedness on the continuum ADM
carrier.**  There is a local trajectory through the supplied Cauchy data;
it satisfies the complete complex Einstein equation, the sourced ADM
constraints, and the weak harmonic-coordinate condition at every time. -/
@[zil_level physical_theorem]
theorem exists_local_harmonicEinstein_evolution
    (D : HarmonicGaugeADMCauchyData ħ c σ₀ initialState) :
    ∃ trajectory : ℝ → ADMMetricMomentumMatterPhaseSpace,
      trajectory 0 = initialState ∧
      ∃ ε > 0,
        (∀ t ∈ Set.Ioo (-ε) ε,
          HasDerivAt trajectory
            (D.toConcreteADMGFreeCauchyData.vectorField (trajectory t)) t)
        ∧ (∀ t ∈ Set.Ioo (-ε) ε,
          D.toConcreteADMGFreeCauchyData.FieldEquation (trajectory t)
          ∧ sourcedHamiltonianConstraint
              (D.toConcreteADMGFreeCauchyData.spatialScalarCurvature
                (trajectory t))
              (D.toConcreteADMGFreeCauchyData.extrinsicNormSq (trajectory t))
              (D.toConcreteADMGFreeCauchyData.energyDensity (trajectory t))
              (inferenceEinsteinCoupling ħ c σ₀)
              (D.toConcreteADMGFreeCauchyData.extrinsicCurvature
                (trajectory t))
          ∧ (∀ i,
              D.toConcreteADMGFreeCauchyData.momentumDivergence
                  (trajectory t) i =
                inferenceEinsteinCoupling ħ c σ₀ *
                  D.toConcreteADMGFreeCauchyData.matterMomentumDensity
                    (trajectory t) i)
          ∧ D.InHarmonicGauge (trajectory t)) := by
  obtain ⟨trajectory, hzero, ε, hε, hevolution, hphysical⟩ :=
    D.toConcreteADMGFreeCauchyData.exists_local_constrained_evolution
  refine ⟨trajectory, hzero, ε, hε, hevolution, ?_⟩
  have hgauge :=
    D.harmonicGauge_propagates trajectory ε hε hzero hevolution
  intro t ht
  exact ⟨(hphysical t ht).1, (hphysical t ht).2.1,
    (hphysical t ht).2.2, hgauge t ht⟩

/-- Harmonic-gauge developments with the same Cauchy datum are unique on
their common time interval.  Gauge propagation is a conclusion of the
preceding theorem; uniqueness uses the reduced Einstein vector field. -/
@[zil_level physical_theorem]
theorem local_harmonicEinstein_evolution_unique
    (D : HarmonicGaugeADMCauchyData ħ c σ₀ initialState)
    {trajectory₁ trajectory₂ : ℝ → ADMMetricMomentumMatterPhaseSpace}
    {ε : ℝ} (hε : 0 < ε)
    (hzero₁ : trajectory₁ 0 = initialState)
    (hzero₂ : trajectory₂ 0 = initialState)
    (hevol₁ : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt trajectory₁
        (D.toConcreteADMGFreeCauchyData.vectorField (trajectory₁ t)) t)
    (hevol₂ : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt trajectory₂
        (D.toConcreteADMGFreeCauchyData.vectorField (trajectory₂ t)) t) :
    Set.EqOn trajectory₁ trajectory₂ (Set.Ioo (-ε) ε) :=
  D.toConcreteADMGFreeCauchyData.local_constrained_evolution_unique
    hε hzero₁ hzero₂ hevol₁ hevol₂

end HarmonicGaugeADMCauchyData

/-! ## C. From trajectory uniqueness to a fixed-Cauchy local isometry -/

universe u v

/-- The common harmonic-coordinate slab around a Cauchy carrier `S`. -/
def LocalHarmonicSlab (S : Type v) (ε : ℝ) :=
  {p : ℝ × S // p.1 ∈ Set.Ioo (-ε) ε}

instance {S : Type v} [TopologicalSpace S] (ε : ℝ) :
    TopologicalSpace (LocalHarmonicSlab S ε) := by
  unfold LocalHarmonicSlab
  infer_instance

/-- The time coordinate of a harmonic-slab point. -/
def LocalHarmonicSlab.time {S : Type v} {ε : ℝ}
    (p : LocalHarmonicSlab S ε) : ℝ :=
  p.1.1

/-- The spatial/Cauchy coordinate of a harmonic-slab point. -/
def LocalHarmonicSlab.space {S : Type v} {ε : ℝ}
    (p : LocalHarmonicSlab S ε) : S :=
  p.1.2

/-- Embed the Cauchy carrier as the zero-time slice of a nonempty harmonic
slab. -/
def LocalHarmonicSlab.cauchyPoint {S : Type v} {ε : ℝ}
    (hε : 0 < ε) (σ : S) : LocalHarmonicSlab S ε :=
  ⟨(0, σ), by constructor <;> linarith⟩

/-- A common metric realization from the continuum ADM state and a spatial
harmonic coordinate. -/
structure HarmonicMetricRealization (S : Type v) where
  metric :
    ADMMetricMomentumMatterPhaseSpace → S →
      Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ

/-- Present a topological causal Einstein development in one common
harmonic-coordinate slab.  The chart records exactly the data consumed by
the Wald gluing layer, while `metric_eq` retains the Lorentzian metric that
the topological carrier deliberately omits. -/
structure HarmonicChartPresentation
    {S : Type v} [TopologicalSpace S]
    {ħ c σ₀ : ℝ} {initialState : ADMMetricMomentumMatterPhaseSpace}
    (D : HarmonicGaugeADMCauchyData ħ c σ₀ initialState)
    (M : HarmonicMetricRealization S)
    (ε : ℝ) (hε : 0 < ε)
    (causalModel :
      LocalHarmonicSlab S ε → LocalHarmonicSlab S ε → Prop)
    (A : SpacetimeDevelopment S)
    (trajectory : ℝ → ADMMetricMomentumMatterPhaseSpace) where
  chart : A.Point ≃ LocalHarmonicSlab S ε
  chart_continuous :
    @Continuous A.Point (LocalHarmonicSlab S ε)
      A.topology inferInstance chart
  chart_inv_continuous :
    @Continuous (LocalHarmonicSlab S ε) A.Point
      inferInstance A.topology chart.symm
  cauchy_chart : ∀ σ,
    chart (A.cauchyEmbedding σ) = LocalHarmonicSlab.cauchyPoint hε σ
  causal_iff : ∀ p q,
    A.causal p q ↔ causalModel (chart p) (chart q)
  einstein_iff : ∀ p,
    A.EinsteinAt p ↔
      D.toConcreteADMGFreeCauchyData.FieldEquation
        (trajectory (chart p).time)
  metric : A.Point → Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ
  metric_eq : ∀ p,
    metric p =
      M.metric (trajectory (chart p).time) (chart p).space

/-- A fixed-Cauchy equivalence equipped with the missing metric-preservation
law.  Because both sides use one harmonic chart and the chart transition is
the identity, equality of component matrices is the full pullback condition
in these coordinates. -/
structure FixedCauchyHarmonicIsometry
    {S : Type v} [TopologicalSpace S]
    {ħ c σ₀ : ℝ} {initialState : ADMMetricMomentumMatterPhaseSpace}
    {D : HarmonicGaugeADMCauchyData ħ c σ₀ initialState}
    {M : HarmonicMetricRealization S}
    {ε : ℝ} {hε : 0 < ε}
    {causalModel :
      LocalHarmonicSlab S ε → LocalHarmonicSlab S ε → Prop}
    {A B : SpacetimeDevelopment S}
    {trajectory₁ trajectory₂ : ℝ → ADMMetricMomentumMatterPhaseSpace}
    (PA : HarmonicChartPresentation D M ε hε causalModel A trajectory₁)
    (PB : HarmonicChartPresentation D M ε hε causalModel B trajectory₂) where
  toFixedCauchyEquiv : SpacetimeDevelopment.FixedCauchyEquiv A B
  chart_transition_identity : ∀ p,
    PB.chart (toFixedCauchyEquiv p) = PA.chart p
  metric_preserving : ∀ p,
    PB.metric (toFixedCauchyEquiv p) = PA.metric p

/-- Equality of the two harmonic-gauge trajectories constructs a genuine
fixed-Cauchy causal--Einstein equivalence whose common-chart transition is
the identity and whose Lorentzian metric components agree pointwise. -/
@[zil_level physical_theorem]
noncomputable def fixedCauchyHarmonicIsometry_of_trajectory_eq
    {S : Type v} [TopologicalSpace S]
    {ħ c σ₀ : ℝ} {initialState : ADMMetricMomentumMatterPhaseSpace}
    {D : HarmonicGaugeADMCauchyData ħ c σ₀ initialState}
    {M : HarmonicMetricRealization S}
    {ε : ℝ} {hε : 0 < ε}
    {causalModel :
      LocalHarmonicSlab S ε → LocalHarmonicSlab S ε → Prop}
    {A B : SpacetimeDevelopment S}
    {trajectory₁ trajectory₂ : ℝ → ADMMetricMomentumMatterPhaseSpace}
    (PA : HarmonicChartPresentation D M ε hε causalModel A trajectory₁)
    (PB : HarmonicChartPresentation D M ε hε causalModel B trajectory₂)
    (heq : Set.EqOn trajectory₁ trajectory₂ (Set.Ioo (-ε) ε)) :
    FixedCauchyHarmonicIsometry PA PB := by
  letI : TopologicalSpace A.Point := A.topology
  letI : TopologicalSpace B.Point := B.topology
  let e : A.Point ≃ B.Point := PA.chart.trans PB.chart.symm
  have hchart (p : A.Point) : PB.chart (e p) = PA.chart p := by
    simp [e]
  let fixed : SpacetimeDevelopment.FixedCauchyEquiv A B :=
    { toEquiv := e
      continuous_toFun := by
        exact PB.chart_inv_continuous.comp PA.chart_continuous
      continuous_invFun := by
        exact PA.chart_inv_continuous.comp PB.chart_continuous
      cauchy_commutes := by
        intro σ
        apply PB.chart.injective
        exact (hchart (A.cauchyEmbedding σ)).trans
          ((PA.cauchy_chart σ).trans (PB.cauchy_chart σ).symm)
      causal_map := by
        intro p q
        exact
          (PB.causal_iff (e p) (e q)).trans <|
            (by rw [hchart, hchart]; exact (PA.causal_iff p q).symm)
      einstein_map := by
        intro p
        calc
          B.EinsteinAt (e p) ↔
              D.toConcreteADMGFreeCauchyData.FieldEquation
                (trajectory₂ (PB.chart (e p)).time) :=
            PB.einstein_iff (e p)
          _ ↔ D.toConcreteADMGFreeCauchyData.FieldEquation
                (trajectory₂ (PA.chart p).time) := by rw [hchart]
          _ ↔ D.toConcreteADMGFreeCauchyData.FieldEquation
                (trajectory₁ (PA.chart p).time) := by
            have hstate :
                trajectory₂ (PA.chart p).time =
                  trajectory₁ (PA.chart p).time := by
              exact (heq (PA.chart p).property).symm
            rw [hstate]
          _ ↔ A.EinsteinAt p := (PA.einstein_iff p).symm }
  refine
    { toFixedCauchyEquiv := fixed
      chart_transition_identity := ?_
      metric_preserving := ?_ }
  · intro p
    exact hchart p
  · intro p
    rw [PB.metric_eq, hchart, PA.metric_eq]
    have hstate :
        trajectory₂ (PA.chart p).time =
          trajectory₁ (PA.chart p).time := by
      exact (heq (PA.chart p).property).symm
    rw [hstate]

/-- **Trajectory uniqueness promotes to fixed-Cauchy local spacetime
isometry.**  This is the adapter previously missing from the Wald layer:
same harmonic Cauchy data imply the same reduced trajectory, and the common
harmonic presentation turns that equality into a causal--Einstein
fixed-Cauchy equivalence with exact metric preservation. -/
@[zil_level physical_theorem]
theorem local_harmonicEinstein_unique_up_to_fixedCauchy_isometry
    {S : Type v} [TopologicalSpace S]
    {ħ c σ₀ : ℝ} {initialState : ADMMetricMomentumMatterPhaseSpace}
    (D : HarmonicGaugeADMCauchyData ħ c σ₀ initialState)
    (M : HarmonicMetricRealization S)
    {ε : ℝ} (hε : 0 < ε)
    (causalModel :
      LocalHarmonicSlab S ε → LocalHarmonicSlab S ε → Prop)
    {A B : SpacetimeDevelopment S}
    {trajectory₁ trajectory₂ : ℝ → ADMMetricMomentumMatterPhaseSpace}
    (hzero₁ : trajectory₁ 0 = initialState)
    (hzero₂ : trajectory₂ 0 = initialState)
    (hevol₁ : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt trajectory₁
        (D.toConcreteADMGFreeCauchyData.vectorField (trajectory₁ t)) t)
    (hevol₂ : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt trajectory₂
        (D.toConcreteADMGFreeCauchyData.vectorField (trajectory₂ t)) t)
    (PA : HarmonicChartPresentation D M ε hε causalModel A trajectory₁)
    (PB : HarmonicChartPresentation D M ε hε causalModel B trajectory₂) :
    Nonempty (FixedCauchyHarmonicIsometry PA PB) := by
  have heq :=
    D.local_harmonicEinstein_evolution_unique hε hzero₁ hzero₂
      hevol₁ hevol₂
  exact ⟨fixedCauchyHarmonicIsometry_of_trajectory_eq
    (causalModel := causalModel) PA PB heq⟩

/- ZIL-BEGIN -/

zil attach harmonicGaugeSourceAt where
  formalizes @ "definition:the-harmonic-wave-coordinate-source-is-the-contracted-christoffel-field-g-inverse-mu-nu-gamma-rho-mu-nu",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.christoffelFromMetric",
  caveat @ "scope:pointwise-coordinate-definition-the-continuum-weak-realization-is-the-h-minus-one-residual-below"

zil attach HarmonicGaugeADMCauchyData.harmonicGauge_propagates where
  formalizes @ "claim:zero-weak-harmonic-gauge-source-remains-zero-under-the-homogeneous-contracted-bianchi-subsidiary-evolution",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.zero_of_linear_constraint_evolution",
  caveat @ "premise:the-frechet-derivative-of-the-weak-contracted-christoffel-map-along-the-adm-vector-field-equals-the-declared-bounded-homogeneous-subsidiary-generator"

zil attach HarmonicGaugeADMCauchyData.exists_local_harmonicEinstein_evolution where
  formalizes @ "claim:the-continuum-adm-cauchy-datum-has-a-local-harmonic-gauge-trajectory-satisfying-the-complex-einstein-equation-and-both-sourced-adm-constraints",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.exists_local_constrained_evolution",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HarmonicGaugeLocalEinstein.HarmonicGaugeADMCauchyData.harmonicGauge_propagates",
  caveat @ "strong-visible-premise:the-gauge-reduced-vector-field-is-C-one-at-the-initial-state-and-globally-lipschitz-on-the-current-completed-adm-phase-carrier",
  caveat @ "regularity-boundary:the-current-h-dot-one-carrier-does-not-by-itself-supply-the-higher-sobolev-product-estimates-needed-to-derive-that-lipschitz-premise-from-the-raw-quadratic-einstein-nonlinearity"

zil attach local_harmonicEinstein_unique_up_to_fixedCauchy_isometry where
  formalizes @ "claim:two-local-harmonic-einstein-developments-of-the-same-cauchy-data-presented-in-one-common-harmonic-slab-are-equivalent-by-a-fixed-cauchy-causal-einstein-map-that-preserves-the-lorentzian-metric",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation.ConcreteADMGFreeCauchyData.local_constrained_evolution_unique",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.WaldMaximalDevelopment.SpacetimeDevelopment.FixedCauchyEquiv",
  caveat @ "scope:the-chart-transition-is-proved-to-be-the-identity-in-a-supplied-common-harmonic-chart-global-atlas-gluing-is-the-next-layer",
  caveat @ "premise:each-topological-causal-einstein-development-is-supplied-with-a-faithful-common-harmonic-chart-presentation-and-a-shared-metric-realization"

zil_file_contract physlib.harmonicGaugeLocalEinstein where
  promises "The metric-built contracted Christoffel field defines harmonic gauge. On the actual completed continuum ADM carrier, a Frechet-level homogeneous subsidiary equation propagates its zero weak residual. The existing constrained Picard-Lindelof trajectory consequently satisfies the complex Einstein equation, sourced Hamiltonian and momentum constraints, and harmonic gauge throughout its local interval, and is unique there. Two developments faithfully presented in one common harmonic slab are then related by an actual fixed-Cauchy causal-Einstein equivalence whose chart transition is the identity and whose Lorentzian metric matrices agree pointwise."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.WaldMaximalDevelopment",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric"
  ]
  forbids_substitutes [
    "claiming-the-h-dot-one-adm-carrier-is-a-three-dimensional-sobolev-multiplication-algebra",
    "calling-phase-trajectory-uniqueness-a-spacetime-isometry-without-the-common-harmonic-chart-and-metric-preservation-proof",
    "hiding-the-contracted-bianchi-harmonic-subsidiary-identity-as-trajectory-level-gauge-propagation"
  ]
  witnessed_by [
    harmonicGaugeSourceAt,
    HarmonicGaugeADMCauchyData.harmonicGaugeResidual_hasDerivAt_along,
    HarmonicGaugeADMCauchyData.harmonicGauge_propagates,
    HarmonicGaugeADMCauchyData.exists_local_harmonicEinstein_evolution,
    HarmonicGaugeADMCauchyData.local_harmonicEinstein_evolution_unique,
    fixedCauchyHarmonicIsometry_of_trajectory_eq,
    local_harmonicEinstein_unique_up_to_fixedCauchy_isometry
  ]

/- ZIL-END -/

end HarmonicGaugeLocalEinstein

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity
