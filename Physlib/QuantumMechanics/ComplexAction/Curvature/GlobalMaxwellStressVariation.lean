/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalElectrograviticAction
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
meta import Zil

/-!
# Compact global Maxwell stress variation

This file composes the canonical atlas integration theorem with the local
four-dimensional Maxwell stress variation. On a compact manifold, local
finiteness reduces the canonical atlas to finitely many active charts, so
the derivative of the actual manifold action is the finite sum of the
constructed chart stress integrals.

It also constructs the nonlinear coordinate Maxwell action on the Banach
space of bounded continuous covariant-metric, contravariant-metric, and
Faraday fields. Its Fréchet derivative is derived from the explicit density
and dominated integration. On inverse-compatible metric tangents, the local
derivative is exactly the Maxwell stress-energy pairing. This field-space
result uses a fixed coordinate measure; it does not claim the still-separate
Einstein--Hilbert jet, boundary, and manifold-metric Fréchet construction.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Bundle Module MeasureTheory Set Filter
open scoped BoundedContinuousFunction Manifold Topology

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations

universe v

open Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation
open PseudoRiemannianMetric

variable {n : WithTop ℕ∞}
variable {E M : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [TopologicalSpace M] [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M]
variable [IsManifold 𝓘(ℝ, E) (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x)]
variable [T2Space M] [SigmaCompactSpace M]

/-! # A. Compact atlas stress variation -/

/-- The Maxwell stress contribution of one canonical coordinate chart. -/
noncomputable def canonicalMaxwellChartStressDerivative
    (a : M) (g gInv h F : (chartAt E a).target → FourTensor) : ℝ :=
  ∫ x, maxwellMetricStressVariationDensity g gInv h F x
    ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a)

/-- On a compact four-dimensional manifold, the derivative of the actual
canonical Maxwell action is the finite sum of the stress-energy integrals
constructed on the active canonical charts. The proof composes the finite
atlas reduction with the determinant, measure-factorization, and local
stress-variation lemmas. -/
@[zil_level physical_theorem]
lemma canonicalMaxwellActionPath_hasDerivAt_stressEnergy_of_compact_fourDimensionalCharts
    [CompactSpace M]
    (hdim : Module.finrank ℝ E = 4)
    (metricPath : ℝ → PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (manifoldGInvPath : ℝ → M → FourTensor)
    (manifoldF : M → FourTensor)
    (g gInv h F : ∀ a : M, (chartAt E a).target → FourTensor)
    (bound : ∀ a : M, (chartAt E a).target → ℝ)
    (s : Set ℝ) (hs : s ∈ 𝓝 (0 : ℝ))
    (hintegrable : ∀ᶠ t in 𝓝 (0 : ℝ), Integrable
      (fun x ↦ maxwellScalarLagrangian (manifoldGInvPath t x) (manifoldF x))
      (lorentzianVolumeMeasure (metricPath t)))
    (hmetric : ∀ a ∈ canonicalActiveCharts (E := E) (M := M),
      ∀ t ∈ s, ∀ y,
        fourDimensionalChartMetricMatrix hdim (metricPath t) a y =
          g a y + t • h a y)
    (hmetricMeas : ∀ a ∈ canonicalActiveCharts (E := E) (M := M),
      ∀ t ∈ s, Measurable fun y : (chartAt E a).target ↦
        ENNReal.ofReal (chartMetricDensity (metricPath t) a y))
    (hpathLorentz : ∀ a ∈ canonicalActiveCharts (E := E) (M := M),
      ∀ (t : ℝ), t ∈ s → ∀ y,
        Matrix.det (g a y + t • h a y) < 0)
    (hGInvPath : ∀ a ∈ canonicalActiveCharts (E := E) (M := M),
      ∀ t ∈ s, ∀ y,
        manifoldGInvPath t (chartInverse (E := E) a y) =
          gInv a y + t • inverseMetricVariation (gInv a y) (h a y))
    (hField : ∀ a ∈ canonicalActiveCharts (E := E) (M := M),
      ∀ y, manifoldF (chartInverse (E := E) a y) = F a y)
    (hmeas : ∀ a ∈ canonicalActiveCharts (E := E) (M := M),
      ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable
        (fun x ↦ maxwellMetricDensity
          (g a x + t • h a x)
          (gInv a x + t • inverseMetricVariation (gInv a x) (h a x))
          (F a x)) (canonicalMaxwellChartCoordinateMeasure (E := E) a))
    (hint : ∀ a ∈ canonicalActiveCharts (E := E) (M := M), Integrable
      (fun x ↦ maxwellMetricDensity (g a x) (gInv a x) (F a x))
      (canonicalMaxwellChartCoordinateMeasure (E := E) a))
    (hderivMeas : ∀ a ∈ canonicalActiveCharts (E := E) (M := M),
      AEStronglyMeasurable
        (maxwellMetricStressVariationDensity (g a) (gInv a) (h a) (F a))
        (canonicalMaxwellChartCoordinateMeasure (E := E) a))
    (hlipschitz : ∀ a ∈ canonicalActiveCharts (E := E) (M := M),
      ∀ᵐ x ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a),
        LipschitzOnWith (Real.nnabs (bound a x))
          (fun t ↦ maxwellMetricDensity
            (g a x + t • h a x)
            (gInv a x + t • inverseMetricVariation (gInv a x) (h a x))
            (F a x)) s)
    (hbound : ∀ a ∈ canonicalActiveCharts (E := E) (M := M),
      Integrable (bound a)
        (canonicalMaxwellChartCoordinateMeasure (E := E) a))
    (hInv : ∀ a ∈ canonicalActiveCharts (E := E) (M := M),
      ∀ᵐ x ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a),
        g a x * gInv a x = 1)
    (hLorentz : ∀ a ∈ canonicalActiveCharts (E := E) (M := M),
      ∀ᵐ x ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a),
        Matrix.det (g a x) < 0)
    (hgInv : ∀ a ∈ canonicalActiveCharts (E := E) (M := M),
      ∀ᵐ x ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a),
        ∀ i j, gInv a x i j = gInv a x j i)
    (hh : ∀ a ∈ canonicalActiveCharts (E := E) (M := M),
      ∀ᵐ x ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a),
        ∀ i j, h a x i j = h a x j i)
    (hF : ∀ a ∈ canonicalActiveCharts (E := E) (M := M),
      ∀ᵐ x ∂(canonicalMaxwellChartCoordinateMeasure (E := E) a),
        ∀ i j, F a x i j = -F a x j i) :
    HasDerivAt
      (canonicalMaxwellActionPath metricPath manifoldGInvPath manifoldF)
      (∑ a ∈ canonicalActiveCharts (E := E) (M := M),
        canonicalMaxwellChartStressDerivative
          (E := E) a (g a) (gInv a) (h a) (F a)) 0 := by
  apply canonicalMaxwellActionPath_hasDerivAt_of_compact_chart_sum
    metricPath manifoldGInvPath manifoldF
    (fun a ↦ canonicalMaxwellChartStressDerivative
      (E := E) a (g a) (gInv a) (h a) (F a)) hintegrable
  intro a ha
  exact canonicalMaxwellChartActionPath_hasDerivAt_stressEnergy_of_fourDimensionalChart
    hdim metricPath manifoldGInvPath manifoldF a
    (g a) (gInv a) (h a) (F a) (bound a) s
    (hmetric a ha) (hmetricMeas a ha) (hpathLorentz a ha)
    (hGInvPath a ha) (hField a ha) hs (hmeas a ha) (hint a ha)
    (hderivMeas a ha) (hlipschitz a ha) (hbound a ha) (hInv a ha)
    (hLorentz a ha) (hgInv a ha) (hh a ha) (hF a ha)

/-! # B. Full Maxwell field-space Fréchet variation -/

/-- Euclidean coordinates for all sixteen components of a four-tensor. -/
abbrev EuclideanFourTensor := EuclideanSpace ℝ (Fin 4 × Fin 4)

/-- Read Euclidean tensor coordinates as the repository's matrix tensor. -/
def fourTensorOfEuclidean (q : EuclideanFourTensor) : FourTensor :=
  fun i j ↦ q (i, j)

/-- Write a repository matrix tensor in Euclidean component coordinates. -/
def euclideanOfFourTensor (q : FourTensor) : EuclideanFourTensor :=
  WithLp.toLp 2 fun ij ↦ q ij.1 ij.2

/-- Euclidean encoding followed by matrix decoding preserves every tensor
component. -/
@[simp] lemma fourTensorOfEuclidean_euclideanOfFourTensor
    (q : FourTensor) :
    fourTensorOfEuclidean (euclideanOfFourTensor q) = q := by
  ext i j
  rfl

/-- Matrix decoding followed by Euclidean encoding preserves every tensor
coordinate. -/
@[simp] lemma euclideanOfFourTensor_fourTensorOfEuclidean
    (q : EuclideanFourTensor) :
    euclideanOfFourTensor (fourTensorOfEuclidean q) = q := by
  ext ij
  rfl

/-- Matrix decoding preserves addition of Euclidean tensor coordinates. -/
@[simp] lemma fourTensorOfEuclidean_add (p q : EuclideanFourTensor) :
    fourTensorOfEuclidean (p + q) =
      fourTensorOfEuclidean p + fourTensorOfEuclidean q := by
  ext i j
  rfl

/-- Matrix decoding preserves scalar multiplication of Euclidean tensor
coordinates. -/
@[simp] lemma fourTensorOfEuclidean_smul (r : ℝ)
    (q : EuclideanFourTensor) :
    fourTensorOfEuclidean (r • q) = r • fourTensorOfEuclidean q := by
  ext i j
  rfl

/-- The local Maxwell field carrier, with covariant metric, contravariant
metric, and Faraday tensor treated as independent Euclidean coordinates. -/
abbrev MaxwellLocalFieldSpace :=
  (EuclideanFourTensor × EuclideanFourTensor) × EuclideanFourTensor

/-- The nonlinear Maxwell coordinate density on its complete local field
carrier. -/
noncomputable def maxwellLocalFieldDensity
    (field : MaxwellLocalFieldSpace) : ℝ :=
  maxwellMetricDensity (fourTensorOfEuclidean field.1.1)
    (fourTensorOfEuclidean field.1.2) (fourTensorOfEuclidean field.2)

/-- The nonlinear local Maxwell density is Fréchet differentiable at every
Lorentzian field configuration. -/
lemma maxwellLocalFieldDensity_differentiableAt
    (g gInv F : FourTensor) (hLorentz : Matrix.det g < 0) :
    DifferentiableAt ℝ maxwellLocalFieldDensity
      ((euclideanOfFourTensor g, euclideanOfFourTensor gInv),
        euclideanOfFourTensor F) := by
  have hdet : DifferentiableAt ℝ
      (fun field : MaxwellLocalFieldSpace ↦
        -Matrix.det (fourTensorOfEuclidean field.1.1))
      ((euclideanOfFourTensor g, euclideanOfFourTensor gInv),
        euclideanOfFourTensor F) := by
    simp only [Matrix.det_apply]
    unfold fourTensorOfEuclidean
    fun_prop
  have hdet_ne : -Matrix.det g ≠ 0 := by linarith
  have hvolume : DifferentiableAt ℝ
      (fun field : MaxwellLocalFieldSpace ↦
        Real.sqrt (-Matrix.det (fourTensorOfEuclidean field.1.1)))
      ((euclideanOfFourTensor g, euclideanOfFourTensor gInv),
        euclideanOfFourTensor F) :=
    DifferentiableAt.sqrt
      (f := fun field : MaxwellLocalFieldSpace ↦
        -Matrix.det (fourTensorOfEuclidean field.1.1))
      hdet (by simpa using hdet_ne)
  have hinvariant : DifferentiableAt ℝ
      (fun field : MaxwellLocalFieldSpace ↦
        maxwellInvariant (fourTensorOfEuclidean field.1.2)
          (fourTensorOfEuclidean field.2))
      ((euclideanOfFourTensor g, euclideanOfFourTensor gInv),
        euclideanOfFourTensor F) := by
    unfold maxwellInvariant raiseBothIndices
    unfold fourTensorOfEuclidean
    fun_prop
  change DifferentiableAt ℝ
    (fun field : MaxwellLocalFieldSpace ↦
      -(1 / 4 : ℝ) *
        Real.sqrt (-Matrix.det (fourTensorOfEuclidean field.1.1)) *
        maxwellInvariant (fourTensorOfEuclidean field.1.2)
          (fourTensorOfEuclidean field.2))
    ((euclideanOfFourTensor g, euclideanOfFourTensor gInv),
      euclideanOfFourTensor F)
  exact (hvolume.const_mul (-(1 / 4 : ℝ))).mul hinvariant

/-- Euclidean coordinates of a physical metric tangent: the covariant
direction is `h`, the contravariant direction is `-g⁻¹hg⁻¹`, and the
Faraday direction vanishes. -/
noncomputable def maxwellLocalMetricDirection
    (gInv h : FourTensor) : MaxwellLocalFieldSpace :=
  ((euclideanOfFourTensor h,
      euclideanOfFourTensor (inverseMetricVariation gInv h)), 0)

/-- Euclidean coordinates of a background metric, inverse metric, and
Faraday tensor. -/
noncomputable def maxwellLocalBackground
    (g gInv F : FourTensor) : MaxwellLocalFieldSpace :=
  ((euclideanOfFourTensor g, euclideanOfFourTensor gInv),
    euclideanOfFourTensor F)

/-- Evaluating the full local Fréchet derivative on a physical metric
tangent recovers the Maxwell stress-energy pairing. This identifies the
already constructed directional formula as one evaluation of a single
continuous linear derivative on all 48 local field coordinates. -/
@[zil_level physical_theorem]
lemma maxwellLocalFieldDensity_fderiv_metricDirection
    (g gInv h F : FourTensor)
    (hInv : g * gInv = 1) (hLorentz : Matrix.det g < 0)
    (hgInv : ∀ i j, gInv i j = gInv j i)
    (hh : ∀ i j, h i j = h j i)
    (hF : ∀ i j, F i j = -F j i) :
    fderiv ℝ maxwellLocalFieldDensity (maxwellLocalBackground g gInv F)
        (maxwellLocalMetricDirection gInv h) =
      lorentzianVolumeDensity g / 2 *
        tensorPairing (maxwellStressEnergy g gInv F)
          (inverseMetricVariation gInv h) := by
  have hfrechet :=
    (maxwellLocalFieldDensity_differentiableAt g gInv F hLorentz).hasFDerivAt
  have hcurve : HasDerivAt
      (fun t : ℝ ↦ maxwellLocalBackground g gInv F +
        t • maxwellLocalMetricDirection gInv h)
      (maxwellLocalMetricDirection gInv h) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (maxwellLocalMetricDirection gInv h)).const_add
        (maxwellLocalBackground g gInv F)
  have hline := hfrechet.comp_hasDerivAt_of_eq 0 hcurve (by
    simp [maxwellLocalBackground])
  have hstress := maxwellMetricDensity_covariantLine_hasDerivAt_stressEnergy
    g gInv h F hInv hLorentz hgInv hh hF
  have hline' : HasDerivAt
      (fun t : ℝ ↦ maxwellMetricDensity
        (g + t • h) (gInv + t • inverseMetricVariation gInv h) F)
      ((fderiv ℝ maxwellLocalFieldDensity (maxwellLocalBackground g gInv F))
        (maxwellLocalMetricDirection gInv h)) 0 := by
    apply hline.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun t ↦ by
      simp [maxwellLocalFieldDensity, maxwellLocalBackground,
        maxwellLocalMetricDirection]
  exact hline'.unique hstress

/-- The supremum-norm Banach carrier of bounded continuous Maxwell fields.
Every covariant-metric, contravariant-metric, and Faraday component is an
independent field coordinate. -/
abbrev MaxwellFieldSpace (X : Type*) [TopologicalSpace X] :=
  X →ᵇ MaxwellLocalFieldSpace

/-- The nonlinear Maxwell action on the full bounded-continuous field
carrier, integrated against a fixed coordinate measure. -/
noncomputable def maxwellFieldAction
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (background : X → MaxwellLocalFieldSpace)
    (field : MaxwellFieldSpace X) : ℝ :=
  ∫ x, maxwellLocalFieldDensity (background x + field x) ∂μ

/-- The pointwise Fréchet derivative of the nonlinear Maxwell density,
pulled back to the global field carrier by continuous evaluation. -/
noncomputable def maxwellFieldDensityDerivative
    {X : Type*} [TopologicalSpace X]
    (background : X → MaxwellLocalFieldSpace)
    (field : MaxwellFieldSpace X) (x : X) :
    MaxwellFieldSpace X →L[ℝ] ℝ :=
  (fderiv ℝ maxwellLocalFieldDensity (background x + field x)).comp
    (BoundedContinuousFunction.evalCLM ℝ x)

/-- The full nonlinear Maxwell field action has a genuine Fréchet
derivative. Pointwise differentiability is derived from the explicit
determinant and polynomial density; the premises contain only the standard
measurability, domination, and Lorentzian-neighborhood controls required to
pass that derivative through the integral. -/
@[zil_level physical_theorem]
lemma maxwellFieldAction_hasFDerivAt
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (background : X → MaxwellLocalFieldSpace)
    (bound : X → ℝ) (s : Set (MaxwellFieldSpace X))
    (field₀ : MaxwellFieldSpace X)
    (hs : s ∈ 𝓝 field₀)
    (hmeas : ∀ᶠ field in 𝓝 field₀, AEStronglyMeasurable
      (fun x ↦ maxwellLocalFieldDensity (background x + field x)) μ)
    (hint : Integrable
      (fun x ↦ maxwellLocalFieldDensity (background x + field₀ x)) μ)
    (hderivMeas : AEStronglyMeasurable
      (maxwellFieldDensityDerivative background field₀) μ)
    (hderivBound : ∀ᵐ x ∂μ, ∀ field ∈ s,
      ‖maxwellFieldDensityDerivative background field x‖ ≤ bound x)
    (hbound : Integrable bound μ)
    (hLorentz : ∀ᵐ x ∂μ, ∀ field ∈ s,
      Matrix.det
        (fourTensorOfEuclidean (background x + field x).1.1) < 0) :
    HasFDerivAt (maxwellFieldAction μ background)
      (∫ x, maxwellFieldDensityDerivative background field₀ x ∂μ) field₀ := by
  refine globalAction_hasFDerivAt_of_dominated
    (P := MaxwellFieldSpace X) (X := X) μ
    (fun field x ↦ maxwellLocalFieldDensity (background x + field x))
    (maxwellFieldDensityDerivative background) bound s field₀ hs
    hmeas hint hderivMeas hderivBound hbound ?_
  filter_upwards [hLorentz] with x hx
  intro field hfield
  have hlocal : DifferentiableAt ℝ maxwellLocalFieldDensity
      (background x + field x) := by
    change DifferentiableAt ℝ maxwellLocalFieldDensity
      (((background x).1.1 + (field x).1.1,
          (background x).1.2 + (field x).1.2),
        (background x).2 + (field x).2)
    simpa only [euclideanOfFourTensor_fourTensorOfEuclidean,
      Prod.fst_add, Prod.snd_add] using
      maxwellLocalFieldDensity_differentiableAt
      (fourTensorOfEuclidean (background x + field x).1.1)
      (fourTensorOfEuclidean (background x + field x).1.2)
      (fourTensorOfEuclidean (background x + field x).2) (hx field hfield)
  exact hlocal.hasFDerivAt.comp field
    ((BoundedContinuousFunction.evalCLM ℝ x).hasFDerivAt.const_add
      (background x))

/- ZIL-BEGIN -/

zil attach
    canonicalMaxwellActionPath_hasDerivAt_stressEnergy_of_compact_fourDimensionalCharts where
  formalizes @ "claim:compact-canonical-maxwell-action-varies-as-finite-chart-stress-sum",
  supported_by @ "lean:canonicalMaxwellActionPath_hasDerivAt_of_compact_chart_sum",
  supported_by @ "claim:local-chart-maxwell-stress-variation",
  caveat @ "premise:the-explicit-local-hypotheses-hold-on-every-active-chart",
  caveat @ "scope:one-parameter-metric-derivative-not-a-field-space-frechet-derivative"

zil attach maxwellLocalFieldDensity_fderiv_metricDirection where
  formalizes @ "claim:maxwell-local-frechet-derivative-evaluates-to-stress-pairing",
  supported_by @ "lean:maxwellLocalFieldDensity_differentiableAt",
  supported_by @ "lean:maxwellMetricDensity_covariantLine_hasDerivAt_stressEnergy",
  caveat @ "scope:inverse-compatible-metric-tangent-with-fixed-faraday-field"

zil attach maxwellFieldAction_hasFDerivAt where
  formalizes @ "claim:nonlinear-maxwell-action-has-full-field-space-frechet-derivative",
  supported_by @ "lean:maxwellLocalFieldDensity_differentiableAt",
  supported_by @ "lean:globalAction_hasFDerivAt_of_dominated",
  caveat @ "premise:measurability-domination-and-lorentzian-neighborhood-control",
  caveat @ "scope:bounded-continuous-independent-metric-inverse-metric-and-faraday-fields",
  caveat @ "scope:fixed-coordinate-measure-not-the-einstein-hilbert-jet-boundary-variation"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
