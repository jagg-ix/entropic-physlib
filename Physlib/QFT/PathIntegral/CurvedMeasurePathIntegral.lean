/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.PathIntegral.MeasureExpectation
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Curved-background measure path integrals

This file equips the shared measure-theoretic path-integral model with a
curved-background reference measure `dμ_g = ρ_g dμ`.  The construction is
kept at the standard measure and operator-contract level: a base measure,
a nonnegative volume density, curvature-coupled imaginary actions, and
gauge-shifted sources.

The point is to give Chern-Simons/Wilson-loop, gravity, one-loop, ABJM,
and matrix-model formalizations a common curved-measure interface without
depending on any project-specific helper nomenclature.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory

namespace Physlib.QFT.PathIntegral

/-- Geometric measure datum for curved-background integration. -/
structure CurvedMeasureDatum (α : Type*) [MeasurableSpace α] where
  /-- The base reference measure. -/
  baseMeasure : Measure α
  /-- The nonnegative volume density `ρ_g`. -/
  volumeDensity : α → ℝ
  /-- Measurability of `ρ_g`. -/
  measurable_volumeDensity : Measurable volumeDensity
  /-- Nonnegativity of `ρ_g`. -/
  volumeDensity_nonneg : ∀ x, 0 ≤ volumeDensity x

namespace CurvedMeasureDatum

variable {α : Type*} [MeasurableSpace α] (g : CurvedMeasureDatum α)

/-- Curved reference measure `dμ_g = ρ_g dμ`, encoded by `Measure.withDensity`. -/
def volumeMeasure : Measure α :=
  g.baseMeasure.withDensity (fun x => ENNReal.ofReal (g.volumeDensity x))

/-- The curved measure is absolutely continuous with respect to the base measure. -/
theorem volumeMeasure_absolutelyContinuous :
    g.volumeMeasure ≪ g.baseMeasure := by
  simpa [volumeMeasure] using
    withDensity_absolutelyContinuous g.baseMeasure
      (fun x => ENNReal.ofReal (g.volumeDensity x))

/-- Flat-density limit: if `ρ_g = 1`, the curved measure is the base measure. -/
theorem volumeMeasure_eq_base_of_density_one
    (hρ : g.volumeDensity = fun _ => (1 : ℝ)) :
    g.volumeMeasure = g.baseMeasure := by
  simp [volumeMeasure, hρ]

end CurvedMeasureDatum

/-- A path-integral model whose reference measure is supplied by curved-background data. -/
structure CurvedMeasurePathIntegralModel (α : Type*) [MeasurableSpace α] where
  /-- Curved-background measure datum. -/
  geom : CurvedMeasureDatum α
  /-- Planck constant `ℏ > 0`. -/
  hbar : ℝ
  /-- Positivity of `ℏ`. -/
  hbar_pos : 0 < hbar
  /-- Real-action functional. -/
  actionRe : α → ℝ
  /-- Imaginary-action functional. -/
  actionIm : α → ℝ
  /-- Measurability of the real action. -/
  measurable_actionRe : Measurable actionRe
  /-- Measurability of the imaginary action. -/
  measurable_actionIm : Measurable actionIm
  /-- Nonnegativity of the imaginary action. -/
  actionIm_nonneg : ∀ x, 0 ≤ actionIm x

namespace CurvedMeasurePathIntegralModel

variable {α : Type*} [MeasurableSpace α] (c : CurvedMeasurePathIntegralModel α)

/-- Forget the curved wrapper, using `dμ_g` as the reference measure. -/
def toMeasurePathIntegralModel : MeasurePathIntegralModel α where
  μ := c.geom.volumeMeasure
  hbar := c.hbar
  hbar_pos := c.hbar_pos
  actionRe := c.actionRe
  actionIm := c.actionIm
  measurable_actionRe := c.measurable_actionRe
  measurable_actionIm := c.measurable_actionIm
  actionIm_nonneg := c.actionIm_nonneg

/-- Curved partition functional `Z_g`. -/
def partition : ℂ :=
  c.toMeasurePathIntegralModel.partition

/-- Curved unnormalised expectation. -/
def unnormalizedExpectation (O : α → ℂ) : ℂ :=
  c.toMeasurePathIntegralModel.unnormalizedExpectation O

/-- Curved normalised expectation. -/
def normalizedExpectation (O : α → ℂ) : ℂ :=
  c.toMeasurePathIntegralModel.normalizedExpectation O

/-- Curved source-coupled partition `Z_g[J]`. -/
def sourceCoupledPartition (J : α → ℂ) : ℂ :=
  c.toMeasurePathIntegralModel.sourceCoupledPartition J

/-- Curved connected generating functional `W_g[J] = log Z_g[J]`. -/
def connectedGeneratingFunctional (J : α → ℂ) : ℂ :=
  c.toMeasurePathIntegralModel.connectedGeneratingFunctional J

/-- Zero-source compatibility in the curved model. -/
theorem sourceCoupledPartition_zero :
    c.sourceCoupledPartition (fun _ => (0 : ℂ)) = c.partition := by
  unfold sourceCoupledPartition partition
  simpa using c.toMeasurePathIntegralModel.sourceCoupledPartition_zero

/-- The flat-density limit rewrites the reduced model's measure as the base measure. -/
theorem toMeasurePathIntegralModel_measure_eq_base_of_density_one
    (hρ : c.geom.volumeDensity = fun _ => (1 : ℝ)) :
    c.toMeasurePathIntegralModel.μ = c.geom.baseMeasure := by
  simpa [toMeasurePathIntegralModel] using
    c.geom.volumeMeasure_eq_base_of_density_one hρ

/-- Flat-density limit: the curved partition is the base-measure integral. -/
theorem partition_eq_base_integral_of_density_one
    (hρ : c.geom.volumeDensity = fun _ => (1 : ℝ)) :
    c.partition = ∫ x, c.toMeasurePathIntegralModel.weight x ∂c.geom.baseMeasure := by
  unfold partition toMeasurePathIntegralModel
  rw [c.geom.volumeMeasure_eq_base_of_density_one hρ]
  simp [MeasurePathIntegralModel.partition]

/-- Curved partition over the base measure with the `toReal ∘ ofReal` density factor. -/
theorem partition_eq_base_integral_toReal_density_smul :
    c.partition =
      ∫ x, ((ENNReal.ofReal (c.geom.volumeDensity x)).toReal : ℝ) •
        c.toMeasurePathIntegralModel.weight x ∂c.geom.baseMeasure := by
  unfold partition toMeasurePathIntegralModel CurvedMeasureDatum.volumeMeasure
  exact
    integral_withDensity_eq_integral_toReal_smul
      (μ := c.geom.baseMeasure)
      (f := fun x => ENNReal.ofReal (c.geom.volumeDensity x))
      (f_meas := c.geom.measurable_volumeDensity.ennreal_ofReal)
      (hf_lt_top := Filter.Eventually.of_forall (fun _ => by simp))
      (g := fun x => c.toMeasurePathIntegralModel.weight x)

/-- Since `ρ_g ≥ 0`, the `toReal ∘ ofReal` density factor is exactly `ρ_g`. -/
theorem density_toReal_ofReal_eq (x : α) :
    ((ENNReal.ofReal (c.geom.volumeDensity x)).toReal : ℝ) = c.geom.volumeDensity x :=
  ENNReal.toReal_ofReal (c.geom.volumeDensity_nonneg x)

/-- Curved partition over the base measure with explicit density factor `ρ_g`. -/
theorem partition_eq_base_integral_density_smul :
    c.partition =
      ∫ x, c.geom.volumeDensity x • c.toMeasurePathIntegralModel.weight x ∂c.geom.baseMeasure := by
  rw [c.partition_eq_base_integral_toReal_density_smul]
  congr with x
  simp [c.density_toReal_ofReal_eq x]

/-! ## Curvature and gauge operator contracts -/

/-- Curved-background operator data for scalar-curvature and gauge-source couplings. -/
structure CurvedOperatorStack (α : Type*) [MeasurableSpace α] where
  /-- Scalar curvature structure. -/
  scalarCurvature : α → ℝ
  /-- Measurability of scalar curvature. -/
  measurable_scalarCurvature : Measurable scalarCurvature
  /-- Gauge potential/source shift. -/
  gaugePotential : α → ℂ
  /-- Measurability of the gauge potential/source shift. -/
  measurable_gaugePotential : Measurable gaugePotential

/-- Imaginary-action coupling to scalar curvature: `S_I + ξ R`. -/
def curvatureCoupledActionIm (ops : CurvedOperatorStack α) (ξ : ℝ) (x : α) : ℝ :=
  c.actionIm x + ξ * ops.scalarCurvature x

/-- The curvature-coupled imaginary action is measurable. -/
theorem measurable_curvatureCoupledActionIm (ops : CurvedOperatorStack α) (ξ : ℝ) :
    Measurable (curvatureCoupledActionIm (c := c) ops ξ) := by
  unfold curvatureCoupledActionIm
  exact c.measurable_actionIm.add (measurable_const.mul ops.measurable_scalarCurvature)

/-- A lower bound on `S_I` sufficient to keep `S_I + ξR` nonnegative. -/
theorem curvatureCoupledActionIm_nonneg_of_lower_bound
    (ops : CurvedOperatorStack α) (ξ : ℝ)
    (h_lower : ∀ x, -(ξ * ops.scalarCurvature x) ≤ c.actionIm x) :
    ∀ x, 0 ≤ curvatureCoupledActionIm (c := c) ops ξ x := by
  intro x
  unfold curvatureCoupledActionIm
  linarith [h_lower x]

/-- Curvature-coupled curved model, with the same geometry and modified imaginary action. -/
def toCurvatureCoupledModel (ops : CurvedOperatorStack α) (ξ : ℝ)
    (h_nonneg : ∀ x, 0 ≤ curvatureCoupledActionIm (c := c) ops ξ x) :
    CurvedMeasurePathIntegralModel α where
  geom := c.geom
  hbar := c.hbar
  hbar_pos := c.hbar_pos
  actionRe := c.actionRe
  actionIm := curvatureCoupledActionIm (c := c) ops ξ
  measurable_actionRe := c.measurable_actionRe
  measurable_actionIm := measurable_curvatureCoupledActionIm (c := c) ops ξ
  actionIm_nonneg := h_nonneg

/-- Curvature coupling preserves the geometric measure datum. -/
theorem toCurvatureCoupledModel_geom
    (ops : CurvedOperatorStack α) (ξ : ℝ)
    (h_nonneg : ∀ x, 0 ≤ curvatureCoupledActionIm (c := c) ops ξ x) :
    (toCurvatureCoupledModel (c := c) ops ξ h_nonneg).geom = c.geom := rfl

/-- Gauge-shifted source `J + A`. -/
def gaugeShiftedSource (ops : CurvedOperatorStack α) (J : α → ℂ) : α → ℂ :=
  fun x => J x + ops.gaugePotential x

/-- Gauge-shifted sources are measurable when the original source is measurable. -/
theorem measurable_gaugeShiftedSource (ops : CurvedOperatorStack α)
    (J : α → ℂ) (hJ : Measurable J) :
    Measurable (gaugeShiftedSource ops J) :=
  hJ.add ops.measurable_gaugePotential

/-- Gauge-coupled curved partition `Z_g[J + A]`. -/
def gaugeCoupledPartition (ops : CurvedOperatorStack α) (J : α → ℂ) : ℂ :=
  c.sourceCoupledPartition (gaugeShiftedSource ops J)

/-- If the gauge potential vanishes, the gauge-coupled partition is the usual source partition. -/
theorem gaugeCoupledPartition_eq_sourceCoupled_of_zeroGauge
    (ops : CurvedOperatorStack α) (J : α → ℂ)
    (hA : ops.gaugePotential = fun _ => (0 : ℂ)) :
    gaugeCoupledPartition (c := c) ops J = c.sourceCoupledPartition J := by
  unfold gaugeCoupledPartition gaugeShiftedSource
  simp [hA]

end CurvedMeasurePathIntegralModel

end Physlib.QFT.PathIntegral

end
