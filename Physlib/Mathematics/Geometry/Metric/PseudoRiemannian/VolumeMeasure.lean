/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Defs
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Canonical Lorentzian measure from a pseudo-Riemannian metric

This file constructs the metric volume measure instead of accepting a
curved-space density as external data.  On a finite-dimensional smooth
manifold modelled on a real inner-product space, the metric is pulled back
through each chart, its density is `sqrt |det g|`, and the resulting
Euclidean measures are pushed to the manifold and glued by a smooth
partition of unity.

The determinant covariance theorem
`pseudoVolumeDensity_comp` is the load-bearing change-of-coordinates law:
the density acquires exactly the absolute Jacobian.  The construction uses
the standard orthonormal basis and Mathlib's canonical Euclidean Haar
measure, so it introduces neither a coordinate volume weight nor a supplied
background measure.  The global representative fixes one smooth partition
subordinate to the chart cover; its local density is the canonical
pseudo-Riemannian density.

The absolute determinant is valid in every nondegenerate signature.  On the
Lorentzian branch `det g < 0` it reduces to the familiar `sqrt (-det g)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Bundle Module MeasureTheory Set
open scoped Manifold

namespace PseudoRiemannianMetric

universe v

/-- The absolute pseudo-Riemannian density represented in a basis. -/
def pseudoVolumeDensity {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (b : Basis ι ℝ V) : ℝ :=
  Real.sqrt |Q.discr b|

lemma pseudoVolumeDensity_nonneg {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (b : Basis ι ℝ V) :
    0 ≤ pseudoVolumeDensity Q b :=
  Real.sqrt_nonneg _

/-- **Metric-density covariance.** Pulling a quadratic form through a
linear coordinate change multiplies `sqrt |det g|` by the absolute
Jacobian. -/
theorem pseudoVolumeDensity_comp
    {ι V W : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (b : Basis ι ℝ V) (b' : Basis ι ℝ W)
    (Q : QuadraticForm ℝ W) (f : V →ₗ[ℝ] W) :
    pseudoVolumeDensity (Q.comp f) b =
      |(f.toMatrix b b').det| * pseudoVolumeDensity Q b' := by
  unfold pseudoVolumeDensity
  rw [QuadraticForm.discr_comp b' Q f, abs_mul, abs_mul, ← pow_two]
  rw [Real.sqrt_mul (sq_nonneg |(f.toMatrix b b').det|)]
  rw [Real.sqrt_sq_eq_abs, abs_abs]

/-- The absolute determinant density of a coordinate metric matrix. -/
def absoluteDeterminantDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) : ℝ :=
  Real.sqrt |G.det|

lemma absoluteDeterminantDensity_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) :
    0 ≤ absoluteDeterminantDensity G :=
  Real.sqrt_nonneg _

/-- On the Lorentzian determinant branch the signature-independent
`sqrt |det g|` density is exactly the conventional `sqrt (-det g)`. -/
theorem absoluteDeterminantDensity_eq_sqrt_neg_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.det < 0) :
    absoluteDeterminantDensity G = Real.sqrt (-G.det) := by
  unfold absoluteDeterminantDensity
  rw [abs_of_neg hG]

variable {n : WithTop ℕ∞}
variable {E M : Type v}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace M]
variable [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M]
variable [IsManifold 𝓘(ℝ, E) (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x)]

/-- The inverse of a chart, with its source and target restrictions encoded
in the subtype. -/
def chartInverse (a : M) :
    (chartAt E a).target → M :=
  fun y => ((chartAt E a).toHomeomorphSourceTarget.symm y : M)

lemma chartInverse_continuous (a : M) :
    Continuous (chartInverse (E := E) a) := by
  exact continuous_subtype_val.comp
    (chartAt E a).toHomeomorphSourceTarget.symm.continuous

lemma chartInverse_measurable (a : M) :
    Measurable (chartInverse (E := E) a) :=
  (chartInverse_continuous (E := E) a).measurable

/-- The metric quadratic form pulled from the tangent space to the model
space by the derivative of a chart inverse. -/
def chartMetricQuadraticForm
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E)) (a : M)
    (y : (chartAt E a).target) : QuadraticForm ℝ E :=
  (g.toQuadraticForm (chartInverse (E := E) a y)).comp
    (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E a).symm
      (chartAt E a).target y).toLinearMap

/-- The canonical local pseudo-Riemannian density in a chart. -/
def chartMetricDensity
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E)) (a : M)
    (y : (chartAt E a).target) : ℝ :=
  pseudoVolumeDensity (chartMetricQuadraticForm g a y)
    (stdOrthonormalBasis ℝ E).toBasis

/-- The matrix of the pulled-back chart metric after transporting the
canonical finite-dimensional basis to a chosen finite coordinate index. -/
def chartMetricMatrix {i : Type*}
    (e : Fin (Module.finrank ℝ E) ≃ i)
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E)) (a : M)
    (y : (chartAt E a).target) : Matrix i i ℝ :=
  Matrix.reindex e e <|
    (chartMetricQuadraticForm g a y).toMatrix
      (stdOrthonormalBasis ℝ E).toBasis

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M] in
/-- Reindexing the canonical chart matrix does not alter the metric density. -/
lemma chartMetricDensity_eq_absoluteDeterminantDensity_chartMetricMatrix
    {i : Type*} [Fintype i] [DecidableEq i]
    (e : Fin (Module.finrank ℝ E) ≃ i)
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E)) (a : M)
    (y : (chartAt E a).target) :
    chartMetricDensity g a y =
      absoluteDeterminantDensity (chartMetricMatrix e g a y) := by
  unfold chartMetricDensity pseudoVolumeDensity QuadraticForm.discr
    absoluteDeterminantDensity chartMetricMatrix
  rw [Matrix.det_reindex_self]

lemma chartMetricDensity_nonneg
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E)) (a : M)
    (y : (chartAt E a).target) :
    0 ≤ chartMetricDensity g a y :=
  pseudoVolumeDensity_nonneg _ _

/-- The Euclidean chart measure weighted only by one partition-of-unity
coefficient. The metric determinant remains in the integrand. -/
def chartPartitionMeasure
    (rho : SmoothPartitionOfUnity M 𝓘(ℝ, E) M univ) (a : M) :
    Measure ((chartAt E a).target) :=
  (Measure.comap Subtype.val (volume : Measure E)).withDensity
    (fun y => ENNReal.ofReal (rho a (chartInverse (E := E) a y)))

/-- A smooth chart partition coefficient gives a measurable density on the
coordinate target. -/
lemma chartPartitionDensity_measurable
    (rho : SmoothPartitionOfUnity M 𝓘(ℝ, E) M univ) (a : M) :
    Measurable fun y : (chartAt E a).target =>
      ENNReal.ofReal (rho a (chartInverse (E := E) a y)) := by
  exact ENNReal.measurable_ofReal.comp <|
    ((rho a).contMDiff.continuous.comp
      (chartInverse_continuous (E := E) a)).measurable

/-- One chart's weighted metric measure on its coordinate target. -/
def chartWeightedMeasure
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (ρ : SmoothPartitionOfUnity M 𝓘(ℝ, E) M univ) (a : M) :
    Measure ((chartAt E a).target) :=
  (Measure.comap Subtype.val (volume : Measure E)).withDensity
    (fun y => ENNReal.ofReal
      (ρ a (chartInverse (E := E) a y) * chartMetricDensity g a y))

/-- The weighted metric chart measure factors into the partition-weighted
Euclidean measure followed by the canonical determinant density. -/
lemma chartWeightedMeasure_eq_chartPartitionMeasure_withDensity
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (rho : SmoothPartitionOfUnity M 𝓘(ℝ, E) M univ) (a : M)
    (hmetric : Measurable fun y : (chartAt E a).target =>
      ENNReal.ofReal (chartMetricDensity g a y)) :
    chartWeightedMeasure g rho a =
      (chartPartitionMeasure (E := E) rho a).withDensity
        (fun y => ENNReal.ofReal (chartMetricDensity g a y)) := by
  unfold chartWeightedMeasure chartPartitionMeasure
  rw [← withDensity_mul
    (Measure.comap Subtype.val (volume : Measure E))
    (chartPartitionDensity_measurable (E := E) rho a) hmetric]
  congr 1
  funext y
  exact ENNReal.ofReal_mul (rho.nonneg a _)

/-- Push one chart's weighted metric measure to the manifold. -/
def chartContribution
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (ρ : SmoothPartitionOfUnity M 𝓘(ℝ, E) M univ) (a : M) :
    Measure M :=
  Measure.map (chartInverse (E := E) a) (chartWeightedMeasure g ρ a)

/-- Glue the metric chart measures with a supplied smooth partition. -/
def lorentzianVolumeMeasureUsing
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E))
    (ρ : SmoothPartitionOfUnity M 𝓘(ℝ, E) M univ) : Measure M :=
  Measure.sum (fun a : M => chartContribution g ρ a)

variable [T2Space M] [SigmaCompactSpace M]

/-- A fixed smooth partition subordinate to the canonical chart cover. -/
def canonicalChartPartition :
    SmoothPartitionOfUnity M 𝓘(ℝ, E) M univ :=
  Classical.choose
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source 𝓘(ℝ, E) M)

lemma canonicalChartPartition_isSubordinate :
    (canonicalChartPartition (E := E) (M := M) :
      SmoothPartitionOfUnity M 𝓘(ℝ, E) M univ).IsSubordinate
        (fun a => (chartAt E a).source) :=
  Classical.choose_spec
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source 𝓘(ℝ, E) M)

/-- **Canonical Lorentzian measure built from the metric.** Each chart
contributes Euclidean volume weighted by `sqrt |det g|`; a fixed smooth
subordinate partition glues the compatible local densities. -/
def lorentzianVolumeMeasure
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E)) : Measure M :=
  lorentzianVolumeMeasureUsing g (canonicalChartPartition (E := E) (M := M))

/-- The fixed smooth partition used by the canonical construction sums to
one pointwise. -/
lemma canonicalChartPartition_sum_eq_one (x : M) :
    ∑ᶠ a : M, canonicalChartPartition (E := E) (M := M) a x = 1 :=
  (canonicalChartPartition (E := E) (M := M)).sum_eq_one (mem_univ x)

/-! ## B. Atlas integral formula -/

/-- Integration against the canonical pseudo-Riemannian measure is the
summable gluing of its coordinate-chart integrals. This is the integral
interface supplied by the measure construction itself, rather than an
assumed global density representation. -/
lemma integral_lorentzianVolumeMeasure_eq_tsum_chartWeightedMeasure
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E)) (f : M → F)
    (hf : Integrable f (lorentzianVolumeMeasure g)) :
    (∫ x, f x ∂(lorentzianVolumeMeasure g)) =
      ∑' a : M, ∫ y, f (chartInverse (E := E) a y)
        ∂(chartWeightedMeasure g
          (canonicalChartPartition (E := E) (M := M)) a) := by
  have hchart (a : M) :
      AEStronglyMeasurable f
        (chartContribution g
          (canonicalChartPartition (E := E) (M := M)) a) :=
    hf.1.mono_measure (Measure.le_sum (fun a : M ↦
      chartContribution g
        (canonicalChartPartition (E := E) (M := M)) a) a)
  unfold lorentzianVolumeMeasure lorentzianVolumeMeasureUsing
  rw [integral_sum_measure hf]
  apply tsum_congr
  intro a
  exact integral_map
    (chartInverse_measurable (E := E) a).aemeasurable (hchart a)

/-! ## C. Finite atlas support on compact manifolds -/

variable [CompactSpace M]

/-- The finite set of canonical partition functions with nonempty support on
a compact manifold. -/
def canonicalActiveCharts : Finset M :=
  (LocallyFinite.finite_nonempty_of_compact
    (canonicalChartPartition (E := E) (M := M)).locallyFinite).toFinset

lemma mem_canonicalActiveCharts_iff (a : M) :
    a ∈ canonicalActiveCharts (E := E) (M := M) ↔
      (Function.support
        (canonicalChartPartition (E := E) (M := M) a)).Nonempty :=
  Set.Finite.mem_toFinset _

/-- A chart outside the finite active set contributes the zero coordinate
measure to the canonical pseudo-Riemannian volume construction. -/
lemma chartWeightedMeasure_eq_zero_of_not_mem_canonicalActiveCharts
    (g : PseudoRiemannianMetric E E M n 𝓘(ℝ, E)) (a : M)
    (ha : a ∉ canonicalActiveCharts (E := E) (M := M)) :
    chartWeightedMeasure g
      (canonicalChartPartition (E := E) (M := M)) a = 0 := by
  have hempty :
      Function.support
        (canonicalChartPartition (E := E) (M := M) a) = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp
      (mt (mem_canonicalActiveCharts_iff (E := E) (M := M) a).mpr ha)
  have hzero : ∀ x : M,
      canonicalChartPartition (E := E) (M := M) a x = 0 := by
    intro x
    have hx : x ∉ Function.support
        (canonicalChartPartition (E := E) (M := M) a) := by
      rw [hempty]
      simp
    simpa [Function.mem_support] using hx
  simp [chartWeightedMeasure, hzero]

end PseudoRiemannianMetric
