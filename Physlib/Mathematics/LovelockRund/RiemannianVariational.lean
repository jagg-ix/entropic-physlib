/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.Geometry.Metric.Riemannian.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Metric energy and infinite-index geodesic equations

This module formalizes the central metric and geodesic constructions of
Lovelock--Rund Chapter 7.

There are two complementary layers:

1. `PointwiseMetric` works on an arbitrary normed vector space `E`, with no
   finite-dimensional assumption. Its integrated energy therefore applies to
   continuum and infinite-dimensional field configurations.
2. `infiniteGeodesicResidual` uses iterated `tsum` over an arbitrary coordinate
   index type. When the index type is finite, it reduces definitionally to the
   ordinary finite Christoffel-symbol equation.

A final section connects the generic energy density to Physlib's existing
manifold `RiemannianMetric` structure.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LovelockRund

open MeasureTheory

universe u

variable {X E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A pointwise bilinear metric on a family of copies of `E`. The vector space
`E` may be infinite dimensional. -/
abbrev PointwiseMetric (X E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  X → E →L[ℝ] E →L[ℝ] ℝ

/-- Kinetic or metric energy density `1/2 g(v,v)`. -/
def metricEnergyDensity
    (g : PointwiseMetric X E) (x : X) (v : E) : ℝ :=
  (1 / 2 : ℝ) * g x v v

/-- Pointwise nonnegativity of a metric family. -/
def IsNonnegativeMetric (g : PointwiseMetric X E) : Prop :=
  ∀ x v, 0 ≤ g x v v

/-- A nonnegative pointwise metric has nonnegative energy density. -/
theorem metricEnergyDensity_nonneg
    (g : PointwiseMetric X E) (hg : IsNonnegativeMetric g)
    (x : X) (v : E) :
    0 ≤ metricEnergyDensity g x v := by
  unfold metricEnergyDensity
  exact mul_nonneg (by norm_num) (hg x v)

section ContinuumEnergy

variable [MeasurableSpace X] {μ : Measure X}

/-- Integrated metric energy of a continuum vector field. -/
def continuumMetricEnergy
    (g : PointwiseMetric X E) (v : X → E) (μ : Measure X) : ℝ :=
  ∫ x, metricEnergyDensity g x (v x) ∂μ

/-- The integrated metric energy is nonnegative whenever the metric is
pointwise nonnegative. -/
theorem continuumMetricEnergy_nonneg
    (g : PointwiseMetric X E) (v : X → E) (μ : Measure X)
    (hg : IsNonnegativeMetric g) :
    0 ≤ continuumMetricEnergy g v μ := by
  unfold continuumMetricEnergy
  apply integral_nonneg
  intro x
  exact metricEnergyDensity_nonneg g hg x (v x)

end ContinuumEnergy

/-! ## Arbitrary and infinite coordinate-index geodesics -/

/-- Christoffel connection term with an arbitrary coordinate index type. -/
def infiniteConnectionTerm {ι : Type*}
    (Γ : ι → ι → ι → ℝ) (velocity : ι → ℝ) (i : ι) : ℝ :=
  ∑' j, ∑' k, Γ i j k * velocity j * velocity k

/-- Infinite-index coordinate geodesic residual
`aⁱ + Σⱼ Σₖ Γⁱⱼₖ vʲ vᵏ`. -/
def infiniteGeodesicResidual {ι : Type*}
    (Γ : ι → ι → ι → ℝ)
    (acceleration velocity : ι → ℝ) : ι → ℝ :=
  fun i => acceleration i + infiniteConnectionTerm Γ velocity i

/-- A curve is an affine geodesic when its coordinate residual vanishes. -/
def IsInfiniteGeodesic {ι : Type*}
    (Γ : ι → ι → ι → ℝ)
    (acceleration velocity : ι → ℝ) : Prop :=
  infiniteGeodesicResidual Γ acceleration velocity = 0

/-- For a flat connection, the geodesic equation is zero acceleration. -/
theorem infiniteGeodesicResidual_zero_connection {ι : Type*}
    (acceleration velocity : ι → ℝ) :
    infiniteGeodesicResidual (fun _ _ _ => 0) acceleration velocity =
      acceleration := by
  funext i
  simp [infiniteGeodesicResidual, infiniteConnectionTerm]

/-- Finite-index Christoffel-symbol geodesic residual. -/
def finiteGeodesicResidual {ι : Type*} [Fintype ι]
    (Γ : ι → ι → ι → ℝ)
    (acceleration velocity : ι → ℝ) : ι → ℝ :=
  fun i => acceleration i +
    ∑ j, ∑ k, Γ i j k * velocity j * velocity k

/-- On a finite coordinate index type, the infinite `tsum` formulation reduces
to the ordinary finite sum. -/
theorem infiniteGeodesicResidual_eq_finite
    {ι : Type*} [Fintype ι]
    (Γ : ι → ι → ι → ℝ)
    (acceleration velocity : ι → ℝ) :
    infiniteGeodesicResidual Γ acceleration velocity =
      finiteGeodesicResidual Γ acceleration velocity := by
  funext i
  simp [infiniteGeodesicResidual, infiniteConnectionTerm,
    finiteGeodesicResidual]

/-- A sufficient summability package for the infinite Christoffel term. -/
def IsSummableConnectionAlong {ι : Type*}
    (Γ : ι → ι → ι → ℝ) (velocity : ι → ℝ) : Prop :=
  ∀ i j, Summable fun k => Γ i j k * velocity j * velocity k

/-- Under nested summability, the connection term is represented by the
corresponding iterated infinite sum without any finite-dimensional truncation. -/
theorem infiniteConnectionTerm_eq_tsum {ι : Type*}
    (Γ : ι → ι → ι → ℝ) (velocity : ι → ℝ)
    (_hΓ : IsSummableConnectionAlong Γ velocity) (i : ι) :
    infiniteConnectionTerm Γ velocity i =
      ∑' j, ∑' k, Γ i j k * velocity j * velocity k :=
  rfl

/-! ## Bridge to the existing manifold Riemannian metric -/

section RiemannianMetric

open Bundle Set Finset Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle LinearMap Dual
open PseudoRiemannianMetric InnerProductSpace

variable {Eₘ : Type*} [NormedAddCommGroup Eₘ] [NormedSpace ℝ Eₘ]
variable {H M : Type u} [TopologicalSpace H] [TopologicalSpace M]
variable [ChartedSpace H M] [ChartedSpace H Eₘ]
variable {I : ModelWithCorners ℝ Eₘ H} {n : ℕ∞}
variable [IsManifold I (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

/-- Metric energy density induced by an existing Physlib Riemannian metric. -/
def riemannianMetricEnergyDensity
    (g : PseudoRiemannianMetric.RiemannianMetric I n M)
    (x : M) (v : TangentSpace I x) : ℝ :=
  (1 / 2 : ℝ) * g.inner x v v

/-- Riemannian metric energy is nonnegative. -/
theorem riemannianMetricEnergyDensity_nonneg
    (g : PseudoRiemannianMetric.RiemannianMetric I n M)
    (x : M) (v : TangentSpace I x) :
    0 ≤ riemannianMetricEnergyDensity g x v := by
  by_cases hv : v = 0
  · subst v
    simp [riemannianMetricEnergyDensity]
  · have hpos :=
      PseudoRiemannianMetric.RiemannianMetric.pos_def g x v hv
    unfold riemannianMetricEnergyDensity
    positivity

/-- The metric energy vanishes only for the zero tangent vector. -/
theorem riemannianMetricEnergyDensity_eq_zero_iff
    (g : PseudoRiemannianMetric.RiemannianMetric I n M)
    (x : M) (v : TangentSpace I x) :
    riemannianMetricEnergyDensity g x v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    have hpos :=
      PseudoRiemannianMetric.RiemannianMetric.pos_def g x v hv
    unfold riemannianMetricEnergyDensity at h
    change (1 / 2 : ℝ) * g.val x v v = 0 at h
    nlinarith
  · rintro rfl
    simp [riemannianMetricEnergyDensity]

end RiemannianMetric

end Physlib.Mathematics.LovelockRund

end
