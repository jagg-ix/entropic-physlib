/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Multiplication
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Continuum fields and maximal-domain pointwise operators

This module makes explicit the continuum functional-analytic carrier used by
the Lovelock--Rund variational formalization.

* Generic fields use Mathlib's `Lp U 2 μ`, so the field-value space `U` may be
  infinite dimensional.
* Complex scalar fields on `Space d` reuse Physlib's existing
  `SpaceDHilbertSpace d`.
* Pointwise coefficients act through the existing maximal-domain
  `SpaceDHilbertSpace.mulOperator`; dense-domain and almost-everywhere action
  theorems are inherited directly.

No new Hilbert-space or unbounded-operator implementation is introduced.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LovelockRund

open MeasureTheory
open QuantumMechanics

/-- Generic square-integrable continuum field with possibly
infinite-dimensional values. -/
abbrev ContinuumFieldSpace
    (X U : Type*) [MeasurableSpace X] [NormedAddCommGroup U]
    (μ : Measure X) :=
  Lp U 2 μ

/-- Membership predicate for a representative of a continuum `L²` field. -/
def MemContinuumField
    {X U : Type*} [MeasurableSpace X] [NormedAddCommGroup U]
    (μ : Measure X) (f : X → U) : Prop :=
  MemLp f 2 μ

/-- Every element of the existing `Lp` carrier has a square-integrable
representative. -/
theorem continuumField_memLp
    {X U : Type*} [MeasurableSpace X] [NormedAddCommGroup U]
    {μ : Measure X} (f : ContinuumFieldSpace X U μ) :
    MemContinuumField μ (f : X → U) :=
  Lp.memLp f

/-- The scalar spatial continuum Hilbert space already used by Physlib. -/
abbrev ScalarContinuumHilbertSpace (d : ℕ) :=
  SpaceDHilbertSpace d

/-- Maximal-domain pointwise multiplication by a complex coefficient. -/
def pointwiseFieldOperator {d : ℕ} (a : Space d → ℂ) :
    ScalarContinuumHilbertSpace d →ₗ.[ℂ] ScalarContinuumHilbertSpace d :=
  SpaceDHilbertSpace.mulOperator volume a

/-- Almost-everywhere strongly measurable coefficients produce densely
defined pointwise operators. -/
theorem pointwiseFieldOperator_hasDenseDomain
    {d : ℕ} {a : Space d → ℂ}
    (ha : AEStronglyMeasurable a) :
    (pointwiseFieldOperator a).HasDenseDomain := by
  simpa [pointwiseFieldOperator] using
    SpaceDHilbertSpace.mulOperator_hasDenseDomain ha

/-- The maximal-domain operator acts by pointwise multiplication almost
everywhere. -/
theorem pointwiseFieldOperator_apply_ae
    {d : ℕ} {a : Space d → ℂ}
    (ψ : (pointwiseFieldOperator a).domain) :
    pointwiseFieldOperator a ψ =ᵐ[volume] a • ψ := by
  simpa [pointwiseFieldOperator] using
    SpaceDHilbertSpace.mulOperator_apply_ae (f := a) ψ

/-- Pointwise Euler--Lagrange residual as a maximal-domain multiplication
operator on the continuum Hilbert space. -/
def pointwiseEulerLagrangeOperator {d : ℕ}
    (eulerLagrange : Space d → ℂ) :
    ScalarContinuumHilbertSpace d →ₗ.[ℂ] ScalarContinuumHilbertSpace d :=
  pointwiseFieldOperator eulerLagrange

/-- A measurable pointwise Euler--Lagrange residual defines a densely defined
operator. -/
theorem pointwiseEulerLagrangeOperator_hasDenseDomain
    {d : ℕ} {eulerLagrange : Space d → ℂ}
    (hEL : AEStronglyMeasurable eulerLagrange) :
    (pointwiseEulerLagrangeOperator eulerLagrange).HasDenseDomain :=
  pointwiseFieldOperator_hasDenseDomain hEL

end Physlib.Mathematics.LovelockRund

end
