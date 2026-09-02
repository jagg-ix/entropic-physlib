/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.PiTensorProduct
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Pointwise tensor fields with arbitrary coordinate index

This module formalizes the coordinate algebra used in Lovelock--Rund Chapters
2--4 without imposing a finite coordinate index type.

A tensor field is represented pointwise by its component function. Contraction
and covariant differentiation use `tsum` over an arbitrary index type. When the
index type is finite, the definitions reduce to the ordinary finite sums.

The tensor-product foundations are inherited from Mathlib and
`Physlib.PiTensorProduct`; this file adds only the component bridges needed by
the book's formulas.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LovelockRund

/-- Pointwise contravariant vector field components. -/
abbrev ContravariantVectorField (X ι : Type*) := X → ι → ℝ

/-- Pointwise covariant vector field components. -/
abbrev CovariantVectorField (X ι : Type*) := X → ι → ℝ

/-- Pointwise tensor field with two covariant indices. -/
abbrev CovariantTensor2Field (X ι : Type*) := X → ι → ι → ℝ

/-- Pointwise tensor field with two contravariant indices. -/
abbrev ContravariantTensor2Field (X ι : Type*) := X → ι → ι → ℝ

/-- Infinite-index contraction of one covector with one vector. -/
def infiniteVectorContraction {X ι : Type*}
    (A : CovariantVectorField X ι)
    (V : ContravariantVectorField X ι) (x : X) : ℝ :=
  ∑' i, A x i * V x i

/-- Finite-index contraction of one covector with one vector. -/
def finiteVectorContraction {X ι : Type*} [Fintype ι]
    (A : CovariantVectorField X ι)
    (V : ContravariantVectorField X ι) (x : X) : ℝ :=
  ∑ i, A x i * V x i

/-- On finite index types, infinite contraction agrees with finite
contraction. -/
theorem infiniteVectorContraction_eq_finite
    {X ι : Type*} [Fintype ι]
    (A : CovariantVectorField X ι)
    (V : ContravariantVectorField X ι) (x : X) :
    infiniteVectorContraction A V x = finiteVectorContraction A V x := by
  simp [infiniteVectorContraction, finiteVectorContraction]

/-- Double contraction of a covariant and a contravariant rank-two tensor. -/
def infiniteTensor2Contraction {X ι : Type*}
    (A : CovariantTensor2Field X ι)
    (B : ContravariantTensor2Field X ι) (x : X) : ℝ :=
  ∑' i, ∑' j, A x i j * B x i j

/-- Finite counterpart of the double contraction. -/
def finiteTensor2Contraction {X ι : Type*} [Fintype ι]
    (A : CovariantTensor2Field X ι)
    (B : ContravariantTensor2Field X ι) (x : X) : ℝ :=
  ∑ i, ∑ j, A x i j * B x i j

/-- Finite compatibility of the double contraction. -/
theorem infiniteTensor2Contraction_eq_finite
    {X ι : Type*} [Fintype ι]
    (A : CovariantTensor2Field X ι)
    (B : ContravariantTensor2Field X ι) (x : X) :
    infiniteTensor2Contraction A B x =
      finiteTensor2Contraction A B x := by
  simp [infiniteTensor2Contraction, finiteTensor2Contraction]

/-- Pointwise symmetry of a rank-two tensor field. -/
def IsSymmetricTensor2 {X ι : Type*}
    (A : X → ι → ι → ℝ) : Prop :=
  ∀ x i j, A x i j = A x j i

/-- Pointwise skew symmetry of a rank-two tensor field. -/
def IsSkewTensor2 {X ι : Type*}
    (A : X → ι → ι → ℝ) : Prop :=
  ∀ x i j, A x i j = -A x j i

/-- Connection coefficients `Γⁱⱼₖ` over an arbitrary coordinate index type. -/
abbrev ConnectionCoefficients (X ι : Type*) :=
  X → ι → ι → ι → ℝ

/-- Data supplying pointwise partial derivatives of vector and covector
components. It is deliberately independent of a particular coordinate-chart
implementation. -/
structure ComponentDerivativeData (X ι : Type*) where
  /-- Partial derivative `∂ₖ Vⁱ`. -/
  partialVector : ContravariantVectorField X ι → X → ι → ι → ℝ
  /-- Partial derivative `∂ₖ Aᵢ`. -/
  partialCovector : CovariantVectorField X ι → X → ι → ι → ℝ

/-- Covariant derivative of a contravariant vector,
`Vⁱ_;k = ∂ₖVⁱ + Γⁱ_jk Vʲ`. -/
def covariantDerivativeVector {X ι : Type*}
    (D : ComponentDerivativeData X ι)
    (Γ : ConnectionCoefficients X ι)
    (V : ContravariantVectorField X ι)
    (x : X) (i k : ι) : ℝ :=
  D.partialVector V x i k +
    ∑' j, Γ x i j k * V x j

/-- Covariant derivative of a covector,
`A_i;k = ∂ₖA_i - Γʲ_ik A_j`. -/
def covariantDerivativeCovector {X ι : Type*}
    (D : ComponentDerivativeData X ι)
    (Γ : ConnectionCoefficients X ι)
    (A : CovariantVectorField X ι)
    (x : X) (i k : ι) : ℝ :=
  D.partialCovector A x i k -
    ∑' j, Γ x j i k * A x j

/-- Finite-index version of the vector covariant derivative. -/
def finiteCovariantDerivativeVector {X ι : Type*} [Fintype ι]
    (D : ComponentDerivativeData X ι)
    (Γ : ConnectionCoefficients X ι)
    (V : ContravariantVectorField X ι)
    (x : X) (i k : ι) : ℝ :=
  D.partialVector V x i k +
    ∑ j, Γ x i j k * V x j

/-- Finite-index version of the covector covariant derivative. -/
def finiteCovariantDerivativeCovector {X ι : Type*} [Fintype ι]
    (D : ComponentDerivativeData X ι)
    (Γ : ConnectionCoefficients X ι)
    (A : CovariantVectorField X ι)
    (x : X) (i k : ι) : ℝ :=
  D.partialCovector A x i k -
    ∑ j, Γ x j i k * A x j

/-- Finite compatibility of the vector covariant derivative. -/
theorem covariantDerivativeVector_eq_finite
    {X ι : Type*} [Fintype ι]
    (D : ComponentDerivativeData X ι)
    (Γ : ConnectionCoefficients X ι)
    (V : ContravariantVectorField X ι)
    (x : X) (i k : ι) :
    covariantDerivativeVector D Γ V x i k =
      finiteCovariantDerivativeVector D Γ V x i k := by
  simp [covariantDerivativeVector, finiteCovariantDerivativeVector]

/-- Finite compatibility of the covector covariant derivative. -/
theorem covariantDerivativeCovector_eq_finite
    {X ι : Type*} [Fintype ι]
    (D : ComponentDerivativeData X ι)
    (Γ : ConnectionCoefficients X ι)
    (A : CovariantVectorField X ι)
    (x : X) (i k : ι) :
    covariantDerivativeCovector D Γ A x i k =
      finiteCovariantDerivativeCovector D Γ A x i k := by
  simp [covariantDerivativeCovector, finiteCovariantDerivativeCovector]

/-- Parallel vector field equation in arbitrary coordinates. -/
def IsParallelVectorField {X ι : Type*}
    (D : ComponentDerivativeData X ι)
    (Γ : ConnectionCoefficients X ι)
    (V : ContravariantVectorField X ι) : Prop :=
  ∀ x i k, covariantDerivativeVector D Γ V x i k = 0

end Physlib.Mathematics.LovelockRund

end
