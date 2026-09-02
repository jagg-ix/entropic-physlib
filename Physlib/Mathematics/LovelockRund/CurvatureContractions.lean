/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.LovelockRund.SubmanifoldGeometry
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Infinite curvature contractions and the Einstein tensor

This module formalizes the Ricci, scalar-curvature, and Einstein-tensor
contractions used in Lovelock--Rund Section 7.3.

The coordinate index type is arbitrary. Infinite contractions use `tsum`;
finite-index compatibility theorems recover the standard finite sums.
Convergence is therefore carried by the usual `Summable` conditions of the
ambient `tsum` API rather than hidden behind a finite-dimensional assumption.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LovelockRund

/-- Inverse metric components. -/
abbrev InverseMetricComponents (X ι : Type*) :=
  X → ι → ι → ℝ

/-- Infinite Ricci contraction `R_ij = Σₖ R_kikj`. -/
def infiniteRicci {X ι : Type*}
    (R : CurvatureComponents X ι) : X → ι → ι → ℝ :=
  fun x i j => ∑' k, R x k i k j

/-- Finite Ricci contraction. -/
def finiteRicci {X ι : Type*} [Fintype ι]
    (R : CurvatureComponents X ι) : X → ι → ι → ℝ :=
  fun x i j => ∑ k, R x k i k j

/-- Infinite Ricci contraction agrees with the finite contraction on finite
index types. -/
theorem infiniteRicci_eq_finite
    {X ι : Type*} [Fintype ι]
    (R : CurvatureComponents X ι) :
    infiniteRicci R = finiteRicci R := by
  funext x i j
  simp [infiniteRicci, finiteRicci]

/-- Infinite scalar curvature `R = Σᵢⱼ gⁱʲ Rᵢⱼ`. -/
def infiniteScalarCurvature {X ι : Type*}
    (gInv : InverseMetricComponents X ι)
    (ricci : X → ι → ι → ℝ) : X → ℝ :=
  fun x => ∑' i, ∑' j, gInv x i j * ricci x i j

/-- Finite scalar curvature. -/
def finiteScalarCurvature {X ι : Type*} [Fintype ι]
    (gInv : InverseMetricComponents X ι)
    (ricci : X → ι → ι → ℝ) : X → ℝ :=
  fun x => ∑ i, ∑ j, gInv x i j * ricci x i j

/-- Infinite scalar curvature agrees with the finite contraction on finite
index types. -/
theorem infiniteScalarCurvature_eq_finite
    {X ι : Type*} [Fintype ι]
    (gInv : InverseMetricComponents X ι)
    (ricci : X → ι → ι → ℝ) :
    infiniteScalarCurvature gInv ricci =
      finiteScalarCurvature gInv ricci := by
  funext x
  simp [infiniteScalarCurvature, finiteScalarCurvature]

/-- Infinite scalar curvature constructed directly from a Riemann tensor. -/
def scalarCurvatureOfRiemann {X ι : Type*}
    (gInv : InverseMetricComponents X ι)
    (R : CurvatureComponents X ι) : X → ℝ :=
  infiniteScalarCurvature gInv (infiniteRicci R)

/-- Einstein tensor components
`G_ij = R_ij - (1/2) g_ij R`. -/
def einsteinTensorComponents {X ι : Type*}
    (metric ricci : X → ι → ι → ℝ)
    (scalar : X → ℝ) : X → ι → ι → ℝ :=
  fun x i j => ricci x i j - (1 / 2 : ℝ) * metric x i j * scalar x

/-- Pointwise expansion of the Einstein tensor. -/
theorem einsteinTensorComponents_apply
    {X ι : Type*}
    (metric ricci : X → ι → ι → ℝ)
    (scalar : X → ℝ) (x : X) (i j : ι) :
    einsteinTensorComponents metric ricci scalar x i j =
      ricci x i j - (1 / 2 : ℝ) * metric x i j * scalar x :=
  rfl

/-- If Ricci and scalar curvature both vanish, the Einstein tensor vanishes. -/
theorem einsteinTensorComponents_eq_zero
    {X ι : Type*}
    (metric ricci : X → ι → ι → ℝ)
    (scalar : X → ℝ)
    (hRicci : ricci = 0) (hScalar : scalar = 0) :
    einsteinTensorComponents metric ricci scalar = 0 := by
  funext x i j
  simp [einsteinTensorComponents, hRicci, hScalar]

/-- Einstein-space residual `Ric_ij - λ g_ij`. -/
def einsteinSpaceResidual {X ι : Type*}
    (metric ricci : X → ι → ι → ℝ)
    (lambda : X → ℝ) : X → ι → ι → ℝ :=
  fun x i j => ricci x i j - lambda x * metric x i j

/-- Vanishing Einstein-space residual is exactly proportionality of Ricci and
the metric. -/
theorem einsteinSpaceResidual_eq_zero_iff
    {X ι : Type*}
    (metric ricci : X → ι → ι → ℝ)
    (lambda : X → ℝ) :
    einsteinSpaceResidual metric ricci lambda = 0 ↔
      ∀ x i j, ricci x i j = lambda x * metric x i j := by
  constructor
  · intro h x i j
    have hx := congrFun (congrFun (congrFun h x) i) j
    simpa [einsteinSpaceResidual, sub_eq_zero] using hx
  · intro h
    funext x i j
    simp [einsteinSpaceResidual, h x i j]

/-- Constant sectional-curvature form
`R_ijkl = K (g_ik g_jl - g_il g_jk)`. -/
def IsConstantSectionalCurvature {X ι : Type*}
    (metric : X → ι → ι → ℝ)
    (R : CurvatureComponents X ι)
    (K : X → ℝ) : Prop :=
  ∀ x i j k l,
    R x i j k l = K x *
      (metric x i k * metric x j l -
        metric x i l * metric x j k)

/-- Constant-sectional-curvature tensors are skew in the last two indices. -/
theorem constantSectionalCurvature_skew_last
    {X ι : Type*}
    (metric : X → ι → ι → ℝ)
    (R : CurvatureComponents X ι)
    (K : X → ℝ)
    (hK : IsConstantSectionalCurvature metric R K) :
    ∀ x i j k l, R x i j l k = -R x i j k l := by
  intro x i j k l
  rw [hK x i j l k, hK x i j k l]
  ring

/-- Zero sectional curvature gives a zero curvature tensor. -/
theorem constantSectionalCurvature_zero
    {X ι : Type*}
    (metric : X → ι → ι → ℝ)
    (R : CurvatureComponents X ι)
    (hK : IsConstantSectionalCurvature metric R 0) :
    R = 0 := by
  funext x i j k l
  simpa using hK x i j k l

end Physlib.Mathematics.LovelockRund

end
