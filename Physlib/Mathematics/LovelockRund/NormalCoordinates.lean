/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.LovelockRund.RiemannianVariational
public import Physlib.Mathematics.LovelockRund.TensorFields

/-!
# Normal coordinates and curvature at a point

This module formalizes the normal-coordinate consequences described in
Lovelock--Rund Sections 4.3 and 7.3.

At the center of normal coordinates the connection coefficients vanish. Thus
covariant derivatives reduce to partial derivatives and the geodesic equation
has no connection term at that point. Curvature need not vanish: it is encoded
by the first derivatives of the connection.

The coordinate index type is arbitrary and may be infinite.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LovelockRund

/-- A connection is normal at `x` when all of its coefficients vanish there. -/
def IsNormalConnectionAt {X ι : Type*}
    (Γ : ConnectionCoefficients X ι) (x : X) : Prop :=
  ∀ i j k, Γ x i j k = 0

/-- In normal coordinates, the covariant derivative of a vector equals its
partial derivative at the center. -/
theorem covariantDerivativeVector_normal
    {X ι : Type*}
    (D : ComponentDerivativeData X ι)
    (Γ : ConnectionCoefficients X ι)
    (V : ContravariantVectorField X ι)
    (x : X) (hΓ : IsNormalConnectionAt Γ x)
    (i k : ι) :
    covariantDerivativeVector D Γ V x i k =
      D.partialVector V x i k := by
  unfold covariantDerivativeVector
  have hsum : (∑' j, Γ x i j k * V x j) = 0 := by
    calc
      (∑' j, Γ x i j k * V x j) = ∑' _j : ι, (0 : ℝ) := by
        apply tsum_congr
        intro j
        simp [hΓ i j k]
      _ = 0 := tsum_zero
  rw [hsum, add_zero]

/-- In normal coordinates, the covariant derivative of a covector equals its
partial derivative at the center. -/
theorem covariantDerivativeCovector_normal
    {X ι : Type*}
    (D : ComponentDerivativeData X ι)
    (Γ : ConnectionCoefficients X ι)
    (A : CovariantVectorField X ι)
    (x : X) (hΓ : IsNormalConnectionAt Γ x)
    (i k : ι) :
    covariantDerivativeCovector D Γ A x i k =
      D.partialCovector A x i k := by
  unfold covariantDerivativeCovector
  have hsum : (∑' j, Γ x j i k * A x j) = 0 := by
    calc
      (∑' j, Γ x j i k * A x j) = ∑' _j : ι, (0 : ℝ) := by
        apply tsum_congr
        intro j
        simp [hΓ j i k]
      _ = 0 := tsum_zero
  rw [hsum, sub_zero]

/-- The geodesic connection term vanishes at the center of normal
coordinates. -/
theorem infiniteConnectionTerm_normal
    {X ι : Type*}
    (Γ : ConnectionCoefficients X ι)
    (velocity : ι → ℝ) (x : X)
    (hΓ : IsNormalConnectionAt Γ x) (i : ι) :
    infiniteConnectionTerm (Γ x) velocity i = 0 := by
  unfold infiniteConnectionTerm
  calc
    (∑' j, ∑' k, Γ x i j k * velocity j * velocity k) =
        ∑' _j : ι, (0 : ℝ) := by
      apply tsum_congr
      intro j
      calc
        (∑' k, Γ x i j k * velocity j * velocity k) =
            ∑' _k : ι, (0 : ℝ) := by
          apply tsum_congr
          intro k
          simp [hΓ i j k]
        _ = 0 := tsum_zero
    _ = 0 := tsum_zero

/-- At the center of normal coordinates, the geodesic residual is just the
coordinate acceleration. -/
theorem infiniteGeodesicResidual_normal
    {X ι : Type*}
    (Γ : ConnectionCoefficients X ι)
    (acceleration velocity : ι → ℝ)
    (x : X) (hΓ : IsNormalConnectionAt Γ x) :
    infiniteGeodesicResidual (Γ x) acceleration velocity =
      acceleration := by
  funext i
  simp [infiniteGeodesicResidual,
    infiniteConnectionTerm_normal Γ velocity x hΓ i]

/-- First derivatives of connection coefficients. The final index is the
coordinate derivative index. -/
abbrev ConnectionDerivative (X ι : Type*) :=
  X → ι → ι → ι → ι → ℝ

/-- Curvature at a normal-coordinate center, where quadratic connection terms
vanish:
`Rⁱ_jkl = ∂ₖΓⁱ_jl - ∂ₗΓⁱ_jk`. -/
def normalCoordinateCurvature {X ι : Type*}
    (partialΓ : ConnectionDerivative X ι) :
    X → ι → ι → ι → ι → ℝ :=
  fun x i j k l =>
    partialΓ x i j l k - partialΓ x i j k l

/-- Normal-coordinate curvature is skew in the final two indices. -/
theorem normalCoordinateCurvature_skew
    {X ι : Type*}
    (partialΓ : ConnectionDerivative X ι)
    (x : X) (i j k l : ι) :
    normalCoordinateCurvature partialΓ x i j l k =
      -normalCoordinateCurvature partialΓ x i j k l := by
  unfold normalCoordinateCurvature
  ring

/-- Vanishing first derivatives of the connection at a normal center force
curvature to vanish there. -/
theorem normalCoordinateCurvature_eq_zero
    {X ι : Type*}
    (partialΓ : ConnectionDerivative X ι)
    (x : X)
    (hpartial : ∀ i j k l, partialΓ x i j k l = 0) :
    ∀ i j k l,
      normalCoordinateCurvature partialΓ x i j k l = 0 := by
  intro i j k l
  simp [normalCoordinateCurvature, hpartial]

/-- Normal coordinates eliminate connection coefficients at one point but do
not by themselves eliminate curvature. This theorem packages the distinction:
curvature at the center is exactly the antisymmetrized first derivative of the
connection. -/
theorem normal_coordinates_connection_zero_curvature_derivative
    {X ι : Type*}
    (Γ : ConnectionCoefficients X ι)
    (partialΓ : ConnectionDerivative X ι)
    (x : X) (hΓ : IsNormalConnectionAt Γ x) :
    (∀ i j k, Γ x i j k = 0) ∧
      (∀ i j k l,
        normalCoordinateCurvature partialΓ x i j k l =
          partialΓ x i j l k - partialΓ x i j k l) :=
  ⟨hΓ, fun _ _ _ _ => rfl⟩

end Physlib.Mathematics.LovelockRund

end
