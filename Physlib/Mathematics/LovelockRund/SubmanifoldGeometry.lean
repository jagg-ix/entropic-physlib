/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.LovelockRund.TensorFields

/-!
# Hypersurface geometry and the Gauss--Codazzi equations

This module formalizes the component identities developed in Lovelock--Rund
Sections 7.4 and 7.5. The tangent index type is arbitrary, so the algebraic
Gauss and Codazzi equations are not restricted to a fixed finite dimension.

For a hypersurface with scalar second fundamental form `h`, the Gauss equation
is

`R^Σ_ijkl = R^M_ijkl + h_ik h_jl - h_il h_jk`.

The Codazzi equation identifies the antisymmetrized covariant derivative of
`h` with the ambient curvature carrying one normal index.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LovelockRund

/-- Algebraic curvature tensor components with four covariant tangent
indices. -/
abbrev CurvatureComponents (X ι : Type*) :=
  X → ι → ι → ι → ι → ℝ

/-- Scalar second fundamental form of a hypersurface. -/
abbrev SecondFundamentalForm (X ι : Type*) :=
  X → ι → ι → ℝ

/-- Covariant derivative components `h_ij;k`. -/
abbrev SecondFundamentalDerivative (X ι : Type*) :=
  X → ι → ι → ι → ℝ

/-- Ambient curvature components with one normal and three tangent slots. -/
abbrev NormalAmbientCurvature (X ι : Type*) :=
  X → ι → ι → ι → ℝ

/-- Hypersurface data satisfying the Gauss equation. -/
structure GaussEquationData (X ι : Type*) where
  /-- Ambient tangential curvature. -/
  ambientCurvature : CurvatureComponents X ι
  /-- Intrinsic curvature of the hypersurface. -/
  intrinsicCurvature : CurvatureComponents X ι
  /-- Second fundamental form. -/
  secondFundamental : SecondFundamentalForm X ι
  /-- Symmetry of the second fundamental form. -/
  secondFundamental_symm :
    ∀ x i j, secondFundamental x i j = secondFundamental x j i
  /-- Gauss equation. -/
  gauss : ∀ x i j k l,
    intrinsicCurvature x i j k l =
      ambientCurvature x i j k l +
        secondFundamental x i k * secondFundamental x j l -
        secondFundamental x i l * secondFundamental x j k

namespace GaussEquationData

variable {X ι : Type*}

/-- In a flat ambient space, intrinsic curvature is generated entirely by the
second fundamental form. -/
theorem intrinsicCurvature_of_flatAmbient
    (G : GaussEquationData X ι)
    (hflat : G.ambientCurvature = 0) :
    ∀ x i j k l,
      G.intrinsicCurvature x i j k l =
        G.secondFundamental x i k * G.secondFundamental x j l -
          G.secondFundamental x i l * G.secondFundamental x j k := by
  intro x i j k l
  rw [G.gauss]
  simp [hflat]

/-- A totally geodesic hypersurface has intrinsic curvature equal to the
ambient tangential curvature. -/
theorem intrinsicCurvature_of_totallyGeodesic
    (G : GaussEquationData X ι)
    (htot : G.secondFundamental = 0) :
    G.intrinsicCurvature = G.ambientCurvature := by
  funext x i j k l
  rw [G.gauss]
  simp [htot]

/-- A totally geodesic hypersurface in a flat ambient space is intrinsically
flat. -/
theorem intrinsicCurvature_eq_zero
    (G : GaussEquationData X ι)
    (hflat : G.ambientCurvature = 0)
    (htot : G.secondFundamental = 0) :
    G.intrinsicCurvature = 0 := by
  rw [G.intrinsicCurvature_of_totallyGeodesic htot, hflat]

/-- The Gauss correction is skew under interchange of the final two tangent
indices. -/
theorem gaussCorrection_swap
    (G : GaussEquationData X ι)
    (x : X) (i j k l : ι) :
    (G.secondFundamental x i l * G.secondFundamental x j k -
        G.secondFundamental x i k * G.secondFundamental x j l) =
      -(G.secondFundamental x i k * G.secondFundamental x j l -
        G.secondFundamental x i l * G.secondFundamental x j k) := by
  ring

end GaussEquationData

/-- Hypersurface data satisfying the Codazzi equation. -/
structure CodazziEquationData (X ι : Type*) where
  /-- Covariant derivative of the second fundamental form. -/
  covariantSecondFundamental : SecondFundamentalDerivative X ι
  /-- Ambient curvature with one normal index. -/
  ambientNormalCurvature : NormalAmbientCurvature X ι
  /-- Codazzi equation. -/
  codazzi : ∀ x i j k,
    covariantSecondFundamental x i j k -
        covariantSecondFundamental x i k j =
      ambientNormalCurvature x i j k

namespace CodazziEquationData

variable {X ι : Type*}

/-- In a flat ambient space, the covariant derivative of the second
fundamental form is symmetric in the derivative and second tangent slots. -/
theorem derivative_symm_of_flatAmbient
    (C : CodazziEquationData X ι)
    (hflat : C.ambientNormalCurvature = 0) :
    ∀ x i j k,
      C.covariantSecondFundamental x i j k =
        C.covariantSecondFundamental x i k j := by
  intro x i j k
  have h := C.codazzi x i j k
  simp [hflat, sub_eq_zero] at h
  exact h

/-- Vanishing antisymmetrized derivative is equivalent to vanishing normal
ambient curvature. -/
theorem derivative_symm_iff_normalCurvature_zero
    (C : CodazziEquationData X ι) :
    (∀ x i j k,
      C.covariantSecondFundamental x i j k =
        C.covariantSecondFundamental x i k j) ↔
      C.ambientNormalCurvature = 0 := by
  constructor
  · intro h
    funext x i j k
    rw [← C.codazzi x i j k, h x i j k, sub_self]
    rfl
  · intro h
    exact C.derivative_symm_of_flatAmbient h

end CodazziEquationData

/-- Combined Gauss--Codazzi hypersurface package. -/
structure GaussCodazziData (X ι : Type*) where
  toGauss : GaussEquationData X ι
  toCodazzi : CodazziEquationData X ι

/-- Normal curvature in a chosen tangent direction, represented as the ratio
of the second and first fundamental forms. -/
def normalCurvature (firstFundamental secondFundamental : ℝ) : ℝ :=
  secondFundamental / firstFundamental

/-- Multiplying the normal curvature by a nonzero first fundamental form
recovers the second fundamental form. -/
theorem normalCurvature_mul_first
    (firstFundamental secondFundamental : ℝ)
    (hfirst : firstFundamental ≠ 0) :
    normalCurvature firstFundamental secondFundamental *
        firstFundamental = secondFundamental := by
  exact div_mul_cancel₀ secondFundamental hfirst

end Physlib.Mathematics.LovelockRund

end
