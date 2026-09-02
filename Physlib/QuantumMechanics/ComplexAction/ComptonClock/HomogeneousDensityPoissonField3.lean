/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonHodgeStar3

/-!
# An explicit homogeneous-density static Poisson field

The global field API is non-vacuous.  For constants `G` and `ρ`, define

`Φ(x) = (2πGρ/3) (x₀² + x₁² + x₂²)`.

Its Cartesian Hessian is `(4πGρ/3) I₃`, so its Laplacian is exactly `4πGρ`.
This constructs a concrete `StaticPoissonField3` with constant density and provides a directly
usable test model for the metric, connection, Ricci, and Einstein adapters.

The quadratic potential is a whole-space algebraic solution of the constant-source Poisson
equation.  It is not an isolated finite-mass source, does not satisfy asymptotic-flatness boundary
conditions, and is not a nonlinear interior Schwarzschild solution.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

/-- The coefficient of the isotropic quadratic potential for constant density `ρ`. -/
def homogeneousDensityPotentialCoefficient (G ρ : ℝ) : ℝ :=
  2 * Real.pi * G * ρ / 3

/-- The isotropic quadratic potential whose Laplacian is `4πGρ`. -/
def homogeneousDensityPotential3
    (G ρ : ℝ) (x : StaticPotentialSpace3) : ℝ :=
  homogeneousDensityPotentialCoefficient G ρ *
    (((fun y : Fin 3 → ℝ => y 0 ^ 2) +
      (fun y : Fin 3 → ℝ => y 1 ^ 2) +
      (fun y : Fin 3 → ℝ => y 2 ^ 2)) x)

/-- The homogeneous-density potential is smooth, hence in particular globally `C²`. -/
theorem homogeneousDensityPotential3_contDiff (G ρ : ℝ) :
    ContDiff ℝ 2 (homogeneousDensityPotential3 G ρ) := by
  unfold homogeneousDensityPotential3
  change ContDiff ℝ 2 (fun x : Fin 3 → ℝ =>
    homogeneousDensityPotentialCoefficient G ρ *
      (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2))
  fun_prop

/-- The Cartesian gradient is radial and linear in the coordinates. -/
theorem firstSpatialDerivativeAt3_homogeneousDensityPotential
    (G ρ : ℝ) (x : StaticPotentialSpace3) (i : Fin 3) :
    firstSpatialDerivativeAt3 (homogeneousDensityPotential3 G ρ) x i =
      2 * homogeneousDensityPotentialCoefficient G ρ * x i := by
  let a := homogeneousDensityPotentialCoefficient G ρ
  have h0 := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) x).pow 2
  have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) x).pow 2
  have h2 := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) x).pow 2
  have h := ((h0.add h1).add h2).const_mul a
  rw [firstSpatialDerivativeAt3]
  rw [show homogeneousDensityPotential3 G ρ =
    fun y => a * (((fun z : Fin 3 → ℝ => z 0 ^ 2) +
      (fun z : Fin 3 → ℝ => z 1 ^ 2) +
      (fun z : Fin 3 → ℝ => z 2 ^ 2)) y) by
        rfl]
  rw [h.fderiv]
  fin_cases i <;> simp [coordinateDirection3] <;> ring

/-- The Cartesian Hessian is the constant scalar matrix `(4πGρ/3) I₃`. -/
theorem secondSpatialDerivativeAt3_homogeneousDensityPotential
    (G ρ : ℝ) (x : StaticPotentialSpace3) (i j : Fin 3) :
    secondSpatialDerivativeAt3 (homogeneousDensityPotential3 G ρ) x i j =
      if i = j then 2 * homogeneousDensityPotentialCoefficient G ρ else 0 := by
  rw [secondSpatialDerivativeAt3]
  have happ :
      fderiv ℝ
          (fun y => fderiv ℝ (homogeneousDensityPotential3 G ρ) y
            (coordinateDirection3 j)) x
          (coordinateDirection3 i) =
        ((fderiv ℝ (fderiv ℝ (homogeneousDensityPotential3 G ρ)) x)
          (coordinateDirection3 i)) (coordinateDirection3 j) := by
    rw [fderiv_clm_apply]
    · simp
    · exact ((homogeneousDensityPotential3_contDiff G ρ).fderiv_right
        (m := 1) (by norm_num)).differentiable (by norm_num) x
    · fun_prop
  rw [← happ]
  have hfun :
      (fun y => fderiv ℝ (homogeneousDensityPotential3 G ρ) y
        (coordinateDirection3 j)) =
        fun y => 2 * homogeneousDensityPotentialCoefficient G ρ * y j := by
    funext y
    exact firstSpatialDerivativeAt3_homogeneousDensityPotential G ρ y j
  rw [hfun]
  have hcoord := (hasFDerivAt_apply (𝕜 := ℝ) j x).const_mul
    (2 * homogeneousDensityPotentialCoefficient G ρ)
  rw [hcoord.fderiv]
  fin_cases i <;> fin_cases j <;> simp [coordinateDirection3]

/-- The explicit quadratic potential satisfies the constant-density Poisson equation. -/
theorem laplacianAt3_homogeneousDensityPotential (G ρ : ℝ) (x : StaticPotentialSpace3) :
    laplacianAt3 (homogeneousDensityPotential3 G ρ) x =
      4 * Real.pi * G * ρ := by
  rw [laplacianAt3,
    secondSpatialDerivativeAt3_homogeneousDensityPotential,
    secondSpatialDerivativeAt3_homogeneousDensityPotential,
    secondSpatialDerivativeAt3_homogeneousDensityPotential]
  simp [homogeneousDensityPotentialCoefficient]
  ring

/-- A concrete global static Poisson field with constant density. -/
def homogeneousDensityPoissonField3 (G ρ : ℝ) : StaticPoissonField3 where
  newtonConstant := G
  potential := homogeneousDensityPotential3 G ρ
  density := fun _ => ρ
  potential_contDiff := homogeneousDensityPotential3_contDiff G ρ
  poisson := laplacianAt3_homogeneousDensityPotential G ρ

@[simp]
lemma homogeneousDensityPoissonField3_newtonConstant (G ρ : ℝ) :
    (homogeneousDensityPoissonField3 G ρ).newtonConstant = G := by
  rfl

@[simp]
lemma homogeneousDensityPoissonField3_potential
    (G ρ : ℝ) (x : StaticPotentialSpace3) :
    (homogeneousDensityPoissonField3 G ρ).potential x =
      homogeneousDensityPotential3 G ρ x := by
  rfl

@[simp]
lemma homogeneousDensityPoissonField3_density
    (G ρ : ℝ) (x : StaticPotentialSpace3) :
    (homogeneousDensityPoissonField3 G ρ).density x = ρ := by
  rfl

/--
The explicit homogeneous field supplies the complete pointwise linearized geometry and field
equations, including the independently provided complex imaginary sector.
-/
theorem homogeneousDensityPoissonField3_pointwiseGeometry
    (G ρ c : ℝ)
    (Λ S : StaticPotentialSpace3 → Matrix (Fin 4) (Fin 4) ℝ)
    (hc : c ≠ 0)
    (hImaginary : ∀ x, Λ x = (8 * Real.pi * G / c ^ 4) • S x) :
    ∀ x,
      ((homogeneousDensityPoissonField3 G ρ).jetAt x).SatisfiesPoisson G ρ
      ∧ ((homogeneousDensityPoissonField3 G ρ).jetAt x).hodgeFluxDivergence3 =
          4 * Real.pi * G * ρ
      ∧ ((homogeneousDensityPoissonField3 G ρ).jetAt x).leviCivita4 c =
          weakFieldLinearizedConnection4Spatial
            (firstSpatialDerivativeAt3 (homogeneousDensityPotential3 G ρ) x 0)
            (firstSpatialDerivativeAt3 (homogeneousDensityPotential3 G ρ) x 1)
            (firstSpatialDerivativeAt3 (homogeneousDensityPotential3 G ρ) x 2) c
      ∧ ricciMatrixFromConnection (fun _ => 0)
          (((homogeneousDensityPoissonField3 G ρ).jetAt x).leviCivitaDeriv4 c) =
          !![4 * Real.pi * G * ρ / c ^ 2, 0, 0, 0;
             0, 4 * Real.pi * G * ρ / c ^ 2, 0, 0;
             0, 0, 4 * Real.pi * G * ρ / c ^ 2, 0;
             0, 0, 0, 4 * Real.pi * G * ρ / c ^ 2]
      ∧ einsteinFieldEquation
          (((homogeneousDensityPoissonField3 G ρ).jetAt x).ricci4 c)
          (((homogeneousDensityPoissonField3 G ρ).jetAt x).scalar4 c)
          minkowskiMetric4 (restDustStressEnergy4 ρ c)
          (8 * Real.pi * G / c ^ 4)
      ∧ complexEinsteinFieldEquation
          (((homogeneousDensityPoissonField3 G ρ).jetAt x).einstein4 c) (Λ x)
          (restDustStressEnergy4 ρ c) (S x)
          (8 * Real.pi * G / c ^ 4) := by
  intro x
  rcases (homogeneousDensityPoissonField3 G ρ).pointwise_staticLinearizedGeometry
      c Λ S hc hImaginary x with ⟨hPoisson, hConnection, hRicci, hEFE, hComplex⟩
  have hHodge :=
    (homogeneousDensityPoissonField3 G ρ).hodgeFluxDivergence3_at x
  have hPotential :
      (homogeneousDensityPoissonField3 G ρ).potential =
        homogeneousDensityPotential3 G ρ := by
    rfl
  rw [hPotential] at hConnection hRicci
  rw [laplacianAt3_homogeneousDensityPotential] at hRicci
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hPoisson
  · simpa using hHodge
  · exact hConnection
  · exact hRicci
  · simpa using hEFE
  · simpa using hComplex

end Physlib.QuantumMechanics.ComplexAction.ComptonClock

end
