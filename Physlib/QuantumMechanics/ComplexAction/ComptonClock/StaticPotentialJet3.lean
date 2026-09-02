/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1

/-!
# A typed local jet for static Newtonian potentials

`WeakFieldEinstein3Plus1` proves the complete static linearized `Fin 4` curvature and Einstein
equations from a spatial gradient and a symmetric spatial Hessian.  This module packages those local
data into one reusable object rather than requiring downstream developments to pass nine unrelated
real numbers.

A `StaticPotentialJet3` contains

* the potential value,
* its `Fin 3` spatial gradient,
* its `3×3` Hessian,
* a proof that the Hessian is symmetric.

The adapters below feed the jet into the existing metric, metric-derived Levi-Civita connection,
connection derivative, Ricci, scalar, Einstein, and complex-Einstein carriers.  No new physical
assumption is introduced: the jet is local differential data, not a global solution or a claim that
an arbitrary collection of numbers comes from a globally defined potential.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

/-- Local second-order spatial data of a static real potential in three Cartesian coordinates. -/
structure StaticPotentialJet3 where
  value : ℝ
  gradient : Fin 3 → ℝ
  hessian : Matrix (Fin 3) (Fin 3) ℝ
  hessian_symm : hessianᵀ = hessian

namespace StaticPotentialJet3

/-- Construct a typed jet from the six independent entries of a symmetric Hessian. -/
def ofComponents
    (value dx dy dz dxx dyy dzz dxy dxz dyz : ℝ) : StaticPotentialJet3 where
  value := value
  gradient := ![dx, dy, dz]
  hessian := !![dxx, dxy, dxz; dxy, dyy, dyz; dxz, dyz, dzz]
  hessian_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

/-- The local spatial Laplacian, the trace of the symmetric Hessian. -/
def laplacian (J : StaticPotentialJet3) : ℝ :=
  J.hessian 0 0 + J.hessian 1 1 + J.hessian 2 2

/-- The symmetric Hessian identifies the two `xy` mixed entries. -/
lemma hessian_10_eq_01 (J : StaticPotentialJet3) :
    J.hessian 1 0 = J.hessian 0 1 := by
  simpa [Matrix.transpose_apply] using congrFun (congrFun J.hessian_symm 0) 1

/-- The symmetric Hessian identifies the two `xz` mixed entries. -/
lemma hessian_20_eq_02 (J : StaticPotentialJet3) :
    J.hessian 2 0 = J.hessian 0 2 := by
  simpa [Matrix.transpose_apply] using congrFun (congrFun J.hessian_symm 0) 2

/-- The symmetric Hessian identifies the two `yz` mixed entries. -/
lemma hessian_21_eq_12 (J : StaticPotentialJet3) :
    J.hessian 2 1 = J.hessian 1 2 := by
  simpa [Matrix.transpose_apply] using congrFun (congrFun J.hessian_symm 1) 2

/-- The component constructor has the expected spatial Laplacian. -/
@[simp]
lemma laplacian_ofComponents
    (value dx dy dz dxx dyy dzz dxy dxz dyz : ℝ) :
    (ofComponents value dx dy dz dxx dyy dzz dxy dxz dyz).laplacian =
      dxx + dyy + dzz := by
  rfl

/-- The metric derivatives selected by a typed potential jet. -/
def metricDeriv4 (J : StaticPotentialJet3) (c : ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  weakFieldMetricDeriv4Spatial (J.gradient 0) (J.gradient 1) (J.gradient 2) c

/-- The metric-derived linearized Levi-Civita connection selected by the jet gradient. -/
def leviCivita4 (J : StaticPotentialJet3) (c : ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  weakFieldLinearizedLeviCivita4Spatial
    (J.gradient 0) (J.gradient 1) (J.gradient 2) c

/-- The metric-derived connection derivative selected by the symmetric jet Hessian. -/
def leviCivitaDeriv4 (J : StaticPotentialJet3) (c : ℝ) :
    Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ :=
  weakFieldLinearizedLeviCivitaDeriv4Spatial
    (J.hessian 0 0) (J.hessian 1 1) (J.hessian 2 2)
    (J.hessian 0 1) (J.hessian 0 2) (J.hessian 1 2) c

/-- The complete connection-derived linearized Ricci matrix selected by the jet Hessian. -/
def ricci4 (J : StaticPotentialJet3) (c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  weakFieldLinearizedRicci4Spatial
    (J.hessian 0 0) (J.hessian 1 1) (J.hessian 2 2)
    (J.hessian 0 1) (J.hessian 0 2) (J.hessian 1 2) c

/-- The linearized scalar curvature selected by the jet Hessian. -/
def scalar4 (J : StaticPotentialJet3) (c : ℝ) : ℝ :=
  weakFieldLinearizedScalar4Spatial
    (J.hessian 0 0) (J.hessian 1 1) (J.hessian 2 2)
    (J.hessian 0 1) (J.hessian 0 2) (J.hessian 1 2) c

/-- The linearized Einstein tensor selected by the jet Hessian. -/
def einstein4 (J : StaticPotentialJet3) (c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  weakFieldLinearizedEinstein4Spatial
    (J.hessian 0 0) (J.hessian 1 1) (J.hessian 2 2)
    (J.hessian 0 1) (J.hessian 0 2) (J.hessian 1 2) c

/-- The local Poisson predicate carried by the jet. -/
def SatisfiesPoisson (J : StaticPotentialJet3) (G ρ : ℝ) : Prop :=
  J.laplacian = 4 * Real.pi * G * ρ

/-- The entire compact Christoffel array selected by the jet is metric-derived. -/
lemma leviCivita4_eq_connection (J : StaticPotentialJet3) (c : ℝ) :
    J.leviCivita4 c =
      weakFieldLinearizedConnection4Spatial
        (J.gradient 0) (J.gradient 1) (J.gradient 2) c :=
  weakFieldLinearizedLeviCivita4Spatial_eq_connection
    (J.gradient 0) (J.gradient 1) (J.gradient 2) c

/-- The jet connection derivative is exactly the Hessian derivative of the metric connection. -/
lemma leviCivitaDeriv4_eq_connectionDeriv (J : StaticPotentialJet3) (c : ℝ) :
    J.leviCivitaDeriv4 c =
      weakFieldLinearizedConnDeriv4Spatial
        (J.hessian 0 0) (J.hessian 1 1) (J.hessian 2 2)
        (J.hessian 0 1) (J.hessian 0 2) (J.hessian 1 2) c :=
  weakFieldLinearizedLeviCivitaDeriv4Spatial_eq_connectionDeriv
    (J.hessian 0 0) (J.hessian 1 1) (J.hessian 2 2)
    (J.hessian 0 1) (J.hessian 0 2) (J.hessian 1 2) c

/-- Every jet-derived Ricci component is `(∇²Φ/c²)` on the diagonal and zero off it. -/
lemma ricci4_eq (J : StaticPotentialJet3) (c : ℝ) :
    J.ricci4 c =
      !![J.laplacian / c ^ 2, 0, 0, 0;
         0, J.laplacian / c ^ 2, 0, 0;
         0, 0, J.laplacian / c ^ 2, 0;
         0, 0, 0, J.laplacian / c ^ 2] := by
  simpa [ricci4, laplacian, spatialLaplacian3] using
    weakFieldLinearizedRicci4Spatial_eq
      (J.hessian 0 0) (J.hessian 1 1) (J.hessian 2 2)
      (J.hessian 0 1) (J.hessian 0 2) (J.hessian 1 2) c

/-- The jet-derived scalar curvature is `-2∇²Φ/c²`. -/
lemma scalar4_eq (J : StaticPotentialJet3) (c : ℝ) :
    J.scalar4 c = -2 * J.laplacian / c ^ 2 := by
  simpa [scalar4, laplacian, spatialLaplacian3] using
    weakFieldLinearizedScalar4Spatial_eq
      (J.hessian 0 0) (J.hessian 1 1) (J.hessian 2 2)
      (J.hessian 0 1) (J.hessian 0 2) (J.hessian 1 2) c

/-- The jet-derived Einstein tensor has only the source-bearing `00` component. -/
lemma einstein4_eq (J : StaticPotentialJet3) (c : ℝ) :
    J.einstein4 c =
      !![2 * J.laplacian / c ^ 2, 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 0, 0] := by
  simpa [einstein4, laplacian, spatialLaplacian3] using
    weakFieldLinearizedEinstein4Spatial_eq
      (J.hessian 0 0) (J.hessian 1 1) (J.hessian 2 2)
      (J.hessian 0 1) (J.hessian 0 2) (J.hessian 1 2) c

/-- The jet-level sourced Einstein equation is equivalent to the jet's Poisson predicate. -/
theorem efe4_iff_poisson (J : StaticPotentialJet3) (G c ρ : ℝ) (hc : c ≠ 0) :
    einsteinFieldEquation (J.ricci4 c) (J.scalar4 c) minkowskiMetric4
        (restDustStressEnergy4 ρ c) (8 * Real.pi * G / c ^ 4)
      ↔ J.SatisfiesPoisson G ρ := by
  simpa [ricci4, scalar4, SatisfiesPoisson, laplacian, spatialLaplacian3] using
    weakFieldLinearizedEFE4Spatial_iff_poisson
      G c ρ (J.hessian 0 0) (J.hessian 1 1) (J.hessian 2 2)
      (J.hessian 0 1) (J.hessian 0 2) (J.hessian 1 2) hc

/-- A jet satisfying Poisson plus the explicit imaginary sector gives the complex field equation. -/
theorem complexEFE4_of_poisson
    (J : StaticPotentialJet3) (G c ρ : ℝ) (Λ S : Matrix (Fin 4) (Fin 4) ℝ)
    (hc : c ≠ 0) (hPoisson : J.SatisfiesPoisson G ρ)
    (hImaginary : Λ = (8 * Real.pi * G / c ^ 4) • S) :
    complexEinsteinFieldEquation (J.einstein4 c) Λ
      (restDustStressEnergy4 ρ c) S (8 * Real.pi * G / c ^ 4) := by
  exact weakFieldLinearizedComplexEFE4Spatial_of_poisson
    G c ρ (J.hessian 0 0) (J.hessian 1 1) (J.hessian 2 2)
    (J.hessian 0 1) (J.hessian 0 2) (J.hessian 1 2) Λ S hc
    (by simpa [SatisfiesPoisson, laplacian, spatialLaplacian3] using hPoisson)
    hImaginary

end StaticPotentialJet3

end Physlib.QuantumMechanics.ComplexAction.ComptonClock

end
