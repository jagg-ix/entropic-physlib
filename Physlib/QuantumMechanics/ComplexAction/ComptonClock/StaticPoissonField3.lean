/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3Analytic

/-!
# A global static Poisson field and its pointwise linearized geometry

This module packages the global input needed by the local analytic jet construction:

* one Newton coupling,
* one `C²` potential on Cartesian `ℝ³`,
* one spatial density,
* Poisson's equation at every point.

Each point is converted to `StaticPotentialJet3` using the actual Fréchet derivatives of the same
potential.  The existing jet adapters then provide the metric-derived Levi-Civita connection,
connection-derived Ricci tensor, and real or complex linearized Einstein carriers.

This is a reusable family of local static linearized models.  It does not assert boundary
conditions, existence or uniqueness of a Poisson solution, asymptotic behavior, or an exact
nonlinear spacetime solution.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

/--
A static Newtonian potential and density satisfying Poisson's equation throughout Cartesian
three-space.

The coupling is stored with the field so downstream theorems cannot accidentally use a different
`G` for its source equation.
-/
structure StaticPoissonField3 where
  newtonConstant : ℝ
  potential : StaticPotentialSpace3 → ℝ
  density : StaticPotentialSpace3 → ℝ
  potential_contDiff : ContDiff ℝ 2 potential
  poisson : ∀ x, laplacianAt3 potential x =
    4 * Real.pi * newtonConstant * density x

namespace StaticPoissonField3

/-- The analytic second-order jet of the field at `x`. -/
def jetAt (F : StaticPoissonField3) (x : StaticPotentialSpace3) : StaticPotentialJet3 :=
  StaticPotentialJet3.ofFunctionAt F.potential x F.potential_contDiff.contDiffAt

@[simp]
lemma jetAt_value (F : StaticPoissonField3) (x : StaticPotentialSpace3) :
    (F.jetAt x).value = F.potential x := by
  rfl

@[simp]
lemma jetAt_gradient (F : StaticPoissonField3) (x : StaticPotentialSpace3) (i : Fin 3) :
    (F.jetAt x).gradient i = firstSpatialDerivativeAt3 F.potential x i := by
  rfl

@[simp]
lemma jetAt_hessian
    (F : StaticPoissonField3) (x : StaticPotentialSpace3) (i j : Fin 3) :
    (F.jetAt x).hessian i j = secondSpatialDerivativeAt3 F.potential x i j := by
  rfl

@[simp]
lemma jetAt_laplacian (F : StaticPoissonField3) (x : StaticPotentialSpace3) :
    (F.jetAt x).laplacian = laplacianAt3 F.potential x := by
  rfl

/-- Every pointwise analytic jet carries the field's Poisson equation. -/
theorem jetAt_satisfiesPoisson (F : StaticPoissonField3) (x : StaticPotentialSpace3) :
    (F.jetAt x).SatisfiesPoisson F.newtonConstant (F.density x) := by
  exact (StaticPotentialJet3.satisfiesPoisson_ofFunctionAt_iff
    F.potential x F.potential_contDiff.contDiffAt F.newtonConstant (F.density x)).2
    (F.poisson x)

/-- The field's Poisson law has the standard weak-field `R₀₀` form at every point. -/
theorem weakFieldRicci00_at
    (F : StaticPoissonField3) (c : ℝ) (x : StaticPotentialSpace3) :
    weakFieldRicci00 (laplacianAt3 F.potential x) c =
      4 * Real.pi * F.newtonConstant * F.density x / c ^ 2 := by
  rw [weakFieldRicci00, F.poisson x]

/-- The complete compact connection at each point is the metric-derived Levi-Civita connection. -/
theorem leviCivita4_at_eq_connection
    (F : StaticPoissonField3) (c : ℝ) (x : StaticPotentialSpace3) :
    (F.jetAt x).leviCivita4 c =
      weakFieldLinearizedConnection4Spatial
        (firstSpatialDerivativeAt3 F.potential x 0)
        (firstSpatialDerivativeAt3 F.potential x 1)
        (firstSpatialDerivativeAt3 F.potential x 2) c := by
  simpa only [jetAt_gradient] using
    StaticPotentialJet3.leviCivita4_eq_connection (F.jetAt x) c

/-- The connection-derived Ricci tensor at each point is governed by the field Laplacian. -/
theorem ricci4_at_eq (F : StaticPoissonField3) (c : ℝ) (x : StaticPotentialSpace3) :
    (F.jetAt x).ricci4 c =
      !![laplacianAt3 F.potential x / c ^ 2, 0, 0, 0;
         0, laplacianAt3 F.potential x / c ^ 2, 0, 0;
         0, 0, laplacianAt3 F.potential x / c ^ 2, 0;
         0, 0, 0, laplacianAt3 F.potential x / c ^ 2] := by
  simpa only [jetAt_laplacian] using StaticPotentialJet3.ricci4_eq (F.jetAt x) c

/--
The same pointwise Ricci matrix is explicitly the contraction of the derivative of the
metric-derived Levi-Civita connection.
-/
theorem ricciFromConnection_at_eq
    (F : StaticPoissonField3) (c : ℝ) (x : StaticPotentialSpace3) :
    ricciMatrixFromConnection (fun _ => 0) ((F.jetAt x).leviCivitaDeriv4 c) =
      !![laplacianAt3 F.potential x / c ^ 2, 0, 0, 0;
         0, laplacianAt3 F.potential x / c ^ 2, 0, 0;
         0, 0, laplacianAt3 F.potential x / c ^ 2, 0;
         0, 0, 0, laplacianAt3 F.potential x / c ^ 2] := by
  change (F.jetAt x).ricci4 c =
    !![laplacianAt3 F.potential x / c ^ 2, 0, 0, 0;
       0, laplacianAt3 F.potential x / c ^ 2, 0, 0;
       0, 0, laplacianAt3 F.potential x / c ^ 2, 0;
       0, 0, 0, laplacianAt3 F.potential x / c ^ 2]
  exact F.ricci4_at_eq c x

/-- Poisson's equation supplies the real static linearized Einstein equation at every point. -/
theorem einsteinFieldEquation_at
    (F : StaticPoissonField3) (c : ℝ) (hc : c ≠ 0) (x : StaticPotentialSpace3) :
    einsteinFieldEquation
        ((F.jetAt x).ricci4 c) ((F.jetAt x).scalar4 c) minkowskiMetric4
        (restDustStressEnergy4 (F.density x) c)
        (8 * Real.pi * F.newtonConstant / c ^ 4) := by
  exact (StaticPotentialJet3.efe4_iff_poisson
    (F.jetAt x) F.newtonConstant c (F.density x) hc).2
    (F.jetAt_satisfiesPoisson x)

/--
The pointwise complex field equation follows when its independent imaginary-sector relation is
provided as a spatial field.
-/
theorem complexEinsteinFieldEquation_at
    (F : StaticPoissonField3) (c : ℝ)
    (Λ S : StaticPotentialSpace3 → Matrix (Fin 4) (Fin 4) ℝ)
    (hc : c ≠ 0)
    (hImaginary : ∀ x, Λ x =
      (8 * Real.pi * F.newtonConstant / c ^ 4) • S x)
    (x : StaticPotentialSpace3) :
    complexEinsteinFieldEquation ((F.jetAt x).einstein4 c) (Λ x)
      (restDustStressEnergy4 (F.density x) c) (S x)
      (8 * Real.pi * F.newtonConstant / c ^ 4) := by
  exact StaticPotentialJet3.complexEFE4_of_poisson
    (F.jetAt x) F.newtonConstant c (F.density x) (Λ x) (S x) hc
    (F.jetAt_satisfiesPoisson x) (hImaginary x)

/--
The reusable field-level geometry/EFE family.

It records, for every point, the analytic Poisson jet, its metric-derived connection, its complete
Ricci matrix, and both real and explicitly conditioned complex Einstein carriers.
-/
theorem pointwise_staticLinearizedGeometry
    (F : StaticPoissonField3) (c : ℝ)
    (Λ S : StaticPotentialSpace3 → Matrix (Fin 4) (Fin 4) ℝ)
    (hc : c ≠ 0)
    (hImaginary : ∀ x, Λ x =
      (8 * Real.pi * F.newtonConstant / c ^ 4) • S x) :
    ∀ x,
      (F.jetAt x).SatisfiesPoisson F.newtonConstant (F.density x)
      ∧ (F.jetAt x).leviCivita4 c =
          weakFieldLinearizedConnection4Spatial
            (firstSpatialDerivativeAt3 F.potential x 0)
            (firstSpatialDerivativeAt3 F.potential x 1)
            (firstSpatialDerivativeAt3 F.potential x 2) c
      ∧ ricciMatrixFromConnection (fun _ => 0)
          ((F.jetAt x).leviCivitaDeriv4 c) =
          !![laplacianAt3 F.potential x / c ^ 2, 0, 0, 0;
             0, laplacianAt3 F.potential x / c ^ 2, 0, 0;
             0, 0, laplacianAt3 F.potential x / c ^ 2, 0;
             0, 0, 0, laplacianAt3 F.potential x / c ^ 2]
      ∧ einsteinFieldEquation
          ((F.jetAt x).ricci4 c) ((F.jetAt x).scalar4 c) minkowskiMetric4
          (restDustStressEnergy4 (F.density x) c)
          (8 * Real.pi * F.newtonConstant / c ^ 4)
      ∧ complexEinsteinFieldEquation ((F.jetAt x).einstein4 c) (Λ x)
          (restDustStressEnergy4 (F.density x) c) (S x)
          (8 * Real.pi * F.newtonConstant / c ^ 4) := by
  intro x
  exact ⟨F.jetAt_satisfiesPoisson x, F.leviCivita4_at_eq_connection c x,
    F.ricciFromConnection_at_eq c x, F.einsteinFieldEquation_at c hc x,
    F.complexEinsteinFieldEquation_at c Λ S hc hImaginary x⟩

end StaticPoissonField3

end Physlib.QuantumMechanics.ComplexAction.ComptonClock

end
