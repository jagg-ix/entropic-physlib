/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import
  Mathlib.Analysis.Calculus.FDeriv.Symmetric

public import
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3

/-!
# Analytic construction of a static potential jet

`StaticPotentialJet3` is deliberately a local data carrier.  This module supplies the complementary
analytic construction: a twice continuously differentiable potential `Φ : ℝ³ → ℝ` determines a
typed jet at every point.  Its Hessian symmetry is not assumed independently; it follows from the
symmetry of the second Fréchet derivative.

The Cartesian coordinate directions are represented by `Pi.single i 1` in `Fin 3 → ℝ`.  The
resulting jet can be passed directly to the metric, Levi-Civita, Ricci, Einstein, and complex
Einstein adapters already defined in `StaticPotentialJet3`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

/-- The Cartesian real vector space used as the domain of a static three-dimensional potential. -/
abbrev StaticPotentialSpace3 := Fin 3 → ℝ

/-- The `i`th Cartesian coordinate direction in `StaticPotentialSpace3`. -/
def coordinateDirection3 (i : Fin 3) : StaticPotentialSpace3 :=
  Pi.single i 1

/-- The first Cartesian derivative of `Φ` at `x`. -/
def firstSpatialDerivativeAt3
    (Φ : StaticPotentialSpace3 → ℝ) (x : StaticPotentialSpace3) (i : Fin 3) : ℝ :=
  fderiv ℝ Φ x (coordinateDirection3 i)

/-- The iterated second Cartesian derivative of `Φ` at `x`. -/
def secondSpatialDerivativeAt3
    (Φ : StaticPotentialSpace3 → ℝ) (x : StaticPotentialSpace3)
    (i j : Fin 3) : ℝ :=
  fderiv ℝ (fderiv ℝ Φ) x (coordinateDirection3 i) (coordinateDirection3 j)

/-- The trace of the second Fréchet derivative in the three Cartesian coordinate directions. -/
def laplacianAt3 (Φ : StaticPotentialSpace3 → ℝ) (x : StaticPotentialSpace3) : ℝ :=
  secondSpatialDerivativeAt3 Φ x 0 0 +
    secondSpatialDerivativeAt3 Φ x 1 1 +
    secondSpatialDerivativeAt3 Φ x 2 2

/-- Schwarz symmetry for the Cartesian components of the second Fréchet derivative. -/
theorem secondSpatialDerivativeAt3_comm
    (Φ : StaticPotentialSpace3 → ℝ) (x : StaticPotentialSpace3)
    (hΦ : ContDiffAt ℝ 2 Φ x) (i j : Fin 3) :
    secondSpatialDerivativeAt3 Φ x i j = secondSpatialDerivativeAt3 Φ x j i := by
  exact (hΦ.isSymmSndFDerivAt (by simp)).eq
    (coordinateDirection3 i) (coordinateDirection3 j)

namespace StaticPotentialJet3

set_option backward.isDefEq.respectTransparency false in
/--
Construct the local typed jet of a `C²` potential.

The smoothness proof is used only to establish Hessian symmetry.  The value and derivative data are
the ordinary first and iterated second Fréchet derivatives in the Cartesian coordinate directions.
-/
def ofFunctionAt
    (Φ : StaticPotentialSpace3 → ℝ) (x : StaticPotentialSpace3)
    (hΦ : ContDiffAt ℝ 2 Φ x) : StaticPotentialJet3 where
  value := Φ x
  gradient := firstSpatialDerivativeAt3 Φ x
  hessian := fun i j => secondSpatialDerivativeAt3 Φ x i j
  hessian_symm := by
    ext i j
    simp only [Matrix.transpose_apply]
    exact secondSpatialDerivativeAt3_comm Φ x hΦ j i

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma value_ofFunctionAt
    (Φ : StaticPotentialSpace3 → ℝ) (x : StaticPotentialSpace3)
    (hΦ : ContDiffAt ℝ 2 Φ x) :
    (ofFunctionAt Φ x hΦ).value = Φ x := by
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma gradient_ofFunctionAt
    (Φ : StaticPotentialSpace3 → ℝ) (x : StaticPotentialSpace3)
    (hΦ : ContDiffAt ℝ 2 Φ x) (i : Fin 3) :
    (ofFunctionAt Φ x hΦ).gradient i = firstSpatialDerivativeAt3 Φ x i := by
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma hessian_ofFunctionAt
    (Φ : StaticPotentialSpace3 → ℝ) (x : StaticPotentialSpace3)
    (hΦ : ContDiffAt ℝ 2 Φ x) (i j : Fin 3) :
    (ofFunctionAt Φ x hΦ).hessian i j = secondSpatialDerivativeAt3 Φ x i j := by
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma laplacian_ofFunctionAt
    (Φ : StaticPotentialSpace3 → ℝ) (x : StaticPotentialSpace3)
    (hΦ : ContDiffAt ℝ 2 Φ x) :
    (ofFunctionAt Φ x hΦ).laplacian = laplacianAt3 Φ x := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The analytic jet's Poisson predicate is exactly the coordinate Laplacian equation. -/
theorem satisfiesPoisson_ofFunctionAt_iff
    (Φ : StaticPotentialSpace3 → ℝ) (x : StaticPotentialSpace3)
    (hΦ : ContDiffAt ℝ 2 Φ x) (G ρ : ℝ) :
    (ofFunctionAt Φ x hΦ).SatisfiesPoisson G ρ ↔
      laplacianAt3 Φ x = 4 * Real.pi * G * ρ := by
  rfl

/-- The analytic jet's real Einstein equation is equivalent to Poisson's equation at the point. -/
theorem efe4_ofFunctionAt_iff_poisson
    (Φ : StaticPotentialSpace3 → ℝ) (x : StaticPotentialSpace3)
    (hΦ : ContDiffAt ℝ 2 Φ x) (G c ρ : ℝ) (hc : c ≠ 0) :
    einsteinFieldEquation
        ((ofFunctionAt Φ x hΦ).ricci4 c)
        ((ofFunctionAt Φ x hΦ).scalar4 c)
        minkowskiMetric4 (restDustStressEnergy4 ρ c) (8 * Real.pi * G / c ^ 4)
      ↔ laplacianAt3 Φ x = 4 * Real.pi * G * ρ := by
  rw [efe4_iff_poisson (ofFunctionAt Φ x hΦ) G c ρ hc]
  exact satisfiesPoisson_ofFunctionAt_iff Φ x hΦ G ρ

/--
Poisson's equation for a `C²` potential, together with the explicitly independent imaginary sector,
produces the complex Einstein carrier at the selected point.
-/
theorem complexEFE4_ofFunctionAt_poisson
    (Φ : StaticPotentialSpace3 → ℝ) (x : StaticPotentialSpace3)
    (hΦ : ContDiffAt ℝ 2 Φ x)
    (G c ρ : ℝ) (Λ S : Matrix (Fin 4) (Fin 4) ℝ)
    (hc : c ≠ 0) (hPoisson : laplacianAt3 Φ x = 4 * Real.pi * G * ρ)
    (hImaginary : Λ = (8 * Real.pi * G / c ^ 4) • S) :
    complexEinsteinFieldEquation ((ofFunctionAt Φ x hΦ).einstein4 c) Λ
      (restDustStressEnergy4 ρ c) S (8 * Real.pi * G / c ^ 4) := by
  apply complexEFE4_of_poisson
  · exact hc
  · exact (satisfiesPoisson_ofFunctionAt_iff Φ x hΦ G ρ).2 hPoisson
  · exact hImaginary

end StaticPotentialJet3

end Physlib.QuantumMechanics.ComplexAction.ComptonClock

end
