/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.ClassicalFieldTheory.Local.Variation
public import Physlib.QFT.ScalarGreenFunctions.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Classical scalar action and finite functional derivatives

This file formalizes the classical and functional-differential starting point
of Rivers, Sections 1.1--1.3, at a finite regularized set of spacetime points.
The repository's `ClassicalFieldTheory.Local.AdmissibleVariation` supplies the
continuum compactly-supported test-function layer; here we prove the coordinate
identities used by a lattice or cylindrical approximation.

Main results:

* `finiteFunctionalDerivative` implements variation of one field coordinate;
* evaluation functionals satisfy the defining delta-coordinate rule;
* the quartic potential `g A^4/4!` has derivative `g A^3/3!`;
* the local scalar Euler--Lagrange force is `m² A + g A³/3!`;
* nonnegative mass-square and quartic coupling give a nonnegative potential.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

/-- Variation of one coordinate of a finite scalar configuration. -/
def coordinateVariation {X : Type*} [DecidableEq X]
    (φ : X → ℝ) (x : X) (t : ℝ) : X → ℝ :=
  fun y => φ y + if y = x then t else 0

@[simp] lemma coordinateVariation_same {X : Type*} [DecidableEq X]
    (φ : X → ℝ) (x : X) (t : ℝ) :
    coordinateVariation φ x t x = φ x + t := by
  simp [coordinateVariation]

@[simp] lemma coordinateVariation_other {X : Type*} [DecidableEq X]
    (φ : X → ℝ) {x y : X} (h : y ≠ x) (t : ℝ) :
    coordinateVariation φ x t y = φ y := by
  simp [coordinateVariation, h]

/-- Finite-coordinate realization of a functional derivative. -/
def finiteFunctionalDerivative {X : Type*} [DecidableEq X]
    (F : (X → ℝ) → ℝ) (φ : X → ℝ) (x : X) : ℝ :=
  deriv (fun t => F (coordinateVariation φ x t)) 0

/-- Evaluation functional `F[φ] = f(φ(x))`. -/
def evaluationFunctional {X : Type*}
    (f : ℝ → ℝ) (x : X) (φ : X → ℝ) : ℝ :=
  f (φ x)

/-- Finite version of `δ f(φ(x)) / δφ(x) = f'(φ(x))`, Rivers Eq. (1.11). -/
lemma finiteFunctionalDerivative_evaluation
    {X : Type*} [DecidableEq X]
    (f : ℝ → ℝ) (f' : ℝ) (φ : X → ℝ) (x : X)
    (hf : HasDerivAt f f' (φ x)) :
    finiteFunctionalDerivative (evaluationFunctional f x) φ x = f' := by
  unfold finiteFunctionalDerivative evaluationFunctional
  have hinner : HasDerivAt (fun t : ℝ => φ x + t) 1 0 :=
    (hasDerivAt_id 0).const_add (φ x)
  have hf0 : HasDerivAt f f' (φ x + 0) := by rwa [add_zero]
  have hc : HasDerivAt (f ∘ fun t : ℝ => φ x + t) (f' * 1) 0 := hf0.comp (0 : ℝ) hinner
  have hcomp : HasDerivAt (fun t : ℝ => f (φ x + t)) f' 0 := by
    simpa [Function.comp_def] using hc
  simpa [coordinateVariation] using hcomp.deriv

/-- Varying a different coordinate gives zero derivative. -/
lemma finiteFunctionalDerivative_evaluation_other
    {X : Type*} [DecidableEq X]
    (f : ℝ → ℝ) (φ : X → ℝ) {x y : X} (hxy : y ≠ x) :
    finiteFunctionalDerivative (evaluationFunctional f y) φ x = 0 := by
  unfold finiteFunctionalDerivative evaluationFunctional
  have hconst :
      (fun t => f (coordinateVariation φ x t y)) = fun _ => f (φ y) := by
    funext t
    rw [coordinateVariation_other φ hxy]
  rw [hconst]
  simp

/-- Quartic scalar self-interaction `g A^4 / 4!`. -/
def quarticPotential (g A : ℝ) : ℝ :=
  g * A ^ 4 / 24

/-- Derivative `U'(A) = g A^3 / 3!`. -/
lemma quarticPotential_hasDerivAt (g A : ℝ) :
    HasDerivAt (quarticPotential g) (g * A ^ 3 / 6) A := by
  have hp : HasDerivAt (fun x : ℝ => x ^ 4) (4 * A ^ 3) A := by simpa using hasDerivAt_pow 4 A
  have hfun : quarticPotential g = fun x : ℝ => (g / 24) * x ^ 4 := by
    funext x; unfold quarticPotential; ring
  have key : g * A ^ 3 / 6 = (g / 24) * (4 * A ^ 3) := by ring
  rw [hfun, key]
  exact hp.const_mul (g / 24)

/-- Mass potential `(1/2)m²A²`. -/
def massPotential (massSq A : ℝ) : ℝ :=
  (1 / 2) * massSq * A ^ 2

lemma massPotential_hasDerivAt (massSq A : ℝ) :
    HasDerivAt (massPotential massSq) (massSq * A) A := by
  have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * A) A := by simpa using hasDerivAt_pow 2 A
  have key : massSq * A = (1 / 2) * massSq * (2 * A) := by ring
  unfold massPotential
  rw [key]
  exact hp.const_mul ((1 / 2) * massSq)

/-- Local scalar potential `(1/2)m²A² + gA⁴/4!`. -/
def scalarPotential (massSq g A : ℝ) : ℝ :=
  massPotential massSq A + quarticPotential g A

/-- Local Euler--Lagrange force `m²A + gA³/3!`. -/
def scalarPotentialDerivative (massSq g A : ℝ) : ℝ :=
  massSq * A + g * A ^ 3 / 6

lemma scalarPotential_hasDerivAt (massSq g A : ℝ) :
    HasDerivAt (scalarPotential massSq g)
      (scalarPotentialDerivative massSq g A) A := by
  unfold scalarPotential scalarPotentialDerivative
  exact (massPotential_hasDerivAt massSq A).add
    (quarticPotential_hasDerivAt g A)

/-- Functional derivative of the local scalar potential at one regularized
spacetime coordinate. -/
lemma finiteFunctionalDerivative_scalarPotential
    {X : Type*} [DecidableEq X]
    (massSq g : ℝ) (φ : X → ℝ) (x : X) :
    finiteFunctionalDerivative
        (evaluationFunctional (scalarPotential massSq g) x) φ x =
      scalarPotentialDerivative massSq g (φ x) :=
  finiteFunctionalDerivative_evaluation
    (scalarPotential massSq g)
    (scalarPotentialDerivative massSq g (φ x)) φ x
    (scalarPotential_hasDerivAt massSq g (φ x))

/-- Nonnegative stable scalar potential for nonnegative `m²` and `g`. -/
lemma scalarPotential_nonneg
    (massSq g A : ℝ) (hm : 0 ≤ massSq) (hg : 0 ≤ g) :
    0 ≤ scalarPotential massSq g A := by
  unfold scalarPotential massPotential quarticPotential
  positivity

/-- Finite regularized Euler--Lagrange operator `(Kφ)(x) + U'(φ(x))`. -/
def finiteScalarEulerLagrange {X : Type*} [Fintype X]
    (K : X → X → ℝ) (massSq g : ℝ) (φ : X → ℝ) (x : X) : ℝ :=
  (∑ y, K x y * φ y) + scalarPotentialDerivative massSq g (φ x)

/-- Pointwise expansion of the quartic finite Euler--Lagrange operator. -/
lemma finiteScalarEulerLagrange_apply {X : Type*} [Fintype X]
    (K : X → X → ℝ) (massSq g : ℝ) (φ : X → ℝ) (x : X) :
    finiteScalarEulerLagrange K massSq g φ x =
      (∑ y, K x y * φ y) + massSq * φ x + g * (φ x) ^ 3 / 6 := by
  simp [finiteScalarEulerLagrange, scalarPotentialDerivative, add_assoc]

end Physlib.QFT.ScalarGreenFunctions

end
