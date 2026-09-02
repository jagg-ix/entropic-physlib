/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.Continuum

/-!
# Continuum distributional Dyson--Schwinger hierarchy

Rivers' continuum Dyson--Schwinger equations contain coincident fields and
Dirac delta contact terms. This file states the hierarchy as an equality of
tempered distributions and evaluates its first members on Schwartz tests.

The external-field layer uses the pointwise kernel-composition integral already
defined in `Continuum.lean`:

`(A B C)(x,y) = ∫ dz A(x,z) B(z) C(z,y)`.

It supplies both the continuum Dyson equation

`Delta = Delta_0 + Delta_0 B Delta`

and the exact two-coupling resolvent difference formula whose quotient is the
finite-difference form of `∂_g Delta_g = Delta_g B Delta_g`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open Physlib

/-- Distribution-valued quartic scalar Dyson--Schwinger data on continuum
configuration space. -/
structure ContinuumQuarticDysonSchwingerData (d : ℕ) where
  /-- Full continuum Green hierarchy. -/
  green : List (Space d) → ℂ
  /-- Distributional kinetic contribution in the active point. -/
  kineticTerm : List (Space d) → ScalarContactDistribution d
  /-- Distribution representing one field insertion at the active point. -/
  oneFieldTerm : List (Space d) → ScalarContactDistribution d
  /-- Distribution representing the cubic interaction insertion. -/
  cubicFieldTerm : List (Space d) → ScalarContactDistribution d
  /-- Mass-square coefficient. -/
  massSq : ℂ
  /-- Quartic coupling. -/
  coupling : ℂ
  /-- Planck constant. -/
  hbar : ℂ
  /-- Bose symmetry of the Green hierarchy. -/
  bose : ∀ xs ys : List (Space d), xs.Perm ys → green xs = green ys
  /-- Complete distributional Dyson--Schwinger hierarchy. -/
  equation : ∀ xs : List (Space d),
    kineticTerm xs + massSq • oneFieldTerm xs +
        (coupling / 6) • cubicFieldTerm xs =
      -(Complex.I * hbar) • continuumContactTerm green xs

namespace ContinuumQuarticDysonSchwingerData

variable {d : ℕ}

/-- The distributional hierarchy evaluated on one Schwartz test function. -/
lemma equation_apply
    (D : ContinuumQuarticDysonSchwingerData d)
    (xs : List (Space d)) (η : SchwartzMap (Space d) ℂ) :
    D.kineticTerm xs η + D.massSq * D.oneFieldTerm xs η +
        (D.coupling / 6) * D.cubicFieldTerm xs η =
      -(Complex.I * D.hbar) * continuumContactTerm D.green xs η := by
  have h := congrArg (fun u : ScalarContactDistribution d => u η)
    (D.equation xs)
  simpa [mul_assoc] using h

/-- One-leg continuum equation: there is no contact term. -/
lemma oneLegEquation_apply
    (D : ContinuumQuarticDysonSchwingerData d)
    (η : SchwartzMap (Space d) ℂ) :
    D.kineticTerm [] η + D.massSq * D.oneFieldTerm [] η +
        (D.coupling / 6) * D.cubicFieldTerm [] η = 0 := by
  simpa [continuumContactTerm] using D.equation_apply [] η

/-- Two-leg continuum equation with the exact Dirac contact `G₀ δ_y`. -/
lemma twoLegEquation_apply
    (D : ContinuumQuarticDysonSchwingerData d)
    (y : Space d) (η : SchwartzMap (Space d) ℂ) :
    D.kineticTerm [y] η + D.massSq * D.oneFieldTerm [y] η +
        (D.coupling / 6) * D.cubicFieldTerm [y] η =
      -(Complex.I * D.hbar) * (D.green [] * η y) := by
  simpa using D.equation_apply [y] η

/-- Three-leg continuum equation with both distributional contact removals. -/
lemma threeLegEquation_apply
    (D : ContinuumQuarticDysonSchwingerData d)
    (y z : Space d) (η : SchwartzMap (Space d) ℂ) :
    D.kineticTerm [y, z] η + D.massSq * D.oneFieldTerm [y, z] η +
        (D.coupling / 6) * D.cubicFieldTerm [y, z] η =
      -(Complex.I * D.hbar) *
        (D.green [z] * η y + D.green [y] * η z) := by
  simpa using D.equation_apply [y, z] η

/-- Bose symmetry remains available at every continuum order. -/
lemma green_eq_of_perm
    (D : ContinuumQuarticDysonSchwingerData d)
    (xs ys : List (Space d)) (h : xs.Perm ys) :
    D.green xs = D.green ys :=
  D.bose xs ys h

end ContinuumQuarticDysonSchwingerData

/-! ## Continuum external-field Dyson equation -/

/-- Pointwise continuum solution of the external-field Dyson equation. -/
structure ContinuumExternalFieldDysonData (d : ℕ) where
  /-- Free Feynman kernel. -/
  freePropagator : Space d × Space d → ℂ
  /-- Dressed external-field kernel. -/
  dressedPropagator : Space d × Space d → ℂ
  /-- Pointwise external background. -/
  background : ContinuumScalarField d
  /-- Continuum Dyson equation. -/
  equation : ∀ x y : Space d,
    dressedPropagator (x, y) = freePropagator (x, y) +
      pointwiseKernelComposition freePropagator dressedPropagator
        background x y

namespace ContinuumExternalFieldDysonData

variable {d : ℕ}

/-- Named pointwise form of the continuum Dyson equation. -/
lemma dysonEquation
    (D : ContinuumExternalFieldDysonData d) (x y : Space d) :
    D.dressedPropagator (x, y) = D.freePropagator (x, y) +
      pointwiseKernelComposition D.freePropagator D.dressedPropagator
        D.background x y :=
  D.equation x y

/-- A vanishing external background reduces the dressed propagator to the free
one. -/
lemma dressed_eq_free_of_background_zero
    (D : ContinuumExternalFieldDysonData d)
    (hB : D.background = fun _ => 0) :
    D.dressedPropagator = D.freePropagator := by
  funext z
  rcases z with ⟨x, y⟩
  rw [D.equation x y, hB]
  simp

end ContinuumExternalFieldDysonData

/-! ## Exact continuum resolvent flow -/

/-- A continuum propagator family satisfying the exact resolvent difference
identity between any two couplings. -/
structure ContinuumResolventFlowData (d : ℕ) where
  /-- Pointwise external background. -/
  background : ContinuumScalarField d
  /-- Propagator at coupling `g`. -/
  propagator : ℂ → Space d × Space d → ℂ
  /-- Exact two-coupling resolvent identity. -/
  difference : ∀ (g h : ℂ) (x y : Space d),
    propagator h (x, y) - propagator g (x, y) =
      (h - g) * pointwiseKernelComposition
        (propagator g) (propagator h) background x y

namespace ContinuumResolventFlowData

variable {d : ℕ}

/-- Difference quotient form of the exact continuum resolvent identity. -/
lemma differenceQuotient
    (D : ContinuumResolventFlowData d)
    (g h : ℂ) (hgh : h ≠ g) (x y : Space d) :
    (D.propagator h (x, y) - D.propagator g (x, y)) / (h - g) =
      pointwiseKernelComposition
        (D.propagator g) (D.propagator h) D.background x y := by
  rw [D.difference g h x y]
  field_simp [sub_ne_zero.mpr hgh]

end ContinuumResolventFlowData

end Physlib.QFT.ScalarGreenFunctions

end
