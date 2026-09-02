/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.Basic

/-!
# Scalar Dyson--Schwinger hierarchy

This file gives a finite regularized form of Rivers' scalar Dyson--Schwinger
hierarchy, Eqs. (1.28)--(1.36).  The regularized spacetime index `X` is finite;
continuum kernels can subsequently be obtained through the repository's
existing approximation and dominated-convergence interfaces.

For a quartic interaction `U(A) = g A^4 / 4!`, the hierarchy has the form

`K_x G_(n+1) + (g/3!) G_(n+3) = -i hbar * contact`,

where the contact term removes one external insertion whenever its point
coincides with `x`.  The recursive definition `contactTerm` retains the
remaining insertions exactly and therefore represents the full sum of delta
contacts in Eq. (1.32d).

The file also records the parity bookkeeping behind the decoupling of even and
odd Green functions: the `(n+1)`- and `(n+3)`-point terms have the same parity,
and each nonzero contact term has order `(n-1)`, again of that parity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open scoped BigOperators

/-- A scalar Green hierarchy indexed by ordered external insertions. -/
abbrev GreenHierarchy (X : Type*) := List X → ℂ

/-- A regularized two-point kinetic kernel. -/
abbrev KineticKernel (X : Type*) := X → X → ℂ

/-- Application of a finite regularized kinetic kernel to the first leg of a
Green function. -/
def kineticInsertion {X : Type*} [Fintype X]
    (K : KineticKernel X) (G : GreenHierarchy X) (x : X) (xs : List X) : ℂ :=
  ∑ y, K x y * G (y :: xs)

/-- Quartic interaction insertion `G_(n+3)(x,x,x,...)`. -/
def quarticInsertion {X : Type*}
    (G : GreenHierarchy X) (x : X) (xs : List X) : ℂ :=
  G (x :: x :: x :: xs)

/-- Contact term in the scalar Dyson--Schwinger hierarchy.

For `xs = [x₁,...,xₙ]`, this is
`Σ_j δ(x,x_j) G(xs with x_j removed)`.  The recursive hierarchy passed to the
next call remembers the preceding insertions, so removing a later element does
not discard the prefix. -/
def contactTerm {X : Type*} [DecidableEq X]
    (G : GreenHierarchy X) (x : X) : List X → ℂ
  | [] => 0
  | y :: ys =>
      (if x = y then G ys else 0) +
        contactTerm (fun zs => G (y :: zs)) x ys

@[simp] lemma contactTerm_nil {X : Type*} [DecidableEq X]
    (G : GreenHierarchy X) (x : X) :
    contactTerm G x [] = 0 := rfl

@[simp] lemma contactTerm_singleton {X : Type*} [DecidableEq X]
    (G : GreenHierarchy X) (x y : X) :
    contactTerm G x [y] = if x = y then G [] else 0 := by
  simp [contactTerm]

@[simp] lemma contactTerm_pair {X : Type*} [DecidableEq X]
    (G : GreenHierarchy X) (x y z : X) :
    contactTerm G x [y, z] =
      (if x = y then G [z] else 0) +
        (if x = z then G [y] else 0) := by
  simp [contactTerm]

/-- Finite regularized data satisfying the quartic scalar Dyson--Schwinger
hierarchy.  `kinetic` may already include the mass term; `massSq` is retained
separately to mirror Rivers' `Box + m²` notation. -/
structure QuarticDysonSchwingerData (X : Type*) [Fintype X] [DecidableEq X] where
  /-- Regularized kinetic part of the inverse free propagator. -/
  kinetic : KineticKernel X
  /-- Scalar mass-square coefficient. -/
  massSq : ℂ
  /-- Quartic coupling `g`. -/
  coupling : ℂ
  /-- Planck constant. -/
  hbar : ℂ
  /-- Full Green-function hierarchy. -/
  green : GreenHierarchy X
  /-- Bose symmetry of the Green functions. -/
  bose : ∀ xs ys : List X, xs.Perm ys → green xs = green ys
  /-- The quartic Dyson--Schwinger hierarchy. -/
  equation : ∀ (x : X) (xs : List X),
    kineticInsertion kinetic green x xs + massSq * green (x :: xs) +
        (coupling / 6) * quarticInsertion green x xs =
      -(Complex.I * hbar) * contactTerm green x xs

namespace QuarticDysonSchwingerData

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Named restatement of the complete hierarchy. -/
lemma hierarchy (D : QuarticDysonSchwingerData X) (x : X) (xs : List X) :
    kineticInsertion D.kinetic D.green x xs + D.massSq * D.green (x :: xs) +
        (D.coupling / 6) * quarticInsertion D.green x xs =
      -(Complex.I * D.hbar) * contactTerm D.green x xs :=
  D.equation x xs

/-- One-leg equation, Rivers Eq. (1.32a). -/
lemma oneLegEquation (D : QuarticDysonSchwingerData X) (x : X) :
    kineticInsertion D.kinetic D.green x [] + D.massSq * D.green [x] +
        (D.coupling / 6) * D.green [x, x, x] = 0 := by
  simpa [quarticInsertion] using D.equation x []

/-- Two-leg equation, including the canonical contact term of Eq. (1.32b). -/
lemma twoLegEquation (D : QuarticDysonSchwingerData X) (x y : X) :
    kineticInsertion D.kinetic D.green x [y] + D.massSq * D.green [x, y] +
        (D.coupling / 6) * D.green [x, x, x, y] =
      -(Complex.I * D.hbar) * (if x = y then D.green [] else 0) := by
  simpa [quarticInsertion] using D.equation x [y]

/-- Three-leg equation, with both possible contact removals. -/
lemma threeLegEquation (D : QuarticDysonSchwingerData X) (x y z : X) :
    kineticInsertion D.kinetic D.green x [y, z] + D.massSq * D.green [x, y, z] +
        (D.coupling / 6) * D.green [x, x, x, y, z] =
      -(Complex.I * D.hbar) *
        ((if x = y then D.green [z] else 0) +
          (if x = z then D.green [y] else 0)) := by
  simpa [quarticInsertion] using D.equation x [y, z]

/-- Bose symmetry is available at every order. -/
lemma green_eq_of_perm (D : QuarticDysonSchwingerData X)
    (xs ys : List X) (h : xs.Perm ys) : D.green xs = D.green ys :=
  D.bose xs ys h

/-- The ordinary and quartic terms in the hierarchy have equal parity. -/
lemma interactionOrder_sameParity (xs : List X) (x : X) :
    (x :: xs).length % 2 = (x :: x :: x :: xs).length % 2 := by
  simp
  omega

/-- For a nonempty external list, the Green function appearing in a contact
term has order `n-1`, which has the same parity as the `n+1` ordinary term. -/
lemma contactOrder_sameParity (n : ℕ) (hn : 0 < n) :
    (n + 1) % 2 = (n - 1) % 2 := by
  omega

/-- The three orders coupled by the quartic hierarchy all have one common
parity.  This is the combinatorial reason the even and odd sectors decouple. -/
lemma hierarchyOrders_sameParity (n : ℕ) (hn : 0 < n) :
    (n + 1) % 2 = (n + 3) % 2 ∧
      (n + 1) % 2 = (n - 1) % 2 := by
  constructor <;> omega

end QuarticDysonSchwingerData

end Physlib.QFT.ScalarGreenFunctions

end
