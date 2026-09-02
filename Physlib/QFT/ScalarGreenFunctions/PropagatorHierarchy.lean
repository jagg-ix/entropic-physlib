/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.ContinuumDysonSchwinger
public import Physlib.QFT.ScalarGreenFunctions.FreeTheory

/-!
# Propagator form of the scalar Dyson--Schwinger hierarchy

After choosing the causal inverse `K⁻¹ = -Delta_F`, Rivers rewrites the
Dyson--Schwinger hierarchy as a propagator recursion: an active external line
either contracts with an existing external insertion or reaches a quartic
vertex and creates three new lines.

This file formalizes that diagrammatic equation at two levels:

* a finite regularized index type, where the interaction convolution is a
  finite sum;
* continuum `Space d`, where the interaction convolution is a Bochner integral.

The recursive contact convolution remembers every preceding insertion, so it
removes exactly one external leg and retains the remaining order.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open scoped BigOperators
open MeasureTheory

/-! ## Finite regularized propagator hierarchy -/

/-- Free-propagator convolution with all possible external contact removals. -/
def propagatorContactTerm {X : Type*}
    (Delta : X → X → ℂ) (G : List X → ℂ) (x : X) : List X → ℂ
  | [] => 0
  | y :: ys =>
      Delta x y * G ys +
        propagatorContactTerm Delta (fun zs => G (y :: zs)) x ys

@[simp] lemma propagatorContactTerm_nil {X : Type*}
    (Delta : X → X → ℂ) (G : List X → ℂ) (x : X) :
    propagatorContactTerm Delta G x [] = 0 :=
  rfl

@[simp] lemma propagatorContactTerm_singleton {X : Type*}
    (Delta : X → X → ℂ) (G : List X → ℂ) (x y : X) :
    propagatorContactTerm Delta G x [y] = Delta x y * G [] := by
  simp [propagatorContactTerm]

@[simp] lemma propagatorContactTerm_pair {X : Type*}
    (Delta : X → X → ℂ) (G : List X → ℂ) (x y z : X) :
    propagatorContactTerm Delta G x [y, z] =
      Delta x y * G [z] + Delta x z * G [y] := by
  simp [propagatorContactTerm]

/-- Finite quartic interaction convolution through the free propagator. -/
def finiteQuarticPropagatorInsertion {X : Type*} [Fintype X]
    (Delta : X → X → ℂ) (G : List X → ℂ)
    (x : X) (xs : List X) : ℂ :=
  ∑ y, Delta x y * G (y :: y :: y :: xs)

/-- Finite regularized propagator-form Dyson--Schwinger hierarchy. -/
structure PropagatorDysonSchwingerData
    (X : Type*) [Fintype X] where
  /-- Causal free propagator. -/
  freePropagator : X → X → ℂ
  /-- Full Green hierarchy. -/
  green : List X → ℂ
  /-- Quartic coupling. -/
  coupling : ℂ
  /-- Planck constant. -/
  hbar : ℂ
  /-- Bose symmetry. -/
  bose : ∀ xs ys : List X, xs.Perm ys → green xs = green ys
  /-- Propagator-form hierarchy. -/
  equation : ∀ (x : X) (xs : List X),
    green (x :: xs) =
      Complex.I * hbar *
          propagatorContactTerm freePropagator green x xs +
        (coupling / 6) *
          finiteQuarticPropagatorInsertion freePropagator green x xs

namespace PropagatorDysonSchwingerData

variable {X : Type*} [Fintype X]

/-- One-leg equation: only the quartic insertion remains. -/
lemma oneLegEquation
    (D : PropagatorDysonSchwingerData X) (x : X) :
    D.green [x] =
      (D.coupling / 6) *
        finiteQuarticPropagatorInsertion
          D.freePropagator D.green x [] := by
  simpa using D.equation x []

/-- Two-leg equation: the free propagator appears as the single contact term. -/
lemma twoLegEquation
    (D : PropagatorDysonSchwingerData X) (x y : X) :
    D.green [x, y] =
      Complex.I * D.hbar * (D.freePropagator x y * D.green []) +
        (D.coupling / 6) *
          finiteQuarticPropagatorInsertion
            D.freePropagator D.green x [y] := by
  simpa using D.equation x [y]

/-- Three-leg equation with both free-propagator contact contractions. -/
lemma threeLegEquation
    (D : PropagatorDysonSchwingerData X) (x y z : X) :
    D.green [x, y, z] =
      Complex.I * D.hbar *
          (D.freePropagator x y * D.green [z] +
            D.freePropagator x z * D.green [y]) +
        (D.coupling / 6) *
          finiteQuarticPropagatorInsertion
            D.freePropagator D.green x [y, z] := by
  simpa using D.equation x [y, z]

end PropagatorDysonSchwingerData

/-! ## Continuum propagator hierarchy -/

/-- Continuum free-propagator contact convolution. -/
def continuumPropagatorContactTerm {d : ℕ}
    (Delta : Space d × Space d → ℂ)
    (G : List (Space d) → ℂ) (x : Space d) : List (Space d) → ℂ
  | [] => 0
  | y :: ys =>
      Delta (x, y) * G ys +
        continuumPropagatorContactTerm Delta
          (fun zs => G (y :: zs)) x ys

@[simp] lemma continuumPropagatorContactTerm_singleton {d : ℕ}
    (Delta : Space d × Space d → ℂ)
    (G : List (Space d) → ℂ) (x y : Space d) :
    continuumPropagatorContactTerm Delta G x [y] =
      Delta (x, y) * G [] := by
  simp [continuumPropagatorContactTerm]

@[simp] lemma continuumPropagatorContactTerm_pair {d : ℕ}
    (Delta : Space d × Space d → ℂ)
    (G : List (Space d) → ℂ) (x y z : Space d) :
    continuumPropagatorContactTerm Delta G x [y, z] =
      Delta (x, y) * G [z] + Delta (x, z) * G [y] := by
  simp [continuumPropagatorContactTerm]

/-- Continuum quartic insertion convolved with the causal free propagator. -/
def continuumQuarticPropagatorInsertion {d : ℕ}
    (Delta : Space d × Space d → ℂ)
    (G : List (Space d) → ℂ)
    (x : Space d) (xs : List (Space d)) : ℂ :=
  ∫ y, Delta (x, y) * G (y :: y :: y :: xs)

/-- Continuum propagator-form Dyson--Schwinger hierarchy. -/
structure ContinuumPropagatorDysonSchwingerData (d : ℕ) where
  /-- Causal free propagator kernel. -/
  freePropagator : Space d × Space d → ℂ
  /-- Full continuum Green hierarchy. -/
  green : List (Space d) → ℂ
  /-- Quartic coupling. -/
  coupling : ℂ
  /-- Planck constant. -/
  hbar : ℂ
  /-- Bose symmetry. -/
  bose : ∀ xs ys : List (Space d), xs.Perm ys → green xs = green ys
  /-- Continuum propagator hierarchy. -/
  equation : ∀ (x : Space d) (xs : List (Space d)),
    green (x :: xs) =
      Complex.I * hbar *
          continuumPropagatorContactTerm freePropagator green x xs +
        (coupling / 6) *
          continuumQuarticPropagatorInsertion
            freePropagator green x xs

namespace ContinuumPropagatorDysonSchwingerData

variable {d : ℕ}

/-- Continuum one-leg equation. -/
lemma oneLegEquation
    (D : ContinuumPropagatorDysonSchwingerData d) (x : Space d) :
    D.green [x] =
      (D.coupling / 6) *
        continuumQuarticPropagatorInsertion
          D.freePropagator D.green x [] := by
  simpa [continuumPropagatorContactTerm] using D.equation x []

/-- Continuum two-leg equation with the free propagator as its contact part. -/
lemma twoLegEquation
    (D : ContinuumPropagatorDysonSchwingerData d)
    (x y : Space d) :
    D.green [x, y] =
      Complex.I * D.hbar *
          (D.freePropagator (x, y) * D.green []) +
        (D.coupling / 6) *
          continuumQuarticPropagatorInsertion
            D.freePropagator D.green x [y] := by
  simpa using D.equation x [y]

/-- Continuum three-leg equation with both contact contractions. -/
lemma threeLegEquation
    (D : ContinuumPropagatorDysonSchwingerData d)
    (x y z : Space d) :
    D.green [x, y, z] =
      Complex.I * D.hbar *
          (D.freePropagator (x, y) * D.green [z] +
            D.freePropagator (x, z) * D.green [y]) +
        (D.coupling / 6) *
          continuumQuarticPropagatorInsertion
            D.freePropagator D.green x [y, z] := by
  simpa using D.equation x [y, z]

end ContinuumPropagatorDysonSchwingerData

end Physlib.QFT.ScalarGreenFunctions

end
