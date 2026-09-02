/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.PerturbativeSeries
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.NoncommRing

/-!
# Scalar fields coupled to an external field

This file formalizes the finite-dimensional or regularized content of Rivers,
Section 1.6 and the complex-field extension in Section 1.7.

The central object is a family

`A(g) = K + g B`, `Delta(g) = -A(g)⁻¹`,

where `B` is an external scalar background. From two-sided inverse identities
we prove:

* the Dyson resolvent equation `Delta = Delta₀ + Delta₀(gB)Delta`;
* the exact two-coupling resolvent identity
  `Delta(h)-Delta(g)=Delta(g)((h-g)B)Delta(h)`, whose differential limit is
  Eq. (1.69);
* the finite Neumann-series remainder identity;
* determinant-ratio and vacuum-normalization identities;
* the factor-of-two relation between real- and complex-scalar loop actions.

All determinants and inverses here are finite regularizations. The repository's
existing approximation and path-integral modules provide the later continuum
interfaces.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open scoped BigOperators Matrix

/-- Finite regularized external-field propagator data at one coupling. -/
structure ExternalFieldResolventData (n : ℕ) where
  /-- Free inverse propagator `K`. -/
  kinetic : Matrix (Fin n) (Fin n) ℂ
  /-- Multiplication or background operator `B`. -/
  background : Matrix (Fin n) (Fin n) ℂ
  /-- External coupling. -/
  coupling : ℂ
  /-- Free propagator `Delta₀ = -K⁻¹`. -/
  freePropagator : Matrix (Fin n) (Fin n) ℂ
  /-- Dressed propagator `Delta = -(K+gB)⁻¹`. -/
  dressedPropagator : Matrix (Fin n) (Fin n) ℂ
  /-- Right inverse equation for the free propagator. -/
  free_right_inverse : freePropagator * kinetic = -1
  /-- Dressed inverse equation. -/
  dressed_left_inverse :
    (kinetic + coupling • background) * dressedPropagator = -1

namespace ExternalFieldResolventData

variable {n : ℕ}

/-- The external-field insertion `gB`. -/
def interaction (D : ExternalFieldResolventData n) :
    Matrix (Fin n) (Fin n) ℂ :=
  D.coupling • D.background

/-- Finite Dyson equation for the external-field propagator,
`Delta = Delta₀ + Delta₀(gB)Delta`. -/
lemma dysonEquation (D : ExternalFieldResolventData n) :
    D.dressedPropagator = D.freePropagator +
      D.freePropagator * D.interaction * D.dressedPropagator := by
  have hmul :=
    congrArg (fun M => D.freePropagator * M) D.dressed_left_inverse
  have hexp :
      D.freePropagator * ((D.kinetic + D.coupling • D.background) * D.dressedPropagator) =
        -D.dressedPropagator +
          D.freePropagator * D.interaction * D.dressedPropagator := by
    unfold interaction
    rw [← Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, D.free_right_inverse, neg_one_mul]
  have hraw :
      -D.dressedPropagator +
          D.freePropagator * D.interaction * D.dressedPropagator =
        -D.freePropagator := by
    rw [← hexp, hmul, mul_neg_one]
  have hneg := congrArg Neg.neg hraw
  have hsub :
      D.dressedPropagator -
          D.freePropagator * D.interaction * D.dressedPropagator =
        D.freePropagator := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
  exact (sub_eq_iff_eq_add).mp hsub

end ExternalFieldResolventData

/-- A two-sided family of finite external-field resolvents. -/
structure ExternalFieldResolventFamily (n : ℕ) where
  kinetic : Matrix (Fin n) (Fin n) ℂ
  background : Matrix (Fin n) (Fin n) ℂ
  propagator : ℂ → Matrix (Fin n) (Fin n) ℂ
  left_inverse : ∀ g,
    (kinetic + g • background) * propagator g = -1
  right_inverse : ∀ g,
    propagator g * (kinetic + g • background) = -1

namespace ExternalFieldResolventFamily

variable {n : ℕ}

/-- The inverse operator at coupling `g`. -/
def operator (F : ExternalFieldResolventFamily n) (g : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  F.kinetic + g • F.background

lemma operator_sub (F : ExternalFieldResolventFamily n) (g h : ℂ) :
    F.operator h - F.operator g = (h - g) • F.background := by
  ext i j
  simp [operator]
  ring

/-- Exact resolvent identity. Dividing by `h-g` and taking `h → g` yields the
finite regularized version of `dDelta/dg = Delta B Delta`, Eq. (1.69). -/
lemma resolventDifference
    (F : ExternalFieldResolventFamily n) (g h : ℂ) :
    F.propagator h - F.propagator g =
      F.propagator g * ((h - g) • F.background) * F.propagator h := by
  rw [← F.operator_sub g h]
  symm
  calc
    F.propagator g * (F.operator h - F.operator g) * F.propagator h =
        F.propagator g * F.operator h * F.propagator h -
          F.propagator g * F.operator g * F.propagator h := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = F.propagator h - F.propagator g := by
      simp only [operator]
      rw [Matrix.mul_assoc, F.left_inverse, F.right_inverse]
      simp [sub_eq_add_neg, add_comm]

end ExternalFieldResolventFamily

/-! ## Neumann expansion -/

/-- Finite Neumann sum `1 + A + ... + Aᴺ`. -/
def neumannPartial {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ k ∈ Finset.range (N + 1), A ^ k

lemma neumannPartial_succ {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) :
    neumannPartial A (N + 1) = neumannPartial A N + A ^ (N + 1) := by
  unfold neumannPartial
  rw [Finset.sum_range_succ]

/-- Exact finite Neumann remainder identity. -/
lemma one_sub_mul_neumannPartial {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) :
    (1 - A) * neumannPartial A N = 1 - A ^ (N + 1) := by
  induction N with
  | zero => simp [neumannPartial]
  | succ N ih =>
      rw [neumannPartial_succ, Matrix.mul_add, ih]
      rw [Matrix.sub_mul, Matrix.one_mul]
      rw [← pow_succ']
      abel

/-! ## Determinants, vacuum factors, and normalization -/

/-- Finite determinant ratio `det K / det(K+gB)`. -/
def externalDeterminantRatio {n : ℕ}
    (kinetic background : Matrix (Fin n) (Fin n) ℂ) (g : ℂ) : ℂ :=
  kinetic.det / (kinetic + g • background).det

@[simp] lemma externalDeterminantRatio_zero {n : ℕ}
    (kinetic background : Matrix (Fin n) (Fin n) ℂ)
    (hdet : kinetic.det ≠ 0) :
    externalDeterminantRatio kinetic background 0 = 1 := by
  simp [externalDeterminantRatio, hdet]

/-- Unnormalised external-field generating functional: a vacuum-loop factor
multiplying the open-line or source factor. -/
def externalUnnormalizedGenerating
    (vacuumFactor : ℂ) (openLineExponent : ℂ) : ℂ :=
  vacuumFactor * Complex.exp openLineExponent

/-- Normalization by the zero-source vacuum functional. -/
def externalNormalizedGenerating
    (vacuumFactor : ℂ) (openLineExponent : ℂ) : ℂ :=
  externalUnnormalizedGenerating vacuumFactor openLineExponent /
    externalUnnormalizedGenerating vacuumFactor 0

/-- Vacuum-to-vacuum loops cancel from normalized Green-function generation. -/
lemma externalNormalizedGenerating_eq_exp
    (vacuumFactor openLineExponent : ℂ) (hvac : vacuumFactor ≠ 0) :
    externalNormalizedGenerating vacuumFactor openLineExponent =
      Complex.exp openLineExponent := by
  unfold externalNormalizedGenerating externalUnnormalizedGenerating
  simp [hvac]

/-- Real-scalar one-loop trace-log action, with coefficient `1/2`. -/
def realScalarLoopAction (traceLog : ℂ) : ℂ :=
  (1 / 2 : ℂ) * traceLog

/-- Complex-scalar one-loop trace-log action. -/
def complexScalarLoopAction (traceLog : ℂ) : ℂ :=
  traceLog

/-- A complex scalar contains two real scalar components, so its loop action is
twice the real-scalar loop action. -/
lemma complexScalarLoopAction_eq_two_real (traceLog : ℂ) :
    complexScalarLoopAction traceLog =
      2 * realScalarLoopAction traceLog := by
  unfold complexScalarLoopAction realScalarLoopAction
  ring

end Physlib.QFT.ScalarGreenFunctions

end
