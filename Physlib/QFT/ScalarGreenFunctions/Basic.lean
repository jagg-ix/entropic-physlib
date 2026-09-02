/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.PathIntegral.MeasureExpectation
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Scalar Green functions and generating functionals

This file formalizes the measure-theoretic and finite-source backbone of
R. J. Rivers, *Path Integral Methods in Quantum Field Theory*, Chapter 1,
"Scalar Green functions and their perturbative solutions".

The repository already provides `MeasurePathIntegralModel`, normalized and
unnormalized expectations, source-coupled partitions, connected generating
functionals, and finite `n`-point correlations. This module specializes those
interfaces to one scalar field and makes Bose symmetry structural by indexing
field insertions with a `Multiset`.

The main constructions correspond to Eqs. (1.14)--(1.20):

* `fieldMonomial` is the product of scalar field insertions;
* `scalarGreenFunction` is the normalized time/path-ordered correlation;
* `scalarGeneratingFunctional` is the source-coupled partition `Z[J]`;
* `sourceMoment` and `formalGeneratingCoefficient` package the formal
  exponential generating series used to extract Green functions.

No continuum product of distributions is introduced here. The field carrier
and path-space measure are inherited from the existing regularized or
measure-theoretic model supplied by the caller.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open scoped BigOperators
open MeasureTheory
open Physlib.QFT.PathIntegral

variable {α X : Type*} [MeasurableSpace α]

/-- Product of scalar-field insertions indexed by a multiset. Using a multiset
makes Bose symmetry independent of an arbitrary ordering of the insertions. -/
def fieldMonomial (field : α → X → ℂ) (xs : Multiset X) : α → ℂ :=
  fun φ => (xs.map (field φ)).prod

@[simp] lemma fieldMonomial_empty (field : α → X → ℂ) :
    fieldMonomial field 0 = fun _ => 1 := by
  funext φ
  simp [fieldMonomial]

@[simp] lemma fieldMonomial_cons
    (field : α → X → ℂ) (x : X) (xs : Multiset X) (φ : α) :
    fieldMonomial field (x ::ₘ xs) φ =
      field φ x * fieldMonomial field xs φ := by
  simp [fieldMonomial]

/-- Unnormalised scalar Green function. -/
def unnormalizedScalarGreenFunction
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ)
    (xs : Multiset X) : ℂ :=
  m.unnormalizedExpectation (fieldMonomial field xs)

/-- Normalized scalar Green function. -/
def scalarGreenFunction
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ)
    (xs : Multiset X) : ℂ :=
  m.normalizedExpectation (fieldMonomial field xs)

/-- The zero-leg unnormalised Green function is the partition functional. -/
lemma unnormalizedScalarGreenFunction_empty
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ) :
    unnormalizedScalarGreenFunction m field 0 = m.partition := by
  unfold unnormalizedScalarGreenFunction
    MeasurePathIntegralModel.unnormalizedExpectation
    MeasurePathIntegralModel.partition
  simp [fieldMonomial]

/-- With a nonzero partition functional, the normalized zero-leg Green
function is one, matching `Z[0] = 1`. -/
@[simp] lemma scalarGreenFunction_empty
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ)
    (hZ : m.partition ≠ 0) :
    scalarGreenFunction m field 0 = 1 := by
  change unnormalizedScalarGreenFunction m field 0 / m.partition = 1
  rw [unnormalizedScalarGreenFunction_empty]
  exact div_self hZ

/-- Two scalar insertions commute inside the field monomial. -/
lemma fieldMonomial_pair_comm (field : α → X → ℂ) (x y : X) :
    fieldMonomial field (x ::ₘ y ::ₘ 0) =
      fieldMonomial field (y ::ₘ x ::ₘ 0) := by
  funext φ
  simp [fieldMonomial, mul_comm]

/-- Bose symmetry of the two-point Green function. Higher permutation
symmetry is built into the multiset index itself. -/
lemma scalarGreenFunction_pair_comm
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ) (x y : X) :
    scalarGreenFunction m field (x ::ₘ y ::ₘ 0) =
      scalarGreenFunction m field (y ::ₘ x ::ₘ 0) := by
  unfold scalarGreenFunction
  rw [fieldMonomial_pair_comm]

section FiniteSource

variable [Fintype X]

/-- Finite regularized source pairing `J · φ = Σ_x J(x) φ(x)`. -/
def scalarSourcePairing
    (field : α → X → ℂ) (J : X → ℂ) (φ : α) : ℂ :=
  ∑ x, J x * field φ x

@[simp] lemma scalarSourcePairing_zero
    (field : α → X → ℂ) (φ : α) :
    scalarSourcePairing field (fun _ => 0) φ = 0 := by
  simp [scalarSourcePairing]

lemma scalarSourcePairing_add
    (field : α → X → ℂ) (J K : X → ℂ) (φ : α) :
    scalarSourcePairing field (fun x => J x + K x) φ =
      scalarSourcePairing field J φ + scalarSourcePairing field K φ := by
  simp [scalarSourcePairing, add_mul, Finset.sum_add_distrib]

lemma scalarSourcePairing_const_mul
    (field : α → X → ℂ) (c : ℂ) (J : X → ℂ) (φ : α) :
    scalarSourcePairing field (fun x => c * J x) φ =
      c * scalarSourcePairing field J φ := by
  simp [scalarSourcePairing, mul_assoc, Finset.mul_sum]

/-- Source-coupled scalar generating functional `Z[J]`. -/
def scalarGeneratingFunctional
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ)
    (J : X → ℂ) : ℂ :=
  m.sourceCoupledPartition (scalarSourcePairing field J)

/-- Connected scalar generating functional `W[J] = log Z[J]`. -/
def scalarConnectedGeneratingFunctional
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ)
    (J : X → ℂ) : ℂ :=
  Complex.log (scalarGeneratingFunctional m field J)

/-- At zero source the scalar generating functional is the partition
functional. -/
@[simp] lemma scalarGeneratingFunctional_zero
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ) :
    scalarGeneratingFunctional m field (fun _ => 0) = m.partition := by
  unfold scalarGeneratingFunctional
  have hpair : scalarSourcePairing field (fun _ => 0) = fun _ => 0 := by
    funext φ
    exact scalarSourcePairing_zero field φ
  rw [hpair, m.sourceCoupledPartition_zero]

/-- At zero source the connected functional is `log Z`. -/
@[simp] lemma scalarConnectedGeneratingFunctional_zero
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ) :
    scalarConnectedGeneratingFunctional m field (fun _ => 0) =
      Complex.log m.partition := by
  simp [scalarConnectedGeneratingFunctional]

/-- The source-profile moment of order `n`, obtained by summing the `n`-point
correlation over all finite regularized insertion positions. -/
def sourceMoment
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ)
    (J : X → ℂ) (n : ℕ) : ℂ :=
  ∑ xs : Fin n → X,
    (∏ i : Fin n, J (xs i)) *
      m.nPointCorrelation n (fun i φ => field φ (xs i))

/-- Formal coefficient of the scalar-source generating series. This is the
finite-source version of the coefficient in Eq. (1.16), including the factor
`(i/ℏ)^n / n!`. -/
def formalGeneratingCoefficient
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ)
    (J : X → ℂ) (n : ℕ) : ℂ :=
  ((Complex.I / (m.hbar : ℂ)) ^ n / (n.factorial : ℂ)) *
    sourceMoment m field J n

/-- Finite truncation of the formal Green-function generating series. No
convergence of the infinite perturbative series is assumed. -/
def truncatedFormalGeneratingFunctional
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ)
    (J : X → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), formalGeneratingCoefficient m field J n

lemma truncatedFormalGeneratingFunctional_succ
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ)
    (J : X → ℂ) (N : ℕ) :
    truncatedFormalGeneratingFunctional m field J (N + 1) =
      truncatedFormalGeneratingFunctional m field J N +
        formalGeneratingCoefficient m field J (N + 1) := by
  unfold truncatedFormalGeneratingFunctional
  rw [Finset.sum_range_succ]

end FiniteSource

end Physlib.QFT.ScalarGreenFunctions

end
