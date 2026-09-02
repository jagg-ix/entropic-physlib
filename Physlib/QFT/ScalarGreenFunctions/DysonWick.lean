/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.SourceJet
public import Physlib.QFT.PerturbationTheory.WickAlgebra.WicksTheorem

/-!
# The Dyson--Wick interaction-operator expansion

Rivers Eq. (1.53) constructs the interacting generating functional formally as

`Z = N exp[-i F[-i hbar δ/δJ] / hbar] Z₀`.

For the quartic scalar interaction, the source operator inserts four equal
source derivatives and sums over the interaction point. Since a source jet is
indexed by a multiset, commutativity of functional derivatives and Bose
symmetry are built into its type.

This file formalizes:

* the quartic source insertion `δ⁴/δJ(x)⁴`;
* the summed quartic interaction operator;
* repeated interaction-operator application;
* finite exponential truncations with coefficient `(-i/hbar)^n / n!`;
* normalization by the empty-source coefficient;
* distribution of every Dyson coefficient over the existing Wick-contraction
  expansion.

The construction is formal. It does not assume convergence of the infinite
Dyson series, matching Rivers' explicit distinction between a uniquely fixed
formal series and a summable function.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open scoped BigOperators
open FieldSpecification

/-- Add four coincident source derivatives at the interaction point `x`. -/
def quarticSourceInsertion {X : Type*}
    (x : X) (xs : Multiset X) : Multiset X :=
  Multiset.replicate 4 x + xs

@[simp] lemma card_quarticSourceInsertion {X : Type*}
    (x : X) (xs : Multiset X) :
    (quarticSourceInsertion x xs).card = 4 + xs.card := by
  unfold quarticSourceInsertion
  rw [Multiset.card_add, Multiset.card_replicate]

/-- The finite regularized quartic interaction operator
`Σ_x δ⁴/δJ(x)⁴` acting on a source jet. -/
def quarticSourceOperator (X : Type*) [Fintype X] :
    SourceJet X →ₗ[ℂ] SourceJet X where
  toFun Z := fun xs => ∑ x, Z (quarticSourceInsertion x xs)
  map_add' Z W := by
    funext xs
    simp [Finset.sum_add_distrib]
  map_smul' c Z := by
    funext xs
    simp [Finset.mul_sum]

@[simp] lemma quarticSourceOperator_apply
    {X : Type*} [Fintype X] (Z : SourceJet X) (xs : Multiset X) :
    quarticSourceOperator X Z xs =
      ∑ x, Z (quarticSourceInsertion x xs) :=
  rfl

/-- Repeated application of a linear interaction operator. -/
def iteratedInteraction {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (v : V) : ℕ → V
  | 0 => v
  | n + 1 => T (iteratedInteraction T v n)

@[simp] lemma iteratedInteraction_zero
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (v : V) :
    iteratedInteraction T v 0 = v :=
  rfl

@[simp] lemma iteratedInteraction_succ
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (v : V) (n : ℕ) :
    iteratedInteraction T v (n + 1) =
      T (iteratedInteraction T v n) :=
  rfl

/-- The order-`n` coefficient of the formal Dyson interaction exponential. -/
def dysonWickCoefficient
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (hbar : ℝ) (T : V →ₗ[ℂ] V) (v₀ : V) (n : ℕ) : V :=
  (((-Complex.I) / (hbar : ℂ)) ^ n / (n.factorial : ℂ)) •
    iteratedInteraction T v₀ n

@[simp] lemma dysonWickCoefficient_zero
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (hbar : ℝ) (T : V →ₗ[ℂ] V) (v₀ : V) :
    dysonWickCoefficient hbar T v₀ 0 = v₀ := by
  simp [dysonWickCoefficient]

/-- Finite truncation of the interaction-operator exponential. -/
def dysonWickTruncation
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (hbar : ℝ) (T : V →ₗ[ℂ] V) (v₀ : V) (N : ℕ) : V :=
  ∑ n ∈ Finset.range (N + 1), dysonWickCoefficient hbar T v₀ n

lemma dysonWickTruncation_succ
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (hbar : ℝ) (T : V →ₗ[ℂ] V) (v₀ : V) (N : ℕ) :
    dysonWickTruncation hbar T v₀ (N + 1) =
      dysonWickTruncation hbar T v₀ N +
        dysonWickCoefficient hbar T v₀ (N + 1) := by
  unfold dysonWickTruncation
  rw [Finset.sum_range_succ]

/-- The quartic scalar specialization of the Dyson--Wick truncation. -/
def quarticDysonWickTruncation
    {X : Type*} [Fintype X]
    (hbar : ℝ) (Z₀ : SourceJet X) (N : ℕ) : SourceJet X :=
  dysonWickTruncation hbar (quarticSourceOperator X) Z₀ N

/-- Normalize a source jet by its empty-source coefficient. -/
def normalizeSourceJet {X : Type*} (Z : SourceJet X) : SourceJet X :=
  fun xs => Z xs / Z 0

@[simp] lemma normalizeSourceJet_empty
    {X : Type*} (Z : SourceJet X) (hZ : Z 0 ≠ 0) :
    normalizeSourceJet Z 0 = 1 := by
  exact div_self hZ

/-- Normalized finite quartic Dyson--Wick truncation. -/
def normalizedQuarticDysonWickTruncation
    {X : Type*} [Fintype X]
    (hbar : ℝ) (Z₀ : SourceJet X) (N : ℕ) : SourceJet X :=
  normalizeSourceJet (quarticDysonWickTruncation hbar Z₀ N)

@[simp] lemma normalizedQuarticDysonWickTruncation_empty
    {X : Type*} [Fintype X]
    (hbar : ℝ) (Z₀ : SourceJet X) (N : ℕ)
    (hZ : quarticDysonWickTruncation hbar Z₀ N 0 ≠ 0) :
    normalizedQuarticDysonWickTruncation hbar Z₀ N 0 = 1 :=
  normalizeSourceJet_empty _ hZ

/-- Any scalar Dyson coefficient distributes termwise across the complete
Wick-contraction expansion already proved in Physlib. -/
lemma dysonCoefficient_smul_wicks_theorem
    {𝓕 : FieldSpecification} (c : ℂ) (φs : List 𝓕.FieldOp) :
    c • WickAlgebra.timeOrder (WickAlgebra.ofFieldOpList φs) =
      ∑ φsΛ : WickContraction φs.length, c • φsΛ.wickTerm := by
  rw [wicks_theorem φs, Finset.smul_sum]

/-- The explicit order-`n` Dyson coefficient multiplies every Wick contraction
uniformly. -/
lemma dysonOrder_smul_wicks_theorem
    {𝓕 : FieldSpecification} (hbar : ℝ) (n : ℕ)
    (φs : List 𝓕.FieldOp) :
    (((-Complex.I) / (hbar : ℂ)) ^ n / (n.factorial : ℂ)) •
        WickAlgebra.timeOrder (WickAlgebra.ofFieldOpList φs) =
      ∑ φsΛ : WickContraction φs.length,
        (((-Complex.I) / (hbar : ℂ)) ^ n / (n.factorial : ℂ)) •
          φsΛ.wickTerm :=
  dysonCoefficient_smul_wicks_theorem _ φs

end Physlib.QFT.ScalarGreenFunctions

end
