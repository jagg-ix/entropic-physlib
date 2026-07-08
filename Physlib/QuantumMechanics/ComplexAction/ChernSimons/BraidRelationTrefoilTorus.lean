/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.FinCases

/-!
# The braid (Artin) relation, the half/full twist, and the trefoil torus braid word

The **trefoil knot** is the `(2,3)` torus knot. Algebraically it is the closure of a braid: `σ₁³` in the
`2`-strand braid group `B₂`, equivalently `(σ₁σ₂)²` in `B₃`. The governing relation is the **Artin (braid)
relation** `σ₁σ₂σ₁ = σ₂σ₁σ₂` — the Yang–Baxter / Reidemeister-III move that is also the defining relation of
`B₃`. This file formalizes the group-theoretic content of that structure (Mathlib has no braid group, so the
relation is taken as a hypothesis on two elements of any monoid):

* **The half-twist** `Δ = σ₁σ₂σ₁ = σ₂σ₁σ₂` (`halfTwist`); under the braid relation it conjugates the
  generators into each other — `Δσ₁ = σ₂Δ` (`halfTwist_conj_a`), `Δσ₂ = σ₁Δ` (`halfTwist_conj_b`).
* **The full twist** `Δ² = (σ₁σ₂)³` (`fullTwist`, `fullTwist_eq_halfTwist_sq`): the generator of the centre
  of `B₃`. `fullTwist_central_a` / `fullTwist_central_b`: it **commutes** with both generators.
* **The trefoil braid word** `(σ₁σ₂)²` (the `(3,2)` torus / trefoil): `trefoilBraidWord_eq` rewrites it as
  `σ₁²σ₂σ₁` using the braid relation.

These are exactly the identities that make the trefoil's `B₃` presentation consistent; the knot *topology*
itself is not formalized (Mathlib has no knot theory).

## References

* Artin braid relation / `B₃` presentation; trefoil `= T(2,3)` torus knot `=` closure of `σ₁³` (`B₂`) `=`
  closure of `(σ₁σ₂)²` (`B₃`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.BraidRelationTrefoilTorus

variable {G : Type*} [Monoid G] {a b : G}

/-- **The half-twist** `Δ = σ₁σ₂σ₁` of `B₃`. Under the braid relation it also equals `σ₂σ₁σ₂`. -/
def halfTwist (a b : G) : G := a * b * a

/-- **The full twist** `Δ² = (σ₁σ₂)³`, the generator of the centre of `B₃`. -/
def fullTwist (a b : G) : G := (a * b) ^ 3

/-- **[The half-twist has two forms]** `Δ = σ₁σ₂σ₁ = σ₂σ₁σ₂` — this *is* the braid (Artin) relation. -/
theorem halfTwist_eq_symm (h : a * b * a = b * a * b) : halfTwist a b = b * a * b := h

/-- **[Half-twist conjugation, `Δσ₁ = σ₂Δ`]** the half-twist conjugates the first generator into the second. -/
theorem halfTwist_conj_a (h : a * b * a = b * a * b) : halfTwist a b * a = b * halfTwist a b := by
  unfold halfTwist
  nth_rewrite 1 [h]
  simp only [mul_assoc]

/-- **[Half-twist conjugation, `Δσ₂ = σ₁Δ`]** the half-twist conjugates the second generator into the first. -/
theorem halfTwist_conj_b (h : a * b * a = b * a * b) : halfTwist a b * b = a * halfTwist a b := by
  unfold halfTwist
  rw [show a * b * a * b = a * (b * a * b) from by simp only [mul_assoc], ← h]

/-- **[Full twist = square of half-twist]** `(σ₁σ₂)³ = Δ²`. -/
theorem fullTwist_eq_halfTwist_sq (h : a * b * a = b * a * b) :
    fullTwist a b = (halfTwist a b) ^ 2 := by
  unfold fullTwist halfTwist
  rw [pow_two]
  nth_rewrite 2 [h]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

/-- **[The full twist is central, `Δ²σ₁ = σ₁Δ²`]** the full twist commutes with the first generator. -/
theorem fullTwist_central_a (h : a * b * a = b * a * b) : fullTwist a b * a = a * fullTwist a b := by
  rw [fullTwist_eq_halfTwist_sq h, pow_two, mul_assoc, halfTwist_conj_a h, ← mul_assoc,
    halfTwist_conj_b h, mul_assoc]

/-- **[The full twist is central, `Δ²σ₂ = σ₂Δ²`]** the full twist commutes with the second generator. -/
theorem fullTwist_central_b (h : a * b * a = b * a * b) : fullTwist a b * b = b * fullTwist a b := by
  rw [fullTwist_eq_halfTwist_sq h, pow_two, mul_assoc, halfTwist_conj_b h, ← mul_assoc,
    halfTwist_conj_a h, mul_assoc]

/-- **[The trefoil braid word]** `(σ₁σ₂)² = σ₁²σ₂σ₁`: the `(3,2)` torus / trefoil braid word, rewritten with
the braid relation. (`(σ₁σ₂)²` is the trefoil as a `3`-braid; its closure is the `(2,3)` torus knot.) -/
theorem trefoilBraidWord_eq (h : a * b * a = b * a * b) : (a * b) ^ 2 = a * a * b * a := by
  rw [show (a * b) ^ 2 = a * (b * a * b) from by simp only [pow_two, mul_assoc], ← h]
  simp only [mul_assoc]

/-! ## §B — the braid relation is the Yang–Baxter equation (symmetric / flip solution) -/

/-- **The braid-form Yang–Baxter equation** `R₁R₂R₁ = R₂R₁R₂`. For `R₁ = R⊗1`, `R₂ = 1⊗R` on `V⊗V⊗V` this is
the constant Yang–Baxter equation `(R⊗1)(1⊗R)(R⊗1) = (1⊗R)(R⊗1)(1⊗R)` — the integrability /
Reidemeister-III consistency condition; it is identical to the Artin braid relation. -/
def YangBaxter (R₁ R₂ : G) : Prop := R₁ * R₂ * R₁ = R₂ * R₁ * R₂

/-- **[The flip / symmetric braiding solves Yang–Baxter, in `S₃`]** the adjacent transpositions
`s₁ = (0 1)`, `s₂ = (1 2)` of the symmetric group `S₃` satisfy the braid-form Yang–Baxter equation
`s₁s₂s₁ = s₂s₁s₂` — the flip `R(x⊗y) = y⊗x` is the simplest (symmetric, `R² = 1`) solution of the Yang–Baxter
equation, realizing the trefoil braid in `S₃`. -/
theorem symmetric_braid_relation :
    YangBaxter (Equiv.swap (0 : Fin 3) 1) (Equiv.swap 1 2) := by
  unfold YangBaxter
  ext x
  fin_cases x <;> decide

/-- **[Full twist central in `S₃`]** instantiates `fullTwist_central_a` on the symmetric (flip) realization. -/
theorem symmetric_fullTwist_central :
    fullTwist (Equiv.swap (0 : Fin 3) 1) (Equiv.swap 1 2) * Equiv.swap 0 1
      = Equiv.swap 0 1 * fullTwist (Equiv.swap (0 : Fin 3) 1) (Equiv.swap 1 2) :=
  fullTwist_central_a symmetric_braid_relation

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.BraidRelationTrefoilTorus

end
