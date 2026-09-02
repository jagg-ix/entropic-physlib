/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Int.Cast.Lemmas
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil

/-!
# Cellular-automaton locality: interaction radii and the causal cone

The general locality theory of deterministic update rules on lattice
configurations `ℤ → A`, in the sense of Hedlund's characterization of shift
endomorphisms: a rule is **local of radius `r`** when the updated value at a
site depends only on the configuration within distance `r` of that site
(`IsLocalRule`). Locality alone produces exact causality, for every alphabet
and every rule:

* **Additive interaction radius under composition.** A radius-`r₂` rule after
  a radius-`r₁` rule is a radius-`r₂ + r₁` rule (`comp_isLocalRule`), by the
  triangle inequality on the lattice.
* **The causal cone.** `n` steps of a radius-`r` rule form a radius-`n * r`
  rule (`iterate_isLocalRule`): the state at a site after `n` steps depends
  only on initial data inside the cone `|y - x| ≤ n * r` - the exact lattice
  form of a finite propagation speed, the deterministic precursor of the
  Lieb-Robinson bound, with speed `r` sites per step and no error term.

Instances live with their models - the integer automaton of
`Physlib.QuantumMechanics.ComplexAction.AutomatonBosonDuality` packs to a
radius-one rule and inherits an exact unit-speed cone there.

**Honest boundary.** Exact statements about deterministic lattice rules on
`ℤ`: no operator-norm Lieb-Robinson bound, no continuum limit, no tightness
claim for the cone of an arbitrary rule, and no higher-dimensional lattices.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CellularAutomatonLocality

variable {A : Type*}

/-- **Local rule of radius `r`** on lattice configurations: the updated value
at a site is determined by the configuration within distance `r` of that
site. -/
def IsLocalRule (r : ℕ) (F : (ℤ → A) → (ℤ → A)) : Prop :=
  ∀ (s t : ℤ → A) (x : ℤ), (∀ y : ℤ, |y - x| ≤ (r : ℤ) → s y = t y) →
    F s x = F t x

/-- **Composition adds interaction radii**: a radius-`r₂` rule after a
radius-`r₁` rule is a radius-`r₂ + r₁` rule, by the triangle inequality on the
lattice. -/
@[zil_level physical_theorem]
theorem comp_isLocalRule {r₁ r₂ : ℕ} {F G : (ℤ → A) → (ℤ → A)}
    (hG : IsLocalRule r₂ G) (hF : IsLocalRule r₁ F) :
    IsLocalRule (r₂ + r₁) (G ∘ F) := by
  intro s t x hagree
  simp only [Function.comp_apply]
  refine hG (F s) (F t) x fun y hy => ?_
  refine hF s t y fun z hz => ?_
  refine hagree z ?_
  have htri : |z - x| ≤ |z - y| + |y - x| := abs_sub_le z y x
  push_cast
  push_cast at hz hy
  linarith

/-- **The causal cone of a local rule**: `n` steps of a radius-`r` rule form a
radius-`n * r` rule - the state at a site after `n` steps depends only on
initial data inside the cone `|y - x| ≤ n * r`. Exact finite propagation
speed from locality alone. -/
@[zil_level physical_theorem]
theorem iterate_isLocalRule {r : ℕ} {F : (ℤ → A) → (ℤ → A)}
    (hF : IsLocalRule r F) (n : ℕ) : IsLocalRule (n * r) F^[n] := by
  induction n with
  | zero =>
      intro s t x hagree
      simpa using hagree x (by simp)
  | succ n ih =>
      have hcomp := comp_isLocalRule hF ih
      have harith : (n + 1) * r = r + n * r := by ring
      rw [Function.iterate_succ', harith]
      exact hcomp

end Physlib.QuantumMechanics.ComplexAction.CellularAutomatonLocality

end

open Physlib.QuantumMechanics.ComplexAction.CellularAutomatonLocality in
#physlib_axiom_clean_all [
  comp_isLocalRule,
  iterate_isLocalRule ]

open Physlib.QuantumMechanics.ComplexAction.CellularAutomatonLocality in
#physlib_non_vacuous_all [
  comp_isLocalRule,
  iterate_isLocalRule ]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.CellularAutomatonLocality.comp_isLocalRule where
  formalizes @ "claim:composed-local-rules-have-additive-interaction-radius",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hedlund-1969-endomorphisms-and-automorphisms-of-the-shift-dynamical-system"

zil attach Physlib.QuantumMechanics.ComplexAction.CellularAutomatonLocality.iterate_isLocalRule where
  formalizes @ "claim:n-steps-of-a-radius-r-local-rule-see-only-the-radius-nr-cone",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hedlund-1969-endomorphisms-and-automorphisms-of-the-shift-dynamical-system",
  caveat @ "claim:exact-lattice-cone-only-no-operator-norm-lieb-robinson-bound-and-no-continuum-limit"

zil_file_contract physlib.cellularAutomatonLocality where
  promises "The general locality theory of deterministic lattice rules: composition adds interaction radii, and n steps of a radius-r rule depend only on the radius-nr cone - exact finite propagation speed from locality alone, for every alphabet and every rule."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Function.iterate_succ'", "lean:abs_sub_le"]
  forbids_substitutes ["an operator-norm Lieb-Robinson bound or its continuum limit",
    "a tightness claim for the cone of an arbitrary local rule",
    "higher-dimensional or graph-indexed lattices"]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.CellularAutomatonLocality.comp_isLocalRule,
    Physlib.QuantumMechanics.ComplexAction.CellularAutomatonLocality.iterate_isLocalRule ]

/- ZIL-END -/

#zil_formalization_lint physlib.cellularAutomatonLocality
