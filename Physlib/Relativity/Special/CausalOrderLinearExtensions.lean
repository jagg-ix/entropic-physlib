/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Order.Extension.Linear
public import Physlib.Relativity.Special.SimultaneityConventionShear
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil

/-!
# Causal order and the conventionality of its linear extensions

The order-theoretic backbone of the conventionality of simultaneity: a causal
order on events is a partial order, a global time assignment compatible with it
is a linear extension, and the invariant physical content of temporal order is
exactly comparability.

* **Admissible time orders exist.** Every partial order admits a linear
  extension (`exists_linearExtension`) - the Szpilrajn extension theorem.
* **Non-implied order is reversible.** If the causal order does not force
  `a ≤ b`, some linear extension puts `b` strictly before `a`
  (`exists_linearExtension_reversing`): the augmented relation
  `x ≤ y ∨ (x ≤ b ∧ a ≤ y)` is again a partial order once `¬ a ≤ b`, and
  Szpilrajn extends it.
* **The realizer identity.** The causal order is the intersection of its
  linear extensions: `a ≤ b` iff every linear extension orders `a` before `b`
  (`le_iff_forall_linearExtension`) - the Dushnik-Miller realizer description
  of a partial order. Comparable pairs are ordered the same way by every
  admissible time assignment; nothing else is.
* **Incomparable order is pure convention.** For causally incomparable events
  two admissible linear extensions order the pair in opposite ways
  (`incomparable_reversible`) - the discrete statement that simultaneity
  (temporal order of spacelike-separated events) is convention, while causal
  order is invariant, in the sense of Malament's analysis of the
  conventionality debate.

**Honest boundary.** Pure order theory over an abstract event set: no
spacetime metric, no signal protocol, and no claim that a particular physical
synchrony is preferred. The bridge to kinematic synchrony conventions is the
companion `Physlib.Relativity.Special.SimultaneityConventionShear`, which
realizes convention-dependence for concrete synchrony shears.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Relativity.Special.CausalOrderLinearExtensions

variable {α : Type*}

/-- **Linear extension of a causal order**: a linear order relation on events
containing the partial (causal) order - an admissible global time
assignment. -/
def IsLinearExtension [PartialOrder α] (s : α → α → Prop) : Prop :=
  IsLinearOrder α s ∧ ∀ x y : α, x ≤ y → s x y

/-- **Admissible time orders exist**: every causal order admits a linear
extension (Szpilrajn's extension theorem). -/
@[zil_level physical_theorem]
theorem exists_linearExtension [PartialOrder α] :
    ∃ s : α → α → Prop, IsLinearExtension s := by
  obtain ⟨s, hlin, hext⟩ := extend_partialOrder ((· ≤ ·) : α → α → Prop)
  exact ⟨s, hlin, fun x y h => hext x y h⟩

/-- **Non-implied order is reversible in some extension**: if the causal order
does not force `a ≤ b`, then some linear extension orders `b` before `a` and
not `a` before `b`. The augmented relation `x ≤ y ∨ (x ≤ b ∧ a ≤ y)` is a
partial order precisely because `¬ a ≤ b`, and Szpilrajn extends it. -/
@[zil_level physical_theorem]
theorem exists_linearExtension_reversing [PartialOrder α] {a b : α}
    (h : ¬ a ≤ b) :
    ∃ s : α → α → Prop, IsLinearExtension s ∧ s b a ∧ ¬ s a b := by
  set r' : α → α → Prop := fun x y => x ≤ y ∨ (x ≤ b ∧ a ≤ y) with hr'
  haveI : IsPartialOrder α r' := by
    refine { refl := fun x => Or.inl le_rfl, trans := ?_, antisymm := ?_ }
    · rintro x y z (hxy | ⟨hxb, hay⟩) (hyz | ⟨hyb, haz⟩)
      · exact Or.inl (hxy.trans hyz)
      · exact Or.inr ⟨hxy.trans hyb, haz⟩
      · exact Or.inr ⟨hxb, hay.trans hyz⟩
      · exact absurd (hay.trans hyb) h
    · rintro x y (hxy | ⟨hxb, hay⟩) (hyx | ⟨hyb, hax⟩)
      · exact le_antisymm hxy hyx
      · exact absurd ((hax.trans hxy).trans hyb) h
      · exact absurd ((hay.trans hyx).trans hxb) h
      · exact absurd (hay.trans hyb) h
  obtain ⟨s, hlin, hext⟩ := extend_partialOrder r'
  have hba : s b a := hext b a (Or.inr ⟨le_rfl, le_rfl⟩)
  refine ⟨s, ⟨hlin, fun x y hxy => hext x y (Or.inl hxy)⟩, hba, fun hab => ?_⟩
  have heq : a = b := by
    haveI : IsLinearOrder α s := hlin
    exact antisymm hab hba
  exact h (by rw [heq])

/-- **The causal order is the intersection of its linear extensions**:
`a ≤ b` holds iff every admissible time assignment orders `a` before `b` -
the Dushnik-Miller realizer description. The invariant content of temporal
order under change of time convention is exactly causal comparability. -/
@[zil_level physical_theorem]
theorem le_iff_forall_linearExtension [PartialOrder α] {a b : α} :
    a ≤ b ↔ ∀ s : α → α → Prop, IsLinearExtension s → s a b := by
  constructor
  · exact fun h s hs => hs.2 a b h
  · intro hall
    by_contra h
    obtain ⟨s, hs, _, hnab⟩ := exists_linearExtension_reversing h
    exact hnab (hall s hs)

/-- **Temporal order of incomparable events is pure convention**: for causally
incomparable `a` and `b` there are two admissible linear extensions ordering
the pair in opposite ways, each refusing the reverse order. -/
@[zil_level physical_theorem]
theorem incomparable_reversible [PartialOrder α] {a b : α}
    (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) :
    ∃ s₁ s₂ : α → α → Prop, IsLinearExtension s₁ ∧ IsLinearExtension s₂ ∧
      s₁ b a ∧ ¬ s₁ a b ∧ s₂ a b ∧ ¬ s₂ b a := by
  obtain ⟨s₁, hs₁, h1, h2⟩ := exists_linearExtension_reversing hab
  obtain ⟨s₂, hs₂, h3, h4⟩ := exists_linearExtension_reversing hba
  exact ⟨s₁, s₂, hs₁, hs₂, h1, h2, h3, h4⟩

end Physlib.Relativity.Special.CausalOrderLinearExtensions

end

open Physlib.Relativity.Special.CausalOrderLinearExtensions in
#physlib_axiom_clean_all [
  exists_linearExtension,
  exists_linearExtension_reversing,
  le_iff_forall_linearExtension,
  incomparable_reversible ]

open Physlib.Relativity.Special.CausalOrderLinearExtensions in
#physlib_non_vacuous_all [
  exists_linearExtension,
  exists_linearExtension_reversing,
  le_iff_forall_linearExtension,
  incomparable_reversible ]

/- ZIL-BEGIN -/

zil attach Physlib.Relativity.Special.CausalOrderLinearExtensions.exists_linearExtension where
  formalizes @ "claim:every-causal-order-admits-an-admissible-global-time-assignment",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:szpilrajn-1930-sur-lextension-de-lordre-partiel",
  supported_by @ "lean:extend_partialOrder"

zil attach Physlib.Relativity.Special.CausalOrderLinearExtensions.exists_linearExtension_reversing where
  formalizes @ "claim:causally-unforced-order-is-reversed-by-some-admissible-time-assignment",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:szpilrajn-1930-sur-lextension-de-lordre-partiel"

zil attach Physlib.Relativity.Special.CausalOrderLinearExtensions.le_iff_forall_linearExtension where
  formalizes @ "claim:the-causal-order-is-the-intersection-of-its-linear-extensions",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:dushnik-miller-1941-partially-ordered-sets",
  caveat @ "claim:pure-order-theory-no-spacetime-metric-or-signal-protocol-is-modeled"

zil attach Physlib.Relativity.Special.CausalOrderLinearExtensions.incomparable_reversible where
  formalizes @ "claim:temporal-order-of-causally-incomparable-events-is-convention-causal-order-is-invariant",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:malament-1977-causal-theories-of-time-and-the-conventionality-of-simultaneity",
  caveat @ "claim:conventionality-here-is-order-theoretic-freedom-not-a-statement-about-preferred-physical-synchrony"

zil_file_contract physlib.causalOrderLinearExtensions where
  promises "The order-theoretic backbone of simultaneity conventionality: every causal order admits a linear extension, causally unforced order is reversed by some extension via an augmented partial order, the causal order equals the intersection of its linear extensions, and incomparable pairs are ordered oppositely by two admissible extensions - comparability is the convention-invariant content of temporal order."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:extend_partialOrder", "lean:IsLinearOrder",
    "lean:IsPartialOrder"]
  forbids_substitutes ["a spacetime-metric or lightcone construction of the causal order",
    "a signal-exchange synchrony protocol",
    "a claim that some physical synchrony convention is preferred"]
  witnessed_by [
    Physlib.Relativity.Special.CausalOrderLinearExtensions.exists_linearExtension,
    Physlib.Relativity.Special.CausalOrderLinearExtensions.exists_linearExtension_reversing,
    Physlib.Relativity.Special.CausalOrderLinearExtensions.le_iff_forall_linearExtension,
    Physlib.Relativity.Special.CausalOrderLinearExtensions.incomparable_reversible ]

/- ZIL-END -/

#zil_formalization_lint physlib.causalOrderLinearExtensions
