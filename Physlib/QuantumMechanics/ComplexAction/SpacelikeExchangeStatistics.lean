/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance
public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics

/-!
# Exchange statistics from a spacelike causal count

The exchange phase of an `n`-constituent composite is `(−1)ⁿ` (`Particles.HadronSpinStatistics.compositeTwist`
`= (−1)ⁿ`, from `ribbonTwist ½ = −1`). This file gives the exponent `n` a **frame-independent, causal**
meaning: `n` is the cardinality of a **spacelike family** — a causal antichain, a set of events that are
pairwise causally unrelated, `causalSign x y = 0`. Because `causalSign` is the antisymmetric Pauli–Jordan
kernel of `CausalSetIntervalAbundance` (`causalSign_isPauliJordan`), being spacelike and hence the count `n`
are Lorentz invariants, not coordinate data — the statistics `(−1)ⁿ` is therefore frame-independent.

* **§A — the spacelike characterization.** `causalSign_eq_zero_iff` (`causalSign x y = 0 ⟺ x, y causally
  unrelated`, i.e. neither precedes the other) and `causalSign_eq_zero_comm` (the spacelike relation is
  symmetric, from the Pauli–Jordan antisymmetry). These are the load-bearing derivations.
* **§B — the spacelike family (causal antichain).** `IsSpacelikeFamily S` (every distinct pair has
  `causalSign = 0`); `spacelikeFamily_causalSign_sum_zero` (the total causal sign over the family's pairs
  vanishes — a spacelike antichain has no internal causal structure).
* **§C — the exchange statistics.** `fermionic_exchange_prod` (`∏_{x∈S} ribbonTwist ½ = (−1)^{|S|}`, each
  causally-independent fermionic constituent contributing `−1`) and `spacelike_exchange_eq_compositeTwist`
  (`∏_{x∈S} ribbonTwist ½ = compositeTwist |S|`): the composite exchange phase is the fermion count over the
  spacelike family, so an odd antichain is a fermion and an even one a boson.

**Honest layering.** The genuine derivations are the spacelike characterization (§A) and the vanishing of the
causal sum over a spacelike family (§B, which uses the antichain hypothesis). §C reuses the verified
`compositeTwist_eq`/`ribbonTwist_fermion` and re-expresses the statistics as a product over the antichain
members — the causal reading of the constituent count `n = |S|`. No hadron dynamics is asserted; the content
is the identification of the statistical exponent with a Lorentz-invariant causal count.

## References

* Bridges `CausalSetIntervalAbundance` (`causalSign`, `causalSign_isPauliJordan`) and
  `Particles.HadronSpinStatistics` (`compositeTwist`, `compositeTwist_eq`) / `ExchangeStatisticsSpectrum`.
  The Pauli–Jordan / Sorkin–Johnston statistics context is `SorkinJohnstonRegionState`.


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.SpacelikeExchangeStatistics

open Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

variable {α : Type*} [Preorder α] [DecidableRel ((· < ·) : α → α → Prop)]


/-- **Spacelike ⟺ `causalSign = 0`**: two events have zero causal sign iff neither precedes the other — they
are causally unrelated (mutually spacelike). -/
lemma causalSign_eq_zero_iff (x y : α) :
    causalSign x y = 0 ↔ ¬ x < y ∧ ¬ y < x := by
  unfold causalSign
  by_cases h1 : x < y <;> by_cases h2 : y < x <;>
    simp [h1, h2]

/-- **The spacelike relation is symmetric** `causalSign x y = 0 ⟺ causalSign y x = 0`, from the Pauli–Jordan
antisymmetry `causalSign x y = −causalSign y x`. -/
lemma causalSign_eq_zero_comm (x y : α) : causalSign x y = 0 ↔ causalSign y x = 0 := by
  rw [causalSign_isPauliJordan x y, neg_eq_zero]


/-- A finite family of events is **spacelike** (a causal antichain) if every distinct pair is causally
unrelated, `causalSign x y = 0` — equivalently the Pauli–Jordan kernel vanishes across the family. -/
def IsSpacelikeFamily [DecidableEq α] (S : Finset α) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → causalSign x y = 0

/-- **A spacelike family has no internal causal structure** `∑_{(x,y)∈S², x≠y} causalSign x y = 0`: every
off-diagonal pair contributes zero, so the total causal sign over the antichain vanishes. -/
lemma spacelikeFamily_causalSign_sum_zero [DecidableEq α] (S : Finset α)
    (hS : IsSpacelikeFamily S) :
    (∑ p ∈ S.offDiag, causalSign p.1 p.2) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hp
  exact hS p.1 hx p.2 hy hne


omit [Preorder α] [DecidableRel ((· < ·) : α → α → Prop)] in
/-- **The fermionic exchange phase over `n` constituents is `(−1)ⁿ`** `∏_{x∈S} ribbonTwist ½ = (−1)^{|S|}`:
each fermionic constituent contributes `ribbonTwist ½ = −1`. Read over a spacelike family `S`
(`IsSpacelikeFamily`), the `|S|` factors are the `|S|` causally-independent constituents. -/
lemma fermionic_exchange_prod (S : Finset α) :
    (∏ _x ∈ S, ribbonTwist (1 / 2)) = (-1) ^ S.card := by
  rw [Finset.prod_const, ribbonTwist_fermion]

omit [Preorder α] [DecidableRel ((· < ·) : α → α → Prop)] in
/-- **The composite exchange statistics is the spacelike count** `∏_{x∈S} ribbonTwist ½ = compositeTwist |S|`:
the exchange phase of the family equals the `n`-constituent composite twist with `n = |S|` the cardinality of
the causal antichain. Hence an **odd** spacelike family is a fermion and an **even** one a boson, with the
parity fixed by a Lorentz-invariant count. -/
lemma spacelike_exchange_eq_compositeTwist (S : Finset α) :
    (∏ _x ∈ S, ribbonTwist (1 / 2)) = compositeTwist S.card := by
  rw [fermionic_exchange_prod, compositeTwist_eq]

end Physlib.QuantumMechanics.ComplexAction.SpacelikeExchangeStatistics
