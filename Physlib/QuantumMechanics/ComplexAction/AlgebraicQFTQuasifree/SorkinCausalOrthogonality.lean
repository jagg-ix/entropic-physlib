/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CausalOrthogonalityQuasiLocalNet
public import Physlib.QuantumMechanics.ComplexAction.SpacelikeExchangeStatistics

/-!
# Sorkin's spacelike relation is the causal orthogonality relation: microcausality from Pauli–Jordan

Links the abstract causal orthogonality relation of the quasi-local algebra (`CausalOrthogonalityQuasiLocalNet`,
Labuschagne–Majewski) to the Sorkin(–Johnston) causal-set machinery (`SpacelikeExchangeStatistics`,
`CausalSetIntervalAbundance`). Sorkin's causal-order sign `causalSign` is the antisymmetric **Pauli–Jordan**
function, and two events are **spacelike** exactly when it vanishes (`causalSign x y = 0`). That vanishing is
precisely the orthogonality relation `α ⊥ β` (causal independence):

* the **Sorkin spacelike relation is the orthogonality relation** `sorkinOrth x y := causalSign x y = 0`,
  symmetric (`sorkinOrth_symm`, from Pauli–Jordan antisymmetry `causalSign x y = −causalSign y x`) and equal to
  mutual spacelike separation `¬x<y ∧ ¬y<x` (`sorkinOrth_iff_spacelike`) — the `symm` axiom of
  `CausalOrthogonality` realized by the causal set;
* a **Sorkin spacelike family is a set of pairwise-orthogonal regions** (`isSpacelikeFamily_iff_pairwise_sorkinOrth`)
  — `IsSpacelikeFamily` (a causal antichain) is exactly a pairwise causally-independent family;
* **microcausality**: for a quasi-local net whose orthogonality is the Sorkin spacelike relation, the observables
  of a spacelike family *mutually commute* (`sorkin_spacelike_family_microcausality`) — the vanishing of the
  Pauli–Jordan function spacelike *is* the causal-independence axiom `[𝒜_x, 𝒜_y] = 0`, and the Sorkin–Johnston
  vacuum built from `causalSign` is therefore microcausal.

So the abstract quasi-local orthogonality relation has a concrete causal-set model: `α ⊥ β` is `causalSign = 0`,
a spacelike family is a pairwise-orthogonal antichain, and causal independence is the Pauli–Jordan commutator
vanishing spacelike.

* **§A — the Sorkin spacelike relation is the orthogonality relation** (`sorkinOrth`, `sorkinOrth_symm`,
  `sorkinOrth_iff_spacelike`).
* **§B — a spacelike family is pairwise orthogonal** (`isSpacelikeFamily_iff_pairwise_sorkinOrth`).
* **§C — microcausality of a spacelike family** (`sorkin_spacelike_family_microcausality`).

**Honest layering.** `sorkinOrth`, its symmetry and the spacelike characterization are exact reuse of
`causalSign_eq_zero_comm`/`causalSign_eq_zero_iff`; the family identity is definitional. §C realizes the
`QuasiLocalNet.causalIndependence` axiom for the Sorkin relation *under the hypothesis* that the net's
orthogonality is `causalSign = 0`; the region-order axioms (heredity, directedness) of `CausalOrthogonality`
concern region containment on `𝒦(M,g)`, a separate structure from the causal-set order, and are not asserted for
`sorkinOrth`. ## References

* R.D. Sorkin (causal sets, Pauli–Jordan / Sorkin–Johnston vacuum). Repo carriers:
  `CausalSetIntervalAbundance` (`causalSign`), `SpacelikeExchangeStatistics` (`IsSpacelikeFamily`),
  `AlgebraicQFTQuasifree.CausalOrthogonalityQuasiLocalNet` (`QuasiLocalNet`, `causalIndependence_symm`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CausalOrthogonalityQuasiLocalNet
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant
open Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance
open Physlib.QuantumMechanics.ComplexAction.SpacelikeExchangeStatistics

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.SorkinCausalOrthogonality

variable {α : Type*} [Preorder α] [DecidableRel ((· < ·) : α → α → Prop)]


/-- **The Sorkin causal orthogonality relation** `x ⊥ y := causalSign x y = 0` — two events are orthogonal
(causally independent) exactly when the Pauli–Jordan function vanishes, i.e. they are spacelike separated. -/
def sorkinOrth (x y : α) : Prop := causalSign x y = 0

/-- **[The Sorkin orthogonality relation is symmetric] `x ⊥ y ⟹ y ⊥ x`.** From the Pauli–Jordan antisymmetry
`causalSign x y = −causalSign y x`, spacelike separation is symmetric — the `symm` axiom of a causal
orthogonality relation, realized by the causal set. -/
lemma sorkinOrth_symm {x y : α} (hxy : sorkinOrth x y) : sorkinOrth y x :=
  (causalSign_eq_zero_comm x y).mp hxy

/-- **[The Sorkin orthogonality relation is spacelike separation] `x ⊥ y ⟺ ¬x<y ∧ ¬y<x`.** Two events are
orthogonal exactly when neither causally precedes the other — mutual spacelike separation. -/
lemma sorkinOrth_iff_spacelike (x y : α) : sorkinOrth x y ↔ ¬ x < y ∧ ¬ y < x :=
  causalSign_eq_zero_iff x y


/-- **[A Sorkin spacelike family is a pairwise-orthogonal antichain] `IsSpacelikeFamily S ⟺ ∀ x,y ∈ S distinct, x ⊥ y`.**
A causal antichain (`IsSpacelikeFamily`) is exactly a family of pairwise causally-independent regions — the
finite set of mutually-orthogonal regions the quasi-local net's causal independence applies to. -/
lemma isSpacelikeFamily_iff_pairwise_sorkinOrth [DecidableEq α] (S : Finset α) :
    IsSpacelikeFamily S ↔ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → sorkinOrth x y :=
  Iff.rfl


/-- **[Microcausality: a Sorkin spacelike family has mutually-commuting observables].** For a quasi-local net `Q`
whose orthogonality relation is the Sorkin spacelike relation (`causalSign = 0`), the observables of any two
distinct events of a spacelike family *mutually commute*: `𝒜_x ⊆ 𝒜_y'` and `𝒜_y ⊆ 𝒜_x'`. The vanishing of the
Pauli–Jordan function spacelike is exactly the causal-independence axiom `[𝒜_x, 𝒜_y] = 0`, so the Sorkin–Johnston
construction is microcausal. -/
lemma sorkin_spacelike_family_microcausality {A : Type*} [Monoid A] [DecidableEq α]
    (Q : QuasiLocalNet A α) (h : ∀ x y : α, Q.causal.orth x y ↔ sorkinOrth x y)
    {S : Finset α} (hS : IsSpacelikeFamily S) {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
    Q.alg x ⊆ commutant (Q.alg y) ∧ Q.alg y ⊆ commutant (Q.alg x) := by
  have hxy : Q.causal.orth x y := (h x y).mpr (hS x hx y hy hne)
  exact ⟨Q.causalIndependence hxy, causalIndependence_symm Q hxy⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.SorkinCausalOrthogonality

end
