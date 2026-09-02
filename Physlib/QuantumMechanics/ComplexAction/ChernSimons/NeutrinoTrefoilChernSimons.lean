/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.BraidRelationTrefoilTorus

/-!
# The neutrino as a Chern-Simons-Witten trefoil (a three-crossing loop)

In the τ-coherence-loop model the neutrino is a *three-crossing structure with zero charge* — the trefoil
knot (the `(2,3)` torus knot, closure of the braid `σ₁³`). This file gives that three-node loop its
**Chern-Simons-Witten** content, joining `Particles.NeutrinoModel`'s fractional `ℤ/3` (cube-root-of-unity) structure to
the trefoil knot invariants already in the repo.

* **§A — the neutrino's CSW Wilson-loop invariant.** Witten: the Chern-Simons Wilson loop along a knot is its
  Jones polynomial / Kauffman bracket. The neutrino trefoil's invariant is `A⁷ + A³ + A⁻¹ − A⁻⁹`
  (`neutrino_csw_invariant`, reusing `QuantumGroupSkein.TrefoilBracketTemperleyLieb.trefoil_kauffman_bracket`). It is the
  *same* trefoil bracket as the electron's (`neutrinoJones := electronJones`): the neutrino and electron share
  the trefoil topology and are distinguished by **charge**, not knot type.
* **§B — the three-crossing braid.** The neutrino loop is the closure of the trefoil braid; in `B₃` the word
  `(σ₁σ₂)² = σ₁²σ₂σ₁` (`neutrino_braid_word`, reusing `ChernSimons.BraidRelationTrefoilTorus.trefoilBraidWord_eq`).
* **§C — the `ℤ/3` framing.** The trefoil has writhe `3`; the Chern-Simons framing phase per crossing is the
  cube root of unity `ω` (`Particles.NeutrinoModel.cubeRoot`), so after the three crossings it closes, `ω³ = 1`
  (`cubeRoot_pow_three`), and the three crossing phases cancel, `1 + ω + ω² = 0` (`cubeRoot_sum_zero`) —
  *this* is why the three-crossing neutrino is **neutral** (zero charge).
* **§D — the main result** `neutrino_chern_simons_witten`: the neutrino as a CSW trefoil — Wilson loop `=`
  Kauffman bracket, `ω³ = 1` (the three-crossing loop closes), `1 + ω + ω² = 0` (the crossing phases cancel
  ⟹ neutral).

**Honest layering.** Proven: the neutrino trefoil's CSW Wilson-loop invariant is the trefoil Kauffman bracket
(reused), the trefoil `B₃` braid word holds, the `ℤ/3` framing closes (`ω³=1`) and its phases cancel
(`1+ω+ω²=0`). The *identification* neutrino `=` trefoil is the model reading; the knot invariants and the
cube-root algebra are exact. The knot *topology* (that this braid closure is the trefoil) is not in Mathlib
and is not claimed; only the braid-word and bracket algebra.

## References

* Witten, *QFT and the Jones Polynomial* (Wilson loop = Jones); the three-crossing neutrino. `Physlib`
  (`QuantumGroupSkein.TrefoilBracketTemperleyLieb`, `ChernSimons.BraidRelationTrefoilTorus`, `ChernSimons.TrefoilFermionChernSimonsInvariant`,
  `Particles.NeutrinoModel`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.TrefoilBracketTemperleyLieb
open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.QuantumGroupSl2Casimir
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.BraidRelationTrefoilTorus

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.NeutrinoTrefoilChernSimons


/-- **The neutrino trefoil's Chern-Simons-Witten invariant** — the trefoil Kauffman bracket / Jones
polynomial `A⁷ + A³ + A⁻¹ − A⁻⁹`. It is the *same* trefoil invariant as the electron's
(`= electronJones`): the neutrino and electron share the trefoil topology, distinguished by charge. -/
def neutrinoJones (A : ℂ) : ℂ := electronJones A

/-- **[The neutrino trefoil's CSW Wilson loop IS the Kauffman bracket]** the closure of the trefoil braid
`σ₁³` has Chern-Simons-Witten invariant `A⁷ + A³ + A⁻¹ − A⁻⁹` (reusing
`QuantumGroupSkein.TrefoilBracketTemperleyLieb.trefoil_kauffman_bracket`). -/
lemma neutrino_csw_invariant (A : ℂ) (hA : A ≠ 0) :
    kauffmanClosure (kauffmanLoopValue A) (tlMul (kauffmanLoopValue A) (crossingTL A)
        (tlMul (kauffmanLoopValue A) (crossingTL A) (crossingTL A)))
      = neutrinoJones A :=
  trefoil_kauffman_bracket A hA


/-- **[The neutrino's three-crossing braid word]** in `B₃`, `(σ₁σ₂)² = σ₁²σ₂σ₁` (Artin relation) — the
trefoil braid whose three crossings make up the neutrino loop (reusing
`ChernSimons.BraidRelationTrefoilTorus.trefoilBraidWord_eq`). -/
lemma neutrino_braid_word {G : Type*} [Monoid G] {a b : G} (h : a * b * a = b * a * b) :
    (a * b) ^ 2 = a * a * b * a :=
  trefoilBraidWord_eq h


/-- **[The three-crossing framing closes]** `ω³ = 1` — the trefoil's writhe-`3` Chern-Simons framing phase
returns to the identity after the three crossings (`Particles.NeutrinoModel.cubeRoot_pow_three`). -/
lemma neutrino_framing_closes : cubeRoot ^ 3 = 1 := cubeRoot_pow_three

/-- **[The three crossing phases cancel ⟹ the neutrino is neutral]** `1 + ω + ω² = 0`
(`Particles.NeutrinoModel.cubeRoot_sum_zero`). -/
lemma neutrino_crossings_neutral : 1 + cubeRoot + cubeRoot ^ 2 = 0 := cubeRoot_sum_zero


/-- **[The neutrino, as a CSW trefoil]** its Chern-Simons-Witten Wilson-loop invariant is the trefoil
Kauffman bracket, its `ℤ/3` framing closes after three crossings (`ω³ = 1`), and the three crossing phases
cancel (`1 + ω + ω² = 0`) — so the three-crossing neutrino is neutral. The neutrino is the trefoil knot read
through Chern-Simons-Witten theory. -/
lemma neutrino_chern_simons_witten (A : ℂ) (hA : A ≠ 0) :
    kauffmanClosure (kauffmanLoopValue A) (tlMul (kauffmanLoopValue A) (crossingTL A)
          (tlMul (kauffmanLoopValue A) (crossingTL A) (crossingTL A))) = neutrinoJones A
      ∧ cubeRoot ^ 3 = 1
      ∧ 1 + cubeRoot + cubeRoot ^ 2 = 0 :=
  ⟨trefoil_kauffman_bracket A hA, cubeRoot_pow_three, cubeRoot_sum_zero⟩

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.NeutrinoTrefoilChernSimons

end

end
