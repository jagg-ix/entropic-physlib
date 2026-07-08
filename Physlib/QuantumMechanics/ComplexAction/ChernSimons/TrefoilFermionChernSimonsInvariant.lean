/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.TrefoilBracketTemperleyLieb

/-!
# The Chern-Simons-Witten knot invariant of the fermion trefoil — chirality as particle/antiparticle

Witten's *QFT and the Jones Polynomial* identifies the expectation value of a Wilson loop along a knot, in
Chern-Simons theory, with the **Jones polynomial** of that knot (the Kauffman bracket up to a writhe framing).
In the soliton/winding picture a fermion is a knot — concretely the **trefoil** `σ₁³` — so the electron records
a Chern-Simons-Witten invariant: its Kauffman bracket

 `⟨electron⟩ = A⁷ + A³ + A⁻¹ − A⁻⁹` (`electron_csw_invariant`, reusing
 `QuantumGroupSkein.TrefoilBracketTemperleyLieb.trefoil_kauffman_bracket`).

The **positron** is the *mirror* trefoil — the charge-conjugate knot — whose bracket is the image under the
**mirror substitution `A → A⁻¹`** (`positronJones`, `positronJones_eq`):

 `⟨positron⟩ = A⁻⁷ + A⁻³ + A − A⁹`.

The trefoil is the simplest **chiral** knot: it is *not* equal to its mirror, and the Chern-Simons-Witten Jones
invariant detects this (`trefoil_chiral_distinguishes`). So the topological invariant **distinguishes the
electron from the positron** — the knot-theoretic realization of the particle/antiparticle (charge-conjugation)
distinction, with `A → A⁻¹` the mirror/charge-conjugation operation (matching the winding `q → −q` of
`Fermion.AnnihilationTwoPhotons`).

* **§A — the electron invariant.** `electronJones`; `electron_csw_invariant` (= the trefoil Kauffman bracket,
 reusing the Sawin/Witten theorem).
* **§B — the positron and chirality.** `positronJones` (`A → A⁻¹` mirror), `positronJones_eq`,
 `trefoil_chiral_distinguishes` (electron ≠ positron — the Jones invariant separates particle/antiparticle).

Proven: the electron trefoil's Kauffman bracket is the Witten Chern-Simons knot invariant
(reused), the positron's is its mirror `A → A⁻¹`, and the two differ (the trefoil is chiral). The
*identification* of the electron with the trefoil is the soliton-model representation; the chirality/charge-
conjugation correspondence is genuine knot theory applied to it. The framing/writhe factor relating the
Kauffman bracket to the normalized Jones polynomial is suppressed (`A → A⁻¹` is the relevant mirror operation).

## References

* E. Witten, *QFT and the Jones Polynomial* (Wilson loop = Jones polynomial); trefoil chirality. `Physlib`
 (`QuantumGroupSkein.TrefoilBracketTemperleyLieb.trefoil_kauffman_bracket`, `ChernSimons.WittenJonesPolynomialChernSimons`).

No additional assumptions.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.TrefoilBracketTemperleyLieb
open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.QuantumGroupSl2Casimir

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant

/-! ## §A — the electron's Chern-Simons-Witten invariant (the trefoil Kauffman bracket) -/

/-- **The electron's Chern-Simons-Witten knot invariant** — the Kauffman bracket of the right trefoil `σ₁³`,
`A⁷ + A³ + A⁻¹ − A⁻⁹` (Witten: the Wilson-loop expectation = the Jones polynomial). -/
def electronJones (A : ℂ) : ℂ := A ^ 7 + A ^ 3 + A⁻¹ - (A ^ 9)⁻¹

/-- **[The electron invariant IS the trefoil Kauffman bracket]** the Chern-Simons-Witten Wilson-loop invariant
of the electron trefoil equals the Sawin/Witten trefoil bracket (`trefoil_kauffman_bracket`). -/
theorem electron_csw_invariant (A : ℂ) (hA : A ≠ 0) :
    kauffmanClosure (kauffmanLoopValue A) (tlMul (kauffmanLoopValue A) (crossingTL A)
        (tlMul (kauffmanLoopValue A) (crossingTL A) (crossingTL A)))
      = electronJones A :=
  trefoil_kauffman_bracket A hA

/-! ## §B — the positron (mirror trefoil) and the chirality that separates them -/

/-- **The positron's Chern-Simons-Witten invariant** — the *mirror* trefoil's bracket, the image of the
electron's under the charge-conjugation substitution `A → A⁻¹`. -/
def positronJones (A : ℂ) : ℂ := electronJones A⁻¹

/-- **[The positron invariant]** `⟨positron⟩ = A⁻⁷ + A⁻³ + A − A⁹` — the mirror of the electron trefoil. -/
theorem positronJones_eq (A : ℂ) :
    positronJones A = (A ^ 7)⁻¹ + (A ^ 3)⁻¹ + A - A ^ 9 := by
  simp only [positronJones, electronJones, inv_pow, inv_inv]

/-- **[The trefoil is chiral: the invariant separates electron from positron]** `⟨electron⟩ ≠ ⟨positron⟩`
(here at `A = 2`): the trefoil is not equal to its mirror, so the Chern-Simons-Witten Jones invariant
distinguishes the electron (right trefoil) from the positron (left/mirror trefoil) — the topological
realization of the particle/antiparticle (charge-conjugation) distinction. -/
theorem trefoil_chiral_distinguishes : electronJones 2 ≠ positronJones 2 := by
  rw [positronJones_eq, ← sub_ne_zero]; unfold electronJones; norm_num

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant

end

end
