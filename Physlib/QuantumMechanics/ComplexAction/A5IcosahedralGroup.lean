/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Physlib.QuantumMechanics.ComplexAction.CliffordRootSystemInduction

/-!
# The icosahedral group A₅ and the binary icosahedral 2I Möbius group

The `5`-fold / icosahedral sibling of the tetrahedral `A₄` / `2T` structure (`A4FlavorGenerations`,
`TetrahedralCelestialSphere`). The icosahedral rotation group is `A₅ = alternatingGroup (Fin 5)` (order `60`),
the quotient of the binary icosahedral group `2I` (order `120`, `CliffordRootSystemInduction.binaryIcosahedralCoordinates`,
the `120` unit Hurwitz–golden quaternions) by its centre `{±1}`. `2I ⊂ SU(2) ⊂ SL(2,ℂ)` acts on the Riemann /
celestial sphere by Möbius transformations (`RiemannSphereBlochSL2CLinks.sl2c_onePoint_mobius`), with the
icosahedron / dodecahedron as its orbit configurations — the icosahedral analogue of the tetrahedron-on-CP¹ of
`TetrahedralCelestialSphere`.

* **§A — the icosahedral rotation group.** `card_A5` (`|A₅| = 60`) and **`A5_simple`** (`A₅` is simple — the
  smallest non-abelian simple group, `alternatingGroup.isSimpleGroup_five`).
* **§B — the binary icosahedral double cover.** `binaryIcosahedral_double_covers_A5`
  (`|2I| = 120 = 2·|A₅|`, the spin double cover `2I → A₅` via `SU(2) → SO(3)`);
  `binaryIcosahedral_order_factorial` (`|2I| = 5! = 120`, the `5`-fold order — `2I ≅ SL(2,𝔽₅)`).

**Honest layering.** Exact: the group order `|A₅| = 60`, its simplicity (Mathlib), and the double-cover /
factorial relations to `2I` (from `CliffordRootSystemInduction.binaryIcosahedralCoordinates_card = 120`).
Interpretive (docstring): the Möbius action of `2I` on the Riemann sphere and its icosahedral orbit
configurations (the golden-ratio vertices), paralleling `TetrahedralCelestialSphere` for `2T`.

## References

* Binary polyhedral groups / McKay (`2I = E₈`); `A₅ ≅ PSL(2,𝔽₅)` icosahedral rotation group; the icosahedral
  Möbius group on `CP¹`. Built on `CliffordRootSystemInduction` (`2I`, `binaryIcosahedralCoordinates_card`) and
  `Mathlib`'s `alternatingGroup.isSimpleGroup_five`. Sibling of `A4FlavorGenerations` /
  `TetrahedralCelestialSphere` (`2T`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.CliffordRootSystemInduction

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.A5IcosahedralGroup


/-- **The icosahedral rotation group has order 60** `|A₅| = |alternatingGroup (Fin 5)| = 5!/2 = 60`. -/
lemma card_A5 : Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  rw [card_alternatingGroup, Fintype.card_fin]; decide

/-- **A₅ is simple** — the icosahedral rotation group is the smallest non-abelian simple group (Mathlib's
`alternatingGroup.isSimpleGroup_five`). -/
lemma A5_simple : IsSimpleGroup (alternatingGroup (Fin 5)) := inferInstance


/-- **`2I` is the two-to-one spin double cover of `A₅`** `|2I| = 120 = 2·|A₅|`: the binary icosahedral group
(`CliffordRootSystemInduction.binaryIcosahedralCoordinates`, the `120` unit quaternions in `SU(2)`) covers the
icosahedral rotation group `A₅ ⊂ SO(3)` two-to-one, via `SU(2) → SO(3)`. -/
lemma binaryIcosahedral_double_covers_A5 :
    binaryIcosahedralCoordinates.card = 2 * Fintype.card (alternatingGroup (Fin 5)) := by
  rw [binaryIcosahedralCoordinates_card, card_A5]

/-- **`|2I| = 5! = 120`** — the `5`-fold order of the binary icosahedral group `2I ≅ SL(2,𝔽₅)`. -/
lemma binaryIcosahedral_order_factorial :
    binaryIcosahedralCoordinates.card = Nat.factorial 5 := by
  rw [binaryIcosahedralCoordinates_card]; decide

end Physlib.QuantumMechanics.ComplexAction.A5IcosahedralGroup
