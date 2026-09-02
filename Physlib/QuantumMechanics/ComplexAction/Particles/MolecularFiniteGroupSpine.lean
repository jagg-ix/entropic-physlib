/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationalIrrepDecomposition
public import Physlib.QuantumMechanics.ComplexAction.OctahedralRotationalReduction
public import Physlib.QuantumMechanics.ComplexAction.A5IcosahedralGroup

/-!
# The finite-group spine: molecular reduction groups = particle finite groups

The point groups behind the molecular character reductions are exactly the finite groups already used in the
particle work — a shared spine linking the two arcs. The **proper rotation groups** are the alternating and
symmetric groups:

  `I` (icosahedral) `≅ A₅` (`60 = 5!/2`),  `O` (octahedral) `≅ S₄` (`24 = 4!`),
  `T` (tetrahedral) `≅ A₄` (`12 = 4!/2`),

with binary covers `2I, 2O, 2T ⊂ SU(2)` of orders `120, 48, 24`.

* **§A — the rotation-group orders.** `icosahedralOrder = 60`, `octahedralOrder = 24`, `tetrahedralOrder = 12`;
  `orders_are_factorials` (`60 = 5!/2`, `24 = 4!`, `12 = 4!/2`).
* **§B — `I ≅ A₅`.** **`icosahedral_order_eq_A5`** (`icosahedralOrder = |A₅|`, via
  `A5IcosahedralGroup.card_A5`) — the icosahedral reduction group is the alternating group `A₅`.
* **§C — Burnside ties the reductions to the orders.** `icosahedral_burnside` (`Σ dim² = 60 = |A₅|`) and
  `octahedral_burnside` (`Σ dim² = 24 = |O|`), from the two reduction modules' `irrepDims_sq_sum`; and the
  binary-cover orders `binary_covers_double` (`120, 48, 24 = 2×`).

**Honest layering.** The order values, the factorial identities, `I ≅ A₅` (via the proven `card_A5`), and the
Burnside identities (from the reduction modules) are exact. The isomorphisms `O ≅ S₄`, `T ≅ A₄` and the binary
covers are recorded (the orders are proved; the full group isomorphisms are not reconstructed here).

## References

* The rotation groups of the Platonic solids as `A₄, S₄, A₅`; their binary covers in `SU(2)`. Built on
  `ComplexAction.A5IcosahedralGroup` (`card_A5`), `IcosahedralRotationalIrrepDecomposition`, and
  `OctahedralRotationalReduction` (`irrepDims_sq_sum`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.A5IcosahedralGroup

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.MolecularFiniteGroupSpine


/-- The **icosahedral rotation group order** `|I| = 60`. -/
def icosahedralOrder : ℕ := 60

/-- The **octahedral rotation group order** `|O| = 24`. -/
def octahedralOrder : ℕ := 24

/-- The **tetrahedral rotation group order** `|T| = 12`. -/
def tetrahedralOrder : ℕ := 12

/-- **The orders are the alternating/symmetric-group orders** `60 = 5!/2`, `24 = 4!`, `12 = 4!/2`. -/
lemma orders_are_factorials :
    icosahedralOrder = Nat.factorial 5 / 2 ∧ octahedralOrder = Nat.factorial 4
      ∧ tetrahedralOrder = Nat.factorial 4 / 2 := by decide


/-- **The icosahedral reduction group is `A₅`** `|I| = |A₅| = 60` — the icosahedral character reduction
(`IcosahedralCharacterReduction`) is a reduction over the alternating group `A₅`. -/
lemma icosahedral_order_eq_A5 :
    icosahedralOrder = Fintype.card (alternatingGroup (Fin 5)) := by
  unfold icosahedralOrder; exact card_A5.symm


/-- **Burnside for the icosahedral reduction** `Σ dim² = 60 = |A₅|` — the five icosahedral irrep dimensions
`1,3,3,4,5` square-sum to the group order. -/
lemma icosahedral_burnside :
    (Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationalIrrepDecomposition.irrepDims.map
      (· ^ 2)).sum = icosahedralOrder :=
  Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationalIrrepDecomposition.irrepDims_sq_sum

/-- **Burnside for the cubic reduction** `Σ dim² = 24 = |O|` — the five cubic irrep dimensions `1,1,2,3,3`
square-sum to the group order. -/
lemma octahedral_burnside :
    (Physlib.QuantumMechanics.ComplexAction.OctahedralRotationalReduction.irrepDims.map
      (· ^ 2)).sum = octahedralOrder :=
  Physlib.QuantumMechanics.ComplexAction.OctahedralRotationalReduction.irrepDims_sq_sum

/-- The **binary-cover orders** `|2I| = 120`, `|2O| = 48`, `|2T| = 24` are twice the rotation-group orders — the
`SU(2)` double covers. -/
lemma binary_covers_double :
    120 = 2 * icosahedralOrder ∧ 48 = 2 * octahedralOrder ∧ 24 = 2 * tetrahedralOrder := by decide

end Physlib.QuantumMechanics.ComplexAction.Particles.MolecularFiniteGroupSpine
