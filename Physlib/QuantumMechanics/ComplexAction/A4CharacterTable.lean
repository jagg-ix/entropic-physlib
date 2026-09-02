/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Physlib.QuantumMechanics.ComplexAction.A4FlavorGenerations
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import Mathlib.GroupTheory.Perm.Fin
meta import Mathlib.Data.Fintype.Perm
meta import Mathlib.Data.Fintype.Basic

/-!
# The A₄ character table and the irreducibility of the three-generation representation

The standard three-dimensional representation of `A₄ = alternatingGroup (Fin 4)` (the generation
representation of `A4FlavorGenerations`, `dim = 3`) is **irreducible**. This file establishes the character
computation that certifies it, exactly and by evaluation over the group.

The standard-representation character is `χ(g) = (number of fixed points of g) − 1` (the permutation character
`fix(g)` on the four tetrahedron vertices, minus the trivial sub-representation). Its values on the four
conjugacy classes of `A₄` form the character table row:

| class    | `e`  | `(2,2)` double transposition | 3-cycle (two classes) |
|----------|------|------------------------------|-----------------------|
| size     | `1`  | `3`                          | `4 + 4`               |
| `χ`      | `3`  | `−1`                         | `0`                   |

* **§A — the character values** (`stdChar`). `stdChar_one` (`χ(e) = 3 = dim`),
  `stdChar_doubleTransposition` (`χ = −1`), `stdChar_threeCycle` (`χ = 0`) — the character table row, by
  evaluation.
* **§B — the irreducibility criterion** (`stdChar_norm`). `∑_{g ∈ A₄} χ(g)·χ(g⁻¹) = 12 = |A₄|`, i.e. the
  character norm `⟨χ, χ⟩ = 1`. By Mathlib's `FDRep.simple_iff_char_is_norm_one` (over `ℂ`, characteristic
  zero: a finite-dimensional representation is simple iff `∑_g χ(g)χ(g⁻¹) = |G|`), a representation with this
  character is **simple / irreducible**. From the class data:
  `⟨χ,χ⟩ = (1/12)(1·3² + 3·(−1)² + 8·0²) = (9 + 3)/12 = 1`.

**Honest layering.** Proven exactly (by evaluation over the concrete group `alternatingGroup (Fin 4)`): the
character values on each class and the criterion sum `∑_g χ(g)χ(g⁻¹) = |A₄| = 12`. This is the full
character-table certificate of irreducibility. *Not formalized here* (the remaining categorical step): wrapping
the standard representation as an `FDRep ℂ (alternatingGroup (Fin 4))` object and proving its `.character`
equals `stdChar` (the permutation-character = fixed-point-count identity, which Mathlib does not provide as a
lemma), which would let `FDRep.simple_iff_char_is_norm_one` discharge the `Simple` typeclass directly. The
mathematical content of irreducibility — the character norm — is what is computed here.

## References

* Character theory of finite groups; `FDRep.simple_iff_char_is_norm_one` (Mathlib,
  `RepresentationTheory.FinGroupCharZero`). The standard representation: `A4FlavorGenerations.generationSpace`
  (`dim = 3`, `generationSpace_no_fixed_vector`).
-/

set_option autoImplicit false

open scoped BigOperators

open Equiv (Perm)

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.A4CharacterTable


/-- The **standard-representation character** `χ(g) = fix(g) − 1`: the number of tetrahedron vertices fixed by
`g`, minus one (the permutation character on `Fin 4` minus the trivial sub-representation). -/
def stdChar (g : Perm (Fin 4)) : ℤ :=
  ((Finset.univ.filter (fun i => g i = i)).card : ℤ) - 1

/-- **`χ(e) = 3`** — the dimension of the standard representation (all four vertices fixed, minus one). -/
lemma stdChar_one : stdChar 1 = 3 := by native_decide

/-- **`χ = −1` on a double transposition** `(0 1)(2 3)` — no fixed points. -/
lemma stdChar_doubleTransposition : stdChar (Equiv.swap 0 1 * Equiv.swap 2 3) = -1 := by
  native_decide

/-- **`χ = 0` on a 3-cycle** `(0 1 2)` — one fixed point (`3`), minus one. -/
lemma stdChar_threeCycle : stdChar (Equiv.swap 0 1 * Equiv.swap 1 2) = 0 := by native_decide


/-- **The standard representation is irreducible** — the character-norm certificate
`∑_{g ∈ A₄} χ(g)·χ(g⁻¹) = 12 = |A₄|`, i.e. `⟨χ, χ⟩ = 1`. By `FDRep.simple_iff_char_is_norm_one` (finite group,
`ℂ`, characteristic zero) this norm-one character certifies that the three-generation standard representation
is simple / irreducible. -/
lemma stdChar_norm :
    (∑ g : alternatingGroup (Fin 4), stdChar g.val * stdChar (g.val)⁻¹) = 12 := by
  native_decide

/-- **The character is inversion-invariant** `χ(g⁻¹) = χ(g)` (a permutation and its inverse have the same fixed
points), so the criterion sum is the honest character norm `∑_g χ(g)² = ⟨χ,χ⟩·|A₄|`. -/
lemma stdChar_norm_sq :
    (∑ g : alternatingGroup (Fin 4), stdChar g.val * stdChar g.val) = 12 := by
  native_decide

end Physlib.QuantumMechanics.ComplexAction.A4CharacterTable
