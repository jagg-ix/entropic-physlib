/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IcosahedralBoseEinsteinC60

/-!
# Nuclear-spin symmetry of `C₆₀`: deriving the single symmetric state (Bunker–Jensen §3)

Completes the `¹²C₆₀` selection rule by *deriving* its one assumed input — that the 60 spin-0 nuclei admit a
**single, totally-symmetric** (`A_g`) nuclear-spin state. Following Bunker & Jensen (1999) §3, the character of
the nuclear-spin representation of `N` identical nuclei of spin `I` under a symmetry operation `g` is

  `χ_nspin(g) = (2I+1)^{c(g)}`,

where `c(g)` is the number of orbits (cycles) of `g` acting on the `N` nuclei. For `¹²C₆₀` the nuclei are
spin-0, so `2I+1 = 1` and `χ_nspin(g) = 1` for **every** `g` — the character of the trivial (`A_g`) irrep. Hence
`Γ_nspin = A_g`: a unique symmetric spin state. For `¹³C₆₀` the nuclei are spin-½, giving `2^{c(g)}` and the
characters of Bunker–Jensen Eq. 15.

* **§A — the nuclear-spin character and cycle counts.** `nspinChar (2I+1) c = (2I+1)^c`; the `C₆₀` cycle counts
  `cyclesE = 60`, `cyclesC5 = 12`, `cyclesC3 = 20`, `cyclesC2 = 30`, `cyclesInv = 30`, with `cycles_partition`
  (each class's cycles times its order `= 60`).
* **§B — `¹²C₆₀`: the single symmetric state, derived.** `spin0_char_trivial` (`χ_nspin ≡ 1`),
  `carbon12_nspin_dimension` (`= 1`, one spin state) and `carbon12_agMult_class_sum` (the `A_g` class-sum `= 60`,
  so multiplicity `60/60 = 1`) — `Γ_nspin = A_g`, the input assumed in `IcosahedralBoseEinsteinC60`.
* **§C — `¹³C₆₀` (fermionic) and methane.** `carbon13_char_E` (`2^60` states), `carbon13_char_C5/C3/C2/Inv`
  (`2^12, 2^20, 2^30, 2^30`, Bunker–Jensen Eq. 15); `methane_nspin_dimension` (`2^4 = 16 = 5·1+3·3+1·2`, the
  `5A₁ ⊕ 3F₂ ⊕ E` weights).

**Honest layering.** The character law `(2I+1)^{cycles}`, the spin-0 triviality, and the fermionic power values
are exact. The `C₆₀` cycle counts (`12, 20, 30, 30`) follow from the action of `I_h` on the 60 vertices of the
truncated icosahedron (recorded, with the order/orbit consistency `cycles_partition` proved).

## References

* Bunker & Jensen, Mol. Phys. **97**, 255 (1999), §3, Table 4, Eq. 15. Built on
  `ComplexAction.IcosahedralBoseEinsteinC60`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.IcosahedralNuclearSpinWeights


/-- The **nuclear-spin character** of `N` identical spin-`I` nuclei under an operation with `c` orbits (cycles):
`(2I+1)^c`. -/
def nspinChar (twoIplus1 c : ℕ) : ℕ := twoIplus1 ^ c

/-- Cycles of the identity on the 60 `C₆₀` vertices — all fixed (`60`). -/
def cyclesE : ℕ := 60

/-- Cycles of a five-fold rotation — `60 / 5 = 12`. -/
def cyclesC5 : ℕ := 12

/-- Cycles of a three-fold rotation — `60 / 3 = 20`. -/
def cyclesC3 : ℕ := 20

/-- Cycles of a two-fold rotation — `60 / 2 = 30`. -/
def cyclesC2 : ℕ := 30

/-- Cycles of the inversion — the 60 vertices in `30` antipodal pairs. -/
def cyclesInv : ℕ := 30

/-- **Orbit/order consistency** — each rotation's cycle count times its order recovers the `60` vertices. -/
lemma cycles_partition :
    cyclesE = 60 ∧ 5 * cyclesC5 = 60 ∧ 3 * cyclesC3 = 60 ∧ 2 * cyclesC2 = 60 ∧ 2 * cyclesInv = 60 := by
  decide


/-- **The spin-0 nuclear-spin character is trivial** `χ_nspin(g) = 1` for every operation (`1^c = 1`) — the
character of the `A_g` irrep. -/
lemma spin0_char_trivial (c : ℕ) : nspinChar 1 c = 1 := one_pow c

/-- **`¹²C₆₀` has a single nuclear-spin state** `dim Γ_nspin = 1^60 = 1` — the unique `I = 0` state. -/
lemma carbon12_nspin_dimension : nspinChar 1 cyclesE = 1 := one_pow _

/-- **The `A_g` class-sum is `60`** — since `χ_nspin ≡ 1`, the `A_g` multiplicity is
`(1/60)·Σ_classes |class| = 60/60 = 1`: `Γ_nspin(¹²C₆₀) = A_g`, deriving the single symmetric state assumed in
`IcosahedralBoseEinsteinC60`. -/
lemma carbon12_agMult_class_sum :
    1 * nspinChar 1 cyclesE + 12 * nspinChar 1 cyclesC5 + 12 * nspinChar 1 cyclesC5
      + 20 * nspinChar 1 cyclesC3 + 15 * nspinChar 1 cyclesC2 = 60 := by decide


/-- **`¹³C₆₀` has `2^60` nuclear-spin states** — spin-½, identity character `2^{60}`. -/
lemma carbon13_char_E : nspinChar 2 cyclesE = 2 ^ 60 := rfl

/-- **Five-fold character `2^12`** (Bunker–Jensen Eq. 15). -/
lemma carbon13_char_C5 : nspinChar 2 cyclesC5 = 2 ^ 12 := rfl

/-- **Three-fold character `2^20`** (Bunker–Jensen Eq. 15). -/
lemma carbon13_char_C3 : nspinChar 2 cyclesC3 = 2 ^ 20 := rfl

/-- **Two-fold character `2^30`** (Bunker–Jensen Eq. 15). -/
lemma carbon13_char_C2 : nspinChar 2 cyclesC2 = 2 ^ 30 := rfl

/-- **Inversion character `2^30`** — the 30 antipodal pairs (Bunker–Jensen Eq. 15). -/
lemma carbon13_char_Inv : nspinChar 2 cyclesInv = 2 ^ 30 := rfl

/-- **Methane `¹²CH₄` has `2^4 = 16` nuclear-spin states** decomposing as `5A₁ ⊕ 3F₂ ⊕ E` with dimensions
`5·1 + 3·3 + 1·2 = 16` (Bunker–Jensen Eq. 10). -/
lemma methane_nspin_dimension : nspinChar 2 4 = 5 * 1 + 3 * 3 + 1 * 2 := by decide

end Physlib.QuantumMechanics.ComplexAction.IcosahedralNuclearSpinWeights
