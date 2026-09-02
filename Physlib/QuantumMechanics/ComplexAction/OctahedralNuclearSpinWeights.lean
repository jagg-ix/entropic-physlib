/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IcosahedralNuclearSpinWeights

/-!
# A. `³²SF₆` Nuclear-Spin Symmetry

Completes the third Bunker & Jensen (1999) molecule's nuclear-spin analysis. The six spin-½ ¹⁹F nuclei of
`³²SF₆` give `2⁶ = 64` nuclear-spin states; under the full octahedral group `O_h` (order 48) these decompose,
by the `(2I+1)^{cycles} = 2^{cycles}` character, as the ten-irrep representation of Bunker–Jensen Eq. 14.

The `O_h` classes `E, 8C₃, 6C₂, 6C₄, 3C₂, i, 6S₄, 8S₆, 3σ_h, 6σ_d` (sizes `1,8,6,6,3,1,6,8,3,6`) act on the six
`F` atoms with cycle counts `6,2,3,3,4,3,2,1,5,4`, giving spin-½ characters `64,4,8,8,16,8,4,2,32,16`.

* **§A — the class characters.** `char_values` (`= 64,4,8,8,16,8,4,2,32,16`, from `nspinChar 2 cycles`).
* **§B — the decomposition.** `aA1g_48 … aT2u_48` (`= 48·a_Γ`, the class-weighted character sums);
  **`sf6_multiplicities`** (`10,1,8,0,3,0,1,0,6,3` — `Γ_nspin = 10A₁g ⊕ A₂g ⊕ 8E_g ⊕ 3F₂g ⊕ A₂u ⊕ 6F₁u ⊕ 3F₂u`).
* **§C — the count.** `sf6_dimension_sum` (`Σ dim_Γ·a_Γ = 64 = 2⁶`, all spin states recovered).

## A.1. References

* Bunker & Jensen, Mol. Phys. **97**, 255 (1999), Eq. 14. Built on
  `ComplexAction.IcosahedralNuclearSpinWeights` (`nspinChar`); the nuclear-spin companion of
  `ComplexAction.OctahedralRotationalReduction`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.IcosahedralNuclearSpinWeights

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.OctahedralNuclearSpinWeights

/-! ## A.2. The Class Characters -/

/-- Cycles of each `O_h` class on the six `F` atoms — `E→6, 8C₃→2, 6C₂→3, 6C₄→3, 3C₂→4, i→3, 6S₄→2, 8S₆→1,
3σ_h→5, 6σ_d→4`. -/
def cyclesOh : List ℕ := [6, 2, 3, 3, 4, 3, 2, 1, 5, 4]

/-- **The spin-½ nuclear-spin characters** `64,4,8,8,16,8,4,2,32,16` — `2^{cycles}` per class. -/
lemma char_values : cyclesOh.map (nspinChar 2) = [64, 4, 8, 8, 16, 8, 4, 2, 32, 16] := by decide

/-! ## A.3. The Decomposition

Class sizes `1,8,6,6,3,1,6,8,3,6`, characters `64,4,8,8,16,8,4,2,32,16`; each multiplicity times `48` is
`Σ |class|·χ_nspin·χ_Γ` over the ten `O_h` irreps. -/

/-- `A₁g` (`χ = 1,1,1,1,1,1,1,1,1,1`). -/
def aA1g_48 : ℤ := 1*64*1 + 8*4*1 + 6*8*1 + 6*8*1 + 3*16*1 + 1*8*1 + 6*4*1 + 8*2*1 + 3*32*1 + 6*16*1

/-- `A₂g` (`χ = 1,1,−1,−1,1,1,−1,1,1,−1`). -/
def aA2g_48 : ℤ := 1*64*1 + 8*4*1 + 6*8*(-1) + 6*8*(-1) + 3*16*1 + 1*8*1 + 6*4*(-1) + 8*2*1 + 3*32*1 + 6*16*(-1)

/-- `E_g` (`χ = 2,−1,0,0,2,2,0,−1,2,0`). -/
def aEg_48 : ℤ := 1*64*2 + 8*4*(-1) + 6*8*0 + 6*8*0 + 3*16*2 + 1*8*2 + 6*4*0 + 8*2*(-1) + 3*32*2 + 6*16*0

/-- `F₁g` (`χ = 3,0,−1,1,−1,3,1,0,−1,−1`). -/
def aT1g_48 : ℤ := 1*64*3 + 8*4*0 + 6*8*(-1) + 6*8*1 + 3*16*(-1) + 1*8*3 + 6*4*1 + 8*2*0 + 3*32*(-1) + 6*16*(-1)

/-- `F₂g` (`χ = 3,0,1,−1,−1,3,−1,0,−1,1`). -/
def aT2g_48 : ℤ := 1*64*3 + 8*4*0 + 6*8*1 + 6*8*(-1) + 3*16*(-1) + 1*8*3 + 6*4*(-1) + 8*2*0 + 3*32*(-1) + 6*16*1

/-- `A₁u` (`χ = 1,1,1,1,1,−1,−1,−1,−1,−1`). -/
def aA1u_48 : ℤ := 1*64*1 + 8*4*1 + 6*8*1 + 6*8*1 + 3*16*1 + 1*8*(-1) + 6*4*(-1) + 8*2*(-1) + 3*32*(-1) + 6*16*(-1)

/-- `A₂u` (`χ = 1,1,−1,−1,1,−1,1,−1,−1,1`). -/
def aA2u_48 : ℤ := 1*64*1 + 8*4*1 + 6*8*(-1) + 6*8*(-1) + 3*16*1 + 1*8*(-1) + 6*4*1 + 8*2*(-1) + 3*32*(-1) + 6*16*1

/-- `E_u` (`χ = 2,−1,0,0,2,−2,0,1,−2,0`). -/
def aEu_48 : ℤ := 1*64*2 + 8*4*(-1) + 6*8*0 + 6*8*0 + 3*16*2 + 1*8*(-2) + 6*4*0 + 8*2*1 + 3*32*(-2) + 6*16*0

/-- `F₁u` (`χ = 3,0,−1,1,−1,−3,−1,0,1,1`). -/
def aT1u_48 : ℤ := 1*64*3 + 8*4*0 + 6*8*(-1) + 6*8*1 + 3*16*(-1) + 1*8*(-3) + 6*4*(-1) + 8*2*0 + 3*32*1 + 6*16*1

/-- `F₂u` (`χ = 3,0,1,−1,−1,−3,1,0,1,−1`). -/
def aT2u_48 : ℤ := 1*64*3 + 8*4*0 + 6*8*1 + 6*8*(-1) + 3*16*(-1) + 1*8*(-3) + 6*4*1 + 8*2*0 + 3*32*1 + 6*16*(-1)

/-- **`³²SF₆`'s nuclear-spin decomposition** `Γ_nspin = 10A₁g ⊕ A₂g ⊕ 8E_g ⊕ 3F₂g ⊕ A₂u ⊕ 6F₁u ⊕ 3F₂u`
(Bunker–Jensen Eq. 14) — multiplicities `10,1,8,0,3,0,1,0,6,3`. -/
lemma sf6_multiplicities :
    aA1g_48 / 48 = 10 ∧ aA2g_48 / 48 = 1 ∧ aEg_48 / 48 = 8 ∧ aT1g_48 / 48 = 0 ∧ aT2g_48 / 48 = 3
      ∧ aA1u_48 / 48 = 0 ∧ aA2u_48 / 48 = 1 ∧ aEu_48 / 48 = 0 ∧ aT1u_48 / 48 = 6 ∧ aT2u_48 / 48 = 3 := by
  decide

/-! ## A.4. The Count -/

/-- **The decomposition recovers all `64` spin states** `Σ dim_Γ · a_Γ = 10·1 + 1·1 + 8·2 + 3·3 + 1·1 + 6·3 +
3·3 = 64 = 2⁶`. -/
lemma sf6_dimension_sum :
    aA1g_48 / 48 * 1 + aA2g_48 / 48 * 1 + aEg_48 / 48 * 2 + aT1g_48 / 48 * 3 + aT2g_48 / 48 * 3
      + aA1u_48 / 48 * 1 + aA2u_48 / 48 * 1 + aEu_48 / 48 * 2 + aT1u_48 / 48 * 3 + aT2u_48 / 48 * 3 = 64 := by
  decide

end Physlib.QuantumMechanics.ComplexAction.OctahedralNuclearSpinWeights
