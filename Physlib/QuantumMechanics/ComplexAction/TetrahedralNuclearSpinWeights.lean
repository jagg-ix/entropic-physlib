/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IcosahedralNuclearSpinWeights

/-!
# Methane `¹²CH₄` nuclear-spin symmetry: `Γ_nspin = 5A₁ ⊕ 3F₂ ⊕ E` (Bunker–Jensen Eq. 10)

Completes the Bunker & Jensen (1999) molecular set with the `T_d` nuclear-spin decomposition of methane — the
canonical fermionic example, complementing the `¹²C₆₀` boson case. The four spin-½ protons give `2⁴ = 16`
nuclear-spin states; under `T_d` these decompose as `5A₁ ⊕ 3F₂ ⊕ E` (`meta`/`ortho`/`para`, total nuclear spin
`I = 2, 1, 0`), with statistical weights `5, 9, 2` (`= 5·1, 3·3, 1·2`).

The multiplicities come from the same `(2I+1)^{cycles}` character: for the four `T_d` classes acting on the four
H atoms the cycle counts are `E→4, C₃→2, C₂→2, S₄→1, σ_d→3`, giving spin-½ characters `16, 4, 4, 2, 8`.

* **§A — the class characters.** `cyclesE/C3/C2/S4/Sigma` and `char_values` (`= 16, 4, 4, 2, 8`, from
  `nspinChar 2 cycles`).
* **§B — the decomposition.** `aA1_24 … aF2_24` (`= 24·a_Γ`, the class-weighted character sums);
  **`methane_multiplicities`** (`= 5, 0, 1, 0, 3`, i.e. `Γ_nspin = 5A₁ ⊕ 3F₂ ⊕ E`).
* **§C — the counts.** `methane_dimension_sum` (`Σ dim_Γ·a_Γ = 16 = 2⁴`, all spin states recovered) and
  `methane_binomial` (`Σ_k C(4,k) = 16` — the spin states by `m_I`, the `1,4,6,4,1` binomial).

**Honest layering.** The `(2I+1)^{cycles}` character law and the `T_d` character table are standard; the cycle
counts (`4,2,2,1,3`) are the `T_d` action on the four hydrogens (recorded). The multiplicities, the `5A₁⊕3F₂⊕E`
decomposition, and the dimension sum are derived (`decide`) and match Bunker–Jensen Eq. 10.

## References

* Bunker & Jensen, Mol. Phys. **97**, 255 (1999), Eqs. 9–10. Built on
  `ComplexAction.IcosahedralNuclearSpinWeights` (`nspinChar`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.IcosahedralNuclearSpinWeights

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TetrahedralNuclearSpinWeights


/-- Cycles of the identity on the four H atoms — all fixed (`4`). -/
def cyclesE : ℕ := 4

/-- Cycles of a `C₃` (about a C–H axis) — fixes one H, `3`-cycle on the rest (`2` orbits). -/
def cyclesC3 : ℕ := 2

/-- Cycles of a `C₂` — two `2`-cycles (`2` orbits). -/
def cyclesC2 : ℕ := 2

/-- Cycles of an `S₄` — a single `4`-cycle (`1` orbit). -/
def cyclesS4 : ℕ := 1

/-- Cycles of a `σ_d` — fixes two H, swaps two (`3` orbits). -/
def cyclesSigma : ℕ := 3

/-- **The spin-½ nuclear-spin characters** `16, 4, 4, 2, 8` — `2^{cycles}` for each `T_d` class. -/
lemma char_values :
    nspinChar 2 cyclesE = 16 ∧ nspinChar 2 cyclesC3 = 4 ∧ nspinChar 2 cyclesC2 = 4
      ∧ nspinChar 2 cyclesS4 = 2 ∧ nspinChar 2 cyclesSigma = 8 := by decide


/-- `A₁` multiplicity times `|T_d| = 24` — `Σ |class|·χ_nspin·χ_{A₁}` with `χ_{A₁} = (1,1,1,1,1)`. -/
def aA1_24 : ℤ := 1 * 16 * 1 + 8 * 4 * 1 + 3 * 4 * 1 + 6 * 2 * 1 + 6 * 8 * 1

/-- `A₂` multiplicity times `24` — `χ_{A₂} = (1,1,1,−1,−1)`. -/
def aA2_24 : ℤ := 1 * 16 * 1 + 8 * 4 * 1 + 3 * 4 * 1 + 6 * 2 * (-1) + 6 * 8 * (-1)

/-- `E` multiplicity times `24` — `χ_E = (2,−1,2,0,0)`. -/
def aE_24 : ℤ := 1 * 16 * 2 + 8 * 4 * (-1) + 3 * 4 * 2 + 6 * 2 * 0 + 6 * 8 * 0

/-- `F₁` multiplicity times `24` — `χ_{F₁} = (3,0,−1,1,−1)`. -/
def aF1_24 : ℤ := 1 * 16 * 3 + 8 * 4 * 0 + 3 * 4 * (-1) + 6 * 2 * 1 + 6 * 8 * (-1)

/-- `F₂` multiplicity times `24` — `χ_{F₂} = (3,0,−1,−1,1)`. -/
def aF2_24 : ℤ := 1 * 16 * 3 + 8 * 4 * 0 + 3 * 4 * (-1) + 6 * 2 * (-1) + 6 * 8 * 1

/-- **Methane's nuclear-spin decomposition** `Γ_nspin = 5A₁ ⊕ 3F₂ ⊕ E` — multiplicities `5, 0, 1, 0, 3`
(Bunker–Jensen Eq. 10). -/
lemma methane_multiplicities :
    aA1_24 / 24 = 5 ∧ aA2_24 / 24 = 0 ∧ aE_24 / 24 = 1 ∧ aF1_24 / 24 = 0 ∧ aF2_24 / 24 = 3 := by decide


/-- **The decomposition recovers all `16` spin states** `Σ dim_Γ · a_Γ = 5·1 + 1·2 + 3·3 = 16 = 2⁴`. -/
lemma methane_dimension_sum :
    aA1_24 / 24 * 1 + aA2_24 / 24 * 1 + aE_24 / 24 * 2 + aF1_24 / 24 * 3 + aF2_24 / 24 * 3 = 16 := by decide

/-- **The `5, 9, 2` statistical weights sum to `16`** `= 2⁴ = nspinChar 2 4` — the `A₁`/`F₂`/`E` (`I = 2, 1, 0`)
species. -/
lemma methane_weights : 5 * 1 + 3 * 3 + 1 * 2 = nspinChar 2 4 := by decide

/-- **The spin states by `m_I` are the binomial `1, 4, 6, 4, 1`** summing to `16` — `Σ_k C(4,k) = 2⁴`. -/
lemma methane_binomial :
    Nat.choose 4 0 + Nat.choose 4 1 + Nat.choose 4 2 + Nat.choose 4 3 + Nat.choose 4 4 = 16 := by decide

end Physlib.QuantumMechanics.ComplexAction.TetrahedralNuclearSpinWeights
