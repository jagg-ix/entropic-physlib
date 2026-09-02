/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IcosahedralCharacterReduction

/-!
# Cubic rotational-level reduction: SF₆ (`O_h`) and CH₄ (`T_d`)

The companion of `IcosahedralRotationalIrrepDecomposition` for the *cubic* spherical tops of Bunker & Jensen
(1999), Table 2. The rotational multiplet `D^J` of a cubic spherical top reduces onto the five irreps
`A₁, A₂, E, F₁, F₂` (dimensions `1, 1, 2, 3, 3`) shared by `T_d` (CH₄) and `O_h` (SF₆, with a `g` subscript):

  `Γ_rot(J) = a_{A₁}·A₁ ⊕ a_{A₂}·A₂ ⊕ a_E·E ⊕ a_{F₁}·F₁ ⊕ a_{F₂}·F₂`,

via `a_Γ(J) = (1/24)Σ|c|χ^J(c)χ^Γ(c)` over the classes of the octahedral rotation group `O` (order 24):
`E(1)`, `8C₃(120°)`, `3C₂(180°)`, `6C₄(90°)`, `6C₂'(180°)`. Unlike the icosahedral case there is **no golden
ratio** — the fourfold character `chi4 = 1,1,−1,−1` (over `J mod 4`) is already integer, so the dimension sum
rule closes directly.

* **§A — the fourfold character.** `chi4` (`χ^J(90°)`, period 4); reuses `chi3`, `chi2` from
  `IcosahedralCharacterReduction`. `irrepDims` (`1,1,2,3,3`), `irrepDims_sq_sum` (`= 24 = |O|`, Burnside).
* **§B — the five multiplicities.** `aA1_24`, `aA2_24`, `aE_24`, `aT1_24`, `aT2_24` (`= 24·a_Γ(J)`).
* **§C — the dimension sum rule and the table.** **`dimension_sum`** (`Σ dim_Γ · a_Γ(J) = 2J+1`, by `ring`);
  `rot_J1` (`F₁`), `rot_J2` (`E ⊕ F₂`), `sf6_J53` (`4A₁ ⊕ 4A₂ ⊕ 9E ⊕ 14F₁ ⊕ 13F₂`, Bunker–Jensen Eq. 7,
  dimension `107 = 2·53+1`).

**Honest layering.** `chi4` is the elementary `SO(3)` character at `90°`; the multiplicity formulas, the general
dimension sum rule, and the tabulated decompositions are derived (`ring`/`decide`) and validated against
Bunker–Jensen Table 2 and Eq. 7.

## References

* Bunker & Jensen, Mol. Phys. **97**, 255 (1999), Table 2, Eq. 7. Built on
  `ComplexAction.IcosahedralCharacterReduction` (`chi3`, `chi2`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.IcosahedralCharacterReduction

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.OctahedralRotationalReduction


/-- The **fourfold character** `χ^J(90°)` of the `6C₄` class — `1, 1, −1, −1` over `J mod 4`. -/
def chi4 (J : ℕ) : ℤ :=
  match J % 4 with
  | 0 => 1
  | 1 => 1
  | 2 => -1
  | _ => -1

/-- The **dimensions of the five cubic irreps** `A₁, A₂, E, F₁, F₂` — `1, 1, 2, 3, 3`. -/
def irrepDims : List ℕ := [1, 1, 2, 3, 3]

/-- **Burnside's dimension identity** `Σ dim² = 24 = |O|`. -/
lemma irrepDims_sq_sum : (irrepDims.map (· ^ 2)).sum = 24 := by decide


/-- The **`A₁` multiplicity times 24** `(2J+1) + 8·chi3 + 6·chi4 + 9·chi2`. -/
def aA1_24 (J : ℕ) : ℤ := (2 * (J : ℤ) + 1) + 8 * chi3 J + 6 * chi4 J + 9 * chi2 J

/-- The **`A₂` multiplicity times 24** `(2J+1) + 8·chi3 − 6·chi4 − 3·chi2`. -/
def aA2_24 (J : ℕ) : ℤ := (2 * (J : ℤ) + 1) + 8 * chi3 J - 6 * chi4 J - 3 * chi2 J

/-- The **`E` multiplicity times 24** `2(2J+1) − 8·chi3 + 6·chi2`. -/
def aE_24 (J : ℕ) : ℤ := 2 * (2 * (J : ℤ) + 1) - 8 * chi3 J + 6 * chi2 J

/-- The **`F₁` multiplicity times 24** `3(2J+1) + 6·chi4 − 9·chi2`. -/
def aT1_24 (J : ℕ) : ℤ := 3 * (2 * (J : ℤ) + 1) + 6 * chi4 J - 9 * chi2 J

/-- The **`F₂` multiplicity times 24** `3(2J+1) − 6·chi4 + 3·chi2`. -/
def aT2_24 (J : ℕ) : ℤ := 3 * (2 * (J : ℤ) + 1) - 6 * chi4 J + 3 * chi2 J


/-- **The dimension sum rule** `Σ dim_Γ · a_Γ(J) = 2J+1`: the five cubic multiplicities recover the full
`(2J+1)`-dimensional multiplet. The `chi3`, `chi4`, `chi2` cross-terms cancel directly (no golden ratio),
leaving `(1²+1²+2²+3²+3²)(2J+1)/24 = 2J+1`. -/
lemma dimension_sum (J : ℕ) :
    aA1_24 J + aA2_24 J + 2 * aE_24 J + 3 * aT1_24 J + 3 * aT2_24 J = 24 * (2 * (J : ℤ) + 1) := by
  unfold aA1_24 aA2_24 aE_24 aT1_24 aT2_24
  ring

/-- **`J = 1` spans `F₁`** (Bunker–Jensen Table 2). -/
lemma rot_J1 :
    aA1_24 1 = 0 ∧ aA2_24 1 = 0 ∧ aE_24 1 = 0 ∧ aT1_24 1 = 24 ∧ aT2_24 1 = 0 := by decide

/-- **`J = 2` spans `E ⊕ F₂`** (Bunker–Jensen Table 2). -/
lemma rot_J2 :
    aA1_24 2 = 0 ∧ aA2_24 2 = 0 ∧ aE_24 2 = 24 ∧ aT1_24 2 = 0 ∧ aT2_24 2 = 24 := by decide

/-- **`J = 53` (`SF₆`) spans `4A₁ ⊕ 4A₂ ⊕ 9E ⊕ 14F₁ ⊕ 13F₂`** (Bunker–Jensen Eq. 7) — dimension
`4 + 4 + 18 + 42 + 39 = 107 = 2·53 + 1`. -/
lemma sf6_J53 :
    aA1_24 53 = 96 ∧ aA2_24 53 = 96 ∧ aE_24 53 = 216 ∧ aT1_24 53 = 336 ∧ aT2_24 53 = 312 := by decide

end Physlib.QuantumMechanics.ComplexAction.OctahedralRotationalReduction
