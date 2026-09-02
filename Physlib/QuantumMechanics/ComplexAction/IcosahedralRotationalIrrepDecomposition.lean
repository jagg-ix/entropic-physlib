/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IcosahedralCharacterReduction

/-!
# The full icosahedral rotational-level decomposition (Bunker–Jensen 1999)

Extends the `A_g`-only reduction of `IcosahedralCharacterReduction` to the **complete** decomposition of every
rotational multiplet `D^J` into the five gerade icosahedral irreps, following Bunker & Jensen, *Spherical top
molecules and the molecular symmetry group*, Mol. Phys. **97**, 255 (1999), Table 3:

  `Γ_rot(J) = a_A·A_g ⊕ a_{F₁}·F_{1g} ⊕ a_{F₂}·F_{2g} ⊕ a_G·G_g ⊕ a_H·H_g`,

with irrep dimensions `1, 3, 3, 4, 5`. Each multiplicity is a class-sum `a_Γ(J) = (1/60)Σ|c|χ^J(c)χ^Γ(c)`.
The two five-fold classes carry golden-ratio characters, but the weighted combinations
`s₁ = χ^J(72°)φ + χ^J(144°)(1−φ)` (for `F₁`) and `s₂` (for `F₂`) are **integer-valued**
(`s₁ = 1,3,0,−3,−1`, `s₂ = 1,−2,0,2,−1` over `J mod 5`), with `s₁ + s₂ = chi5`.

* **§A — the irreps and five-fold characters.** `irrepDims` (`1,3,3,4,5`), `irrepDims_sq_sum` (`= 60 = |I|`,
  Burnside); `s1`, `s2` and `s1_add_s2` (`= chi5`).
* **§B — the five multiplicities.** `aT160`, `aT260`, `aG60`, `aH60` (`= 60·a_Γ(J)`; `a_A` is
  `IcosahedralCharacterReduction.agMultTimes60`).
* **§C — the dimension sum rule and the table.** **`dimension_sum`** (`Σ dim_Γ · a_Γ(J) = 2J+1` for all `J` —
  the multiplet dimension is recovered); `rot_J1` (`F_{1g}`), `rot_J3` (`F_{2g} ⊕ G_g`), `rot_J100`
  (`4A_g ⊕ 10F_{1g} ⊕ 10F_{2g} ⊕ 13G_g ⊕ 17H_g`, Bunker–Jensen Eq. 8).

**Honest layering.** The five-fold combinations `s1, s2` are the (integer) `SO(3)×I`-character products at the
icosahedral angles (golden-ratio cancellation noted). The multiplicity formulas, the `s1+s2 = chi5` identity,
the general dimension sum rule, and the tabulated decompositions are all *derived* (`linear_combination` /
`decide`), and validated against Bunker–Jensen Table 3.

## References

* Bunker & Jensen, Mol. Phys. **97**, 255 (1999), Tables 3 & Eq. 8. Built on
  `ComplexAction.IcosahedralCharacterReduction` (`chi5`, `chi3`, `chi2`, `agMultTimes60`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.IcosahedralCharacterReduction

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationalIrrepDecomposition


/-- The **dimensions of the five gerade icosahedral irreps** `A_g, F_{1g}, F_{2g}, G_g, H_g` — `1, 3, 3, 4, 5`. -/
def irrepDims : List ℕ := [1, 3, 3, 4, 5]

/-- **Burnside's dimension identity** `Σ dim² = 60 = |I|`. -/
lemma irrepDims_sq_sum : (irrepDims.map (· ^ 2)).sum = 60 := by decide

/-- The **`F₁`-weighted five-fold character** `s₁ = χ^J(72°)·φ + χ^J(144°)·(1−φ)` — golden ratio cancels,
leaving `1, 3, 0, −3, −1` over `J mod 5`. -/
def s1 (J : ℕ) : ℤ :=
  match J % 5 with
  | 0 => 1
  | 1 => 3
  | 2 => 0
  | 3 => -3
  | _ => -1

/-- The **`F₂`-weighted five-fold character** `s₂ = χ^J(72°)·(1−φ) + χ^J(144°)·φ` — `1, −2, 0, 2, −1` over
`J mod 5`. -/
def s2 (J : ℕ) : ℤ :=
  match J % 5 with
  | 0 => 1
  | 1 => -2
  | 2 => 0
  | 3 => 2
  | _ => -1

/-- **The five-fold characters sum to `chi5`** `s₁ + s₂ = chi5` — the `F₁` and `F₂` weights combine to the
`A`/`G` weight (their sum recovers `χ^J(72°) + χ^J(144°)`). -/
lemma s1_add_s2 (J : ℕ) : s1 J + s2 J = chi5 J := by
  obtain h | h | h | h | h : J % 5 = 0 ∨ J % 5 = 1 ∨ J % 5 = 2 ∨ J % 5 = 3 ∨ J % 5 = 4 := by omega
  all_goals simp [s1, s2, chi5, h]


/-- The **`F_{1g}` multiplicity times 60** `3(2J+1) + 12·s₁ − 15·chi2`. -/
def aT160 (J : ℕ) : ℤ := 3 * (2 * (J : ℤ) + 1) + 12 * s1 J - 15 * chi2 J

/-- The **`F_{2g}` multiplicity times 60** `3(2J+1) + 12·s₂ − 15·chi2`. -/
def aT260 (J : ℕ) : ℤ := 3 * (2 * (J : ℤ) + 1) + 12 * s2 J - 15 * chi2 J

/-- The **`G_g` multiplicity times 60** `4(2J+1) − 12·chi5 + 20·chi3`. -/
def aG60 (J : ℕ) : ℤ := 4 * (2 * (J : ℤ) + 1) - 12 * chi5 J + 20 * chi3 J

/-- The **`H_g` multiplicity times 60** `5(2J+1) − 20·chi3 + 15·chi2`. -/
def aH60 (J : ℕ) : ℤ := 5 * (2 * (J : ℤ) + 1) - 20 * chi3 J + 15 * chi2 J


/-- **The dimension sum rule** `Σ dim_Γ · a_Γ(J) = 2J+1`: the five icosahedral multiplicities recover the full
`(2J+1)`-dimensional rotational multiplet. The `chi5`, `chi3`, `chi2` cross-terms cancel (using `s₁+s₂ = chi5`),
leaving `(1²+3²+3²+4²+5²)(2J+1)/60 = 2J+1`. -/
lemma dimension_sum (J : ℕ) :
    agMultTimes60 J + 3 * aT160 J + 3 * aT260 J + 4 * aG60 J + 5 * aH60 J = 60 * (2 * (J : ℤ) + 1) := by
  have hs := s1_add_s2 J
  unfold agMultTimes60 aT160 aT260 aG60 aH60
  linear_combination 36 * hs

/-- **`J = 1` spans `F_{1g}`** — `a_A = a_{F₂} = a_G = a_H = 0`, `a_{F₁} = 1` (Bunker–Jensen Table 3). -/
lemma rot_J1 :
    agMultTimes60 1 = 0 ∧ aT160 1 = 60 ∧ aT260 1 = 0 ∧ aG60 1 = 0 ∧ aH60 1 = 0 := by decide

/-- **`J = 3` spans `F_{2g} ⊕ G_g`** (Bunker–Jensen Table 3). -/
lemma rot_J3 :
    agMultTimes60 3 = 0 ∧ aT160 3 = 0 ∧ aT260 3 = 60 ∧ aG60 3 = 60 ∧ aH60 3 = 0 := by decide

/-- **`J = 100` spans `4A_g ⊕ 10F_{1g} ⊕ 10F_{2g} ⊕ 13G_g ⊕ 17H_g`** (Bunker–Jensen Eq. 8) — dimension
`4 + 30 + 30 + 52 + 85 = 201 = 2·100 + 1`. -/
lemma rot_J100 :
    agMultTimes60 100 = 240 ∧ aT160 100 = 600 ∧ aT260 100 = 600 ∧ aG60 100 = 780 ∧ aH60 100 = 1020 := by
  decide

end Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationalIrrepDecomposition
