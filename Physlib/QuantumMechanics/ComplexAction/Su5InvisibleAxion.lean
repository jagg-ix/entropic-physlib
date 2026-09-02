/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor

/-!
# A. `SU(5)` and the Invisible Axion

Wise, Georgi and Glashow embed the Dine–Fischler–Srednicki (DFS) invisible axion in `SU(5)`: the axion
is the phase of the `SU(3)⊗SU(2)⊗U(1)`-singlet component of a complex adjoint `24` field `Σ`
(a traceless `5×5` matrix), whose vacuum expectation value both breaks `SU(5)` to the Standard Model
and provides the large Peccei–Quinn scale `M_u` that makes the axion invisible.

Building on the `su(5)` weight system (`IsAffineWeight` = tracelessness, the `SU(5)` Cartan structure
of `Su5ChargeQuantizationCartanTensor`), this formalizes the model's algebraic content.

* **§A — the `⟨Σ⟩` VEV and `SU(5) → SU(3)⊗SU(2)⊗U(1)`.** `sigmaVEV ε = (2, 2, 2, −3−ε, −3+ε)` is the
  diagonal of `⟨Σ⟩` (Eq. 8). It is **traceless** — a genuine adjoint `24` — for every `ε`
  (`sigmaVEV_isAffineWeight`, reusing `IsAffineWeight`). The three equal colour entries keep `SU(3)`
  unbroken (`sigmaVEV_su3_unbroken`); the last two entries are equal — `SU(2)_L` unbroken — iff
  `ε = 0` (`su2_unbroken_iff_eps_zero`). At `ε = 0` the VEV is the hypercharge direction
  `(2,2,2,−3,−3)` commuting with `SU(3)⊗SU(2)` (`sigmaVEV_zero_hypercharge`).
* **§B — the Peccei–Quinn symmetry (Eqs. 1–3, 7).** The PQ charges
  `(T, F, H₁, H₂, Σ) = (−1/2, +1/2, +1, −1, −1)` make every Yukawa and scalar coupling PQ-neutral
  (`yukawa1_pq_neutral`, `yukawa2_pq_neutral`, `potential_gTerm_pq_neutral`,
  `potential_hTerm_pq_neutral`): the total PQ charge of each coupling vanishes, exactly the
  "charges sum to zero" pattern of `SU(5)` tracelessness. Because `Σ` carries PQ charge `−1`, the
  phase of its singlet VEV is the axion.

## A.1. References

* M. B. Wise, H. Georgi, S. L. Glashow, "SU(5) and the Invisible Axion", Phys. Rev. Lett. **47**, 402
  (1981) [`Wise:1981ry`], Eqs. (1)–(9). Reuses `Su5ChargeQuantizationCartanTensor` /
  `LeviCivita.SorkinSimplecticNetR4` (`IsAffineWeight`, the `SU(5)` Cartan/weight structure).


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Su5InvisibleAxion

open Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4

/-! ## A.2. The `⟨Σ⟩` VEV and `SU(5) → SU(3)⊗SU(2)⊗U(1)` -/

/-- **The diagonal of the adjoint VEV `⟨Σ⟩`** (Wise–Georgi–Glashow Eq. 8, up to the overall `λ₀/2`):
`(2, 2, 2, −3−ε, −3+ε)`. The parameter `ε` controls `SU(2)_L` breaking. -/
def sigmaVEV (ε : ℝ) : Fin 5 → ℝ := ![2, 2, 2, -3 - ε, -3 + ε]

/-- **`⟨Σ⟩` is a traceless adjoint `24`**: its diagonal sums to zero for every `ε` — the affine/
traceless condition of the `su(5)` weight system. -/
lemma sigmaVEV_isAffineWeight (ε : ℝ) : IsAffineWeight (sigmaVEV ε) := by
  unfold IsAffineWeight sigmaVEV
  simp [Fin.sum_univ_five]; ring

/-- **`SU(3)` colour stays unbroken**: the first three (colour) entries of `⟨Σ⟩` are equal, for every
`ε` — the VEV is an `SU(3)` singlet. -/
lemma sigmaVEV_su3_unbroken (ε : ℝ) :
    sigmaVEV ε 0 = sigmaVEV ε 1 ∧ sigmaVEV ε 1 = sigmaVEV ε 2 := by
  simp [sigmaVEV]

/-- **`SU(2)_L` is unbroken iff `ε = 0`**: the last two entries of `⟨Σ⟩` are equal precisely when
`ε = 0`; a nonzero `ε` splits them and breaks `SU(2)_L → U(1)`. -/
lemma su2_unbroken_iff_eps_zero (ε : ℝ) : sigmaVEV ε 3 = sigmaVEV ε 4 ↔ ε = 0 := by
  simp only [sigmaVEV, Matrix.cons_val]
  constructor <;> intro h <;> [linarith; (rw [h]; ring)]

/-- **At `ε = 0` the VEV is the hypercharge direction** `(2, 2, 2, −3, −3)` — proportional to the
`SU(5)` hypercharge generator `Y ∝ diag(−1/3,−1/3,−1/3, 1/2, 1/2)`, the unique (traceless) direction
commuting with `SU(3)⊗SU(2)`, so `SU(5) → SU(3)⊗SU(2)⊗U(1)`. -/
lemma sigmaVEV_zero_hypercharge : sigmaVEV 0 = ![2, 2, 2, -3, -3] := by
  funext i; fin_cases i <;> simp [sigmaVEV]

/-! ## A.3. The Peccei-Quinn Symmetry and the Axion -/

/-- The fields of the model: the fermion `10` `T`, the fermion `5̄` `F`, the two Higgs `5`'s
`H₁`, `H₂`, and the adjoint `24` `Σ`. -/
inductive Su5Field
  | T | F | H₁ | H₂ | Sig

/-- **The Peccei–Quinn charges** (Wise–Georgi–Glashow Eqs. 2–3):
`q(T) = −1/2`, `q(F) = +1/2`, `q(H₁) = +1`, `q(H₂) = −1`, `q(Σ) = −1`. -/
def pqCharge : Su5Field → ℚ
  | .T => -1/2
  | .F => 1/2
  | .H₁ => 1
  | .H₂ => -1
  | .Sig => -1

/-- **The first Yukawa `T^c T H₁` (Eq. 1) is PQ-neutral**: `2 q(T) + q(H₁) = 0`. -/
lemma yukawa1_pq_neutral : 2 * pqCharge .T + pqCharge .H₁ = 0 := by norm_num [pqCharge]

/-- **The second Yukawa `T̄ F H₂` (Eq. 1) is PQ-neutral**: `−q(T) + q(F) + q(H₂) = 0`. -/
lemma yukawa2_pq_neutral : - pqCharge .T + pqCharge .F + pqCharge .H₂ = 0 := by norm_num [pqCharge]

/-- **The scalar coupling `g H₂^† Σ² H₁` (Eq. 7) is PQ-neutral**: `−q(H₂) + 2 q(Σ) + q(H₁) = 0`. This
term fixes the `Σ` PQ charge relative to the Higgs, tying the axion to the `SU(5)`-breaking field. -/
lemma potential_gTerm_pq_neutral :
    - pqCharge .H₂ + 2 * pqCharge .Sig + pqCharge .H₁ = 0 := by norm_num [pqCharge]

/-- **The scalar coupling `h H₂^† H₁ Tr(Σ²)` (Eq. 7) is PQ-neutral**: `−q(H₂) + q(H₁) + 2 q(Σ) = 0`. -/
lemma potential_hTerm_pq_neutral :
    - pqCharge .H₂ + pqCharge .H₁ + 2 * pqCharge .Sig = 0 := by norm_num [pqCharge]

/-- **`Σ` carries nonzero PQ charge** (`q(Σ) = −1 ≠ 0`): the phase of the `SU(3)⊗SU(2)⊗U(1)`-singlet
component of its VEV is the (invisible) axion — the Nambu–Goldstone boson of the broken PQ symmetry. -/
lemma sigma_pq_charged : pqCharge .Sig ≠ 0 := by norm_num [pqCharge]

end Physlib.QuantumMechanics.ComplexAction.Su5InvisibleAxion
