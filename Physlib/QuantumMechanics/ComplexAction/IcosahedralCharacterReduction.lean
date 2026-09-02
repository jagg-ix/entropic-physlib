/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IcosahedralBoseEinsteinC60

/-!
# Deriving the icosahedral `A_g` selection rule by the character-sum reduction

Derives the allowed rotational levels of `IcosahedralBoseEinsteinC60` from first principles — the projection of
the spin-`J` `SO(3)` representation `D^J` onto the totally-symmetric `A_g` irrep of the icosahedral rotation
group `I` (order `60`). The multiplicity is the class-sum

  `n_A(J) = (1/60) · Σ_{classes} |class| · χ^J(θ_class)`,

with `χ^J(θ) = sin((2J+1)θ/2) / sin(θ/2)` the `SO(3)` character. The five classes of `I` are `E` (`1`, `0°`),
`12 C₅` (`72°`), `12 C₅²` (`144°`), `20 C₃` (`120°`), `15 C₂` (`180°`).

The one non-trivial step: the two five-fold classes have golden-ratio characters (`χ^J(72°) = 1, φ, 0, −φ, −1`
and `χ^J(144°) = 1, 1−φ, 0, φ−1, −1` over `J mod 5`), but their **sum cancels the golden ratio**, leaving the
integer `chi5 = 2, 1, 0, −1, −2`. The remaining characters are `chi3 = 1, 0, −1` (`J mod 3`) and
`chi2 = (−1)^J`. The reduction then multiplies out to an integer.

* **§A — the class characters.** `chi5`/`chi3`/`chi2` (the `SO(3)` characters at the icosahedral rotation
  angles); `class_sizes_sum` (`1+12+12+20+15 = 60 = |I|`).
* **§B — the multiplicity.** `agMultTimes60 J = (2J+1) + 12·chi5 + 20·chi3 + 15·chi2 = 60·n_A(J)`;
  `trivial_rep_J0` (`= 60`, so `n_A(0) = 1`).
* **§C — the derivation.** **`allowedJ_eq_character_reduction`**: `allowedJ = {J < 30 : n_A(J) > 0}` — the
  recorded allowed set *is* the character-sum reduction. `allowed_unit_multiplicity` (`n_A = 1` on allowed —
  statistical weight `1`) and `forbidden_zero_multiplicity` (`n_A = 0` on forbidden — the missing lines).

**Honest layering.** The class characters `chi5/chi3/chi2` are the elementary `SO(3)` characters at the
icosahedral angles (the golden-ratio cancellation in `chi5` is noted); everything downstream — the multiplicity
formula, `n_A(0) = 1`, and the full allowed/forbidden partition of `J < 30` — is *derived* (`decide`). This
upgrades `IcosahedralBoseEinsteinC60.allowedJ` from recorded data to a theorem.

## References

* Reduction of `SO(3)` `D^J` onto icosahedral irreps (Harter–Reimer, Chem. Phys. Lett. **194**, 230 (1992)).
  Built on `ComplexAction.IcosahedralBoseEinsteinC60` (`allowedJ`, `forbiddenJ`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.IcosahedralBoseEinsteinC60

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.IcosahedralCharacterReduction


/-- The **combined five-fold character** `χ^J(72°) + χ^J(144°)` of the two `C₅`-type classes — the golden ratio
cancels, leaving the integer values `2, 1, 0, −1, −2` over `J mod 5`. -/
def chi5 (J : ℕ) : ℤ :=
  match J % 5 with
  | 0 => 2
  | 1 => 1
  | 2 => 0
  | 3 => -1
  | _ => -2

/-- The **three-fold character** `χ^J(120°)` of the `C₃` class — `1, 0, −1` over `J mod 3`. -/
def chi3 (J : ℕ) : ℤ :=
  match J % 3 with
  | 0 => 1
  | 1 => 0
  | _ => -1

/-- The **two-fold character** `χ^J(180°) = (−1)^J` of the `C₂` class. -/
def chi2 (J : ℕ) : ℤ := if J % 2 = 0 then 1 else -1

/-- **The five icosahedral class sizes sum to the group order** `1 + 12 + 12 + 20 + 15 = 60 = |I|`. -/
lemma class_sizes_sum : 1 + 12 + 12 + 20 + 15 = 60 := by decide


/-- The **`A_g` multiplicity times `|I| = 60`** — the class-weighted character sum
`(2J+1) + 12·chi5 + 20·chi3 + 15·chi2`. The `A_g` multiplicity is `n_A(J) = agMultTimes60 J / 60`. -/
def agMultTimes60 (J : ℕ) : ℤ := (2 * (J : ℤ) + 1) + 12 * chi5 J + 20 * chi3 J + 15 * chi2 J

/-- **The `J = 0` level is the trivial representation** `n_A(0) = 1` (`agMultTimes60 0 = 60`). -/
lemma trivial_rep_J0 : agMultTimes60 0 = 60 := by decide


/-- **The allowed levels are the character-sum reduction** `allowedJ = {J < 30 : n_A(J) > 0}`: the recorded
`A_g`-allowed set of `IcosahedralBoseEinsteinC60` is exactly the set of `J < 30` whose `SO(3)` multiplet `D^J`
contains the icosahedral `A_g` irrep — derived, not posited. -/
lemma allowedJ_eq_character_reduction :
    allowedJ = (Finset.range 30).filter (fun J => 0 < agMultTimes60 J) := by decide

/-- **Every allowed level has statistical weight one** `n_A(J) = 1` (`agMultTimes60 = 60`) for `J ∈ allowedJ`
— matching the unit weights reported for `¹²C₆₀`. -/
lemma allowed_unit_multiplicity : ∀ J ∈ allowedJ, agMultTimes60 J = 60 := by decide

/-- **Every forbidden level has zero multiplicity** `n_A(J) = 0` (`agMultTimes60 = 0`) for `J ∈ forbiddenJ` —
the `A_g` irrep is absent, so the level vanishes (the missing lines). -/
lemma forbidden_zero_multiplicity : ∀ J ∈ forbiddenJ, agMultTimes60 J = 0 := by decide

/-- **The multiplicity is `0` or `1` throughout `J < 30`** — no allowed level below `J = 30` carries weight
greater than one. -/
lemma multiplicity_zero_or_one : ∀ J ∈ Finset.range 30, agMultTimes60 J = 0 ∨ agMultTimes60 J = 60 := by
  decide

end Physlib.QuantumMechanics.ComplexAction.IcosahedralCharacterReduction
