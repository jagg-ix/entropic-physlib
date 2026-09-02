/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IcosahedralHighJRotationalLevels
public import Physlib.QuantumMechanics.ComplexAction.IcosahedralBoseEinsteinC60

/-!
# A. `¹²C₆₀` Rotational Line Intensities

The observable of Chan et al. (2025): the intensity of a rotational transition is proportional to the
**nuclear-spin statistical weight** of the level. For the spin-0 boson `¹²C₆₀` the allowed total symmetry is
`A_g`, and since the single nuclear-spin state is itself `A_g`, the weight of level `J` is the `A_g` multiplicity
of `Γ_rot(J)` — the derived `agMultTimes60 J / 60`. This reproduces both the *missing lines* (weight `0`) and
the measured *intensity alternation* (the `2:1` and `3:2` ratios reported for `R(36):R(35)` and `R(66):R(65)`).

* **§A — the statistical weight.** `statisticalWeight J = agMultTimes60 J / 60` (`= a_A(J)`).
* **§B — missing and unit lines (`J < 30`).** `missing_line_zero_weight` (weight `0` on `forbiddenJ` — the 15
  absent lines) and `allowed_line_unit_weight` (weight `1` on `allowedJ`).
* **§C — the measured intensity alternation.** **`intensity_ratio_2_to_1`** (`R(36):R(35)` weights `2:1`) and
  **`intensity_ratio_3_to_2`** (`R(66):R(65)` weights `3:2`) — the icosahedral spin-statistical alternation seen
  in the 30 K spectra; `weight_R126` (weight `5`, the strong `R(126)` line).
* **§D — every high-`J` line is present.** `sixty_dvd` (`60 ∣ agMultTimes60`) and **`high_J_positive_weight`**
  (`J ≥ 30 ⟹ weight ≥ 1`) — no missing lines above `J = 29`, the weight growing like `J/30`.

## A.1. References

* Chan et al., Phys. Rev. Research **7**, L032029 (2025) — the `2:1`/`3:2` intensity alternation. Built on
  `ComplexAction.IcosahedralCharacterReduction` (`agMultTimes60`), `IcosahedralHighJRotationalLevels`,
  `IcosahedralBoseEinsteinC60` (`allowedJ`, `forbiddenJ`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.IcosahedralCharacterReduction
open Physlib.QuantumMechanics.ComplexAction.IcosahedralHighJRotationalLevels
open Physlib.QuantumMechanics.ComplexAction.IcosahedralBoseEinsteinC60

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationalIntensity

/-! ## A.2. The Statistical Weight -/

/-- The **nuclear-spin statistical weight** (line intensity) of rotational level `J` for `¹²C₆₀` — the `A_g`
multiplicity `a_A(J) = agMultTimes60 J / 60`. -/
def statisticalWeight (J : ℕ) : ℤ := agMultTimes60 J / 60

/-! ## A.3. Missing and Unit Lines -/

/-- **The 15 forbidden levels have zero weight** — the missing lines of `R(J < 30)`. -/
lemma missing_line_zero_weight : ∀ J ∈ forbiddenJ, statisticalWeight J = 0 := by decide

/-- **Each allowed level (`J < 30`) has unit weight** — statistical weight `1`. -/
lemma allowed_line_unit_weight : ∀ J ∈ allowedJ, statisticalWeight J = 1 := by decide

/-! ## A.4. The Measured Intensity Alternation -/

/-- **`R(36):R(35)` has a `2:1` intensity ratio** — weights `2` and `1` (the reported alternation). -/
lemma intensity_ratio_2_to_1 : statisticalWeight 36 = 2 ∧ statisticalWeight 35 = 1 := by decide

/-- **`R(66):R(65)` has a `3:2` intensity ratio** — weights `3` and `2` (the reported alternation). -/
lemma intensity_ratio_3_to_2 : statisticalWeight 66 = 3 ∧ statisticalWeight 65 = 2 := by decide

/-- **The `R(126)` line has weight `5`** — the strong high-`J` transition measured for thermometry. -/
lemma weight_R126 : statisticalWeight 126 = 5 := by decide

/-! ## A.5. Every High-`J` Line Is Present -/

/-- **The `A_g` class sum is divisible by 60** `60 ∣ agMultTimes60 J` — so the statistical weight
`agMultTimes60 J / 60` is a genuine non-negative multiplicity. -/
lemma sixty_dvd (J : ℕ) : (60 : ℤ) ∣ agMultTimes60 J := by
  induction J using Nat.strong_induction_on with
  | _ J ih =>
    by_cases h : J < 30
    · rcases multiplicity_zero_or_one J (Finset.mem_range.mpr h) with h' | h'
      · rw [h']; exact dvd_zero _
      · rw [h']
    · have heq : J = (J - 30) + 30 := by omega
      have hp := agMultTimes60_period (J - 30)
      rw [← heq] at hp
      have hih := ih (J - 30) (by omega)
      rw [hp]
      exact dvd_add hih (dvd_refl 60)

/-- **Every `J ≥ 30` line is present** `weight ≥ 1` — above `J = 29` there are no missing lines, the intensity
growing like `J / 30` (far below the `(2J+1)`-fold `K` degeneracy). -/
lemma high_J_positive_weight (J : ℕ) (h : 30 ≤ J) : 1 ≤ statisticalWeight J := by
  have hpos := all_high_J_allowed J h
  obtain ⟨k, hk⟩ := sixty_dvd J
  unfold statisticalWeight
  rw [hk] at hpos ⊢
  rw [Int.mul_ediv_cancel_left _ (by norm_num)]
  omega

end Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationalIntensity
