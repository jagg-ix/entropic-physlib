/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.IcosahedralCharacterReduction

/-!
# High-`J` rotational levels: quasi-periodicity of the icosahedral `A_g` multiplicity

Completes the `A_g` selection rule of `IcosahedralCharacterReduction` for all `J`. The icosahedral class
characters `chi5, chi3, chi2` have periods `5, 3, 2` — all dividing `30` — so only the linear `2J+1` term of the
character sum shifts under `J ↦ J + 30`. Hence the multiplicity satisfies

  `n_A(J + 30) = n_A(J) + 1`,

increasing by exactly one every period of `30`. Consequently **every `J ≥ 30` level is allowed** (its `A_g`
multiplicity is positive), with a statistical weight that grows only like `J / 30` — far below the `(2J+1)`-fold
`K`-degeneracy — exactly as reported for `¹²C₆₀` ("all `J ≥ 30` levels exist but with weight much less than
`2J+1`").

* **§A — periodicity.** `chi5_period`/`chi3_period`/`chi2_period` (period `30`) and **`agMultTimes60_period`**
  (`agMultTimes60 (J+30) = agMultTimes60 J + 60`, i.e. `n_A(J+30) = n_A(J) + 1`).
* **§B — all high-`J` levels exist.** `agMultTimes60_nonneg` (the multiplicity is a genuine non-negative
  count) and **`all_high_J_allowed`** (`30 ≤ J ⟹ 0 < n_A(J)` — no missing lines above `J = 29`).
* **§C — the second period.** `second_period_all_allowed` (`30 ≤ J ≤ 59 ⟹` allowed) — the concrete next block,
  contrasting the 15 gaps of the first period.

**Honest layering.** All results are derived: the period-`30` invariance from the class-character periods, the
`+1` multiplicity shift, non-negativity (by induction on the period), and the positivity for `J ≥ 30`. Built on
the character reduction of `IcosahedralCharacterReduction`.

## References

* Quasi-periodicity of `SO(3) ↓ I` reduction multiplicities. Built on
  `ComplexAction.IcosahedralCharacterReduction` (`agMultTimes60`, `multiplicity_zero_or_one`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.IcosahedralCharacterReduction

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.IcosahedralHighJRotationalLevels


/-- **The five-fold character has period 30** (period `5` divides `30`). -/
lemma chi5_period (J : ℕ) : chi5 (J + 30) = chi5 J := by
  have h : (J + 30) % 5 = J % 5 := by omega
  unfold chi5; rw [h]

/-- **The three-fold character has period 30** (period `3` divides `30`). -/
lemma chi3_period (J : ℕ) : chi3 (J + 30) = chi3 J := by
  have h : (J + 30) % 3 = J % 3 := by omega
  unfold chi3; rw [h]

/-- **The two-fold character has period 30** (period `2` divides `30`). -/
lemma chi2_period (J : ℕ) : chi2 (J + 30) = chi2 J := by
  have h : (J + 30) % 2 = J % 2 := by omega
  unfold chi2; rw [h]

/-- **The `A_g` multiplicity grows by one per period of 30** `agMultTimes60 (J+30) = agMultTimes60 J + 60`, i.e.
`n_A(J+30) = n_A(J) + 1`: only the linear `2J+1` term shifts, the class characters being period-`30`. -/
lemma agMultTimes60_period (J : ℕ) : agMultTimes60 (J + 30) = agMultTimes60 J + 60 := by
  unfold agMultTimes60
  rw [chi5_period, chi3_period, chi2_period]
  push_cast
  ring


/-- **The multiplicity is a non-negative count** `0 ≤ agMultTimes60 J` for every `J` (it is `60·n_A(J)` with
`n_A(J) ≥ 0`). -/
lemma agMultTimes60_nonneg (J : ℕ) : 0 ≤ agMultTimes60 J := by
  induction J using Nat.strong_induction_on with
  | _ J ih =>
    by_cases h : J < 30
    · have := multiplicity_zero_or_one J (Finset.mem_range.mpr h)
      omega
    · have hlt : J - 30 < J := by omega
      have hih := ih (J - 30) hlt
      have heq : J = (J - 30) + 30 := by omega
      have hp := agMultTimes60_period (J - 30)
      rw [← heq] at hp
      omega

/-- **Every `J ≥ 30` level is allowed** `0 < n_A(J)` — above `J = 29` there are no missing lines; the icosahedral
`A_g` irrep appears in every rotational multiplet, with a weight `≈ J/30` far below the `(2J+1)`-fold `K`
degeneracy. -/
lemma all_high_J_allowed (J : ℕ) (h : 30 ≤ J) : 0 < agMultTimes60 J := by
  have heq : J = (J - 30) + 30 := by omega
  have hp := agMultTimes60_period (J - 30)
  rw [← heq] at hp
  have hnn := agMultTimes60_nonneg (J - 30)
  omega


/-- **The whole second period `30 ≤ J ≤ 59` is allowed** — in contrast to the fifteen gaps of the first period,
every level exists (each already with multiplicity at least one). -/
lemma second_period_all_allowed : ∀ J ∈ Finset.Icc 30 59, 0 < agMultTimes60 J := by
  intro J hJ
  simp only [Finset.mem_Icc] at hJ
  exact all_high_J_allowed J hJ.1

end Physlib.QuantumMechanics.ComplexAction.IcosahedralHighJRotationalLevels
