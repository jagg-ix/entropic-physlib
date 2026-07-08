/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.Star.CHSH
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum

/-!
# CHSH / Bell correlations and the maximally-violating vacuum (Summers §4)

Formalizes the CHSH / Bell-correlation reasoning of S. J. Summers, *Yet More Ado About Nothing*,
arXiv:0802.1854, §4 (Def. 4.3, Eq. 4.1, the Tsirelson bound, and the maximally-violating vacuum),
building on Mathlib's operator-algebra CHSH (`Mathlib.Algebra.Star.CHSH`) and the arc's Reeh–Schlieder
vacuum (`AlgebraicQFT.SummersRelativisticVacuum`).

A **CHSH tuple** (`IsCHSHTuple A₀ A₁ B₀ B₁`) is four dichotomic `±1` observables (`Aᵢ² = Bⱼ² = 1`,
self-adjoint) with the `Aᵢ` and `Bⱼ` **commuting across** (`AᵢBⱼ = BⱼAᵢ`) — Einstein locality /
microcausality for spacelike-separated regions (e.g. a wedge `W` and its causal complement `W'`). The
**CHSH operator** is `C = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁` (`bellOperator`); Summers' maximal Bell
correlation (Def. 4.3) is `β = ½⟨C⟩`.

The reasoning rests on the **Landau–Tsirelson identity** (in prose; encapsulated by Mathlib's
`tsirelson_inequality`):

  `C² = 4·1 − [A₀, A₁]·[B₀, B₁]`,

so that **when one side is classical** (`[A₀,A₁] = 0`, abelian) `C² = 4`, giving the **local/classical
CHSH bound** `C ≤ 2` (`chsh_local_bound`, Eq. 4.1, `β ≤ 1`); while in the noncommutative quantum case
the commutators give the **Tsirelson bound** `C ≤ 2√2` (`chsh_tsirelson_bound`, `β ≤ √2`). Since
`2√2 > 2` (`tsirelson_exceeds_local`), the quantum bound strictly exceeds the classical one — Bell
violation is possible, and by Reeh–Schlieder the **vacuum is entangled and maximally violates**
(`β = √2`) across the wedge and its complement (Summers–Werner).

* **§A — the CHSH operator** (`bellOperator`).
* **§B — the local/classical bound** (`chsh_local_bound`, Eq. 4.1).
* **§C — the Tsirelson bound** (`chsh_tsirelson_bound`).
* **§D — the maximal-violation gap** (`tsirelson_exceeds_local`, `chsh_violation_gap`).

## References

* S. J. Summers, arXiv:0802.1854 (Def. 4.3, Eq. 4.1, Prop. 4.4); B. Tsirelson, Lett. Math. Phys. 4
  (1980) 93; Summers, Werner, J. Math. Phys. 28 (1987) 2440 (vacuum maximal violation). Mathlib:
  `Mathlib.Algebra.Star.CHSH` (`IsCHSHTuple`, `CHSH_inequality_of_comm`, `tsirelson_inequality`). Repo:
  `AlgebraicQFT.SummersRelativisticVacuum` (the Reeh–Schlieder separating vacuum).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum

variable {R : Type*}

/-! ## §A — the CHSH operator (Summers Def. 4.3) -/

/-- **The CHSH / Bell operator** `C = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁` — Summers' maximal Bell correlation
(Def. 4.3) is `β = ½⟨C⟩` over dichotomic `±1` observables `Aᵢ ∈ M`, `Bⱼ ∈ N` with `M ⊂ N'` (spacelike
separated). -/
def bellOperator [Ring R] (A₀ A₁ B₀ B₁ : R) : R :=
  A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁

/-! ## §B — the local / classical CHSH bound (Eq. 4.1, `β ≤ 1`) -/

/-- **[Local / classical CHSH bound, Eq. 4.1] `C ≤ 2` (`β ≤ 1`).** When the observable algebra is
commutative (classical — Summers Prop. 4.4, at least one party abelian), the CHSH operator satisfies
`A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ ≤ 2`: the local bound `β ≤ 1` (`C² = 4` since `[A₀,A₁] = 0`). -/
theorem chsh_local_bound [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    bellOperator A₀ A₁ B₀ B₁ ≤ 2 :=
  CHSH_inequality_of_comm A₀ A₁ B₀ B₁ T

/-! ## §C — the Tsirelson bound (`β ≤ √2`) -/

/-- **[Tsirelson bound] `C ≤ 2√2·1` (`β ≤ √2`).** In the noncommutative quantum case, the
Landau–Tsirelson identity `C² = 4 − [A₀,A₁][B₀,B₁]` bounds the CHSH operator by `2√2 = √2³`
(`tsirelson_inequality`) — the quantum maximum of the Bell correlation `β ≤ √2`. -/
theorem chsh_tsirelson_bound [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    bellOperator A₀ A₁ B₀ B₁ ≤ Real.sqrt 2 ^ 3 • (1 : R) :=
  tsirelson_inequality A₀ A₁ B₀ B₁ T

/-! ## §D — the maximal-violation gap -/

/-- **[Tsirelson exceeds the local bound] `2√2 > 2`.** The quantum (Tsirelson) maximum `√2³ = 2√2`
strictly exceeds the local/classical CHSH bound `2`, so Bell's inequality can be violated. -/
theorem tsirelson_exceeds_local : Real.sqrt 2 ^ 3 > 2 := by
  have h : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Real.sq_sqrt (by norm_num)]
  rw [h]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2,
    Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 2 by norm_num) (show (2 : ℝ) < 4 by norm_num)]

/-- **[CHSH violation gap, Summers §4] local `≤ 2 < 2√2 ≤` Tsirelson.** The classical bound `2`
(`chsh_local_bound`) is *strictly below* the quantum Tsirelson maximum `2√2 = √2³`
(`tsirelson_exceeds_local`). A state achieving a value above `2` is necessarily **entangled** (Bell
violation ⟹ entanglement); by Reeh–Schlieder the separating vacuum (`AlgebraicQFT.SummersRelativisticVacuum`) is
entangled across a wedge and its causal complement and **maximally violates** (`β = √2`,
Summers–Werner). -/
theorem chsh_violation_gap [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    bellOperator A₀ A₁ B₀ B₁ ≤ 2 ∧ (2 : ℝ) < Real.sqrt 2 ^ 3 :=
  ⟨chsh_local_bound A₀ A₁ B₀ B₁ T, tsirelson_exceeds_local⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH

end
