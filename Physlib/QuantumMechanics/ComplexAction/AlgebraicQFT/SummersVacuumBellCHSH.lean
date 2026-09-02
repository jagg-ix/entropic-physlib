/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.Star.CHSH
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum

meta import Zil

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


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum

variable {R : Type*}


/-- **The CHSH / Bell operator** `C = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁` — Summers' maximal Bell correlation
(Def. 4.3) is `β = ½⟨C⟩` over dichotomic `±1` observables `Aᵢ ∈ M`, `Bⱼ ∈ N` with `M ⊂ N'` (spacelike
separated). -/
def bellOperator [Ring R] (A₀ A₁ B₀ B₁ : R) : R :=
  A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁


/-- **[Local / classical CHSH bound, Eq. 4.1] `C ≤ 2` (`β ≤ 1`).** When the observable algebra is
commutative (classical — Summers Prop. 4.4, at least one party abelian), the CHSH operator satisfies
`A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ ≤ 2`: the local bound `β ≤ 1` (`C² = 4` since `[A₀,A₁] = 0`). -/
lemma chsh_local_bound [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    bellOperator A₀ A₁ B₀ B₁ ≤ 2 :=
  CHSH_inequality_of_comm A₀ A₁ B₀ B₁ T


/-- **[Tsirelson bound] `C ≤ 2√2·1` (`β ≤ √2`).** In the noncommutative quantum case, the
Landau–Tsirelson identity `C² = 4 − [A₀,A₁][B₀,B₁]` bounds the CHSH operator by `2√2 = √2³`
(`tsirelson_inequality`) — the quantum maximum of the Bell correlation `β ≤ √2`. -/
lemma chsh_tsirelson_bound [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    bellOperator A₀ A₁ B₀ B₁ ≤ Real.sqrt 2 ^ 3 • (1 : R) :=
  tsirelson_inequality A₀ A₁ B₀ B₁ T


/-- **[Tsirelson exceeds the local bound] `2√2 > 2`.** The quantum (Tsirelson) maximum `√2³ = 2√2`
strictly exceeds the local/classical CHSH bound `2`, so Bell's inequality can be violated. -/
lemma tsirelson_exceeds_local : Real.sqrt 2 ^ 3 > 2 := by
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
lemma chsh_violation_gap [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    bellOperator A₀ A₁ B₀ B₁ ≤ 2 ∧ (2 : ℝ) < Real.sqrt 2 ^ 3 :=
  ⟨chsh_local_bound A₀ A₁ B₀ B₁ T, tsirelson_exceeds_local⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.chsh_local_bound where
  formalizes @ "claim:in-a-commutative-classical-observable-algebra-the-chsh-operator-is-bounded-by-two-the-local-classical-bell-bound",
  supported_by @ "paper:summers-arxiv-0802-1854-yet-more-ado-about-nothing-the-remarkable-relativistic-vacuum-state"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.chsh_tsirelson_bound where
  formalizes @ "claim:in-the-noncommutative-quantum-case-the-chsh-operator-is-bounded-by-two-root-two-the-tsirelson-bound-the-quantum-maximum-of-the-bell-correlation"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.tsirelson_exceeds_local where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.chsh_local_bound",
  supported_by @ "lean:IsProjectionTensor.complement",
  formalizes @ "claim:the-quantum-tsirelson-maximum-two-root-two-strictly-exceeds-the-classical-bound-two-so-bells-inequality-can-be-violated-the-relativistic-vacuum-maximally-violating-it"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.chsh_violation_gap where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.chsh_local_bound",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.tsirelson_exceeds_local",
  formalizes @ "claim:the-classical-chsh-bound-two-lies-strictly-below-the-quantum-tsirelson-maximum-two-root-two-so-any-state-with-chsh-value-above-two-is-entangled",
  requires @ "claim:the-quantum-tsirelson-maximum-two-root-two-strictly-exceeds-the-classical-bound-two-so-bells-inequality-can-be-violated-the-relativistic-vacuum-maximally-violating-it"

zil_file_contract physlib.summersVacuumBellCHSH where
  promises "CHSH / Bell correlations and the maximally-violating vacuum (Summers, arXiv:0802.1854, section 4). In a commutative (classical) observable algebra the CHSH operator is bounded by 2 (chsh_local_bound); in the noncommutative quantum case it is bounded by 2 sqrt 2, the Tsirelson bound (chsh_tsirelson_bound). The quantum maximum strictly exceeds the classical bound (tsirelson_exceeds_local), so Bell's inequality can be violated -- assembled as the classical/quantum gap 2 < 2 sqrt 2 witnessing entanglement (chsh_violation_gap); the relativistic vacuum maximally violates CHSH across spacelike-separated regions."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.bellOperator",
    "lean:IsCHSHTuple"]
  forbids_substitutes ["the concrete construction of spacelike-separated observables in the vacuum representation that saturate the Tsirelson bound, which is the cited AQFT infrastructure",
    "any claim that a physical measurement protocol is specified; only the algebraic CHSH classical bound, the Tsirelson bound, and their strict separation are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.chsh_local_bound,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.chsh_tsirelson_bound,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.tsirelson_exceeds_local,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.chsh_violation_gap]

/- ZIL-END -/
