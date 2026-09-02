/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Tactic.Abel

/-!
# The Moyal / Baker split of the operator product

Formalizes the central algebraic content of B. Hiley, *On the relationship between the Wigner–Moyal approach
and the quantum operator algebra of von Neumann* (2015): on the operator algebra (here any associative
`ℂ`-algebra `R`, the von Neumann picture in which the Moyal star product *is* the operator product), the
product of two observables splits into a symmetric and an antisymmetric part —

  the **Baker bracket** (Jordan / anticommutator product) `{a, b}_BB = ½(ab + ba)` (`bakerBracket`),
  the **Moyal bracket** (commutator) `{a, b}_MB = (ab − ba)/(iℏ)` (`moyalBracket`).

The Baker bracket is **symmetric** (`bakerBracket_comm`), the Moyal bracket **antisymmetric**
(`moyalBracket_antisymm`), and the operator product is their sum:

  `ab = {a, b}_BB + (iℏ/2)·{a, b}_MB`   (`product_eq_baker_add_moyal`).

This is Hiley's "Moyal bracket = commutator side; Baker bracket = anticommutator/energy side". The **classical
limit** is the commutative one: when `a` and `b` commute the Moyal bracket vanishes
(`moyalBracket_eq_zero_of_commute`) and the Baker bracket reduces to ordinary multiplication
(`bakerBracket_eq_of_commute`) — the Moyal bracket becomes the (vanishing) Poisson bracket, the Baker bracket
becomes the commutative product. Finally the **pure-state idempotency** `{F, F}_BB = F ⟺ F² = F`
(`bakerBracket_self`, `bakerBracket_self_eq_iff`) is the operator analogue of `ρ² = ρ` (a pure density
matrix).

(The Wigner-transform / Weyl-symbol / continuous integral layer of the paper is not formalized; this is the
exact finite operator-algebra core.)

* **§A — the two brackets** (`bakerBracket`, `moyalBracket`, `bakerBracket_comm`, `moyalBracket_antisymm`).
* **§B — the product split and classical limit** (`product_eq_baker_add_moyal`,
  `moyalBracket_eq_zero_of_commute`, `bakerBracket_eq_of_commute`).
* **§C — pure-state idempotency** (`bakerBracket_self`, `bakerBracket_self_eq_iff`).

## References

* B. J. Hiley (2015), §2.9–§2.11; J. E. Moyal; H. F. Baker / P. Jordan (the symmetric product). Carrier:
  `Mathlib` (`ℂ`-algebra, `Complex.I`); cf. `Moyal.BracketTodaLattice` (the finite-mode first-order bracket).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Moyal.BakerOperatorSplit

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- Local helper: `(2 : ℂ) • x = x + x`. -/
private lemma two_smul_eq (x : R) : (2 : ℂ) • x = x + x := by
  rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]


/-- **The Baker bracket** (Jordan / anticommutator product) `{a, b}_BB = ½(ab + ba)`. -/
noncomputable def bakerBracket (a b : R) : R := (2⁻¹ : ℂ) • (a * b + b * a)

/-- **The Moyal bracket** (commutator over `iℏ`) `{a, b}_MB = (ab − ba)/(iℏ)`. -/
noncomputable def moyalBracket (ℏ : ℝ) (a b : R) : R := (Complex.I * (ℏ : ℂ))⁻¹ • (a * b - b * a)

/-- **[The Baker bracket is symmetric] `{a, b}_BB = {b, a}_BB`.** -/
lemma bakerBracket_comm (a b : R) : bakerBracket a b = bakerBracket b a := by
  rw [bakerBracket, bakerBracket, add_comm]

/-- **[The Moyal bracket is antisymmetric] `{a, b}_MB = −{b, a}_MB`.** -/
lemma moyalBracket_antisymm (ℏ : ℝ) (a b : R) :
    moyalBracket ℏ a b = -moyalBracket ℏ b a := by
  rw [moyalBracket, moyalBracket, ← smul_neg, neg_sub]


/-- **[The operator product splits into Baker + Moyal] `ab = {a, b}_BB + (iℏ/2)·{a, b}_MB`.** The
noncommutative product is the symmetric (Jordan/Baker) part plus `iℏ/2` times the antisymmetric
(commutator/Moyal) part — Hiley's commutator/anticommutator decomposition. -/
lemma product_eq_baker_add_moyal {ℏ : ℝ} (hℏ : ℏ ≠ 0) (a b : R) :
    a * b = bakerBracket a b + (Complex.I * (ℏ : ℂ) * 2⁻¹) • moyalBracket ℏ a b := by
  have hiℏ : Complex.I * (ℏ : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hℏ)
  rw [bakerBracket, moyalBracket, smul_smul,
    show Complex.I * (ℏ : ℂ) * 2⁻¹ * (Complex.I * (ℏ : ℂ))⁻¹ = 2⁻¹ by
      rw [mul_right_comm, mul_inv_cancel₀ hiℏ, one_mul],
    ← smul_add,
    (show a * b + b * a + (a * b - b * a) = (2 : ℂ) • (a * b) by rw [two_smul_eq]; abel),
    smul_smul, show (2⁻¹ : ℂ) * 2 = 1 by norm_num, one_smul]

/-- **[Classical limit: commuting observables have zero Moyal bracket] `ab = ba ⇒ {a, b}_MB = 0`.** The Moyal
bracket becomes the (vanishing) Poisson bracket of commuting quantities. -/
lemma moyalBracket_eq_zero_of_commute (ℏ : ℝ) {a b : R} (h : a * b = b * a) :
    moyalBracket ℏ a b = 0 := by
  rw [moyalBracket, h, sub_self, smul_zero]

/-- **[Classical limit: the Baker bracket is ordinary multiplication on commuting observables] `ab = ba ⇒
{a, b}_BB = ab`.** -/
lemma bakerBracket_eq_of_commute {a b : R} (h : a * b = b * a) : bakerBracket a b = a * b := by
  rw [bakerBracket, h, ← two_smul_eq, smul_smul, show (2⁻¹ : ℂ) * 2 = 1 by norm_num, one_smul]


/-- **[The Baker self-bracket is the square] `{a, a}_BB = a²`.** -/
lemma bakerBracket_self (a : R) : bakerBracket a a = a * a := by
  rw [bakerBracket, ← two_smul_eq, smul_smul, show (2⁻¹ : ℂ) * 2 = 1 by norm_num, one_smul]

/-- **[Pure-state idempotency] `{F, F}_BB = F ⟺ F² = F`.** The Baker-bracket idempotency condition is exactly
operator idempotency `F² = F` — the operator analogue of a pure density matrix `ρ² = ρ`. -/
lemma bakerBracket_self_eq_iff (F : R) : bakerBracket F F = F ↔ F * F = F := by
  rw [bakerBracket_self]

end Physlib.QuantumMechanics.ComplexAction.Moyal.BakerOperatorSplit

end
