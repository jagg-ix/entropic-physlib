/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.StrongReflection

/-!
# Greaves–Thomas §9: strong reflection, PT and CPT invariance for spinors

Formalizes the spinorial generalization (§9) of *H. Greaves, T. Thomas, "The CPT Theorem"*
(arXiv:1204.4674) — **Theorems 5 and 6** for the double cover `bL̃₊ = L̃↑₊ ∪ bL̃↓₊`. For spinor fields the
value space has a `ℤ/2` grading `V = V₀ ⊕ V₁` (`ρ(τ) = (−1)ⁿ` on `Vₙ`), inducing `W = W₀ ⊕ W₁`, and the
spin-statistics assumption is upgraded from commutativity (§6) to **supercommutativity** (their Eq. 19)

  `Φ^λ Φ^μ = (−1)^{ab} Φ^μ Φ^λ`   for `λ ∈ Wₐ, μ ∈ W_b`.

Theorem 5 (strong-reflection invariance, proved in Appendix C) and Theorem 6 (general PT/CPT) are the exact
analogues of Theorems 2 and 3, with commutativity replaced by supercommutativity; **they subsume Theorems
2–3** as the `V = V₀` (purely even) special case. The deduction of Theorem 6 from Theorem 5 is "completely
parallel" to that of Theorem 3 from Theorem 2, so it is the *same* engine `generalPTCPT`.

* **§A — the supercommutation sign** (`superSign`, `superSign_symm`, `superSign_even_left`,
  `superSign_odd_odd`). The `(−1)^{ab}` factor of Eq. 19: symmetric, `= 1` whenever a factor is even
  (recovering §6 commutativity, so Theorem 5 subsumes Theorem 2), and `= −1` for two odd (pure-spinor)
  symbols (anticommutation).
* **§B — `S` on a graded pair** (`strongReflection_super_pair`). The strong reflection `S` sends an
  *anti-commuting* (odd × odd) product to **minus** itself, `S(Φ^λΦ^μ) = −Φ^λΦ^μ`. So `S` is *not* the
  identity on the super-quotient for odd factors — exactly the §6 Remark / Example 13 obstruction: an
  anti-commutative theory is not `S`-invariant, and `ψ̄ψ ↦ −ψ̄ψ` under CPT if spinors are (wrongly) taken to
  commute. Contrast `PTSymmetricQFT.StrongReflection.strongReflection_comm_pair` (even factors, sign `+1`).
* **§C — Example 13 (wrong statistics is inconsistent)** (`super_pair_Sinvariant_eq_zero`). An odd
  (anti-commuting) product that is *also* `S`-invariant — what the commuting-spinor stipulation would
  require of a constraint like `ψ̄ψ` — must vanish. So a nonzero spinor-bilinear constraint cannot be both
  `S`-invariant and built from anticommuting fields: the spin-statistics assumption of Theorems 5–6 is
  genuinely required. **Theorem 6 for spinors itself** is `PTSymmetricQFT.StrongReflection.generalPTCPT`
  verbatim (the deduction is identical to Theorem 3, now with supercommutative input); the `$ = ∗` reading
  is the quantum CPT theorem of Lagrangian QFT.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §8–§9 (Eq. 19 supercommutativity; Theorems 5–6;
  Example 13; the `V = V₀` subsumption of §6).
* Repo dependencies: `PTSymmetricQFT.StrongReflection` (`strongReflection`, `strongReflection_ι`,
  `strongReflection_antihom`, `daggerConj`, `generalPTCPT`); `PTSymmetricQFT.ChargeConjugation`
  (`chargeConjugation`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.SpinorStrongReflection

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ChargeConjugation
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.StrongReflection

variable {U : Type*} [AddCommGroup U] [Module ℂ U]

/-! ## §A — the supercommutation sign `(−1)^{ab}` (Eq. 19) -/

/-- **[Greaves–Thomas Eq. 19] The supercommutation sign** `(−1)^{ab}` for parities `a, b ∈ ℤ/2` of the
graded value space `W = W₀ ⊕ W₁`. It is `+1` unless both factors are odd (pure spinors), where it is `−1`
(anticommutation). -/
def superSign (a b : ZMod 2) : ℤ := (-1) ^ (a.val * b.val)

/-- **The sign is symmetric** `(−1)^{ab} = (−1)^{ba}`. -/
theorem superSign_symm (a b : ZMod 2) : superSign a b = superSign b a := by
  unfold superSign; rw [Nat.mul_comm]

/-- **An even factor commutes** `superSign 0 b = 1` — recovering §6 commutativity (so `V = V₀` makes
Theorem 5 reduce to Theorem 2). -/
theorem superSign_even_left (b : ZMod 2) : superSign 0 b = 1 := by
  unfold superSign; simp

/-- **Two odd factors anticommute** `superSign 1 1 = −1`. -/
theorem superSign_odd_odd : superSign 1 1 = -1 := by decide

/-! ## §B — `S` on an anti-commuting (odd × odd) pair -/

/-- **[§6 Remark / Example 13] `S` negates an anti-commuting product** `S(Φ^λ Φ^μ) = −Φ^λ Φ^μ` when the
symbols anticommute (both odd). Hence `S` is *not* the identity on the super-quotient for odd factors: an
anti-commutative theory fails to be `S`-invariant, and `ψ̄ψ ↦ −ψ̄ψ` under CPT if spinors are (wrongly) taken
to commute. (Even factors give `+1`: `strongReflection_comm_pair`.) -/
theorem strongReflection_super_pair (s t : U)
    (ha : TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t
        = -(TensorAlgebra.ι ℂ t * TensorAlgebra.ι ℂ s)) :
    strongReflection (TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t)
      = -(TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t) := by
  rw [strongReflection_antihom, strongReflection_ι, strongReflection_ι, ← neg_eq_iff_eq_neg, ← ha]

/-! ## §C — Example 13: wrong statistics is inconsistent -/

/-- **[Greaves–Thomas Example 13 / §6 Remark] A nonzero anti-commuting constraint cannot be `S`-invariant.**
If `Φ^λ Φ^μ` anti-commutes (the symbols are odd, true spinors) yet is assumed `S`-invariant — as the
*commuting*-spinor stipulation would force for a constraint like `ψ̄ψ = 1` — then it must vanish. Indeed
`S(Φ^λΦ^μ) = −Φ^λΦ^μ` (`strongReflection_super_pair`), so `S`-invariance gives `F = −F`, hence `2F = 0` and,
over `ℂ`, `F = 0`. This is why `ψ̄ψ ↦ −ψ̄ψ` under CPT and the constraint `ψ̄ψ = 1` is incompatible unless the
correct (anti-commuting) spin-statistics is used — the necessity of the Theorem 5/6 hypothesis. -/
theorem super_pair_Sinvariant_eq_zero (s t : U)
    (ha : TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t
        = -(TensorAlgebra.ι ℂ t * TensorAlgebra.ι ℂ s))
    (hS : strongReflection (TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t)
        = TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t) :
    TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t = 0 := by
  have h1 := strongReflection_super_pair s t ha
  rw [hS] at h1
  have h2 : (2 : ℂ) • (TensorAlgebra.ι ℂ s * TensorAlgebra.ι ℂ t) = 0 := by
    rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp h1
  rcases smul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.SpinorStrongReflection

end
