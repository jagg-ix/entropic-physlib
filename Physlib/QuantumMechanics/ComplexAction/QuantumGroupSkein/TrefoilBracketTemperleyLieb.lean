/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.QuantumGroupSl2Casimir
public import Mathlib.Tactic.FieldSimp

/-!
# The Kauffman bracket of the trefoil, via the Temperley–Lieb algebra (Sawin §1)

Sawin computes (q-alg/9506002, §1) that the Kauffman bracket of the right-handed trefoil is
`A⁷ + A³ + A⁻¹ − A⁻⁹`. Mathlib has no theory of link diagrams, but the bracket of the closure of a braid is
a purely algebraic object — the **Markov trace of the braid's image in the Temperley–Lieb algebra** — so the
value can be derived rigorously with no diagram infrastructure.

The trefoil is the closure of `σ₁³` in the `2`-strand braid group `B₂`. Under the Kauffman skein relation a
positive crossing maps to `σ = A·1 + A⁻¹·e` in the Temperley–Lieb algebra `TL₂ = ℂ⟨1, e⟩` with the single
relation `e² = δ·e`, `δ = −A² − A⁻²` the loop value (`kauffmanLoopValue`, the same `δ` as the `R`-matrix
Temperley–Lieb generator `tlE` of `QuantumGroupSkein.KauffmanRMatrixSkein`). An element `α·1 + β·e` is encoded as the
coordinate pair `(α, β)` (`tlMul` is the resulting product, since `e² = δe`). Closing a `2`-braid sends
`1 ↦ ○○` (two circles, value `δ²`) and `e ↦ ○` (one circle, value `δ`), i.e. the closure functional
`α·1 + β·e ↦ α·δ² + β·δ` (`kauffmanClosure`).

* `trefoil_kauffman_bracket`: the closure of `σ₁³` has Kauffman bracket `A⁷ + A³ + A⁻¹ − A⁻⁹` — exactly
  Sawin's value, with no framing correction.

## References

* S. Sawin, *Links, Quantum Groups and TQFT's*, q-alg/9506002, §1 (Kauffman bracket of the right-handed
  trefoil `= A⁷ + A³ + A⁻¹ − A⁻⁹`); the Temperley–Lieb / Markov-trace computation of link brackets.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.QuantumGroupSl2Casimir

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.TrefoilBracketTemperleyLieb

/-- **Multiplication in `TL₂ = ℂ⟨1, e⟩`** (`e² = δ·e`), in coordinates `(α, β) = α·1 + β·e`:
`(α·1 + β·e)(α'·1 + β'·e) = αα'·1 + (αβ' + α'β + ββ'δ)·e`. -/
noncomputable def tlMul (δ : ℂ) (p q : ℂ × ℂ) : ℂ × ℂ :=
  (p.1 * q.1, p.1 * q.2 + q.1 * p.2 + p.2 * q.2 * δ)

/-- **The Kauffman skein image of a positive crossing** in `TL₂`: `σ = A·1 + A⁻¹·e` (Sawin Eqs. 7–8). -/
noncomputable def crossingTL (A : ℂ) : ℂ × ℂ := (A, A⁻¹)

/-- **The closure (Markov trace) functional** on `TL₂`: closing a `2`-braid sends `1` to two circles
(value `δ²`) and `e` to one circle (value `δ`), so `α·1 + β·e ↦ α·δ² + β·δ`. -/
noncomputable def kauffmanClosure (δ : ℂ) (p : ℂ × ℂ) : ℂ := p.1 * δ ^ 2 + p.2 * δ

/-- **[The Kauffman bracket of the trefoil]** the closure of `σ₁³` (the right-handed trefoil) has Kauffman
bracket `A⁷ + A³ + A⁻¹ − A⁻⁹` — exactly Sawin's value (§1), derived algebraically from the Temperley–Lieb
relation `e² = (−A²−A⁻²)e` with no link-diagram infrastructure. -/
theorem trefoil_kauffman_bracket (A : ℂ) (hA : A ≠ 0) :
    kauffmanClosure (kauffmanLoopValue A)
        (tlMul (kauffmanLoopValue A) (crossingTL A)
          (tlMul (kauffmanLoopValue A) (crossingTL A) (crossingTL A)))
      = A ^ 7 + A ^ 3 + A⁻¹ - (A ^ 9)⁻¹ := by
  simp only [kauffmanClosure, tlMul, crossingTL, kauffmanLoopValue]
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.TrefoilBracketTemperleyLieb

end
