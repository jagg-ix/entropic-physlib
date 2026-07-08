/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet

/-!
# The split property: statistical independence of two fermion regions

Formalizes the **split property** of the Verch local net (`AlgebraicQFTQuasifree.HadamardLocalNet`) and its
**statistical-independence** consequence. For `O` strictly inside `O₁`, the split property asserts an
interpolating algebra `𝒩` (a type-I factor) with

  `R(O) ⊆ 𝒩 ⊆ R(O₁)`   (`HasSplitProperty`).

The *existence* of the interpolant is the deep input (it follows from nuclearity / the Doplicher–Longo
theorem, not formalized here — taken as the hypothesis). What follows *structurally* — and is proved here —
is the **statistical independence** of the inner region and the outer complement: every observable of `R(O)`
commutes with every observable of `R(O₁)'`,

  `∀ a ∈ R(O), ∀ b ∈ R(O₁)', a b = b a`   (`split_statistical_independence`),

because `a ∈ R(O) ⊆ 𝒩` and `b ∈ R(O₁)' ⊆ 𝒩'` (`M ⊆ R(O₁)` gives `R(O₁)' ⊆ 𝒩'` by antitonicity), so `a` and
`b` commute through the interpolant `𝒩`. The interpolant's commutant nests between the two complements,
`R(O₁)' ⊆ 𝒩' ⊆ R(O)'` (`split_commutant_nest`).

Statistical independence is exactly what a tensor-product decomposition of two disjoint fermion regions
requires: the inner-region observables and the outer-complement observables act independently. The split
property is the rigorous route to such a factorization in a type-III₁ theory, where naive
`ℋ = ℋ_O ⊗ ℋ_{O₁'}` fails.

* **§A — the split property and its interpolant** (`HasSplitProperty`, `split_commutant_nest`).
* **§B — statistical independence** (`split_statistical_independence`).

## References

* S. Doplicher, R. Longo (the split property and statistical independence); R. Verch (local nets).
  structures: `AlgebraicQFTQuasifree.HadamardLocalNet` (`LocalNet`), `AlgebraicQFT.GNSVonNeumannHadamard` (`commutant`,
  `commutant_antitone`, `IsVonNeumann`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet

variable {A : Type*} [Monoid A] {ι : Type*} [Preorder ι]

/-! ## §A — the split property and its interpolant -/

/-- **The split property** for `O ⊆ O₁`: an interpolating von Neumann algebra `𝒩` with
`R(O) ⊆ 𝒩 ⊆ R(O₁)`. (The full split requires `𝒩` to be a type-I factor — the input from nuclearity; here
the interpolant is taken as a von Neumann algebra.) -/
def HasSplitProperty (N : LocalNet A ι) (O O₁ : ι) : Prop :=
  ∃ M : Set A, IsVonNeumann M ∧ N.alg O ⊆ M ∧ M ⊆ N.alg O₁

/-- **[The interpolant's commutant nests between the complements] `R(O₁)' ⊆ 𝒩' ⊆ R(O)'`.** Applying the
anti-monotone commutant to `R(O) ⊆ 𝒩 ⊆ R(O₁)`. -/
theorem split_commutant_nest {N : LocalNet A ι} {O O₁ : ι} (h : HasSplitProperty N O O₁) :
    ∃ M : Set A, commutant (N.alg O₁) ⊆ commutant M ∧ commutant M ⊆ commutant (N.alg O) := by
  obtain ⟨M, _, hOM, hMO₁⟩ := h
  exact ⟨M, commutant_antitone hMO₁, commutant_antitone hOM⟩

/-! ## §B — statistical independence -/

/-- **[Statistical independence] `R(O)` and `R(O₁)'` commute.** Under the split property, every observable
of the inner region `R(O)` commutes with every observable of the outer complement `R(O₁)'`: with `a ∈ R(O) ⊆
𝒩` and `b ∈ R(O₁)' ⊆ 𝒩'`, `a` and `b` commute through the interpolant. The inner-region and
outer-complement observables act independently — the algebraic core of a tensor decomposition of two
disjoint fermion regions. -/
theorem split_statistical_independence {N : LocalNet A ι} {O O₁ : ι} (h : HasSplitProperty N O O₁)
    (a : A) (ha : a ∈ N.alg O) (b : A) (hb : b ∈ commutant (N.alg O₁)) :
    a * b = b * a := by
  obtain ⟨M, _, hOM, hMO₁⟩ := h
  have haM : a ∈ M := hOM ha
  have hbM' : b ∈ commutant M := commutant_antitone hMO₁ hb
  exact Set.mem_centralizer_iff.mp hbM' a haM

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence

end
