/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
public import Physlib.Mathematics.Nuclear.OrliczOperatorIdeals
meta import Zil

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
  Carriers: `AlgebraicQFTQuasifree.HadamardLocalNet` (`LocalNet`), `AlgebraicQFT.StarAlgebraGNSFormCommutant` (`commutant`,
  `commutant_antitone`, `IsBicommutantClosed`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet

variable {A : Type*} [Monoid A] {ι : Type*} [Preorder ι]


/-- **The split property** for `O ⊆ O₁`: an interpolating von Neumann algebra `𝒩` with
`R(O) ⊆ 𝒩 ⊆ R(O₁)`. (The full split requires `𝒩` to be a type-I factor — the input from nuclearity; here
the interpolant is taken as a von Neumann algebra.) -/
def HasSplitProperty (N : LocalNet A ι) (O O₁ : ι) : Prop :=
  ∃ M : Set A, IsBicommutantClosed M ∧ N.alg O ⊆ M ∧ M ⊆ N.alg O₁

/-- **[The interpolant's commutant nests between the complements] `R(O₁)' ⊆ 𝒩' ⊆ R(O)'`.** Applying the
anti-monotone commutant to `R(O) ⊆ 𝒩 ⊆ R(O₁)`. -/
lemma split_commutant_nest {N : LocalNet A ι} {O O₁ : ι} (h : HasSplitProperty N O O₁) :
    ∃ M : Set A, commutant (N.alg O₁) ⊆ commutant M ∧ commutant M ⊆ commutant (N.alg O) := by
  obtain ⟨M, _, hOM, hMO₁⟩ := h
  exact ⟨M, commutant_antitone hMO₁, commutant_antitone hOM⟩


/-- **[Statistical independence] `R(O)` and `R(O₁)'` commute.** Under the split property, every observable
of the inner region `R(O)` commutes with every observable of the outer complement `R(O₁)'`: with `a ∈ R(O) ⊆
𝒩` and `b ∈ R(O₁)' ⊆ 𝒩'`, `a` and `b` commute through the interpolant. The inner-region and
outer-complement observables act independently — the algebraic core of a tensor decomposition of two
disjoint fermion regions. -/
lemma split_statistical_independence {N : LocalNet A ι} {O O₁ : ι} (h : HasSplitProperty N O O₁)
    (a : A) (ha : a ∈ N.alg O) (b : A) (hb : b ∈ commutant (N.alg O₁)) :
    a * b = b * a := by
  obtain ⟨M, _, hOM, hMO₁⟩ := h
  have haM : a ∈ M := hOM ha
  have hbM' : b ∈ commutant M := commutant_antitone hMO₁ hb
  exact Set.mem_centralizer_iff.mp hbM' a haM

/-! ## §C Buchholz partition nuclearity and opposite-wedge independence -/

open Physlib.Mathematics.Nuclear.OrliczOperatorIdeals

/-- **The AdS thermal characteristic-number sequence**
`mₙ exp(-β·2πn)` associated with the multiplicity `mₙ` of the `2πn` eigenspace of
the compact AdS generator. -/
noncomputable def buchholzThermalCharacteristic
    (β : ℝ) (multiplicity : ℕ → ℝ) (n : ℕ) : ℝ :=
  multiplicity n * Real.exp (-β * (2 * Real.pi * n))

/-- **Buchholz partition nuclearity.** The partition function
`Tr exp(-βM) = ∑ₙ mₙ exp(-β·2πn)` exists as a summable thermal characteristic sequence. -/
noncomputable def HasBuchholzPartitionNuclearity
    (β : ℝ) (multiplicity : ℕ → ℝ) : Prop :=
  Summable (buchholzThermalCharacteristic β multiplicity)

/-- **Partition nuclearity is membership in the `p=1` Orlicz operator ideal.**
This identifies the paper's finite partition-function condition with the repository's
characteristic-number nuclearity carrier rather than introducing a second nuclearity notion. -/
theorem buchholz_partitionNuclearity_iff_orliczOne
    (β : ℝ) (multiplicity : ℕ → ℝ) :
    HasBuchholzPartitionNuclearity β multiplicity ↔
      inOrliczIdeal (orliczPow (p := (1 : ℝ)) zero_lt_one le_rfl)
        (buchholzThermalCharacteristic β multiplicity) := by
  simp [HasBuchholzPartitionNuclearity, inOrliczIdeal, orliczPow]

/-- **The delegated nuclearity-to-split implication at a pair of regions.**
Buchholz cites this operator-algebraic step; it is exposed as a named premise rather than
being conflated with sequence summability. -/
def BuchholzNuclearityImpliesSplit
    (N : LocalNet A ι) (O O₁ : ι) (β : ℝ) (multiplicity : ℕ → ℝ) : Prop :=
  HasBuchholzPartitionNuclearity β multiplicity → HasSplitProperty N O O₁

/-- **[Partition nuclearity ⇒ statistical independence, through the split property].**
Once the cited nuclearity-to-split theorem is supplied, the paper's partition-function
summability produces an interpolating algebra and hence actual operator commutation between
the inner algebra and the outer commutant. -/
theorem buchholz_partitionNuclearity_statistical_independence
    {N : LocalNet A ι} {O O₁ : ι} {β : ℝ} {multiplicity : ℕ → ℝ}
    (hnuclear : HasBuchholzPartitionNuclearity β multiplicity)
    (htoSplit : BuchholzNuclearityImpliesSplit N O O₁ β multiplicity)
    (a : A) (ha : a ∈ N.alg O) (b : A) (hb : b ∈ commutant (N.alg O₁)) :
    a * b = b * a :=
  split_statistical_independence (htoSplit hnuclear) a ha b hb

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence.buchholz_partitionNuclearity_iff_orliczOne where
  formalizes @ "claim:buchholz-ads-partition-function-nuclearity-is-membership-in-the-p-one-orlicz-operator-ideal",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads",
  supported_by @ "definition:orlicz-operator-ideal-characteristic-number-summability"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence.buchholz_partitionNuclearity_statistical_independence where
  formalizes @ "claim:buchholz-partition-nuclearity-implies-opposite-region-statistical-independence-through-the-split-property",
  requires @ "theorem:doplicher-longo-nuclearity-implies-split-property",
  supported_by @ "paper:buchholz-florig-summers-2000-second-law-tcp-einstein-causality-in-ads",
  caveat @ "claim:the-nuclearity-to-split-operator-algebra-theorem-is-an-explicit-premise-while-the-split-to-commutation-consequence-is-proved"

zil_file_contract physlib.buchholzPartitionNuclearitySplit where
  promises "The multiplicity-weighted AdS partition function is represented by its exact thermal characteristic-number sequence and proved to be the p=1 Orlicz operator-ideal nuclearity condition already used by the repository. Given the explicitly named Doplicher-Longo nuclearity-to-split implication, the existing split interpolant theorem proves operator statistical independence."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence.HasSplitProperty",
    "lean:Physlib.Mathematics.Nuclear.OrliczOperatorIdeals.inOrliczIdeal"]
  forbids_substitutes ["a proof of the Doplicher-Longo nuclearity-to-split theorem from sequence summability alone",
    "identifying commuting algebras with a tensor-product factorization without the type-I split interpolant"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence.buchholz_partitionNuclearity_iff_orliczOne,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence.buchholz_partitionNuclearity_statistical_independence]

/- ZIL-END -/
