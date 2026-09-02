/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The Gram structure of the decoherence functional and the history-Hilbert isomorphism

The critical section of Dowker–Johnston–Sorkin (arXiv:1002.0589, §2.3.2, §3): the construction that
produces the history Hilbert space and shows it *is* the standard Hilbert space.

Two structural facts do the work:

* **Lemma 1** (Eqs. 2.5–2.6): an inner-product-preserving linear map is injective — the tool that
  turns the inner-product-preserving map into a Hilbert-space isomorphism onto its image.
* **The Gram structure** (Eq. 3.7): the Schwinger–Keldysh decoherence functional is
  `D(α,β) = ⟨ψ_α, ψ_β⟩`, the Gram matrix of the *restricted-evolution* states `ψ_α`. A Gram matrix is
  automatically Hermitian and strongly positive — this is *why* the decoherence functional satisfies
  the positivity axioms of `QuantumMeasureHistoryHilbert.IsDecoherenceFunctional`.

* **§A — Lemma 1.** `innerPreserving_injective`: a linear `f` with `⟨f u, f v⟩ = ⟨u, v⟩` is injective.
* **§B — a Gram matrix is a decoherence kernel.** `gramDecoherence ψ α β = ⟨ψ α, ψ β⟩`; Hermitian
  (`gram_hermitian`) and strongly positive (`gram_posSemidef`, the quadratic form is `‖Σ c_α ψ_α‖² ≥ 0`).
* **§C — the restricted-evolution decoherence functional.** When the states are additive over disjoint
  events (`ψ_{α⊔β} = ψ_α + ψ_β`), the Gram kernel is a genuine decoherence functional
  (`gram_isDecoherenceFunctional`) — the §3.2 verification that `D(α,β) = ⟨ψ_α, ψ_β⟩` satisfies §2.2.
* **§D — the isomorphism map.** `historyInner_gram_eq`: the history inner product of the Gram kernel is
  the standard inner product of the images `T u = Σ_α u(α) ψ_α` — the inner-product-preserving map (Eq.
  3.8) that, by Lemma 1, embeds the history Hilbert space isometrically into the standard one.

**Honest layering.** Proven: Lemma 1, the Hermiticity and strong positivity of a Gram matrix, the
assembly into a decoherence functional under additivity, and the inner-product preservation of the
representation map. Interpretive: the `ψ_α` are the restricted-evolution states of §3.2 (the datum); the
quotient-by-null-space and completion producing the concrete `H₂` are the standard dilation, and the
surjectivity/separability that upgrade the embedding to the full isomorphism `H₂ ≅ ℂⁿ / L²` are the
system-specific analysis of §3–§4, not formalized here.

## References

* F. Dowker, S. Johnston, R. D. Sorkin, "Hilbert spaces from path integrals", J. Phys. A **43** (2010)
  275302 [arXiv:1002.0589], §2.3.2 (Lemma 1), §3.2 (Eq. 3.7). Reuses
  `QuantumMeasureHistoryHilbert` (`IsDecoherenceFunctional`, `historyInner`) and Mathlib
  `InnerProductSpace`.


-/

set_option autoImplicit false

open scoped InnerProductSpace

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HistoryHilbertGramIsomorphism

open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert


/-- **Lemma 1** (Dowker–Johnston–Sorkin, Eqs. 2.5–2.6): a linear map `f : H_A → H_B` that preserves the
inner product, `⟨f u, f v⟩ = ⟨u, v⟩`, is injective. This is the tool that turns the history-Hilbert
representation map into an isomorphism onto its image. -/
lemma innerPreserving_injective {A B : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (f : A →ₗ[ℂ] B) (hf : ∀ u v, ⟪f u, f v⟫_ℂ = ⟪u, v⟫_ℂ) :
    Function.Injective f := by
  intro u v huv
  have h0 : ⟪u - v, u - v⟫_ℂ = 0 := by
    rw [← hf, map_sub, huv, sub_self, inner_zero_left]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)


variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The Gram decoherence kernel** `D(α,β) = ⟨ψ_α, ψ_β⟩` of a family of states `ψ` (Dowker–Johnston–
Sorkin Eq. 3.7 — the restricted-evolution / Schwinger–Keldysh form). -/
def gramDecoherence (ψ : ι → H) (α β : ι) : ℂ := ⟪ψ α, ψ β⟫_ℂ

/-- **A Gram kernel is Hermitian** `⟨ψ_α, ψ_β⟩ = ⟨ψ_β, ψ_α⟩*` — the decoherence Hermiticity axiom. -/
lemma gram_hermitian (ψ : ι → H) (α β : ι) :
    gramDecoherence ψ α β = starRingEnd ℂ (gramDecoherence ψ β α) :=
  (inner_conj_symm (ψ α) (ψ β)).symm

/-- **A Gram kernel is strongly positive**: the quadratic form is `‖Σ_α c_α ψ_α‖² ≥ 0`. This is *why* a
decoherence functional of the form `D(α,β) = ⟨ψ_α, ψ_β⟩` satisfies the strong-positivity axiom — it is
the Gram matrix of a family of vectors. -/
lemma gram_posSemidef (ψ : ι → H) (s : Finset ι) (c : ι → ℂ) :
    0 ≤ (∑ α ∈ s, ∑ β ∈ s, starRingEnd ℂ (c α) * c β * gramDecoherence ψ α β).re := by
  have expand : (∑ α ∈ s, ∑ β ∈ s, starRingEnd ℂ (c α) * c β * gramDecoherence ψ α β)
      = ⟪∑ α ∈ s, c α • ψ α, ∑ β ∈ s, c β • ψ β⟫_ℂ := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [inner_smul_right, gramDecoherence]; ring
  rw [expand]
  simpa using @inner_self_nonneg ℂ H _ _ _ (∑ β ∈ s, c β • ψ β)


variable [DistribLattice ι] [OrderBot ι]

/-- **The restricted-evolution decoherence functional is a decoherence functional** (Dowker–Johnston–
Sorkin §3.2): when the states are additive over disjoint events (`ψ_{α⊔β} = ψ_α + ψ_β`, as the
restricted-evolution states `ψ_α = Σ_{γ∈α} ψ_γ` are), the Gram kernel `D(α,β) = ⟨ψ_α, ψ_β⟩` satisfies
all three §2.2 axioms — Hermiticity, biadditivity, and strong positivity. -/
lemma gram_isDecoherenceFunctional (ψ : ι → H)
    (hadd : ∀ β γ, Disjoint β γ → ψ (β ⊔ γ) = ψ β + ψ γ) :
    IsDecoherenceFunctional (gramDecoherence ψ) where
  hermitian := gram_hermitian ψ
  biadditive α β γ hd := by
    rw [gramDecoherence, gramDecoherence, gramDecoherence, hadd β γ hd, inner_add_right]
  posSemidef := gram_posSemidef ψ


omit [DistribLattice ι] [OrderBot ι] in
/-- **The history inner product is the standard inner product of the representation images** (Dowker–
Johnston–Sorkin Eq. 3.8): `⟨u,v⟩_D = ⟨T u, T v⟩` for `T u = Σ_α u(α) ψ_α`. So the representation map `T`
preserves the inner product, and by Lemma 1 (`innerPreserving_injective`) it embeds the history Hilbert
space isometrically into the standard Hilbert space `H`. -/
lemma historyInner_gram_eq (ψ : ι → H) (s : Finset ι) (u v : ι → ℂ) :
    historyInner (gramDecoherence ψ) s u v
      = ⟪∑ α ∈ s, u α • ψ α, ∑ β ∈ s, v β • ψ β⟫_ℂ := by
  unfold historyInner
  rw [sum_inner]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [inner_smul_right, gramDecoherence]; ring

end Physlib.QuantumMechanics.ComplexAction.HistoryHilbertGramIsomorphism
