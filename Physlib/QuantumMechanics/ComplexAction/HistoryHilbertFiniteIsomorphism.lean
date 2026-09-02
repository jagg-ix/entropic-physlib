/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HistoryHilbertGramIsomorphism
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The full history-Hilbert isomorphism `H₂ ≅ ℂⁿ` (Dowker–Johnston–Sorkin §3.3)

Completing the finite-configuration isomorphism of Dowker–Johnston–Sorkin (arXiv:1002.0589 §3.3): the
history Hilbert space `H₂` of a finite quantum measure system **is** the standard Hilbert space. Because
the system is finite there is no completion — `H₂ = H₁ / ∼₁` is the quotient of the free vector space by
the null space of the degenerate inner product.

The map is `f₀(u) = Σ_α u(α) ψ_α` (Eq. 3.9), which is exactly Mathlib's `Finsupp.linearCombination` of
the restricted-evolution states `ψ_α`. Its three properties assemble the isomorphism:

* it **preserves the inner product** `⟨f₀ u, f₀ v⟩ = ⟨u,v⟩₁` (Eq. 3.10, `gramRep_inner`);
* its **kernel is the null space** `f₀ u = 0 ⟺ ⟨u,u⟩₁ = 0` (Eq. 3.11, `gramRep_mem_ker_iff`), so
  `H₁/ker f₀ = H₂`;
* it is **surjective iff the states span** (Theorem 1, Onto), `Function.Surjective f₀ ↔ span{ψ_α} = ⊤`
  (`gramRep_surjective_iff`).

By the first isomorphism theorem, `f : H₂ = H₁/ker f₀ ≃ₗ ℂⁿ` (Eq. 3.12, `historyHilbertEquiv`) — the
full linear isomorphism, inner-product-preserving hence unitary. This is the paper's conclusion that
the history Hilbert space is the standard Hilbert space for a finite quantum system with a spanning
(pure-initial-state, non-degenerate-evolution) decoherence functional.

* **§A — the representation map** `f₀ = Finsupp.linearCombination ℂ ψ` (`gramRep`, `gramRep_apply`).
* **§B — inner-product preservation** (Eq. 3.10, `gramRep_inner`).
* **§C — kernel is the null space** (Eq. 3.11, `gramRep_mem_ker_iff`).
* **§D — Theorem 1 (Onto)** (`gramRep_surjective_iff`, spanning ⇔ surjective).
* **§E — the full isomorphism** (Eq. 3.12, `historyHilbertEquiv : (ι →₀ ℂ) ⧸ ker f₀ ≃ₗ[ℂ] H`).

**Honest layering.** Proven: all of §A–§E — the representation map, its inner-product preservation and
Gram form, kernel = null space, the onto criterion, and the linear-equivalence `H₂ ≃ₗ ℂⁿ`. Interpretive:
the `ψ_α` are the restricted-evolution states of §3.2 (the datum); the spanning hypothesis `span{ψ_α} =
⊤` is the paper's Theorem-1 condition on the initial state and dynamics (each final configuration
reached with non-zero amplitude); upgrading the linear-equiv to a bundled `LinearIsometryEquiv` on the
quotient inner-product space is left implicit (the inner-product preservation is proved separately).

## References

* F. Dowker, S. Johnston, R. D. Sorkin, "Hilbert spaces from path integrals", J. Phys. A **43** (2010)
  275302 [arXiv:1002.0589], §3.3, Eqs. (3.9)–(3.14), Theorem 1. Reuses
  `HistoryHilbertGramIsomorphism`/`QuantumMeasureHistoryHilbert`, Mathlib `Finsupp.linearCombination`,
  `LinearMap.quotKerEquivOfSurjective`.


-/

set_option autoImplicit false

open scoped InnerProductSpace

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HistoryHilbertFiniteIsomorphism

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]


/-- **The representation map** `f₀(u) = Σ_α u(α) ψ_α` (Dowker–Johnston–Sorkin Eq. 3.9): the linear map
`(ι →₀ ℂ) →ₗ[ℂ] H` sending a finitely-supported weight on the event algebra to the corresponding
combination of restricted-evolution states — Mathlib's `Finsupp.linearCombination` of `ψ`. -/
noncomputable def gramRep (ψ : ι → H) : (ι →₀ ℂ) →ₗ[ℂ] H := Finsupp.linearCombination ℂ ψ

/-- **The representation map as a finite sum** `f₀(u) = Σ_{i ∈ supp u} u(i) • ψ_i`. -/
lemma gramRep_apply (ψ : ι → H) (u : ι →₀ ℂ) :
    gramRep ψ u = ∑ i ∈ u.support, u i • ψ i := by
  rw [gramRep, Finsupp.linearCombination_apply, Finsupp.sum]


/-- **The representation map preserves the inner product** `⟨f₀ u, f₀ v⟩ = Σ_{i,j} u(i)* v(j) ⟨ψ_i, ψ_j⟩`
(Dowker–Johnston–Sorkin Eq. 3.10): the standard inner product of the images is the Gram/history inner
product `⟨u,v⟩₁` of the decoherence functional. -/
lemma gramRep_inner (ψ : ι → H) (u v : ι →₀ ℂ) :
    ⟪gramRep ψ u, gramRep ψ v⟫_ℂ
      = ∑ i ∈ u.support, ∑ j ∈ v.support, starRingEnd ℂ (u i) * v j * ⟪ψ i, ψ j⟫_ℂ := by
  rw [gramRep_apply, gramRep_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right]; ring


/-- **The kernel of the representation map is the null space** `f₀ u = 0 ⟺ ⟨f₀ u, f₀ u⟩ = 0`
(Dowker–Johnston–Sorkin Eq. 3.11): since `⟨f₀ u, f₀ u⟩ = ⟨u,u⟩₁`, the kernel is exactly the null space
of the degenerate history inner product — so `H₁ / ker f₀ = H₂ = H₁/∼₁`. -/
lemma gramRep_mem_ker_iff (ψ : ι → H) (u : ι →₀ ℂ) :
    u ∈ LinearMap.ker (gramRep ψ) ↔ ⟪gramRep ψ u, gramRep ψ u⟫_ℂ = 0 := by
  rw [LinearMap.mem_ker, inner_self_eq_zero]


/-- **Theorem 1 (Onto)** (Dowker–Johnston–Sorkin §3.3): the representation map `f₀` is surjective onto
the standard Hilbert space iff the restricted-evolution states span it, `span{ψ_α} = ⊤`. Physically
(paper's Theorem 1) this holds when, for each final configuration `j`, some history ends at `j` with
non-zero amplitude — a pure initial state with non-degenerate evolution. -/
lemma gramRep_surjective_iff (ψ : ι → H) :
    Function.Surjective (gramRep ψ) ↔ Submodule.span ℂ (Set.range ψ) = ⊤ := by
  rw [← LinearMap.range_eq_top, gramRep, Finsupp.range_linearCombination]


/-- **The full history-Hilbert isomorphism** `f : H₂ = H₁/ker f₀ ≃ₗ[ℂ] ℂⁿ` (Dowker–Johnston–Sorkin
Eq. 3.12): under the spanning (Theorem-1 onto) hypothesis, the history Hilbert space of the finite
quantum measure system is linearly isomorphic to the standard Hilbert space `H`. Together with
`gramRep_inner` (inner-product preservation, Eq. 3.13) this is a *unitary* isomorphism — the history
Hilbert space **is** the standard Hilbert space. -/
noncomputable def historyHilbertEquiv (ψ : ι → H)
    (hspan : Submodule.span ℂ (Set.range ψ) = ⊤) :
    ((ι →₀ ℂ) ⧸ LinearMap.ker (gramRep ψ)) ≃ₗ[ℂ] H :=
  LinearMap.quotKerEquivOfSurjective (gramRep ψ) ((gramRep_surjective_iff ψ).mpr hspan)

/-- **The isomorphism is `f₀` on representatives** `f([u]) = f₀(u)` (Eq. 3.12): the isomorphism sends the
class of a weight `u` to the combination `Σ_α u(α) ψ_α` of restricted-evolution states. -/
lemma historyHilbertEquiv_apply_mk (ψ : ι → H)
    (hspan : Submodule.span ℂ (Set.range ψ) = ⊤) (u : ι →₀ ℂ) :
    historyHilbertEquiv ψ hspan (Submodule.Quotient.mk u) = gramRep ψ u :=
  LinearMap.quotKerEquivOfSurjective_apply_mk (gramRep ψ) _ u

end Physlib.QuantumMechanics.ComplexAction.HistoryHilbertFiniteIsomorphism
