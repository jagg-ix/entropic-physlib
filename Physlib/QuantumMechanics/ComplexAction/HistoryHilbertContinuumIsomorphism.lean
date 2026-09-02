/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HistoryHilbertFiniteIsomorphism
public import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# The continuum history-Hilbert isomorphism `H₂ ≅ L²(ℝᵈ)` (Dowker–Johnston–Sorkin §4)

Completing the continuum case of Dowker–Johnston–Sorkin (arXiv:1002.0589 §4): the history Hilbert
space of a non-relativistic particle **is** the standard `L²(ℝᵈ)`. The finite argument of §3.3 upgrades
to the continuum through two ingredients that this file supplies:

* **Completion** (Eqs. 4.21–4.24). The representation map `f₀(u) = Σ_α u(α)[ψ_α]` (Eq. 4.21) preserves
  the inner product (Eq. 4.22), so it is an **isometry**; an isometry maps Cauchy sequences to Cauchy
  sequences and — because `L²(ℝᵈ)` is complete — extends to `f : H₂ → L²` on the completion `H₂`
  (Eq. 4.23), still inner-product-preserving (Eq. 4.24) and, by Lemma 1, injective.
* **Onto by density** (Theorem 2). Where §3.3 needed `span{ψ_α} = ⊤` (surjective), the continuum needs
  only a **dense** span; then the isometric image of the complete `H₂` is closed and dense, hence all of
  `L²`. This is the content of the paper's Theorem 2 (established there from continuity of the
  propagator).

Both `H₂` and `L²(ℝᵈ)` are *degenerate-inner-product quotient-completions*: `L²` is the standard
Hilbert space `𝓛²/∼` where `⟨ψ,φ⟩₀ = ∫ ψ* φ` and `ψ ∼ φ ⟺ ‖ψ−φ‖₀ = 0` (§4.1, Eqs. 4.1–4.2) — the same
null-space construction as `H₂ = H₁/∼₁`, now completed. (`L²(ℝᵈ)` is Mathlib's `MeasureTheory.Lp ℂ 2`,
a complete inner product space.)

* **§A — Theorem 2 (Onto, density criterion).** `gramRep_denseRange_iff`: `f₀` has dense range iff the
  restricted-evolution states have dense span, `(span{ψ_α}).topologicalClosure = ⊤`.
* **§B — the completion isomorphism.** `denseRange_isometry_surjective`: a **dense-range linear isometry
  from a complete inner product space** is surjective; `historyContinuumEquiv` packages it as a
  `LinearIsometryEquiv` — the isometric isomorphism `H₂ ≃ₗᵢ L²`. Applied with `E = H₂` (the completed
  history space) and `F = L²(ℝᵈ)`, this is the paper's `f : H₂ → L²` being onto (Theorem 2), hence the
  isomorphism.

**Honest layering.** Proven: the dense-range criterion, and the completion isomorphism
(dense-range isometry from a complete space ⇒ surjective isometric isomorphism) — the abstract
content of §4.3 + Theorem 2. Interpretive: that `H₂` is precisely the completion of `H₁/∼₁` and that the
extended `f₀` is an isometry on it is the standard Cauchy-completion (Eq. 4.23); and that the range is
actually **dense** for the free particle / quadratic potential is Theorem 2's propagator-continuity
analysis (§4.3 Lemmas 2–4, measure-theoretic), which is the analytic input to the general theorem here.

## References

* F. Dowker, S. Johnston, R. D. Sorkin, "Hilbert spaces from path integrals", J. Phys. A **43** (2010)
  275302 [arXiv:1002.0589], §4, Eqs. (4.1)–(4.24), Theorem 2. Reuses
  `HistoryHilbertFiniteIsomorphism` (`gramRep`) and Mathlib `LinearIsometryEquiv.ofSurjective`,
  `Submodule.dense_iff_topologicalClosure_eq_top`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HistoryHilbertContinuumIsomorphism

open Physlib.QuantumMechanics.ComplexAction.HistoryHilbertFiniteIsomorphism


variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Theorem 2 (Onto, density form)** (Dowker–Johnston–Sorkin §4.3): the representation map `f₀` has
**dense range** in the standard Hilbert space iff the restricted-evolution states span it densely,
`(span{ψ_α}).topologicalClosure = ⊤`. For the continuum this replaces the finite-case `span = ⊤`
(`gramRep_surjective_iff`); the paper's Theorem 2 establishes this density from continuity of the
propagator. -/
lemma gramRep_denseRange_iff (ψ : ι → H) :
    DenseRange (gramRep ψ) ↔ (Submodule.span ℂ (Set.range ψ)).topologicalClosure = ⊤ := by
  have hset : Set.range (gramRep ψ) = ↑(Submodule.span ℂ (Set.range ψ)) := by
    rw [← LinearMap.coe_range, gramRep, Finsupp.range_linearCombination]
  unfold DenseRange
  rw [hset, Submodule.dense_iff_topologicalClosure_eq_top]


variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **A dense-range linear isometry from a complete space is surjective** (Dowker–Johnston–Sorkin §4.3,
the completion step of Theorem 2): if `f : E →ₗᵢ F` is a linear isometry with dense range and `E` is
complete, then `f` is onto — its image is complete (isometric image of a complete space), hence closed,
and closed + dense = everything. This is why the isometric `f : H₂ → L²` with dense range (Theorem 2) is
onto. -/
lemma denseRange_isometry_surjective (f : E →ₗᵢ[ℂ] F) (hd : DenseRange f) :
    Function.Surjective f := by
  have hcomplete : IsComplete (Set.range f) := by
    rw [← Set.image_univ]
    exact (LinearIsometry.isComplete_image_iff f).mpr
      (completeSpace_iff_isComplete_univ.mp inferInstance)
  have hrange : Set.range f = Set.univ := by
    rw [← IsClosed.closure_eq hcomplete.isClosed]; exact hd.closure_range
  exact Set.range_eq_univ.mp hrange

/-- **The continuum history-Hilbert isomorphism** `f : H₂ ≃ₗᵢ[ℂ] L²` (Dowker–Johnston–Sorkin Eq. 4.23 +
Theorem 2): a dense-range linear isometry from the complete completed-history space `H₂` onto the
standard Hilbert space is an isometric isomorphism. With `E = H₂` and `F = L²(ℝᵈ)`, this is the paper's
conclusion that the history Hilbert space of the particle is `L²(ℝᵈ)`. -/
noncomputable def historyContinuumEquiv (f : E →ₗᵢ[ℂ] F) (hd : DenseRange f) : E ≃ₗᵢ[ℂ] F :=
  LinearIsometryEquiv.ofSurjective f (denseRange_isometry_surjective f hd)

/-- **The isomorphism is `f` on points** — `historyContinuumEquiv f hd x = f x`. -/
lemma historyContinuumEquiv_apply (f : E →ₗᵢ[ℂ] F) (hd : DenseRange f) (x : E) :
    historyContinuumEquiv f hd x = f x := rfl

end Physlib.QuantumMechanics.ComplexAction.HistoryHilbertContinuumIsomorphism
