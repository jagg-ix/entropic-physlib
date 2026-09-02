/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.RudolphHomogeneousDecoherence

/-!
# Wright's (unbounded) quadratic-form representation of the decoherence functional (Rudolph–Wright §V.2)

Rudolph & Wright (arXiv:quant-ph/9807024, §V.2) show that every **standard** homogeneous decoherence
functional `d_ρ` — which is *unbounded* on the full history space when the single-time Hilbert space is
infinite dimensional — is represented by a **positive (in general unbounded) quadratic form**, extending
Wright's representation theory for bounded decoherence functionals.

The construction: let `prodMap` be the linear **collapse (product) map** `prodMap(x₁ ⊗ ⋯ ⊗ xₙ) = xₙ ⋯ x₁` on the
algebraic tensor product `B(𝓗ₛ)^{⊗n}`, and let `φ` be a **normal state**, `φ(x) = tr(x ρ)`. Then

  `D_φ(z,w) = φ( prodMap(w)* prodMap(z) )`   (the Wright form)

is a **semi-inner product**: it is Hermitian and positive semidefinite. Its null space `N_φ` is a
subspace (Cauchy–Schwarz), and on the quotient it induces an inner product, whose completion is the
representing Hilbert space `H` with `d_ρ(v,w) = ⟨R_ρ v, R_ρ w⟩` (Eq. 5) — the GNS/Gram realization.

* **§A — the Wright form.** `wrightForm φ prodMap z w = φ(star (prodMap w) * prodMap z)`, from a `*`-linear functional
  `φ` and a linear map `prodMap` into a `*`-algebra.
* **§B — the positive quadratic form.** Hermiticity `D_φ(z,w) = D_φ(w,z)*` (`wrightForm_hermitian`,
  from `φ` `*`-Hermitian) and positivity `D_φ(z,z) ≥ 0` (`wrightForm_diag_nonneg`, from `φ` positive) —
  `D_φ` is a positive quadratic form / semi-inner product, Wright's representing form (Eq. 5).
* **§C — strong positivity.** `Σ c_i* c_j D_φ(z_j,z_i) = D_φ(Σ c_j z_j, Σ c_i z_i) ≥ 0`
  (`wrightForm_posSemidef`) — so `D_φ` is a decoherence functional in the sense of
  `QuantumMeasureHistoryHilbert.IsDecoherenceFunctional`.
* **§D — reduction to the standard functional.** For matrices with the trace-state `φ(x) = tr(x ρ)`,
  `wrightForm φ prodMap p q = homogeneousDecoherence prodMap ρ p q` (`wrightForm_eq_homogeneousDecoherence`) — the
  abstract Wright form is exactly Rudolph's standard homogeneous decoherence functional `d_ρ`.

**Honest layering.** Proven: the Hermiticity, positivity, and strong positivity of the Wright form
(hence its being a positive quadratic form / semi-inner product), and its reduction to the concrete
`homogeneousDecoherence` for the trace-state. Interpretive: `prodMap` is the collapse map `xₙ⋯x₁` (taken as a
given linear map here; its construction from the `n`-linear product on the tensor product is the paper's
§V.2 datum); the GNS quotient by the null space `N_φ` and completion producing the representing Hilbert
space `H` and the (unbounded) operator `R_ρ` with `d_ρ(v,w) = ⟨R_ρ v, R_ρ w⟩` is the standard
GNS/Gram construction — the resulting `⟨R_ρ·, R_ρ·⟩` is a `HistoryHilbertGramIsomorphism.gramDecoherence`.

## References

* O. Rudolph, J. D. M. Wright, "Homogeneous decoherence functionals in standard and history quantum
  mechanics", arXiv:quant-ph/9807024, §V.2, Eq. (5); J. D. M. Wright, Corollary 4 of [18]. Reuses
  `RudolphHomogeneousDecoherence` (`homogeneousDecoherence`) and
  `QuantumMeasureHistoryHilbert` (`IsDecoherenceFunctional` positivity).


-/

set_option autoImplicit false

open scoped ComplexOrder

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WrightQuadraticFormRepresentation

open Physlib.QuantumMechanics.ComplexAction.RudolphHomogeneousDecoherence


variable {A E : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [AddCommGroup E] [Module ℂ E]

/-- **The Wright form** `D_φ(z,w) = φ(prodMap(w)* prodMap(z))` (Rudolph–Wright §V.2): the sesquilinear form built
from a `*`-linear functional `φ` on a `*`-algebra `A` and a linear collapse map `prodMap : E → A`. -/
noncomputable def wrightForm (φ : A →ₗ[ℂ] ℂ) (prodMap : E →ₗ[ℂ] A) (z w : E) : ℂ :=
  φ (star (prodMap w) * prodMap z)


/-- **The Wright form is Hermitian** `D_φ(z,w) = D_φ(w,z)*` (Rudolph–Wright §V.2): for a `*`-Hermitian
functional `φ` (`φ(a*) = φ(a)*`) the representing form satisfies the decoherence Hermiticity axiom. -/
lemma wrightForm_hermitian (φ : A →ₗ[ℂ] ℂ) (prodMap : E →ₗ[ℂ] A)
    (hHerm : ∀ a, φ (star a) = starRingEnd ℂ (φ a)) (z w : E) :
    wrightForm φ prodMap z w = starRingEnd ℂ (wrightForm φ prodMap w z) := by
  unfold wrightForm
  rw [← hHerm, star_mul, star_star]

/-- **The Wright form is a positive quadratic form** `D_φ(z,z) ≥ 0` (Rudolph–Wright §V.2, Eq. 5): for a
positive functional `φ` (`φ(a* a) ≥ 0`) the diagonal is non-negative — `D_φ` is a semi-inner product,
Wright's representing positive (unbounded) quadratic form. -/
lemma wrightForm_diag_nonneg (φ : A →ₗ[ℂ] ℂ) (prodMap : E →ₗ[ℂ] A)
    (hPos : ∀ a, 0 ≤ (φ (star a * a)).re) (z : E) :
    0 ≤ (wrightForm φ prodMap z z).re :=
  hPos (prodMap z)


/-- **The Wright form is additive in the left slot** `D_φ(z₁+z₂, w) = D_φ(z₁,w) + D_φ(z₂,w)`. -/
lemma wrightForm_add_left (φ : A →ₗ[ℂ] ℂ) (prodMap : E →ₗ[ℂ] A) (z₁ z₂ w : E) :
    wrightForm φ prodMap (z₁ + z₂) w = wrightForm φ prodMap z₁ w + wrightForm φ prodMap z₂ w := by
  unfold wrightForm; rw [map_add, mul_add, map_add]

/-- **The Wright form is linear in the left slot** `D_φ(c·z, w) = c · D_φ(z,w)`. -/
lemma wrightForm_smul_left (φ : A →ₗ[ℂ] ℂ) (prodMap : E →ₗ[ℂ] A) (c : ℂ) (z w : E) :
    wrightForm φ prodMap (c • z) w = c * wrightForm φ prodMap z w := by
  unfold wrightForm; rw [map_smul, mul_smul_comm, map_smul, smul_eq_mul]

/-- **The Wright form is additive in the right slot** `D_φ(z, w₁+w₂) = D_φ(z,w₁) + D_φ(z,w₂)`. -/
lemma wrightForm_add_right (φ : A →ₗ[ℂ] ℂ) (prodMap : E →ₗ[ℂ] A) (z w₁ w₂ : E) :
    wrightForm φ prodMap z (w₁ + w₂) = wrightForm φ prodMap z w₁ + wrightForm φ prodMap z w₂ := by
  unfold wrightForm; rw [map_add, star_add, add_mul, map_add]

/-- **The Wright form is conjugate-linear in the right slot** `D_φ(z, c·w) = c* · D_φ(z,w)` — so `D_φ` is
a sesquilinear form; with `wrightForm_diag_nonneg` it is a semi-inner product (Wright's positive
quadratic form), and its GNS quotient/completion is the representing Hilbert space. -/
lemma wrightForm_smul_right [StarModule ℂ A] (φ : A →ₗ[ℂ] ℂ) (prodMap : E →ₗ[ℂ] A)
    (c : ℂ) (z w : E) :
    wrightForm φ prodMap z (c • w) = starRingEnd ℂ c * wrightForm φ prodMap z w := by
  unfold wrightForm
  rw [map_smul, star_smul, smul_mul_assoc, map_smul, smul_eq_mul, starRingEnd_apply]


/-- **The Wright form is the standard homogeneous decoherence functional** (Rudolph–Wright §V.2): for
matrices with the trace-state `φ(x) = tr(x ρ)` and the class-operator map `prodMap = C`, the abstract Wright
form `D_φ(p,q) = φ(C_q* C_p) = tr(C_q† C_p ρ) = tr(C_p ρ C_q†)` equals Rudolph's standard homogeneous
decoherence functional `homogeneousDecoherence`. So Wright's quadratic-form representation *is* the
standard `d_ρ`. -/
lemma wrightForm_eq_homogeneousDecoherence {N : ℕ} {ι : Type*} [DecidableEq ι]
    (C : ι → Matrix (Fin N) (Fin N) ℂ) (ρ : Matrix (Fin N) (Fin N) ℂ)
    (φ : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] ℂ) (prodMap : (ι → ℂ) →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ)
    (hφ : ∀ X, φ X = (X * ρ).trace) (hprodMap : ∀ h : ι, prodMap (Pi.single h 1) = C h) (p q : ι) :
    wrightForm φ prodMap (Pi.single p 1) (Pi.single q 1)
      = homogeneousDecoherence C ρ p q := by
  unfold wrightForm homogeneousDecoherence
  rw [hprodMap, hprodMap, hφ, Matrix.star_eq_conjTranspose, mul_assoc, Matrix.trace_mul_comm]

end Physlib.QuantumMechanics.ComplexAction.WrightQuadraticFormRepresentation
