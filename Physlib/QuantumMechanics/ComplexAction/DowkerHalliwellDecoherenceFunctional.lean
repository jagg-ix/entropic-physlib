/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HistoryHilbertGramIsomorphism
public import Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston

/-!
# Dowker–Halliwell 1992: the decoherence functional and its normalization

The foundational decoherence functional of Dowker & Halliwell (*Phys. Rev. D* **46** (1992) 1580, "Quantum
mechanics of history"). For a pure state the decoherence functional (Eq. 2.20) is the **Gram matrix of the
branch (path-projected) vectors** `D(α,β) = ⟨Cα Ψ, Cβ Ψ⟩` — already in the repository as
`HistoryHilbertGramIsomorphism.gramDecoherence`, satisfying the elementary properties (Eqs. 2.23–2.25):
Hermiticity, diagonal non-negativity and strong positivity (`gram_isDecoherenceFunctional`).

This module adds the two pieces that complete the Dowker–Halliwell §II picture in the repository:

* the **normalization (Eq. 2.24)** `∑_{α,β} D(α,β) = ‖∑_α ψ_α‖²` — the sum of *all* matrix elements is the squared
  norm of the total branch vector (`= ‖Ψ‖² = 1` when the branches resolve a normalized state);
* the **identification** of the complex-action / entropic history kernel `DecoherenceFunctionalSorkinJohnston.decoherenceFunctional`
  with the Dowker–Halliwell Gram functional at `H = ℂ`: the two Dowker pictures — the 1992 projection/Gram
  decoherence functional and the later complex-action (`S_R + iS_ent`) weight — are one and the same object.

* **`gramDecoherence_total_sum`** — Eq. 2.24 (`∑∑ D = ‖∑ψ‖²`).
* **`decoherenceFunctional_eq_gramDecoherence`** — `decoherenceFunctional w = gramDecoherence (conj ∘ w)`.
* **`decoherenceFunctional_total_sum`** (`∑∑ D = |∑ w|²`) and **`decoherenceFunctional_diag_sum`**
  (`∑_α μ(α) = ∑_α |w(α)|²`, the diagonal normalization Eq. 2.25b).
* **§C — the off-diagonal inequality (§III.B, Eqs. 3.19/3.23).** **`gramDecoherence_offdiag_bound`**
  (`|D(α,β)|² ≤ D(α,α)·D(β,β)`, Cauchy–Schwarz — interference bounded by the geometric mean of Born
  probabilities) and **`decoherenceFunctional_offdiag_eq`** (equality for the pure/rank-one case).
* **§D — approximate decoherence (§III.A, Eqs. 3.4, 3.6).** **`sqrt_mul_le_add_div_two`** (`√(ab) ≤ (a+b)/2`, the
  geometric-≤-arithmetic-mean relation) and **`approxDecoherence_arith_of_geom`** (the geometric-mean decoherence
  condition (3.4) entails the arithmetic one (3.3)).
* **§E — the general off-diagonal bound (Eq. 3.19).** **`decoherence_offdiag_bound`** — `|D(α,β)|² ≤ D(α,α)·D(β,β)`
  for *any* `IsDecoherenceFunctional` (mixed states, not just Gram/pure), from the `2×2` PSD form
  (`two_history_quadratic_nonneg`) via a non-positive discriminant.

**Honest layering.** Exact inner-product / `Finset` identities. The Gram construction and its decoherence-functional
axioms are reused verbatim from `HistoryHilbertGramIsomorphism`; the only new content is the total-sum
normalization and the `H = ℂ` identification with the entropic kernel.

## References

* H. F. Dowker, J. J. Halliwell, *Phys. Rev. D* **46** (1992) 1580, §II, Eqs. 2.20–2.25. Composes
  `HistoryHilbertGramIsomorphism` and `DecoherenceFunctionalSorkinJohnston`.


-/

set_option autoImplicit false

open scoped InnerProductSpace
open Physlib.QuantumMechanics.ComplexAction.HistoryHilbertGramIsomorphism
open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DowkerHalliwellDecoherenceFunctional

variable {ι : Type*}


/-- **The total sum of the decoherence functional is the squared norm of the total branch vector (Eq. 2.24)**
`∑_{α,β} ⟨ψα, ψβ⟩ = ‖∑_α ψα‖²` — by bilinearity of the inner product; equals `‖Ψ‖² = 1` when the branches
`{ψα}` resolve a normalized state `Ψ = ∑ ψα`. -/
lemma gramDecoherence_total_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [Fintype ι] (ψ : ι → H) :
    ∑ α, ∑ β, gramDecoherence ψ α β = (‖∑ α, ψ α‖ : ℂ) ^ 2 := by
  simp_rw [gramDecoherence, ← inner_sum]
  rw [← sum_inner]
  exact inner_self_eq_norm_sq_to_K _


/-- **The complex-action decoherence functional is the Dowker–Halliwell Gram functional at `H = ℂ`**
`decoherenceFunctional w = gramDecoherence (conj ∘ w)` — the 1992 projection/Gram decoherence functional and the
complex-action (`S_R + iS_ent`) history kernel are the same rank-one object, the branch vectors being the (conjugate)
scalar amplitudes `w(α)`. -/
lemma decoherenceFunctional_eq_gramDecoherence (w : ι → ℂ) :
    decoherenceFunctional w = gramDecoherence (fun a => (starRingEnd ℂ) (w a)) := by
  funext α β
  rw [decoherenceFunctional_apply, gramDecoherence, RCLike.inner_apply, Complex.conj_conj]
  ring

/-- **The total sum for the entropic kernel (Eq. 2.24)** `∑_{α,β} D(α,β) = |∑_α w(α)|²` — the squared modulus of
the total history amplitude. -/
lemma decoherenceFunctional_total_sum [Fintype ι] (w : ι → ℂ) :
    ∑ α, ∑ β, decoherenceFunctional w α β = (Complex.normSq (∑ α, w α) : ℂ) := by
  simp_rw [decoherenceFunctional_apply]
  rw [← Finset.sum_mul_sum, ← map_sum, Complex.mul_conj]

/-- **The diagonal normalization (Eq. 2.25b)** `∑_α μ(α) = ∑_α |w(α)|²` — the total quantal (Born) measure is the
sum of the branch weights (`= 1` when the branches are normalized), the classical total probability. -/
lemma decoherenceFunctional_diag_sum [Fintype ι] (w : ι → ℂ) :
    ∑ α, quantalMeasure (decoherenceFunctional w) α = ∑ α, Complex.normSq (w α) := by
  simp_rw [decoherenceFunctional_quantalMeasure]


/-- **The off-diagonal decoherence-functional bound (Eq. 3.23)** `|D(α,β)|² ≤ D(α,α)·D(β,β)` — the interference
(off-diagonal) elements are bounded by the geometric mean of the diagonal Born probabilities. For the pure-state
Gram functional it is the Cauchy–Schwarz inequality `|⟨ψα, ψβ⟩|² ≤ ‖ψα‖²‖ψβ‖²`, the main result of §III.B. -/
lemma gramDecoherence_offdiag_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : ι → H) (α β : ι) :
    ‖gramDecoherence ψ α β‖ ^ 2 ≤ (gramDecoherence ψ α α).re * (gramDecoherence ψ β β).re := by
  have hα : (gramDecoherence ψ α α).re = ‖ψ α‖ ^ 2 := by
    rw [gramDecoherence]; exact inner_self_eq_norm_sq (𝕜 := ℂ) (ψ α)
  have hβ : (gramDecoherence ψ β β).re = ‖ψ β‖ ^ 2 := by
    rw [gramDecoherence]; exact inner_self_eq_norm_sq (𝕜 := ℂ) (ψ β)
  rw [hα, hβ, ← mul_pow]
  gcongr
  exact norm_inner_le_norm (ψ α) (ψ β)

/-- **The off-diagonal bound is saturated for the pure (rank-one) case (Eq. 3.23 equality)** `|D(α,β)|² =
D(α,α)·D(β,β)` — the complex-action / entropic history kernel `D(α,β) = w(α)conj(w(β))` is pure, so
Cauchy–Schwarz holds with equality: `|w(α)|²|w(β)|²`. -/
lemma decoherenceFunctional_offdiag_eq (w : ι → ℂ) (α β : ι) :
    ‖decoherenceFunctional w α β‖ ^ 2
      = (decoherenceFunctional w α α).re * (decoherenceFunctional w β β).re := by
  rw [decoherenceFunctional_apply, decoherenceFunctional_apply, decoherenceFunctional_apply,
    Complex.mul_conj, Complex.mul_conj, Complex.ofReal_re, Complex.ofReal_re,
    norm_mul, mul_pow, RCLike.norm_conj, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]


/-- **Geometric mean ≤ arithmetic mean (Eq. 3.6)** `√(ab) ≤ (a+b)/2` — the geometric mean of the diagonal Born
weights is bounded by their arithmetic mean, showing the geometric-mean decoherence condition (3.4) is tighter
than the arithmetic-mean one (3.3). -/
lemma sqrt_mul_le_add_div_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  rw [Real.sqrt_mul ha]
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb,
    Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- **The approximate-decoherence condition (3.4) implies the arithmetic bound (3.3)** — if an off-diagonal
(real part) term is bounded by `ε` times the *geometric* mean of the diagonal Born weights,
`|Re D(α,α')| ≤ ε√(D(α,α)·D(α',α'))`, then it is bounded by `ε` times their *arithmetic* mean,
`≤ ε·(D(α,α)+D(α',α'))/2`. So the (stronger, more useful) geometric-mean condition entails the arithmetic one. -/
lemma approxDecoherence_arith_of_geom (ε dαα dα'α' r : ℝ) (hε : 0 ≤ ε)
    (hαα : 0 ≤ dαα) (hα'α' : 0 ≤ dα'α') (h : |r| ≤ ε * Real.sqrt (dαα * dα'α')) :
    |r| ≤ ε * ((dαα + dα'α') / 2) :=
  h.trans (by gcongr; exact sqrt_mul_le_add_div_two dαα dα'α' hαα hα'α')


/-- **The off-diagonal bound for any decoherence functional (Eq. 3.19)** `|D(α,β)|² ≤ D(α,α)·D(β,β)` — for an
arbitrary (mixed-state) `IsDecoherenceFunctional`, not just the pure/Gram case: from the positive-semidefiniteness
of the `2×2` history matrix (`two_history_quadratic_nonneg`), the quadratic `t ↦ D(α,α)t² + 2|D(α,β)|²t +
D(β,β)|D(α,β)|² ≥ 0` has non-positive discriminant, giving the Cauchy–Schwarz bound. -/
lemma decoherence_offdiag_bound [DistribLattice ι] [OrderBot ι] {D : ι → ι → ℂ}
    (h : IsDecoherenceFunctional D) (α β : ι) :
    ‖D α β‖ ^ 2 ≤ (D α α).re * (D β β).re := by
  have hnorm : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hA : 0 ≤ (D α α).re := quantalMeasure_nonneg h α
  have hB : 0 ≤ (D β β).re := quantalMeasure_nonneg h β
  rcases eq_or_ne α β with rfl | hαβ
  · rw [hnorm, decoherence_diag_real h α]; nlinarith
  · have heq : ∀ t : ℝ,
        (starRingEnd ℂ (t : ℂ) * (t : ℂ) * D α α).re
          + (starRingEnd ℂ (t : ℂ) * starRingEnd ℂ (D α β) * D α β).re
          + (starRingEnd ℂ (starRingEnd ℂ (D α β)) * (t : ℂ) * D β α).re
          + (starRingEnd ℂ (starRingEnd ℂ (D α β)) * starRingEnd ℂ (D α β) * D β β).re
        = (D α α).re * (t * t) + 2 * ‖D α β‖ ^ 2 * t + (D β β).re * ‖D α β‖ ^ 2 := by
      intro t
      have hh := h.hermitian β α
      simp only [hh, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, decoherence_diag_real h α, decoherence_diag_real h β]
      rw [hnorm]; ring
    have hq : ∀ t : ℝ, 0 ≤ (D α α).re * (t * t) + 2 * ‖D α β‖ ^ 2 * t + (D β β).re * ‖D α β‖ ^ 2 :=
      fun t => (heq t) ▸ two_history_quadratic_nonneg h hαβ (t : ℂ) (starRingEnd ℂ (D α β))
    have hdisc := discrim_le_zero hq
    rw [discrim] at hdisc
    nlinarith [hdisc, sq_nonneg ‖D α β‖, hA, hB, mul_nonneg hA hB]

end Physlib.QuantumMechanics.ComplexAction.DowkerHalliwellDecoherenceFunctional
