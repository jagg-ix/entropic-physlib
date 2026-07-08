/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState

/-!
# History Hilbert space from the decoherence functional (Dowker–Johnston–Sorkin)

Dowker, Johnston & Sorkin, *Hilbert spaces from path integrals* (J. Phys. A **43** (2010) 275302,
arXiv:1002.0589): a Hilbert space can be built directly from a **quantum measure system**
`(Ω, 𝔄, D)` — a sample space of histories, a Boolean **event algebra** `𝔄`, and a **decoherence
functional** `D : 𝔄 × 𝔄 → ℂ`. The decoherence functional is a Hermitian, biadditive, strongly
positive correlation kernel; its GNS/Kolmogorov-dilation construction gives the *history Hilbert space*,
whose inner product is `D` itself.

This is the abstract framework beneath the Sorkin–Johnston vacuum: the SJ two-point function
`SorkinJohnstonRegionState.wightmanTwoPoint` is a decoherence functional, and its positivity is the
strong positivity here.

* **§A — the decoherence functional** (paper §2.2). `IsDecoherenceFunctional D`: Hermiticity
 `D(α,β) = D(β,α)*`, biadditivity on disjoint unions `D(α, β⊔γ) = D(α,β) + D(α,γ)`, and strong
 positivity (the `N×N` matrix `D(αᵢ,αⱼ)` is positive semidefinite). Biadditivity in the first slot
 follows (`biadditive_left`).
* **§B — the quantal measure** (paper §2.2). `quantalMeasure D α = Re D(α,α)`; it is real
 (`decoherence_diag_real`) and non-negative (`quantalMeasure_nonneg`) — quantum measure-theory
 positivity.
* **§C — quantal interference** (the double-slit / quantal sum rule). For disjoint `α, β`,
 `μ(α⊔β) = μ(α) + μ(β) + 2 Re D(α,β)` (`interference`) — the interference term `2 Re D(α,β)` is the
 departure from classical additivity.
* **§D — the history Hilbert space** (paper §2.3). The induced inner product
 `⟨u,v⟩_D = Σ u(α)* v(β) D(α,β)` is Hermitian (`historyInner_conj_symm`) and positive semidefinite
 (`historyInner_self_nonneg`) — the GNS/Kolmogorov inner product whose completion (mod null space) is
 the history Hilbert space.
* **§E — the Sorkin–Johnston bridge.** The SJ two-point function satisfies the decoherence-functional
 Hermiticity condition (`sj_wightman_isHermitian`), so the SJ vacuum's history Hilbert space is this
 construction applied to `wightmanTwoPoint`.

Proven: the algebra of the decoherence functional (Hermiticity/biadditivity
consequences, quantal measure reality and positivity, the interference identity, and the Hermitian
positive-semidefinite history inner product), and the SJ Hermiticity bridge. Interpretive: the event
algebra `𝔄` is modelled as a bounded lattice with disjoint joins (the Boolean structure of §2.1); the
GNS quotient-by-null-space and Cauchy completion producing the concrete Hilbert space are the standard
dilation, encoded in the positive-semidefinite form here.

## References

* F. Dowker, S. Johnston, R. D. Sorkin, "Hilbert spaces from path integrals", J. Phys. A: Math. Theor.
 **43** (2010) 275302 [arXiv:1002.0589], §2. Reuses `SorkinJohnstonRegionState`
 (`wightmanTwoPoint`, `wightman_hermitian`, `IsSymmetricKernel`, `IsPauliJordan`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert

open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
open scoped BigOperators

/-! ## §A — the decoherence functional -/

variable {ι : Type*} [DistribLattice ι] [OrderBot ι]

/-- **A decoherence functional** `D : 𝔄 × 𝔄 → ℂ` (Dowker–Johnston–Sorkin §2.2): Hermitian, biadditive
on disjoint unions, and strongly positive (the `N×N` matrix `D(αᵢ,αⱼ)` is positive semidefinite). This
is the correlation kernel whose GNS construction is the history Hilbert space. -/
structure IsDecoherenceFunctional (D : ι → ι → ℂ) : Prop where
  /-- **Hermiticity** `D(α,β) = D(β,α)*`. -/
  hermitian : ∀ α β, D α β = starRingEnd ℂ (D β α)
  /-- **Biadditivity** `D(α, β⊔γ) = D(α,β) + D(α,γ)` for disjoint `β, γ`. -/
  biadditive : ∀ α β γ, Disjoint β γ → D α (β ⊔ γ) = D α β + D α γ
  /-- **Strong positivity**: for any finite family with coefficients `c`, the quadratic form is
  non-negative — the `N×N` matrix `D(αᵢ,αⱼ)` is positive semidefinite. -/
  posSemidef : ∀ (s : Finset ι) (c : ι → ℂ),
    0 ≤ (∑ α ∈ s, ∑ β ∈ s, starRingEnd ℂ (c α) * c β * D α β).re

variable {D : ι → ι → ℂ}

/-- **Biadditivity in the first argument** `D(α⊔β, γ) = D(α,γ) + D(β,γ)`, from Hermiticity and
second-slot biadditivity. -/
theorem biadditive_left (h : IsDecoherenceFunctional D) (α β γ : ι) (hd : Disjoint α β) :
    D (α ⊔ β) γ = D α γ + D β γ := by
  rw [h.hermitian (α ⊔ β) γ, h.biadditive γ α β hd, map_add, ← h.hermitian α γ, ← h.hermitian β γ]

/-! ## §B — the quantal measure -/

/-- **The quantal measure** `μ(α) = Re D(α,α)` (Dowker–Johnston–Sorkin §2.2). -/
def quantalMeasure (D : ι → ι → ℂ) (α : ι) : ℝ := (D α α).re

/-- **The decoherence functional is real on the diagonal** `D(α,α) = D(α,α)*`, so `Im D(α,α) = 0`. -/
theorem decoherence_diag_real (h : IsDecoherenceFunctional D) (α : ι) : (D α α).im = 0 :=
  Complex.conj_eq_iff_im.mp (h.hermitian α α).symm

/-- **The quantal measure is non-negative** `μ(α) ≥ 0` (positivity of the quantum measure), the `N = 1`
case of strong positivity. -/
theorem quantalMeasure_nonneg (h : IsDecoherenceFunctional D) (α : ι) : 0 ≤ quantalMeasure D α := by
  have := h.posSemidef {α} (fun _ => 1)
  simpa [quantalMeasure] using this

/-! ## §C — quantal interference (the double-slit sum rule) -/

/-- **Quantal interference** `μ(α⊔β) = μ(α) + μ(β) + 2 Re D(α,β)` for disjoint events (Dowker–Johnston–
Sorkin §2.2): the quantum measure fails classical additivity by the interference term `2 Re D(α,β)` —
the double-slit interference between the two histories. -/
theorem interference (h : IsDecoherenceFunctional D) (α β : ι) (hd : Disjoint α β) :
    quantalMeasure D (α ⊔ β) = quantalMeasure D α + quantalMeasure D β + 2 * (D α β).re := by
  unfold quantalMeasure
  have key : D (α ⊔ β) (α ⊔ β) = D α α + D β β + (D α β + D β α) := by
    rw [biadditive_left h α β (α ⊔ β) hd, h.biadditive α α β hd, h.biadditive β α β hd]; ring
  rw [key, h.hermitian β α]
  simp only [Complex.add_re, Complex.conj_re]
  ring

/-! ## §D — the history Hilbert space -/

/-- **The history inner product** `⟨u,v⟩_D = Σ_{α,β} u(α)* v(β) D(α,β)` induced by the decoherence
functional on finitely supported functions on the event algebra (Dowker–Johnston–Sorkin §2.3). -/
noncomputable def historyInner (D : ι → ι → ℂ) (s : Finset ι) (u v : ι → ℂ) : ℂ :=
  ∑ α ∈ s, ∑ β ∈ s, starRingEnd ℂ (u α) * v β * D α β

/-- **The history inner product is positive semidefinite** `⟨u,u⟩_D ≥ 0` (strong positivity): the
norm-squared on the history Hilbert space is non-negative — the property that makes the GNS/Kolmogorov
construction a genuine (pre-)Hilbert space. -/
theorem historyInner_self_nonneg (h : IsDecoherenceFunctional D) (s : Finset ι) (u : ι → ℂ) :
    0 ≤ (historyInner D s u u).re :=
  h.posSemidef s u

/-- **The history inner product is Hermitian** `⟨u,v⟩_D = ⟨v,u⟩_D*` (conjugate symmetry): the induced
sesquilinear form is Hermitian, from the Hermiticity of `D`. -/
theorem historyInner_conj_symm (h : IsDecoherenceFunctional D) (s : Finset ι) (u v : ι → ℂ) :
    starRingEnd ℂ (historyInner D s v u) = historyInner D s u v := by
  unfold historyInner
  rw [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [map_mul, map_mul, Complex.conj_conj, h.hermitian α β, Complex.conj_conj]
  ring

omit [DistribLattice ι] [OrderBot ι] in
/-- **[The history inner product is additive in the second argument] `⟨u, v+w⟩_D = ⟨u,v⟩_D + ⟨u,w⟩_D`**. -/
theorem historyInner_add_right (s : Finset ι) (u v w : ι → ℂ) :
    historyInner D s u (v + w) = historyInner D s u v + historyInner D s u w := by
  unfold historyInner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun β _ => by simp only [Pi.add_apply]; ring

omit [DistribLattice ι] [OrderBot ι] in
/-- **[The history inner product is linear in the second argument] `⟨u, c•v⟩_D = c ⟨u,v⟩_D`**. -/
theorem historyInner_smul_right (s : Finset ι) (c : ℂ) (u v : ι → ℂ) :
    historyInner D s u (c • v) = c * historyInner D s u v := by
  unfold historyInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun β _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

omit [DistribLattice ι] [OrderBot ι] in
/-- **[The history inner product is conjugate-linear in the first argument] `⟨c•u, v⟩_D = c̄ ⟨u,v⟩_D`** — with
`historyInner_add_right`, `historyInner_smul_right` and `historyInner_conj_symm` this makes `⟨·,·⟩_D` a
Hermitian sesquilinear form: the (pre-)inner product of the history Hilbert space. -/
theorem historyInner_smul_left (s : Finset ι) (c : ℂ) (u v : ι → ℂ) :
    historyInner D s (c • u) v = starRingEnd ℂ c * historyInner D s u v := by
  unfold historyInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun β _ => by simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring

/-- **[The history inner product is real on the diagonal] `Im ⟨u,u⟩_D = 0`** — the norm-squared is a real
number (`≥ 0` by `historyInner_self_nonneg`), as required of a Hilbert-space norm. -/
theorem historyInner_self_real (h : IsDecoherenceFunctional D) (s : Finset ι) (u : ι → ℂ) :
    (historyInner D s u u).im = 0 :=
  Complex.conj_eq_iff_im.mp (historyInner_conj_symm h s u u)

/-! ## §E — the Sorkin–Johnston bridge -/

/-- **The Sorkin–Johnston two-point satisfies the decoherence-functional Hermiticity condition**
`W(x,y) = W(y,x)*`: the SJ Wightman function is (the Hermitian part of) a decoherence functional, so the
Sorkin–Johnston vacuum's history Hilbert space is the Dowker–Johnston–Sorkin construction applied to
`wightmanTwoPoint`; its strong positivity is the SJ positive-spectral selection. -/
theorem sj_wightman_isHermitian {α : Type*} (A Δ : α → α → ℝ) (hA : IsSymmetricKernel A)
    (hΔ : IsPauliJordan Δ) (x y : α) :
    wightmanTwoPoint A Δ x y = starRingEnd ℂ (wightmanTwoPoint A Δ y x) :=
  (wightman_hermitian A Δ hA hΔ y x).symm

/-! ## §F — the third-order sum rule (Sorkin's quantum-measure hierarchy) -/

/-- **[Sorkin's third-order sum rule] `I₃ = 0`** (R. D. Sorkin, *Quantum mechanics as quantum measure
theory*, Mod. Phys. Lett. A **9** (1994) 3119): for pairwise-disjoint events,
`μ(α⊔β⊔γ) = μ(α⊔β) + μ(β⊔γ) + μ(α⊔γ) − μ(α) − μ(β) − μ(γ)`. Equivalently the triple-interference term
`I₃ := μ(α⊔β⊔γ) − Σμ(pairs) + Σμ(singles)` vanishes. This is the defining property of a *quantum* measure:
unlike a classical (Kolmogorov) measure it records non-trivial **pairwise** interference (`interference`,
`I₂ = 2 Re D(α,β) ≠ 0` — the double slit), but has **no genuine triple interference** — the level of Sorkin's
measure hierarchy at which the sum-over-histories/path-integral formulation of quantum theory sits. -/
theorem sorkin_third_order_sum_rule (h : IsDecoherenceFunctional D) (α β γ : ι)
    (hab : Disjoint α β) (hbc : Disjoint β γ) (hac : Disjoint α γ) :
    quantalMeasure D (α ⊔ β ⊔ γ)
      = quantalMeasure D (α ⊔ β) + quantalMeasure D (β ⊔ γ) + quantalMeasure D (α ⊔ γ)
        - quantalMeasure D α - quantalMeasure D β - quantalMeasure D γ := by
  have habc : Disjoint (α ⊔ β) γ := hac.sup_left hbc
  rw [interference h (α ⊔ β) γ habc, biadditive_left h α β γ hab,
    interference h β γ hbc, interference h α γ hac, Complex.add_re]
  ring

/-- **[Decoherence ⇒ classical additivity]** if two disjoint events do not interfere (`Re D(α,β) = 0`, the
decoherence condition of consistent-histories), the quantum measure is classically additive on them
`μ(α⊔β) = μ(α) + μ(β)`: the classical (Kolmogorov) limit `I₂ = 0` of the quantum measure. -/
theorem interference_decohered (h : IsDecoherenceFunctional D) (α β : ι) (hd : Disjoint α β)
    (hdec : (D α β).re = 0) :
    quantalMeasure D (α ⊔ β) = quantalMeasure D α + quantalMeasure D β := by
  rw [interference h α β hd, hdec]; ring

/-! ## §G — the two-history decoherence matrix is positive semidefinite -/

/-- **[Two-history strong positivity]** the `2×2` decoherence matrix `[[D(α,α), D(α,β)], [D(β,α), D(β,β)]]`
of any two distinct histories is positive semidefinite: for all complex amplitudes `cα, cβ`,
`Re[ c̄α cα D(α,α) + c̄α cβ D(α,β) + c̄β cα D(β,α) + c̄β cβ D(β,β) ] ≥ 0` — the double-slit specialisation of
strong positivity, the quadratic form whose non-negativity gives the interference bound. -/
theorem two_history_quadratic_nonneg (h : IsDecoherenceFunctional D) {α β : ι} (hαβ : α ≠ β)
    (cα cβ : ℂ) :
    0 ≤ (starRingEnd ℂ cα * cα * D α α).re + (starRingEnd ℂ cα * cβ * D α β).re
        + (starRingEnd ℂ cβ * cα * D β α).re + (starRingEnd ℂ cβ * cβ * D β β).re := by
  classical
  set c : ι → ℂ := fun x => if x = α then cα else cβ with hcdef
  have hcα : c α = cα := if_pos rfl
  have hcβ : c β = cβ := if_neg hαβ.symm
  have hpos := h.posSemidef {α, β} c
  simp only [Finset.sum_pair hαβ, hcα, hcβ, Complex.add_re] at hpos
  linarith [hpos]

/-- **[The interference is bounded by the measures] `|2 Re D(α,β)| ≤ μ(α) + μ(β)`** — a Tsirelson-type bound
on the quantum measure: the double-slit interference term `I₂ = 2 Re D(α,β)` cannot exceed the sum of the
individual quantal measures, a direct consequence of two-history strong positivity (coefficients `(1,1)` and
`(1,−1)`). -/
theorem abs_interference_le (h : IsDecoherenceFunctional D) {α β : ι} (hαβ : α ≠ β) :
    |2 * (D α β).re| ≤ quantalMeasure D α + quantalMeasure D β := by
  have hre : (D β α).re = (D α β).re := by rw [h.hermitian β α, Complex.conj_re]
  have h1 := two_history_quadratic_nonneg h hαβ 1 1
  have h2 := two_history_quadratic_nonneg h hαβ 1 (-1)
  simp only [map_one, map_neg, one_mul, mul_one, neg_mul, mul_neg, neg_neg, Complex.neg_re] at h1 h2
  unfold quantalMeasure
  rw [abs_le]
  constructor <;> linarith [h1, h2, hre]

/-! ## §H — the empty history (normalization) -/

/-- **[The decoherence functional vanishes on the empty history] `D(α, ⊥) = 0`** — the impossible event
`⊥` (the empty set of histories) does not decohere with anything, from biadditivity on `⊥ = ⊥ ⊔ ⊥`. -/
theorem decoherence_bot_right (h : IsDecoherenceFunctional D) (α : ι) : D α ⊥ = 0 := by
  have hb := h.biadditive α ⊥ ⊥ disjoint_bot_left
  rw [sup_idem] at hb
  linear_combination -hb

/-- **[The decoherence functional vanishes on the empty history, left slot] `D(⊥, α) = 0`**. -/
theorem decoherence_bot_left (h : IsDecoherenceFunctional D) (α : ι) : D ⊥ α = 0 := by
  rw [h.hermitian ⊥ α, decoherence_bot_right h α, map_zero]

/-- **[The quantal measure of the empty history is zero] `μ(⊥) = 0`** — the impossible event has zero measure,
the normalization of the quantum measure. -/
theorem quantalMeasure_bot (h : IsDecoherenceFunctional D) : quantalMeasure D ⊥ = 0 := by
  rw [quantalMeasure, decoherence_bot_right h ⊥, Complex.zero_re]

/-! ## §I — the Cauchy–Schwarz inequality for the decoherence functional -/

/-- **[The Cauchy–Schwarz defect] `0 ≤ μ(α)·(μ(α)μ(β) − |D(α,β)|²)`** — feeding the amplitudes
`(D(α,β), −μ(α))` into two-history strong positivity, the resulting quadratic form is `μ(α)` times the
Cauchy–Schwarz defect `μ(α)μ(β) − |D(α,β)|²`. Unconditional (holds even at null events); dividing by a positive
`μ(α)` gives the Cauchy–Schwarz inequality. -/
theorem cauchySchwarz_defect (h : IsDecoherenceFunctional D) {α β : ι} (hαβ : α ≠ β) :
    0 ≤ quantalMeasure D α * (quantalMeasure D α * quantalMeasure D β - Complex.normSq (D α β)) := by
  have hr : (D β α).re = (D α β).re := by rw [h.hermitian β α, Complex.conj_re]
  have hi : (D β α).im = -(D α β).im := by rw [h.hermitian β α, Complex.conj_im]
  have hαα : (D α α).im = 0 := decoherence_diag_real h α
  have hββ : (D β β).im = 0 := decoherence_diag_real h β
  have key := two_history_quadratic_nonneg h hαβ (D α β) (-(quantalMeasure D α : ℂ))
  simp only [map_neg, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, quantalMeasure] at key
  rw [hr, hi, hαα, hββ] at key
  simp only [quantalMeasure, Complex.normSq_apply]
  nlinarith [key]

/-- **[Cauchy–Schwarz for the decoherence functional] `|D(α,β)|² ≤ μ(α)·μ(β)`** (Dowker–Johnston–Sorkin
strong positivity, at a non-null event `μ(α) > 0`): the modulus of the off-diagonal decoherence — the coherence
between two distinct histories — is bounded by the product of their quantal measures. Equivalently the `2×2`
decoherence matrix has non-negative determinant. This is the inequality that makes the history inner product a
genuine (pre-)Hilbert norm, `|⟨α,β⟩_D| ≤ ‖α‖_D ‖β‖_D`. -/
theorem decoherence_cauchySchwarz (h : IsDecoherenceFunctional D) {α β : ι} (hαβ : α ≠ β)
    (hμα : 0 < quantalMeasure D α) :
    Complex.normSq (D α β) ≤ quantalMeasure D α * quantalMeasure D β := by
  nlinarith [cauchySchwarz_defect h hαβ, hμα]

end Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert
