/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Tactic.FieldSimp
/- ZIL-BEGIN -/
public meta import Zil
/- ZIL-END -/
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# The Gibbs inequality: relative entropy is a nonnegative statistical distance

The master inequality of the entropic-time / complex-action program. For discrete probability
distributions `p, q` the **relative entropy** (Kullback–Leibler divergence)

  `D(p‖q) = Σᵢ pᵢ log(pᵢ/qᵢ)`   (`klDivergence`)

is **nonnegative** (`klDivergence_nonneg`) and, for full-support probability distributions, vanishes
exactly when `p = q` (`klDivergence_eq_zero_iff`). It is the statistical divergence whose minimization
underlies Caticha's maximum-entropy inference. It rests on the pointwise convexity bound
`a − b ≤ a log(a/b)`
(`pointwise_gibbs`, from `log x ≤ x − 1`), summed against `Σp = Σq = 1`.

Its thermodynamic face is the **second law / free-energy variational principle**: for the canonical Gibbs
state `πᵢ = e^{−βEᵢ}/Z` the Helmholtz free energy `F[p] = ⟨E⟩_p − T·S[p]` satisfies

  `F[p] − F[π] = T · D(p‖π) ≥ 0`   (`freeEnergy_gibbs_le`, `T = 1/β`),

so the Gibbs state uniquely minimizes the free energy. This is the global (summed) counterpart of the
density-level bound in `EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy`, and the general principle
behind the maximum-entropy bound `H(p) ≤ log deg` of `PermutationInvariantEntanglementEntropy` (the
`q = uniform` case: `D(p‖uniform) = log deg − H(p) ≥ 0`).

* **§A — the pointwise bound.** `pointwise_gibbs` (`a − b ≤ a log(a/b)`).
* **§B — the Gibbs inequality.** `klDivergence`, `klDivergence_nonneg` (`D(p‖q) ≥ 0`),
  `klDivergence_self` (`D(p‖p) = 0`), and the full-support equality case
  `klDivergence_eq_zero_iff`.
* **§C — the free-energy variational principle.** `gibbsState`, `freeEnergy`, `freeEnergy_sub_eq_kl`
  (`F[p] = T·D(p‖π) − T log Z`), `freeEnergy_gibbs_le` (`F[π] ≤ F[p]`).

## References

* J. W. Gibbs; S. Kullback, R. A. Leibler, *On information and sufficiency*, Ann. Math. Statist. 22 (1951)
  79. A. Caticha, *Entropic dynamics* — maximum-entropy inference minimizes the relative entropy.
  Companion to `EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy` (density level) and
  `PermutationInvariantEntanglementEntropy` (the `q = uniform` max-entropy corollary).
-/

set_option autoImplicit false

open Finset

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality

/-! ### §A — the pointwise bound -/

/-- **[Pointwise Gibbs bound]** `a − b ≤ a log(a/b)` for `a ≥ 0`, `b > 0` — the convexity inequality
`log x ≤ x − 1` in the form driving the relative entropy's nonnegativity. -/
lemma pointwise_gibbs {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) : a - b ≤ a * Real.log (a / b) := by
  rcases ha.eq_or_lt with h | h
  · rw [← h, zero_mul]; linarith
  · have hba : 0 < b / a := div_pos hb h
    have hlog : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos hba
    have hpq : Real.log (a / b) = -Real.log (b / a) := by rw [← Real.log_inv, inv_div]
    rw [hpq, mul_neg]
    have he : a * (b / a - 1) = b - a := by
      field_simp
    have hm : a * Real.log (b / a) ≤ b - a := by
      have hml := mul_le_mul_of_nonneg_left hlog h.le
      linarith [hml, he]
    linarith

/-! ### §B — the Gibbs inequality -/

variable {ι : Type*} [Fintype ι]

/-- The discrete **relative entropy** (Kullback–Leibler divergence) `D(p‖q) = Σᵢ pᵢ log(pᵢ/qᵢ)`. -/
noncomputable def klDivergence (p q : ι → ℝ) : ℝ := ∑ i, p i * Real.log (p i / q i)

/-- **[Gibbs inequality `D(p‖q) ≥ 0`]** the relative entropy of any probability distribution `p` from any
full-support distribution `q` is nonnegative — the second law / maximum-entropy master inequality. -/
theorem klDivergence_nonneg (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) : 0 ≤ klDivergence p q := by
  have hsum : ∑ i, (p i - q i) ≤ ∑ i, p i * Real.log (p i / q i) :=
    Finset.sum_le_sum (fun i _ => pointwise_gibbs (hp i) (hq i))
  have hz : ∑ i, (p i - q i) = 0 := by rw [Finset.sum_sub_distrib, hps, hqs, sub_self]
  rw [klDivergence]; linarith [hsum, hz]

/-- **[`D(p‖p) = 0`]** the relative entropy vanishes at coincidence. Uniqueness under full-support
probability hypotheses is supplied separately by `klDivergence_eq_zero_iff`. -/
theorem klDivergence_self (p : ι → ℝ) : klDivergence p p = 0 := by
  rw [klDivergence]
  apply Finset.sum_eq_zero
  intro i _
  rcases eq_or_ne (p i) 0 with h | h
  · rw [h, zero_mul]
  · rw [div_self h, Real.log_one, mul_zero]

/-- **[Strict Gibbs equality case]** the pointwise Gibbs bound is saturated for positive `a, b`
only when `a = b`. -/
lemma eq_of_pointwise_gibbs_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a - b = a * Real.log (a / b)) : a = b := by
  by_contra hne
  have hba_pos : 0 < b / a := div_pos hb ha
  have hba_ne : b / a ≠ 1 := fun hh => hne (by rw [div_eq_one_iff_eq ha.ne'] at hh; exact hh.symm)
  have hlog : Real.log (b / a) < b / a - 1 := Real.log_lt_sub_one_of_pos hba_pos hba_ne
  have hmul : a * Real.log (b / a) < a * (b / a - 1) := mul_lt_mul_of_pos_left hlog ha
  have he : a * (b / a - 1) = b - a := by field_simp
  have hpq : Real.log (a / b) = -Real.log (b / a) := by rw [← Real.log_inv, inv_div]
  rw [hpq, mul_neg] at h
  linarith [hmul, he]

/-- **[KL equality case]** for full-support probability distributions,
`D(p‖q) = 0 ↔ p = q` pointwise. -/
theorem klDivergence_eq_zero_iff {p q : ι → ℝ} (hp : ∀ i, 0 < p i)
    (hq : ∀ i, 0 < q i) (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    klDivergence p q = 0 ↔ p = q := by
  refine ⟨fun h0 => funext (fun i => ?_), fun h => h ▸ klDivergence_self p⟩
  have hnonneg : ∀ j ∈ Finset.univ, 0 ≤ p j * Real.log (p j / q j) - (p j - q j) :=
    fun j _ => by linarith [pointwise_gibbs (hp j).le (hq j)]
  have hklsum : ∑ j, p j * Real.log (p j / q j) = 0 := h0
  have hsum0 : ∑ j, (p j * Real.log (p j / q j) - (p j - q j)) = 0 := by
    rw [Finset.sum_sub_distrib, hklsum, Finset.sum_sub_distrib, hps, hqs]
    ring
  have hterm0 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0
  exact eq_of_pointwise_gibbs_eq (hp i) (hq i)
    (by linarith [hterm0 i (Finset.mem_univ i)])

/-! ### §B′ — information inequalities from `D ≥ 0`

The three most-central inequalities of information theory are immediate corollaries of the Gibbs
inequality: mutual information / entropy subadditivity, the Jensen–Shannon divergence, and
cross-entropy ≥ entropy. -/

/-- **[Mutual information ≥ 0 / entropy subadditivity]** `I(X;Y) = D(p_XY‖p_X⊗p_Y) ≥ 0`: the relative
entropy of a joint distribution from the product of its marginals is nonnegative — equivalently
`S(X,Y) ≤ S(X)+S(Y)`. Supplies the inequality for the object also named `finiteMutualInformation` in
`Thermodynamics.KullbackLeiblerInformationGain` (defined there without a nonnegativity theorem). -/
theorem mutualInformation_nonneg {κ : Type*} [Fintype κ]
    (pXY : ι × κ → ℝ) (pX : ι → ℝ) (pY : κ → ℝ)
    (hpXY : ∀ z, 0 ≤ pXY z) (hpX : ∀ i, 0 < pX i) (hpY : ∀ j, 0 < pY j)
    (hsum : ∑ z, pXY z = 1) (hXsum : ∑ i, pX i = 1) (hYsum : ∑ j, pY j = 1) :
    0 ≤ klDivergence pXY (fun z => pX z.1 * pY z.2) := by
  refine klDivergence_nonneg pXY _ hpXY (fun z => mul_pos (hpX z.1) (hpY z.2)) hsum ?_
  calc ∑ z : ι × κ, pX z.1 * pY z.2
      = ∑ i, ∑ j, pX i * pY j := Fintype.sum_prod_type _
    _ = (∑ i, pX i) * ∑ j, pY j := (Fintype.sum_mul_sum pX pY).symm
    _ = 1 := by rw [hXsum, hYsum, mul_one]

/-- **[Relative entropy is additive over independent systems]** `D(p₁⊗p₂ ‖ q₁⊗q₂) = D(p₁‖q₁) + D(p₂‖q₂)`:
the relative entropy of product distributions tensorizes. This additivity is what makes `D` an extensive
"statistical distance" and underlies the independence structure of the entropic action. -/
theorem klDivergence_prod {κ : Type*} [Fintype κ]
    (p₁ q₁ : ι → ℝ) (p₂ q₂ : κ → ℝ)
    (hp₁ : ∀ i, 0 < p₁ i) (hq₁ : ∀ i, 0 < q₁ i) (hp₂ : ∀ j, 0 < p₂ j) (hq₂ : ∀ j, 0 < q₂ j)
    (hp₁s : ∑ i, p₁ i = 1) (hp₂s : ∑ j, p₂ j = 1) :
    klDivergence (fun z : ι × κ => p₁ z.1 * p₂ z.2) (fun z => q₁ z.1 * q₂ z.2)
      = klDivergence p₁ q₁ + klDivergence p₂ q₂ := by
  have key : ∀ z : ι × κ, p₁ z.1 * p₂ z.2 * Real.log (p₁ z.1 * p₂ z.2 / (q₁ z.1 * q₂ z.2))
      = p₁ z.1 * Real.log (p₁ z.1 / q₁ z.1) * p₂ z.2
        + p₁ z.1 * (p₂ z.2 * Real.log (p₂ z.2 / q₂ z.2)) := by
    intro z
    have a1 := hp₁ z.1; have a2 := hp₂ z.2; have b1 := hq₁ z.1; have b2 := hq₂ z.2
    have e1 : Real.log (p₁ z.1 * p₂ z.2 / (q₁ z.1 * q₂ z.2))
        = Real.log (p₁ z.1 / q₁ z.1) + Real.log (p₂ z.2 / q₂ z.2) := by
      rw [Real.log_div (ne_of_gt (mul_pos a1 a2)) (ne_of_gt (mul_pos b1 b2)),
          Real.log_mul (ne_of_gt a1) (ne_of_gt a2), Real.log_mul (ne_of_gt b1) (ne_of_gt b2),
          Real.log_div (ne_of_gt a1) (ne_of_gt b1), Real.log_div (ne_of_gt a2) (ne_of_gt b2)]
      ring
    rw [e1]; ring
  simp only [klDivergence]
  rw [Finset.sum_congr rfl (fun z _ => key z), Finset.sum_add_distrib]
  congr 1
  · rw [Fintype.sum_prod_type,
      ← Fintype.sum_mul_sum (fun i => p₁ i * Real.log (p₁ i / q₁ i)) p₂, hp₂s, mul_one]
  · rw [Fintype.sum_prod_type,
      ← Fintype.sum_mul_sum p₁ (fun j => p₂ j * Real.log (p₂ j / q₂ j)), hp₁s, one_mul]

/-- The **Jensen–Shannon divergence** `JSD(p,q) = ½D(p‖m) + ½D(q‖m)` with midpoint `m = (p+q)/2` — the
symmetrized, always-finite variant of the relative entropy. -/
noncomputable def jsDivergence (p q : ι → ℝ) : ℝ :=
  (klDivergence p (fun i => (p i + q i) / 2) + klDivergence q (fun i => (p i + q i) / 2)) / 2

/-- **[Jensen–Shannon divergence ≥ 0]** the symmetric divergence is nonnegative, being a convex
combination of two nonnegative relative entropies (`klDivergence_nonneg`). -/
theorem jsDivergence_nonneg (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpos : ∀ i, 0 < p i + q i) (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    0 ≤ jsDivergence p q := by
  have hm : ∀ i, 0 < (p i + q i) / 2 := fun i => div_pos (hpos i) two_pos
  have hmsum : ∑ i, (p i + q i) / 2 = 1 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hps, hqs]; norm_num
  have h1 := klDivergence_nonneg p _ hp hm hps hmsum
  have h2 := klDivergence_nonneg q _ hq hm hqs hmsum
  rw [jsDivergence]; linarith

/-- The **entropy** `H(p) = −Σ pᵢ log pᵢ`. -/
noncomputable def entropy (p : ι → ℝ) : ℝ := -∑ i, p i * Real.log (p i)

/-- The **cross-entropy** `H(p,q) = −Σ pᵢ log qᵢ`. -/
noncomputable def crossEntropy (p q : ι → ℝ) : ℝ := -∑ i, p i * Real.log (q i)

/-- **[Cross-entropy minus entropy is the relative entropy]** `H(p,q) − H(p) = D(p‖q)`. -/
lemma crossEntropy_sub_entropy (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) :
    crossEntropy p q - entropy p = klDivergence p q := by
  have hterm : ∀ i, p i * Real.log (p i) - p i * Real.log (q i) = p i * Real.log (p i / q i) := by
    intro i
    rcases (hp i).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [Real.log_div (ne_of_gt h) (ne_of_gt (hq i))]; ring
  rw [crossEntropy, entropy, klDivergence, sub_neg_eq_add, neg_add_eq_sub,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => hterm i)

/-- **[Cross-entropy ≥ entropy (Gibbs' inequality, coding form)]** `H(p,q) ≥ H(p)`: the expected code
length under a wrong distribution `q` never beats the entropy, with equality iff `q = p`. -/
theorem entropy_le_crossEntropy (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) : entropy p ≤ crossEntropy p q := by
  have h := klDivergence_nonneg p q hp hq hps hqs
  have hid := crossEntropy_sub_entropy p q hp hq
  linarith

/-- The `X`-marginal `p_X(i) = Σⱼ p_XY(i,j)` of a joint distribution. -/
noncomputable def marginalFst {κ : Type*} [Fintype κ] (pXY : ι × κ → ℝ) (i : ι) : ℝ :=
  ∑ j, pXY (i, j)

/-- The `Y`-marginal `p_Y(j) = Σᵢ p_XY(i,j)`. -/
noncomputable def marginalSnd {κ : Type*} [Fintype κ] (pXY : ι × κ → ℝ) (j : κ) : ℝ :=
  ∑ i, pXY (i, j)

lemma sum_pXY_log_marginalFst {κ : Type*} [Fintype κ] (pXY : ι × κ → ℝ) :
    ∑ z, pXY z * Real.log (marginalFst pXY z.1)
      = ∑ i, marginalFst pXY i * Real.log (marginalFst pXY i) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [marginalFst, Finset.sum_mul]

lemma sum_pXY_log_marginalSnd {κ : Type*} [Fintype κ] (pXY : ι × κ → ℝ) :
    ∑ z, pXY z * Real.log (marginalSnd pXY z.2)
      = ∑ j, marginalSnd pXY j * Real.log (marginalSnd pXY j) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [marginalSnd, Finset.sum_mul]

/-- **[Mutual information as an entropy difference]** `I(X;Y) = H(X) + H(Y) − H(X,Y)`: the relative
entropy of the joint from the product of its marginals equals the entropy defect. -/
lemma mutualInfo_eq_entropies {κ : Type*} [Fintype κ] (pXY : ι × κ → ℝ)
    (hpXY : ∀ z, 0 < pXY z) (hmX : ∀ i, 0 < marginalFst pXY i) (hmY : ∀ j, 0 < marginalSnd pXY j) :
    klDivergence pXY (fun z => marginalFst pXY z.1 * marginalSnd pXY z.2)
      = entropy (marginalFst pXY) + entropy (marginalSnd pXY) - entropy pXY := by
  have key : ∀ z : ι × κ, pXY z * Real.log (pXY z / (marginalFst pXY z.1 * marginalSnd pXY z.2))
      = pXY z * Real.log (pXY z) - pXY z * Real.log (marginalFst pXY z.1)
        - pXY z * Real.log (marginalSnd pXY z.2) := by
    intro z
    rw [Real.log_div (ne_of_gt (hpXY z)) (ne_of_gt (mul_pos (hmX z.1) (hmY z.2))),
      Real.log_mul (ne_of_gt (hmX z.1)) (ne_of_gt (hmY z.2))]
    ring
  simp only [klDivergence, entropy]
  rw [Finset.sum_congr rfl (fun z _ => key z), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_pXY_log_marginalFst, sum_pXY_log_marginalSnd]
  ring

/-- **[Entropy subadditivity]** `H(X,Y) ≤ H(X) + H(Y)`: the joint entropy never exceeds the sum of the
marginal entropies, with equality iff `X, Y` are independent. The entropy form of mutual-information
nonnegativity (`mutualInformation_nonneg`), obtained from `I(X;Y) = H(X)+H(Y)−H(X,Y) ≥ 0`. -/
theorem entropy_subadditive {κ : Type*} [Fintype κ] [Nonempty ι] [Nonempty κ]
    (pXY : ι × κ → ℝ) (hpXY : ∀ z, 0 < pXY z) (hsum : ∑ z, pXY z = 1) :
    entropy pXY ≤ entropy (marginalFst pXY) + entropy (marginalSnd pXY) := by
  have hmX : ∀ i, 0 < marginalFst pXY i :=
    fun i => Finset.sum_pos (fun j _ => hpXY (i, j)) Finset.univ_nonempty
  have hmY : ∀ j, 0 < marginalSnd pXY j :=
    fun j => Finset.sum_pos (fun i _ => hpXY (i, j)) Finset.univ_nonempty
  have hXs : ∑ i, marginalFst pXY i = 1 := by
    simp only [marginalFst]; rw [← Fintype.sum_prod_type]; exact hsum
  have hYs : ∑ j, marginalSnd pXY j = 1 := by
    simp only [marginalSnd]; rw [Finset.sum_comm, ← Fintype.sum_prod_type]; exact hsum
  have hprodsum : ∑ z : ι × κ, marginalFst pXY z.1 * marginalSnd pXY z.2 = 1 := by
    rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum (marginalFst pXY) (marginalSnd pXY),
      hXs, hYs, mul_one]
  have hkl := klDivergence_nonneg pXY (fun z => marginalFst pXY z.1 * marginalSnd pXY z.2)
    (fun z => (hpXY z).le) (fun z => mul_pos (hmX z.1) (hmY z.2)) hsum hprodsum
  rw [mutualInfo_eq_entropies pXY hpXY hmX hmY] at hkl
  linarith

/-! ### §C — the free-energy variational principle -/

/-- The canonical (Gibbs) distribution `πᵢ = e^{−βEᵢ}/Z`. -/
noncomputable def gibbsState (β Z : ℝ) (E : ι → ℝ) (i : ι) : ℝ := Real.exp (-β * E i) / Z

/-- The **Helmholtz free energy** `F[p] = ⟨E⟩_p − T·S[p] = Σ pᵢEᵢ + (1/β) Σ pᵢ log pᵢ` at `T = 1/β`
(with `S[p] = −Σ pᵢ log pᵢ`). -/
noncomputable def freeEnergy (β : ℝ) (E p : ι → ℝ) : ℝ :=
  (∑ i, p i * E i) + (1 / β) * ∑ i, p i * Real.log (p i)

/-- **[Free energy is `T·D(p‖π) − T log Z`]** the free energy of any distribution equals the temperature
times its relative entropy from the Gibbs state, shifted by `−T log Z`. -/
lemma freeEnergy_sub_eq_kl (β Z : ℝ) (E p : ι → ℝ) (hβ : β ≠ 0) (hZ : 0 < Z)
    (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1) :
    (1 / β) * klDivergence p (gibbsState β Z E) = freeEnergy β E p + (1 / β) * Real.log Z := by
  have hterm : ∀ i, p i * Real.log (p i / gibbsState β Z E i)
      = p i * Real.log (p i) + β * (p i * E i) + p i * Real.log Z := by
    intro i
    rcases (hp i).eq_or_lt with h | h
    · rw [← h]; ring
    · rw [gibbsState, Real.log_div (ne_of_gt h) (by positivity),
        Real.log_div (Real.exp_ne_zero _) (ne_of_gt hZ), Real.log_exp]
      ring
  rw [klDivergence, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hps, one_mul, freeEnergy]
  field_simp
  ring

/-- **[Second law / free-energy variational principle]** `F[π] ≤ F[p]`: the canonical Gibbs state
minimizes the Helmholtz free energy over all probability distributions, with gap `T·D(p‖π) ≥ 0`. -/
theorem freeEnergy_gibbs_le (β Z : ℝ) (E p : ι → ℝ) (hβ : 0 < β) (hZ : 0 < Z)
    (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1)
    (hπnn : ∀ i, 0 ≤ gibbsState β Z E i) (hπpos : ∀ i, 0 < gibbsState β Z E i)
    (hπs : ∑ i, gibbsState β Z E i = 1) :
    freeEnergy β E (gibbsState β Z E) ≤ freeEnergy β E p := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hp_eq := freeEnergy_sub_eq_kl β Z E p hβne hZ hp hps
  have hπ_eq := freeEnergy_sub_eq_kl β Z E (gibbsState β Z E) hβne hZ hπnn hπs
  rw [klDivergence_self] at hπ_eq
  have hkl : 0 ≤ klDivergence p (gibbsState β Z E) :=
    klDivergence_nonneg p (gibbsState β Z E) hp hπpos hps hπs
  have hinv : 0 < 1 / β := by positivity
  nlinarith [hp_eq, hπ_eq, mul_nonneg hinv.le hkl]

/-- **[Free energy as `⟨E⟩ − T·S`]** `F[p] = Σ pᵢEᵢ − (1/β)·H(p)` — the Helmholtz form with `T = 1/β`
and `H = entropy`. -/
lemma freeEnergy_eq_energy_sub_entropy (β : ℝ) (E p : ι → ℝ) :
    freeEnergy β E p = (∑ i, p i * E i) - (1 / β) * entropy p := by
  rw [freeEnergy, entropy]; ring

/-- **[Maximum-entropy principle (Jaynes / Gibbs)]** among all distributions with the same mean energy
`⟨E⟩` as the canonical state `πᵢ = e^{−βEᵢ}/Z`, the canonical state has the **greatest entropy**,
`H(p) ≤ H(π)`. The thermodynamic dual of `freeEnergy_gibbs_le`, and the variational foundation of
maximum-entropy inference (Caticha) and equilibrium statistical mechanics. -/
theorem gibbs_maximizes_entropy (β Z : ℝ) (E p : ι → ℝ) (hβ : 0 < β) (hZ : 0 < Z)
    (hp : ∀ i, 0 ≤ p i) (hps : ∑ i, p i = 1)
    (hπnn : ∀ i, 0 ≤ gibbsState β Z E i) (hπpos : ∀ i, 0 < gibbsState β Z E i)
    (hπs : ∑ i, gibbsState β Z E i = 1)
    (henergy : ∑ i, p i * E i = ∑ i, gibbsState β Z E i * E i) :
    entropy p ≤ entropy (gibbsState β Z E) := by
  have hfe := freeEnergy_gibbs_le β Z E p hβ hZ hp hps hπnn hπpos hπs
  rw [freeEnergy_eq_energy_sub_entropy, freeEnergy_eq_energy_sub_entropy, henergy] at hfe
  have hinv : (0 : ℝ) < 1 / β := by positivity
  have key : (1 / β) * entropy p ≤ (1 / β) * entropy (gibbsState β Z E) := by linarith
  exact le_of_mul_le_mul_left key hinv

/-! ### §D — the infinite (continuum) index

The Gibbs inequality is not tied to a finite alphabet: the same pointwise bound (`pointwise_gibbs`) sums
over an *arbitrary* index type through the unordered `tsum`, so it holds for a countably-infinite (or any
summable) distribution — the infinite-dimensional / continuum-of-states generalization of `§B`. -/

section Continuum

variable {J : Type*}

/-- The relative entropy `D(p‖q) = Σ' pᵢ log(pᵢ/qᵢ)` over an **arbitrary** index type, via the unordered
sum `tsum` (agreeing with `klDivergence` when the index is finite). -/
noncomputable def klDivergenceTsum (p q : J → ℝ) : ℝ := ∑' i, p i * Real.log (p i / q i)

/-- **[Gibbs inequality on an infinite index]** `D(p‖q) ≥ 0` for summable probability distributions over
an arbitrary (in particular infinite) index type — the continuum generalization of `klDivergence_nonneg`,
proved from the same pointwise bound `pointwise_gibbs` summed through `tsum`. -/
theorem klDivergenceTsum_nonneg (p q : J → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hpsum : Summable p) (hqsum : Summable q)
    (hklsum : Summable fun i => p i * Real.log (p i / q i))
    (hps : ∑' i, p i = 1) (hqs : ∑' i, q i = 1) : 0 ≤ klDivergenceTsum p q := by
  have hle : ∑' i, (p i - q i) ≤ ∑' i, p i * Real.log (p i / q i) :=
    Summable.tsum_le_tsum (fun i => pointwise_gibbs (hp i) (hq i)) (hpsum.sub hqsum) hklsum
  have hz : ∑' i, (p i - q i) = 0 := by rw [Summable.tsum_sub hpsum hqsum, hps, hqs, sub_self]
  rw [klDivergenceTsum]; linarith [hle, hz]

end Continuum

/- ZIL-BEGIN -/

zil attach pointwise_gibbs where
  formalizes @ "claim:pointwise-gibbs-bound-a-minus-b-le-a-log-a-over-b-from-log-convexity",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Real.log_le_sub_one_of_pos",
  caveat @ "claim:scalar-convexity-bound-only-becomes-relative-entropy-nonnegativity-after-summation"

zil attach klDivergence_nonneg where
  formalizes @ "claim:discrete-relative-entropy-is-nonnegative-gibbs-inequality-second-law-master-bound",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:kullback-leibler-1951-on-information-and-sufficiency",
  caveat @ "claim:classical-diagonal-relative-entropy-over-a-fintype-not-the-operator-araki-or-type-iii-monotonicity"

zil attach klDivergence_self where
  supported_by @ "lean:HermitianMat.log_one",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:discrete-relative-entropy-vanishes-when-the-two-input-functions-coincide",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-direction-alone-is-not-uniqueness-the-full-support-converse-is-klDivergence_eq_zero_iff"

zil attach klDivergence_eq_zero_iff where
  formalizes @ "claim:full-support-discrete-relative-entropy-vanishes-if-and-only-if-the-two-probability-distributions-coincide",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.eq_of_pointwise_gibbs_eq",
  caveat @ "claim:requires-strictly-positive-finite-probability-distributions-not-the-general-measure-theoretic-equality-case"

zil attach freeEnergy_sub_eq_kl where
  supported_by @ "lean:HermitianMat.log_exp",
  supported_by @ "lean:KroneckerDelta.sum_mul",
  formalizes @ "claim:helmholtz-free-energy-equals-temperature-times-relative-entropy-from-gibbs-state-minus-t-log-z",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:finite-canonical-ensemble-identity-not-a-continuum-field-free-energy"

zil attach freeEnergy_gibbs_le where
  formalizes @ "claim:canonical-gibbs-state-minimizes-helmholtz-free-energy-second-law-variational-principle",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence_nonneg",
  caveat @ "claim:classical-diagonal-free-energy-not-the-operator-gibbs-variational-principle"

zil attach gibbs_maximizes_entropy where
  formalizes @ "claim:gibbs-canonical-distribution-maximizes-entropy-at-fixed-mean-energy-jaynes-maxent-principle",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:jaynes-1957-information-theory-and-statistical-mechanics",
  requires @ "claim:canonical-gibbs-state-minimizes-helmholtz-free-energy-second-law-variational-principle",
  caveat @ "claim:fixed-energy-classical-maxent-not-the-full-caticha-entropic-dynamics-derivation-of-quantum-mechanics"

zil attach mutualInformation_nonneg where
  formalizes @ "claim:mutual-information-nonnegative-relative-entropy-of-joint-from-product-of-marginals-ge-zero",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence_nonneg",
  caveat @ "claim:supplies-the-missing-inequality-for-finiteMutualInformation-in-thermodynamics-kullbackleiblerinformationgain-classical-not-quantum-mutual-information"

zil attach mutualInfo_eq_entropies where
  supported_by @ "lean:mutualInformation_nonneg",
  formalizes @ "claim:mutual-information-equals-entropy-defect-i-xy-equals-h-x-plus-h-y-minus-h-xy",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:discrete-shannon-entropy-identity-requires-strictly-positive-joint-not-the-von-neumann-analogue"

zil attach entropy_subadditive where
  supported_by @ "lean:klDivergence_nonneg",
  supported_by @ "lean:mutualInfo_eq_entropies",
  formalizes @ "claim:joint-shannon-entropy-subadditive-h-xy-le-h-x-plus-h-y-equality-iff-independent",
  epistemic_status @ "consistency-identity",
  requires @ "claim:mutual-information-equals-entropy-defect-i-xy-equals-h-x-plus-h-y-minus-h-xy",
  caveat @ "claim:classical-discrete-subadditivity-not-the-quantum-von-neumann-strong-subadditivity"

zil attach klDivergence_prod where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:relative-entropy-tensorizes-additive-over-independent-product-distributions",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:classical-product-distributions-not-the-operator-tensor-product-of-states"

zil attach jsDivergence_nonneg where
  supported_by @ "lean:klDivergence_nonneg",
  formalizes @ "claim:jensen-shannon-divergence-nonnegative-symmetrized-relative-entropy",
  epistemic_status @ "consistency-identity",
  requires @ "claim:discrete-relative-entropy-is-nonnegative-gibbs-inequality-second-law-master-bound",
  caveat @ "claim:nonnegativity-only-log-two-boundedness-and-metric-property-of-its-square-root-not-formalized-here"

zil attach entropy_le_crossEntropy where
  formalizes @ "claim:cross-entropy-at-least-entropy-gibbs-inequality-source-coding-form",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence_nonneg",
  caveat @ "claim:expected-code-length-bound-classical-not-quantum"

zil attach klDivergenceTsum_nonneg where
  supported_by @ "lean:pointwise_gibbs",
  formalizes @ "claim:gibbs-inequality-on-an-arbitrary-summable-infinite-continuum-of-states-index",
  epistemic_status @ "consistency-identity",
  requires @ "claim:pointwise-gibbs-bound-a-minus-b-le-a-log-a-over-b-from-log-convexity",
  caveat @ "claim:requires-summability-of-the-kl-summand-as-a-hypothesis-not-a-measure-theoretic-integral-relative-entropy"

zil_file_contract physlib.relativeEntropyGibbsInequality where
  promises "The discrete relative-entropy layer of the entropic-time program. The Gibbs inequality D(p‖q) ≥ 0 (klDivergence_nonneg), its full-support equality case (klDivergence_eq_zero_iff), the free-energy variational principle, Jaynes maximum entropy, standard finite information inequalities, and the summable-index extension are proved from the shared pointwise Gibbs bound. The results concern classical finite or summable distributions, not operator-algebraic relative entropy."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.entropy",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.gibbsState"]
  forbids_substitutes ["any operator-level, Araki, or Type-III von Neumann relative entropy -- everything here is the classical diagonal relative entropy over a Fintype",
    "any quantum von Neumann entropy or strong subadditivity -- the subadditivity proved here is classical Shannon subadditivity",
    "any measure-theoretic or field-theoretic integral relative entropy -- the infinite case uses tsum with an explicit summability hypothesis"]
  witnessed_by [pointwise_gibbs, klDivergence_nonneg, klDivergence_self,
    eq_of_pointwise_gibbs_eq, klDivergence_eq_zero_iff,
    freeEnergy_sub_eq_kl, freeEnergy_gibbs_le, gibbs_maximizes_entropy,
    mutualInformation_nonneg, mutualInfo_eq_entropies, entropy_subadditive,
    klDivergence_prod, jsDivergence_nonneg, entropy_le_crossEntropy,
    klDivergenceTsum_nonneg]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality
