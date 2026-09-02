/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# `Lᵖ` convergence from a uniform bound, and `Lᵖ` ⟹ a.e.-convergent subsequence

Two Mathlib-backed measure-theory lemmas, re-authored generically from the
`NavierStokesClean/Galerkin/{AubinLionsSimon,AubinLionsCompact}` reference tree (where they appear
specialised to `NSField = EuclideanSpace ℝ (Fin 3)` on `volume.restrict (Ioc 0 T)` and dressed with
Navier–Stokes trajectory hypotheses). Both are the pure analytic content and generalise verbatim to an
arbitrary normed space over a general measure:

* `eLpNorm_tendsto_zero_of_aeBound` — a **Vitali / dominated-convergence** bridge: on a *finite* measure,
  if `fₙ → g` a.e. and the `fₙ` are uniformly a.e. norm-bounded (`‖fₙ‖ ≤ C`), with `g ∈ Lᵖ`, then
  `‖fₙ − g‖_{Lᵖ} → 0`. The uniform bound gives uniform integrability for free (the high-norm indicator is
  a.e. zero), and Mathlib's `tendsto_Lp_finite_of_tendsto_ae` finishes.
* `ae_subseq_of_eLpNorm_tendsto` — the **converse extraction**: `‖fₙ − g‖_{Lᵖ} → 0` yields a subsequence
  converging a.e., via convergence in measure (`tendstoInMeasure_of_tendsto_eLpNorm`) and the
  Borel–Cantelli a.e.-subsequence (`TendstoInMeasure.exists_seq_tendsto_ae`).

Together they are the `a.e. ⟺ Lᵖ` interchange at the heart of the Aubin–Lions–Simon compactness argument for
Galerkin approximations of Navier–Stokes, but stated as reusable measure theory.

## References

* J. Simon, *Compact sets in the space `Lᵖ(0,T;B)`*, Ann. Mat. Pura Appl. 146 (1987) 65. Carriers:
  Mathlib `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`, `MeasureTheory.unifIntegrable_of'`,
  `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`,
  `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal NNReal

@[expose] public section

namespace Physlib.Mathematics.LpAeConvergence

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E]

/-- **[Vitali / dominated convergence in `Lᵖ`] a.e. convergence + a uniform norm bound ⟹ `Lᵖ`
convergence.** On a finite measure `μ`, if the strongly measurable `fₙ` are uniformly a.e. norm-bounded by a
constant `C`, converge a.e. to `g`, and `g ∈ Lᵖ` (`1 ≤ p < ∞`), then `‖fₙ − g‖_{Lᵖ} → 0`. The uniform bound
makes the sequence uniformly integrable (the indicator of `{‖fₙ‖ ≥ C+1}` is a.e. zero), so
`tendsto_Lp_finite_of_tendsto_ae` applies. -/
theorem eLpNorm_tendsto_zero_of_aeBound [IsFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → E} {g : α → E} {C : ℝ}
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : MemLp g p μ)
    (hbound : ∀ n, ∀ᵐ t ∂μ, ‖f n t‖ ≤ C)
    (hae : ∀ᵐ t ∂μ, Tendsto (fun n => f n t) atTop (nhds (g t))) :
    Tendsto (fun n => eLpNorm (fun t => f n t - g t) p μ) atTop (nhds 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hUI : UnifIntegrable f p μ := by
    refine unifIntegrable_of' hp hp' hf (fun ε _hε => ?_)
    refine ⟨(max C 0 + 1).toNNReal, by rw [Real.toNNReal_pos]; positivity, fun n => ?_⟩
    have hms : MeasurableSet {x : α | (max C 0 + 1).toNNReal ≤ ‖f n x‖₊} :=
      measurableSet_le measurable_const (hf n).nnnorm.measurable
    have hzero : eLpNorm ({x | (max C 0 + 1).toNNReal ≤ ‖f n x‖₊}.indicator (f n)) p μ = 0 := by
      rw [eLpNorm_eq_zero_iff (((hf n).indicator hms).aestronglyMeasurable) hp0]
      filter_upwards [hbound n] with t ht
      apply Set.indicator_of_notMem
      simp only [Set.mem_setOf_eq, not_le]
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by positivity)]
      exact (ht.trans (le_max_left C 0)).trans_lt (lt_add_one _)
    rw [hzero]; exact zero_le
  exact tendsto_Lp_finite_of_tendsto_ae hp hp'
    (fun n => (hf n).aestronglyMeasurable) hg hUI hae

/-- **[`Lᵖ` convergence ⟹ a.e.-convergent subsequence].** For any measure `μ` and normed space `E` (with the
Borel structure), if `‖fₙ − g‖_{Lᵖ} → 0` (`p ≠ 0`) with `fₙ`, `g` a.e. strongly measurable, then there is a
strictly monotone `φ` with `f (φ n) t → g t` for `μ`-a.e. `t`. The composition of
`tendstoInMeasure_of_tendsto_eLpNorm` (`Lᵖ` ⟹ in measure) with the Borel–Cantelli extraction
`TendstoInMeasure.exists_seq_tendsto_ae`. -/
theorem ae_subseq_of_eLpNorm_tendsto [MeasurableSpace E] [BorelSpace E]
    {p : ℝ≥0∞} (hp : p ≠ 0)
    {f : ℕ → α → E} {g : α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hfg : Tendsto (fun n => eLpNorm (fun t => f n t - g t) p μ) atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ t ∂μ, Tendsto (fun n => f (φ n) t) atTop (nhds (g t)) :=
  (tendstoInMeasure_of_tendsto_eLpNorm hp hf hg hfg).exists_seq_tendsto_ae

/-! ### Borel–Cantelli at geometric rates — the Stein–Nikishin / maximal-estimate engine

The "standard argument" reducing pointwise convergence to a maximal estimate (Stein–Nikishin; Hickman,
arXiv:2304.02507, Cor. 3.2): if the maximal functions of the dyadic differences have `L²` norms decaying
like `4⁻ᵏ`, then Chebyshev gives `μ{2⁻ᵏ ≤ ‖gₖ‖ₑ} ≤ 4⁻ᵏ`, Borel–Cantelli makes the exceptional set null, and
almost every point has an eventually-geometric — hence summable — sequence of maximal values. -/

/-- **[Chebyshev + Borel–Cantelli at geometric rates]** if `‖gₖ‖_{L²(μ)} ≤ 4⁻ᵏ` then almost everywhere,
eventually in `k`, `‖gₖ x‖ₑ < 2⁻ᵏ`. -/
theorem ae_eventually_enorm_lt_of_eLpNorm_le_geometric
    {g : ℕ → α → E} (hg : ∀ k, AEStronglyMeasurable (g k) μ)
    (hbound : ∀ k, eLpNorm (g k) 2 μ ≤ (4⁻¹ : ℝ≥0∞) ^ k) :
    ∀ᵐ x ∂μ, ∀ᶠ k in atTop, ‖g k x‖ₑ < (2⁻¹ : ℝ≥0∞) ^ k := by
  have h2ne : ((2 : ℝ≥0∞))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by norm_num)
  have h2top : ((2 : ℝ≥0∞))⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (by norm_num)
  have hcheb : ∀ k, μ {x | (2⁻¹ : ℝ≥0∞) ^ k ≤ ‖g k x‖ₑ} ≤ (4⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    have hε0 : ((2⁻¹ : ℝ≥0∞)) ^ k ≠ 0 := pow_ne_zero k h2ne
    have hεtop : ((2⁻¹ : ℝ≥0∞)) ^ k ≠ ∞ := ENNReal.pow_ne_top h2top
    have h := meas_ge_le_mul_pow_eLpNorm_enorm (μ := μ) (p := 2)
      two_ne_zero (by norm_num) (hg k) hε0 (fun h => absurd h hεtop)
    refine h.trans ?_
    have htr : ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) := by norm_num
    rw [htr, ENNReal.rpow_natCast, ENNReal.rpow_natCast, ENNReal.inv_pow, inv_inv]
    calc ((2 : ℝ≥0∞) ^ k) ^ (2 : ℕ) * eLpNorm (g k) 2 μ ^ (2 : ℕ)
        ≤ ((2 : ℝ≥0∞) ^ k) ^ (2 : ℕ) * ((4⁻¹ : ℝ≥0∞) ^ k) ^ (2 : ℕ) := by
          gcongr
          exact hbound k
      _ = ((2 : ℝ≥0∞) ^ (2 : ℕ) * ((4⁻¹ : ℝ≥0∞)) ^ (2 : ℕ)) ^ k := by
          rw [pow_right_comm, pow_right_comm (4⁻¹ : ℝ≥0∞), ← mul_pow]
      _ = (4⁻¹ : ℝ≥0∞) ^ k := by
          congr 1
          rw [← ENNReal.inv_pow, show ((4 : ℝ≥0∞)) ^ (2 : ℕ) = 16 from by norm_num,
            show ((2 : ℝ≥0∞)) ^ (2 : ℕ) = 4 from by norm_num,
            show (16 : ℝ≥0∞) = 4 * 4 from by norm_num,
            ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have htsum : (∑' k, μ {x | (2⁻¹ : ℝ≥0∞) ^ k ≤ ‖g k x‖ₑ}) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hcheb)
    rw [ENNReal.tsum_geometric]
    refine ENNReal.inv_ne_top.mpr ?_
    rw [ne_eq, tsub_eq_zero_iff_le, not_le]
    exact ENNReal.inv_lt_one.mpr (by norm_num)
  filter_upwards [ae_eventually_notMem htsum] with x hx
  filter_upwards [hx] with k hk
  simpa [not_le] using hk

/-- **[a.e. summable maximal values]** if `‖gₖ‖_{L²(μ)} ≤ 4⁻ᵏ` then at almost every point the sequence
`k ↦ ‖gₖ x‖` is summable — the a.e. convergence engine behind the reduction of pointwise convergence to a
maximal estimate. -/
theorem ae_summable_norm_of_eLpNorm_le_geometric
    {g : ℕ → α → E} (hg : ∀ k, AEStronglyMeasurable (g k) μ)
    (hbound : ∀ k, eLpNorm (g k) 2 μ ≤ (4⁻¹ : ℝ≥0∞) ^ k) :
    ∀ᵐ x ∂μ, Summable (fun k => ‖g k x‖) := by
  filter_upwards [ae_eventually_enorm_lt_of_eLpNorm_le_geometric hg hbound] with x hx
  have hgeom : Summable (fun k : ℕ => ((2 : ℝ))⁻¹ ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine hgeom.of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hx] with k hk
  have hofReal : (2⁻¹ : ℝ≥0∞) ^ k = ENNReal.ofReal (((2 : ℝ))⁻¹ ^ k) := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    congr 1
    rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [hofReal, ← ofReal_norm_eq_enorm] at hk
  have hlt := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).mp hk
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact hlt.le

end Physlib.Mathematics.LpAeConvergence

end
