/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.LeftRiemannSum
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Convergence of the fixed-step left Riemann kernel

The repository's discrete integration kernel is

`leftRiemannSum N f T = ∑_{i < floor(TN)} f(i/N) / N`.

For a nonnegative function that is non-increasing on `[0,T]`, this module
compares the sum with the interval integral on the covered stepped span. The
upper and lower Darboux estimates, together with the uncovered terminal
interval of length less than `1/N`, give the quantitative error bound

`|leftRiemannSum N f T - ∫₀ᵀ f| ≤ f(0)/N`.

Consequently the fixed-step kernel converges to Mathlib's interval integral as
`N → ∞`. This is the analytic bridge intentionally left open in
`LeftRiemannSum.lean`.

The theorem is specialized to nonnegative antitone functions because this is
the exact structure required by the repository's dissipative Fourier
trajectories. It is not asserted here for arbitrary discontinuous or
oscillatory integrands.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter Finset Set MeasureTheory Topology

namespace Physlib.Mathematics.LeftRiemannSum

/-! ## A. The terminal uncovered interval -/

/-- The interval between the stepped span `floor(TN)/N` and `T` has length
strictly less than one step. -/
lemma horizon_sub_span_lt_step (N : ℕ) (hN : 0 < N) (T : ℝ) :
    T - (stepCount N T : ℝ) * step N < step N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfloor : T * N < (stepCount N T : ℝ) + 1 := by
    exact Nat.lt_floor_add_one _
  have hscaled :
      T < ((stepCount N T : ℝ) + 1) / N := by
    rw [lt_div_iff₀ hNr]
    simpa [mul_comm] using hfloor
  unfold step
  rw [div_eq_mul_inv] at hscaled ⊢
  linarith

private lemma scaled_antitone
    (N : ℕ) (hN : 0 < N) (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hf : AntitoneOn f (Icc 0 T)) :
    AntitoneOn
      (fun x => step N * f (x * step N))
      (Icc 0 (stepCount N T : ℝ)) := by
  intro x hx y hy hxy
  have hs : 0 ≤ (step N : ℝ) := step_nonneg N hN
  apply mul_le_mul_of_nonneg_left _ hs
  apply hf
  · exact ⟨mul_nonneg hx.1 hs,
      (mul_le_mul_of_nonneg_right hx.2 hs).trans
        (span_le_horizon N hN hT)⟩
  · exact ⟨mul_nonneg hy.1 hs,
      (mul_le_mul_of_nonneg_right hy.2 hs).trans
        (span_le_horizon N hN hT)⟩
  · exact mul_le_mul_of_nonneg_right hxy hs

/-! ## B. Darboux comparison on the stepped span -/

/-- For a non-increasing integrand, the left sum is an upper Darboux sum on
the span that it covers. -/
lemma integral_to_span_le_leftRiemannSum
    (N : ℕ) (hN : 0 < N) (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hf : AntitoneOn f (Icc 0 T)) :
    (∫ t in 0..(stepCount N T : ℝ) * step N, f t) ≤
      leftRiemannSum N f T := by
  have hg := scaled_antitone N hN f hT hf
  have hg' : AntitoneOn
      (fun x => step N * f (x * step N))
      (Icc 0 (0 + (stepCount N T : ℝ))) := by
    simpa using hg
  have h := AntitoneOn.integral_le_sum
    (x₀ := 0) (a := stepCount N T) hg'
  simp only [zero_add] at h
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.mul_integral_comp_mul_right] at h
  simpa [leftRiemannSum, mul_comm, mul_left_comm, mul_assoc] using h

/-- The left sum exceeds the integral over its stepped span by at most the
first rectangle `f(0)/N`. -/
lemma leftRiemannSum_le_integral_to_span_add
    (N : ℕ) (hN : 0 < N) (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hf : AntitoneOn f (Icc 0 T)) (hnonneg : ∀ x ∈ Icc 0 T, 0 ≤ f x) :
    leftRiemannSum N f T ≤
      (∫ t in 0..(stepCount N T : ℝ) * step N, f t) +
        step N * f 0 := by
  let g : ℝ → ℝ := fun x => step N * f (x * step N)
  have hg := scaled_antitone N hN f hT hf
  have hg' : AntitoneOn g (Icc 0 (0 + (stepCount N T : ℝ))) := by
    simpa [g] using hg
  have hright := AntitoneOn.sum_le_integral
    (x₀ := 0) (a := stepCount N T) hg'
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at hright
  have hgm : 0 ≤ g (stepCount N T) := by
    apply mul_nonneg (step_nonneg N hN)
    apply hnonneg
    exact ⟨mul_nonneg (Nat.cast_nonneg _) (step_nonneg N hN),
      span_le_horizon N hN hT⟩
  have hshift :
      (∑ i ∈ range (stepCount N T), g i) + g (stepCount N T) =
        g 0 + ∑ i ∈ range (stepCount N T), g (i + 1) := by
    calc
      (∑ i ∈ range (stepCount N T), g i) + g (stepCount N T) =
          ∑ i ∈ range (stepCount N T + 1), g i := by
            rw [sum_range_succ]
      _ = g 0 + ∑ i ∈ range (stepCount N T), g (i + 1) := by
            rw [sum_range_succ']
            simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
            ac_rfl
  have hsum :
      (∑ i ∈ range (stepCount N T), g i) ≤
        (∫ x in 0..(stepCount N T : ℝ), g x) + g 0 := by
    linarith
  change leftRiemannSum N f T ≤
    (∫ t in 0..(stepCount N T : ℝ) * step N, f t) + step N * f 0
  have hscale :
      (step N * ∫ x in 0..(stepCount N T : ℝ), f (x * step N)) =
        ∫ t in 0..(stepCount N T : ℝ) * step N, f t := by
    simpa only [zero_mul] using
      intervalIntegral.mul_integral_comp_mul_right
        (f := f) (a := 0) (b := (stepCount N T : ℝ)) (step N)
  rw [← hscale]
  simpa [leftRiemannSum, g, mul_comm, mul_left_comm, mul_assoc] using hsum

/-! ## C. Quantitative error and convergence -/

/-- The fixed-step left Riemann sum has the explicit error
`|S_N - ∫₀ᵀ f| ≤ f(0)/N` for nonnegative non-increasing `f`. -/
lemma abs_leftRiemannSum_sub_integral_le
    (N : ℕ) (hN : 0 < N) (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hf : AntitoneOn f (Icc 0 T)) (hnonneg : ∀ x ∈ Icc 0 T, 0 ≤ f x) :
    |leftRiemannSum N f T - ∫ t in 0..T, f t| ≤ step N * f 0 := by
  let s : ℝ := (stepCount N T : ℝ) * step N
  have hs0 : 0 ≤ s := mul_nonneg (Nat.cast_nonneg _) (step_nonneg N hN)
  have hsT : s ≤ T := span_le_horizon N hN hT
  have hspan_lower :=
    integral_to_span_le_leftRiemannSum N hN f hT hf
  have hspan_upper :=
    leftRiemannSum_le_integral_to_span_add N hN f hT hf hnonneg
  have hsInt : IntervalIntegrable f volume 0 s := by
    have hanti : AntitoneOn f (uIcc 0 s) := by
      simpa [uIcc_of_le hs0] using
        hf.mono (Icc_subset_Icc_right hsT)
    exact hanti.intervalIntegrable
  have htInt : IntervalIntegrable f volume s T := by
    have hanti : AntitoneOn f (uIcc s T) := by
      simpa [uIcc_of_le hsT] using
        hf.mono (Icc_subset_Icc_left hs0)
    exact hanti.intervalIntegrable
  have htail_nonneg : 0 ≤ ∫ t in s..T, f t :=
    intervalIntegral.integral_nonneg hsT fun t ht => hnonneg t
      ⟨hs0.trans ht.1, ht.2⟩
  have htail_const :
      (∫ t in s..T, f t) ≤ ∫ _ in s..T, f 0 := by
    apply intervalIntegral.integral_mono_on hsT htInt
      (continuous_const.intervalIntegrable _ _)
    intro t ht
    exact hf ⟨le_rfl, hT⟩ ⟨hs0.trans ht.1, ht.2⟩ (hs0.trans ht.1)
  have hf0 : 0 ≤ f 0 := hnonneg 0 ⟨le_rfl, hT⟩
  have hrem : T - s < step N := by
    simpa [s] using horizon_sub_span_lt_step N hN T
  have htail_upper : (∫ t in s..T, f t) ≤ step N * f 0 := by
    have hconst : (∫ _ in s..T, f 0) = (T - s) * f 0 := by
      simp
    rw [hconst] at htail_const
    exact htail_const.trans
      (mul_le_mul_of_nonneg_right hrem.le hf0)
  have hsplit :
      (∫ t in 0..T, f t) = (∫ t in 0..s, f t) + ∫ t in s..T, f t := by
    exact (intervalIntegral.integral_add_adjacent_intervals hsInt htInt).symm
  rw [hsplit, abs_le]
  constructor <;> linarith

/-- As the resolution tends to infinity, the repository fixed-step kernel
converges to Mathlib's interval integral. -/
lemma tendsto_leftRiemannSum_integral
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hf : AntitoneOn f (Icc 0 T)) (hnonneg : ∀ x ∈ Icc 0 T, 0 ≤ f x) :
    Tendsto (fun N : ℕ => leftRiemannSum N f T) atTop
      (𝓝 (∫ t in 0..T, f t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N => abs_nonneg _
  · filter_upwards [eventually_gt_atTop 0] with N hN
    exact abs_leftRiemannSum_sub_integral_le N hN f hT hf hnonneg
  · simpa [step] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (f 0)

end Physlib.Mathematics.LeftRiemannSum

end
