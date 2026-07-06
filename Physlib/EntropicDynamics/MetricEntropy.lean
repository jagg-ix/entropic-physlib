/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The stable pseudo-metric, metric entropy, and the Dudley integral

The metric-complexity layer. A symmetric `p`-stable process with kernel `f` carries a natural pseudo-metric
`d(t,s) = ‖f(t) − f(s)‖_{Lᵖ}` — the `Lᵖ`-norm pullback of the kernel — the same `Lᵖ`-distance structure as the
Cramér / Wasserstein CDF metrics. Its **metric entropy** `H_q(ε) = (log N(ε))^{1/q}` (from the covering number
`N(ε)`, with `q` the Hölder dual of `p`) and its **Dudley integral** `J_q(δ) = ∫₀^δ H_q(ε) dε` control path
continuity; the log-covering count under a `d`-dimensional reduction is bounded linearly in the reduced dimension.

References: J.P. Nolan, *Continuity of Symmetric Stable Processes*, J. Multivariate Anal. 29 (1989). No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.EntropicDynamics.MetricEntropy

/-! ## The stable pseudo-metric `d(t,s) = ‖f(t) − f(s)‖_{Lᵖ}` -/

section StableMetric

variable {T : Type*} {V : Type*} [SeminormedAddCommGroup V]

/-- **The stable pseudo-metric** `d(t,s) = ‖f(t) − f(s)‖_{Lᵖ}`, the `Lᵖ`-norm pullback of the kernel map. -/
def stableDist (f : T → V) (t s : T) : ℝ := ‖f t - f s‖

/-- **Vanishes on the diagonal** `d(t,t) = 0`. -/
theorem stableDist_self (f : T → V) (t : T) : stableDist f t t = 0 := by simp [stableDist]

/-- **Symmetric** `d(t,s) = d(s,t)`. -/
theorem stableDist_comm (f : T → V) (t s : T) : stableDist f t s = stableDist f s t := by
  simp [stableDist, norm_sub_rev]

/-- **Triangle inequality** `d(t,r) ≤ d(t,s) + d(s,r)` (Minkowski). -/
theorem stableDist_triangle (f : T → V) (t s r : T) :
    stableDist f t r ≤ stableDist f t s + stableDist f s r := by
  simp only [stableDist]
  calc ‖f t - f r‖ = ‖(f t - f s) + (f s - f r)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖f t - f s‖ + ‖f s - f r‖ := norm_add_le _ _

/-- **Non-negative** `0 ≤ d(t,s)`. -/
theorem stableDist_nonneg (f : T → V) (t s : T) : 0 ≤ stableDist f t s := norm_nonneg _

end StableMetric

/-! ## Metric entropy `H_q(ε) = (log N(ε))^{1/q}` and the dual index -/

/-- **The metric entropy** `H_q = (log N)^{1/q}` of a covering count `N` at dual index `q`. -/
noncomputable def metricEntropy (q N : ℝ) : ℝ := (Real.log N) ^ (1 / q)

/-- **Monotone in the covering count** `N₁ ≤ N₂ ⟹ H_q(N₁) ≤ H_q(N₂)`. -/
theorem metricEntropy_mono {q : ℝ} (hq : 0 < q) {N₁ N₂ : ℝ} (h1 : 1 ≤ N₁) (h : N₁ ≤ N₂) :
    metricEntropy q N₁ ≤ metricEntropy q N₂ := by
  unfold metricEntropy
  exact Real.rpow_le_rpow (Real.log_nonneg h1) (Real.log_le_log (by linarith) h) (by positivity)

/-- **Non-negative** `0 ≤ H_q(N)` for `N ≥ 1`. -/
theorem metricEntropy_nonneg {q N : ℝ} (hN : 1 ≤ N) : 0 ≤ metricEntropy q N :=
  Real.rpow_nonneg (Real.log_nonneg hN) _

/-- **The dual index is the Hölder conjugate of the stability index** `1/p + 1/q = 1`. -/
theorem conjugate_index {p q : ℝ} (hp : 1 < p) (hq : q = p / (p - 1)) : 1 / p + 1 / q = 1 := by
  subst hq
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **Metric entropy under a `d`-dimensional reduction** `H_q(N) ≤ (n·log(1+4/ε))^{1/q}` when the covering count is
bounded by the `ε`-net packing `(1+4/ε)ⁿ` of an `n`-dimensional reduction — linear in the reduced dimension `n`. -/
theorem metricEntropy_le_dimensional_reduction {q : ℝ} (hq : 0 < q) {N ε : ℝ} (n : ℕ)
    (hN1 : 1 ≤ N) (hNbound : N ≤ (1 + 4 / ε) ^ n) :
    metricEntropy q N ≤ ((n : ℝ) * Real.log (1 + 4 / ε)) ^ (1 / q) := by
  calc metricEntropy q N ≤ metricEntropy q ((1 + 4 / ε) ^ n) := metricEntropy_mono hq hN1 hNbound
    _ = (Real.log ((1 + 4 / ε) ^ n)) ^ (1 / q) := rfl
    _ = ((n : ℝ) * Real.log (1 + 4 / ε)) ^ (1 / q) := by rw [Real.log_pow]

/-! ## The Dudley metric-entropy integral `J_q(δ) = ∫₀^δ H_q(ε) dε` -/

/-- **The Dudley metric-entropy integral** `J_q(δ) = ∫₀^δ H_q(ε) dε`, whose finiteness controls path continuity. -/
noncomputable def metricEntropyIntegral (H : ℝ → ℝ) (δ : ℝ) : ℝ := ∫ ε in (0 : ℝ)..δ, H ε

/-- **Vanishes at the origin** `J_q(0) = 0`. -/
theorem metricEntropyIntegral_zero (H : ℝ → ℝ) : metricEntropyIntegral H 0 = 0 := by
  unfold metricEntropyIntegral
  exact intervalIntegral.integral_same

/-- **Non-negative** for a non-negative scale-entropy on `[0,δ]`. -/
theorem metricEntropyIntegral_nonneg (H : ℝ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hH : ∀ ε ∈ Set.Icc (0 : ℝ) δ, 0 ≤ H ε) : 0 ≤ metricEntropyIntegral H δ :=
  intervalIntegral.integral_nonneg hδ hH

/-- **Monotone in the cutoff** `δ₁ ≤ δ₂ ⟹ J_q(δ₁) ≤ J_q(δ₂)` (given integrability and non-negativity). -/
theorem metricEntropyIntegral_mono (H : ℝ → ℝ) {δ₁ δ₂ : ℝ} (h12 : δ₁ ≤ δ₂)
    (h1 : IntervalIntegrable H MeasureTheory.volume 0 δ₁)
    (h2 : IntervalIntegrable H MeasureTheory.volume δ₁ δ₂)
    (hH : ∀ ε ∈ Set.Icc δ₁ δ₂, 0 ≤ H ε) :
    metricEntropyIntegral H δ₁ ≤ metricEntropyIntegral H δ₂ := by
  unfold metricEntropyIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hnn : 0 ≤ ∫ ε in δ₁..δ₂, H ε := intervalIntegral.integral_nonneg h12 hH
  linarith

end Physlib.EntropicDynamics.MetricEntropy

end
