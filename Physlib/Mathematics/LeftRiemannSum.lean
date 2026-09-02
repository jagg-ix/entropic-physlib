/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# Fixed-step left Riemann sums over an ordered field

Ports `NavierStokes/NSDiscreteIntegralKernel.lean` of the reference tree, generalized from
its hard-coded `1000` steps per unit time over `ℚ` to an arbitrary resolution `N` over any
linearly ordered field with a floor (so both the certified `ℚ` kernel of the source and the
`ℝ` kernel the Navier–Stokes trajectory functionals need): the left Riemann sum

  `leftRiemannSum N f T = ∑_{i < ⌊T·N⌋₊} f(i/N) · (1/N)`

with the order and linearity theory a discrete integration kernel needs — over `ℚ`
decidable and `norm_num`-friendly, no measure theory:

* `leftRiemannSum_zero`, `leftRiemannSum_nonneg` — vanishing at horizon zero, nonnegativity
  on nonnegative integrands;
* `leftRiemannSum_le_of_pointwise` — pointwise inequalities lift to the sums;
* `leftRiemannSum_mono` — monotone in the horizon for nonnegative integrands;
* `leftRiemannSum_linear` — linearity `∫(a·f + b·g) = a·∫f + b·∫g`;
* `sample_lt_horizon`, `span_le_horizon` — every sample point lies strictly below the
  horizon, and the total stepped span never overshoots it — the bookkeeping that
  range-restricted integration against the kernel requires.

**Honest layering.**  This is the exact algebra of the fixed-step kernel; convergence to the
Mathlib interval integral as `N → ∞` is the analytic layer, not taken here.

## References

* Source: `NavierStokes/NSDiscreteIntegralKernel.lean` (reference tree, own authorship),
  re-authored with the step resolution `N` as a parameter and the field generalized.
-/

set_option autoImplicit false

open Finset

@[expose] public section

namespace Physlib.Mathematics.LeftRiemannSum

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]
variable (N : ℕ)

/-- The step size `1/N` at resolution `N` steps per unit time. -/
def step : K := 1 / N

theorem step_pos (hN : 0 < N) : 0 < (step N : K) := by
  unfold step
  exact div_pos one_pos (by exact_mod_cast hN)

theorem step_nonneg (hN : 0 < N) : 0 ≤ (step N : K) := (step_pos N hN).le

/-- The number of steps below the horizon `T`: `⌊T·N⌋₊` (zero for `T ≤ 0`). -/
def stepCount (T : K) : ℕ := ⌊T * N⌋₊

@[simp] theorem stepCount_zero : stepCount N (0 : K) = 0 := by
  simp [stepCount]

theorem stepCount_mono {T₁ T₂ : K} (h : T₁ ≤ T₂) : stepCount N T₁ ≤ stepCount N T₂ := by
  unfold stepCount
  exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right h (by positivity))

/-- **The fixed-step left Riemann sum** `∑_{i < ⌊T·N⌋₊} f(i/N)·(1/N)`. -/
def leftRiemannSum (f : K → K) (T : K) : K :=
  ∑ i ∈ Finset.range (stepCount N T), f ((i : ℚ) * step N) * step N

@[simp] theorem leftRiemannSum_zero (f : K → K) : leftRiemannSum N f (0 : K) = 0 := by
  simp [leftRiemannSum]

/-- Nonnegative integrands give nonnegative sums. -/
theorem leftRiemannSum_nonneg (hN : 0 < N) (f : K → K) (T : K) (hf : ∀ t, 0 ≤ f t) :
    0 ≤ leftRiemannSum N f T :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (hf _) (step_nonneg N hN)

/-- Pointwise inequalities lift to the sums. -/
theorem leftRiemannSum_le_of_pointwise (hN : 0 < N) (f g : K → K) (T : K)
    (h : ∀ t, f t ≤ g t) :
    leftRiemannSum N f T ≤ leftRiemannSum N g T :=
  Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_right (h _) (step_nonneg N hN)

/-- For nonnegative integrands the sum is monotone in the horizon. -/
theorem leftRiemannSum_mono (hN : 0 < N) (f : K → K) {T₁ T₂ : K}
    (hf : ∀ t, 0 ≤ f t) (h : T₁ ≤ T₂) :
    leftRiemannSum N f T₁ ≤ leftRiemannSum N f T₂ := by
  unfold leftRiemannSum
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (stepCount_mono N h)) fun i _ _ => ?_
  exact mul_nonneg (hf _) (step_nonneg N hN)

omit [IsStrictOrderedRing K] in
/-- **Linearity** `∫(a·f + b·g) = a·∫f + b·∫g`. -/
theorem leftRiemannSum_linear (f g : K → K) (a b T : K) :
    leftRiemannSum N (fun t => a * f t + b * g t) T
      = a * leftRiemannSum N f T + b * leftRiemannSum N g T := by
  unfold leftRiemannSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [IsStrictOrderedRing K] in
/-- Constant multiples move through the sum. -/
theorem leftRiemannSum_const_mul (f : K → K) (a T : K) :
    leftRiemannSum N (fun t => a * f t) T = a * leftRiemannSum N f T := by
  unfold leftRiemannSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Every sample point lies strictly below the horizon**: `i < ⌊T·N⌋₊` gives
`i/N < T`. -/
theorem sample_lt_horizon (hN : 0 < N) {T : K} (hT : 0 ≤ T) {i : ℕ}
    (hi : i < stepCount N T) :
    (i : K) * step N < T := by
  have hNq : (0 : K) < (N : K) := by exact_mod_cast hN
  have h1 : (i : K) < (stepCount N T : K) := by exact_mod_cast hi
  have h2 : (stepCount N T : K) ≤ T * N := by
    unfold stepCount
    exact Nat.floor_le (by positivity)
  have h3 : (i : K) < T * N := lt_of_lt_of_le h1 h2
  rw [show (i : K) * step N = (i : K) / N from by unfold step; ring,
    div_lt_iff₀ hNq]
  linarith

/-- **The stepped span never overshoots the horizon**: `⌊T·N⌋₊ · (1/N) ≤ T`. -/
theorem span_le_horizon (hN : 0 < N) {T : K} (hT : 0 ≤ T) :
    (stepCount N T : K) * step N ≤ T := by
  have hNq : (0 : K) < (N : K) := by exact_mod_cast hN
  have h1 : (stepCount N T : K) ≤ T * N := by
    unfold stepCount
    exact Nat.floor_le (by positivity)
  calc (stepCount N T : K) * step N
      ≤ T * N * step N := mul_le_mul_of_nonneg_right h1 (step_nonneg N hN)
    _ = T := by
        unfold step
        field_simp

/-- **Constant integrands undershoot the product**: `∫₀ᵀ c ≤ c·T` — the left sum of a
constant is the stepped span times `c`, and the span never overshoots the horizon. -/
theorem leftRiemannSum_const_le (hN : 0 < N) {c T : K} (hc : 0 ≤ c) (hT : 0 ≤ T) :
    leftRiemannSum N (fun _ => c) T ≤ c * T := by
  unfold leftRiemannSum
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (stepCount N T : K) * (c * step N)
      = c * ((stepCount N T : K) * step N) := by ring
    _ ≤ c * T := mul_le_mul_of_nonneg_left (span_le_horizon N hN hT) hc

end Physlib.Mathematics.LeftRiemannSum

end
