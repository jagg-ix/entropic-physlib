/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ClockUniqueness
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Tactic.FieldSimp

/-!
# Nonlinear clock uniqueness

`EntropicTime.ClockUniqueness` proved uniqueness among **linear** clocks
`φ(t) = c · S_I(t)`. This module extends to general nonlinear clocks.

## What is proved

### §A — Discrete nonlinear uniqueness (unconditional)

On a **discrete worldline** where S_I takes values only in `{n · δ_S | n : ℕ}`
(each irreversible event advances S_I by exactly one Landauer quantum), a clock
is any function `φ : ℕ → ℝ` — no linearity assumed. The tight-step condition
`φ(n+1) − φ(n) = δ_φ` with `φ(0) = 0` forces `φ(n) = n · δ_φ` by induction.

**Any** nonlinear discrete clock with the physical Landauer step equals τ_ent at
all event counts. The proof requires no analytic machinery.

### §B — Key lemma: monotone periodic function is constant

A monotone periodic function on `ℝ` must be constant.

Proof: For any `x`, the Archimedean property gives `n : ℕ` with `n * p ≥ x`;
by monotonicity `f(x) ≤ f(n*p) = f(0)`. Similarly `f(0) ≤ f(x)` by applying
periodicity to move `x` to a non-negative point. Hence `f(x) = f(0)`.

This is proved without continuity or measure theory.

### §C — Continuous nonlinear uniqueness (under monotone remainder)

For any continuous-worldline clock `φ : ℝ → ℝ` satisfying the tight step
`φ(s + δ_S) = φ(s) + δ_φ`, the remainder `g(s) := φ(s) − (δ_φ/δ_S)·s`
is periodic with period `δ_S`. If additionally `g` is monotone (which follows
if `φ` dominates its linear rate on every sub-interval), then `g = 0` by §B,
giving `φ(s) = (δ_φ/δ_S)·s = τ_ent(s)`.

## Scope

The continuous uniqueness needs `g` to be monotone. `g = φ − L` where both
`φ` (entropy-faithful ⇒ non-decreasing) and `L = (δ_φ/δ_S)·s` (strictly
increasing) are monotone, but their difference need not be. The condition
"g is monotone" is an additional hypothesis, not derived from the tight step.
Its physical content: `φ` does not grow slower than its linear average on any
sub-interval. For clocks built from entropy production rates, this holds
whenever the rate is uniformly bounded below — which is the Landauer lower
bound applied continuously rather than event-by-event.

The **discrete case** (§A) has no such caveat: it covers all functions `ℕ → ℝ`
unconditionally.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.NonlinearClockUniqueness

open Physlib.Thermodynamics.SecondLaw
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ClockUniqueness
open Constants

/-! ## §A — Discrete nonlinear uniqueness -/

/-- **Discrete worldline**: S_I only takes values in `{n · δ_S | n : ℕ}`. -/
structure DiscreteWorldline where
  δ_S : ℝ
  δ_S_pos : 0 < δ_S

def DiscreteWorldline.S_I (dw : DiscreteWorldline) (n : ℕ) : ℝ := n * dw.δ_S

/-- **Discrete clock**: any function `ℕ → ℝ` with tight step and zero init.
No linearity assumed. -/
structure DiscreteClock (dw : DiscreteWorldline) where
  φ   : ℕ → ℝ
  δ_φ : ℝ
  init : φ 0 = 0
  step : ∀ n, φ (n + 1) - φ n = δ_φ

/-- **Theorem A1 — Discrete nonlinear uniqueness**: induction forces
`φ(n) = n · δ_φ` for any `φ : ℕ → ℝ` satisfying the tight step. -/
theorem DiscreteClock.eq_linear {dw : DiscreteWorldline}
    (clk : DiscreteClock dw) (n : ℕ) :
    clk.φ n = ↑n * clk.δ_φ := by
  induction n with
  | zero => simp [clk.init]
  | succ n ih =>
    have h := clk.step n
    push_cast
    linarith

/-- Any two discrete clocks with the same step agree everywhere. -/
theorem DiscreteClock.unique {dw : DiscreteWorldline}
    (clk₁ clk₂ : DiscreteClock dw) (hstep : clk₁.δ_φ = clk₂.δ_φ) (n : ℕ) :
    clk₁.φ n = clk₂.φ n := by
  rw [clk₁.eq_linear, clk₂.eq_linear, hstep]

/-- **Theorem A2 — Discrete τ_ent uniqueness**: any discrete clock with step
`δ_S / ℏ` equals τ_ent (`S_I / ℏ`) at every event count. -/
theorem DiscreteClock.eq_tau_ent {dw : DiscreteWorldline}
    (ℏ : ℝ) (_hℏ : 0 < ℏ)
    (clk : DiscreteClock dw) (hstep : clk.δ_φ = dw.δ_S / ℏ) (n : ℕ) :
    clk.φ n = dw.S_I n / ℏ := by
  rw [clk.eq_linear, hstep, DiscreteWorldline.S_I]
  ring

/-! ## §B — Monotone periodic function is constant -/

/-- **Lemma B1 — Iterated period**: `f(x + n * p) = f(x)` for all `n : ℕ`. -/
theorem iterated_period {f : ℝ → ℝ} {p : ℝ}
    (hper : ∀ x, f (x + p) = f x) (n : ℕ) (x : ℝ) :
    f (x + ↑n * p) = f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show x + ↑(n + 1) * p = (x + ↑n * p) + p by push_cast; ring]
    rw [hper (x + ↑n * p)]
    exact ih

/-- **Lemma B2 — Period at ℕ-multiples**: `f(n * p) = f(0)` for all `n : ℕ`. -/
theorem period_at_nat {f : ℝ → ℝ} {p : ℝ}
    (hper : ∀ x, f (x + p) = f x) (n : ℕ) :
    f (↑n * p) = f 0 := by
  have h := iterated_period hper n 0
  simp only [zero_add] at h
  exact h

/-- **Theorem B3 — Monotone periodic is constant**: if `f : ℝ → ℝ` is
non-decreasing and periodic with period `p > 0`, then `f x = f 0` for all `x`.

Proof uses only the Archimedean property and the definition of `Monotone`. -/
theorem monotone_periodic_is_constant {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hper : ∀ x, f (x + p) = f x) (hf : Monotone f) (x : ℝ) :
    f x = f 0 := by
  -- Upper bound: find n with n*p ≥ x, then f(x) ≤ f(n*p) = f(0)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x ≤ ↑n * p := by
    obtain ⟨n, hn⟩ := exists_nat_ge (x / p)
    exact ⟨n, (div_le_iff₀ hp).mp hn⟩
  have hle : f x ≤ f 0 :=
    (period_at_nat hper n) ▸ hf hn
  -- Lower bound: find m with x + m*p ≥ 0, then f(0) ≤ f(x+m*p) = f(x)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 0 ≤ x + ↑m * p := by
    obtain ⟨m, hm⟩ := exists_nat_ge (-x / p)
    refine ⟨m, ?_⟩
    have := (div_le_iff₀ hp).mp hm
    linarith
  have hge : f 0 ≤ f x := by
    have h := hf hm
    rwa [iterated_period hper m x] at h
  linarith

/-! ## §C — Continuous nonlinear uniqueness -/

/-- **General nonlinear clock** (as a function of S_I):
`φ : ℝ → ℝ` with tight step `δ_φ`, monotone (entropy-faithful), init `φ(0) = 0`. -/
structure NonlinearClock (δ_S δ_φ : ℝ) where
  φ    : ℝ → ℝ
  step : ∀ s, φ (s + δ_S) = φ s + δ_φ
  mono : Monotone φ
  init : φ 0 = 0

namespace NonlinearClock

variable {δ_S δ_φ : ℝ}

/-- **τ_ent as a nonlinear clock**: `φ(s) = (δ_φ/δ_S) · s`. -/
noncomputable def ofTauEnt (hS : 0 < δ_S) (hφ : 0 < δ_φ) :
    NonlinearClock δ_S δ_φ where
  φ s  := (δ_φ / δ_S) * s
  step s := by field_simp
  mono := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left hab (div_nonneg hφ.le hS.le)
  init := by simp

/-- **C1 — Value at ℕ-multiples**: `φ(n * δ_S) = n * δ_φ`. -/
theorem at_nat (clk : NonlinearClock δ_S δ_φ) (n : ℕ) :
    clk.φ (↑n * δ_S) = ↑n * δ_φ := by
  induction n with
  | zero => simp [clk.init]
  | succ n ih =>
    rw [show (↑(n + 1) : ℝ) * δ_S = ↑n * δ_S + δ_S by push_cast; ring]
    rw [clk.step (↑n * δ_S), ih]
    push_cast; ring

/-- **The periodic remainder**: `g(s) = φ(s) − (δ_φ/δ_S) · s`. -/
def remainder (clk : NonlinearClock δ_S δ_φ) (s : ℝ) : ℝ :=
  clk.φ s - (δ_φ / δ_S) * s

/-- The remainder is periodic with period `δ_S`. -/
theorem remainder_periodic (hS : 0 < δ_S) (clk : NonlinearClock δ_S δ_φ) :
    ∀ s, clk.remainder (s + δ_S) = clk.remainder s := by
  intro s
  simp only [remainder, clk.step s]
  have hSne : δ_S ≠ 0 := ne_of_gt hS
  field_simp
  ring

/-- The remainder vanishes at zero. -/
theorem remainder_zero (clk : NonlinearClock δ_S δ_φ) :
    clk.remainder 0 = 0 := by
  simp [remainder, clk.init]

/-- The remainder vanishes at every ℕ-multiple of `δ_S`. -/
theorem remainder_at_nat (hS : 0 < δ_S) (clk : NonlinearClock δ_S δ_φ) (n : ℕ) :
    clk.remainder (↑n * δ_S) = 0 := by
  simp only [remainder, clk.at_nat n]
  have hSne : δ_S ≠ 0 := ne_of_gt hS
  field_simp
  ring

/-- **Theorem C2 — Continuous uniqueness under monotone remainder**:
if the remainder `g = φ − L` is non-decreasing, then `φ = τ_ent`.

The monotone-remainder condition is stronger than just "φ is entropy-faithful":
it additionally requires that `φ` does not accumulate deficit relative to its
linear average. -/
theorem unique_of_monotone_remainder (hS : 0 < δ_S)
    (clk : NonlinearClock δ_S δ_φ)
    (hgmono : Monotone clk.remainder)
    (s : ℝ) : clk.φ s = (δ_φ / δ_S) * s := by
  have hgs : clk.remainder s = 0 := by
    rw [monotone_periodic_is_constant hS (clk.remainder_periodic hS) hgmono s]
    exact clk.remainder_zero
  simp only [remainder] at hgs
  linarith

/-- **Theorem C3 — Two nonlinear clocks with monotone remainders agree**: -/
theorem unique_of_monotone_remainders (hS : 0 < δ_S)
    (clk₁ clk₂ : NonlinearClock δ_S δ_φ)
    (hg₁ : Monotone clk₁.remainder)
    (hg₂ : Monotone clk₂.remainder)
    (s : ℝ) : clk₁.φ s = clk₂.φ s := by
  rw [unique_of_monotone_remainder hS clk₁ hg₁ s,
      unique_of_monotone_remainder hS clk₂ hg₂ s]

end NonlinearClock

/-! ## §D — Connection to `EntropyArrowWorldline` -/

/-- **Theorem D1**: an entropy-faithful clock `φ(t) := f(W.S_I_along t)` where
`f : ℝ → ℝ` satisfies the tight step, is equivalent to a `NonlinearClock`
applied to S_I.  If additionally `f` has a monotone remainder, τ_ent is the
unique such clock. -/
theorem worldline_clock_unique_of_monotone_remainder
    (W : EntropyArrowWorldline)
    {δ_S δ_φ : ℝ} (hS : 0 < δ_S)
    (clk : NonlinearClock δ_S δ_φ)
    (hgmono : Monotone clk.remainder)
    (t : ℝ) :
    clk.φ (W.S_I_along t) = (δ_φ / δ_S) * W.S_I_along t :=
  NonlinearClock.unique_of_monotone_remainder hS clk hgmono (W.S_I_along t)

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.NonlinearClockUniqueness
