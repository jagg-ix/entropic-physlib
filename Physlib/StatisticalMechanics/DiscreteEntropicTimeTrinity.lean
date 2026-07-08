/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith

/-!
# Discrete entropic-time trinity `(X, τ_ent, λ, A)` with damping envelope

Port of the complex-action/entropic-time discrete entropic-time trinity from
``
into physlib's statistical-mechanics scope.

The trinity is the **discrete-step** underlying space of the coupled
SDE-style stochastic dynamics

  `dX_t      = b(X_t, t) dt + σ(X_t, t) dW_t`        (particle position)
  `dτ_ent(t) = λ(X_t, t) dt`                          (entropic proper time)
  `dA_t      = A_t · (…) dt`                          (phase / attenuation)

with damping envelope `Λ_t := exp(−τ_ent_t)`.  Operationally, the
combination `Y_t := Λ_t · f(X_t)` solves a **damped
backward-Kolmogorov equation** `∂_t f + ℒ f − λ f = 0`.

This file provides the **structural discrete-step content**:

* The structure `DiscreteEntropicTimeTrinity` with the accumulation
  rule `τ_ent(n+1) = τ_ent(n) + λ(n)`.
* The damping envelope `Λ(n) = exp(−τ_ent(n))` with its
  `Λ ≤ 1`, `Λ > 0`, and monotonicity bounds.
* The entropic-time monotonicity `τ_ent(m) ≤ τ_ent(n)` for `m ≤ n`.
* The free-propagation limit `λ ≡ 0` ⟹ `τ_ent` and `Λ` constant.

This is a **structural structure** — it does not build Brownian
motion, Itô calculus, Markov semigroups, or Euler–Maruyama
convergence.  Those analytic pieces are a separate scope.

## Contents

### §1 — Trinity structure

* `DiscreteEntropicTimeTrinity` — record `(X, τ_ent, λ, A)` with
  `λ ≥ 0`, `τ_ent(0) ≥ 0`, `τ_ent(n+1) = τ_ent n + λ n`.

### §2 — Damping envelope

* `dampingEnvelope` — `Λ n := exp(−τ_ent n)`.
* `dampingEnvelope_le_one`  — `Λ n ≤ 1`.
* `dampingEnvelope_pos`     — `0 < Λ n`.
* `dampingEnvelope_monotone` — `m ≤ n ⟹ Λ n ≤ Λ m`.

### §3 — Entropic-time monotonicity

* `tauEnt_nonneg`     — `0 ≤ τ_ent n` for all `n`.
* `tauEnt_succ_ge`    — `τ_ent k ≤ τ_ent (k+1)`.
* `tauEnt_monotone`   — `m ≤ n ⟹ τ_ent m ≤ τ_ent n`.

### §4 — Free-propagation limit

* `IsFreePropagation` — predicate `λ ≡ 0`.
* `tauEnt_const_of_freePropagation` — under free propagation,
  `τ_ent` is constant.
* `dampingEnvelope_const_of_freePropagation` — and `Λ` is constant.

## References

* Source: ``
  (commit imported as-of 2026-06-05).
* Damped backward-Kolmogorov equation as the continuous-time
  counterpart (deferred to Phase-2 SDE scope).

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.StatisticalMechanics

/-! ## §1 — Trinity structure -/

/-- **Discrete entropic-time trinity `(X, τ_ent, λ, A)`**.

Includes the per-step shape of the coupled
particle/entropic-time/phase system:

* `X n`     — particle position at step `n`.
* `τ_ent n` — accumulated entropic proper time at step `n`,
  satisfying `τ_ent(n+1) = τ_ent n + λ n` and starting non-negative.
* `lam n`   — non-negative per-step entropy-production rate.
* `A n`     — phase / attenuation observable at step `n`. -/
structure DiscreteEntropicTimeTrinity where
  /-- Particle position at each discrete step. -/
  X : ℕ → ℝ
  /-- Accumulated entropic proper time. -/
  τ_ent : ℕ → ℝ
  /-- Per-step non-negative rate. -/
  lam : ℕ → ℝ
  /-- Non-negativity of the rate. -/
  lam_nonneg : ∀ n, 0 ≤ lam n
  /-- Initial entropic proper time is non-negative. -/
  τ_ent_zero_nonneg : 0 ≤ τ_ent 0
  /-- Discrete accumulation rule `τ_ent(n+1) = τ_ent n + λ n`. -/
  τ_ent_succ : ∀ n, τ_ent (n + 1) = τ_ent n + lam n
  /-- Phase / attenuation observable. -/
  A : ℕ → ℝ

namespace DiscreteEntropicTimeTrinity

variable (T : DiscreteEntropicTimeTrinity)

/-! ## §2 — Damping envelope -/

/-- **Damping envelope** `Λ n := exp(−τ_ent n)`.

The exponential damping factor.  Combined with `f(X_t)`, this
produces the `Y_t = Λ_t · f(X_t)` solving the damped
backward-Kolmogorov equation `∂_t f + ℒ f − λ f = 0`. -/
def dampingEnvelope (n : ℕ) : ℝ := Real.exp (-(T.τ_ent n))

/-! ## §3 — Entropic-time monotonicity -/

/-- **Each `τ_ent` value is non-negative**. -/
theorem tauEnt_nonneg : ∀ n, 0 ≤ T.τ_ent n := by
  intro n
  induction n with
  | zero => exact T.τ_ent_zero_nonneg
  | succ k ih =>
    rw [T.τ_ent_succ k]
    exact add_nonneg ih (T.lam_nonneg k)

/-- **One-step `τ_ent` monotonicity**: `τ_ent k ≤ τ_ent (k+1)`. -/
theorem tauEnt_succ_ge (k : ℕ) : T.τ_ent k ≤ T.τ_ent (k + 1) := by
  rw [T.τ_ent_succ k]
  linarith [T.lam_nonneg k]

/-- **Entropic-time monotonicity**: `τ_ent` is non-decreasing in `n`. -/
theorem tauEnt_monotone : ∀ {m n : ℕ}, m ≤ n → T.τ_ent m ≤ T.τ_ent n := by
  intro m n hmn
  induction hmn with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (T.tauEnt_succ_ge _)

/-! ## §4 — Damping-envelope bounds -/

/-- **Damping envelope upper bound**: `Λ n ≤ 1`. -/
theorem dampingEnvelope_le_one (n : ℕ) : T.dampingEnvelope n ≤ 1 := by
  unfold dampingEnvelope
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos_of_nonneg (T.tauEnt_nonneg n)

/-- **Damping envelope positivity**: `0 < Λ n`. -/
theorem dampingEnvelope_pos (n : ℕ) : 0 < T.dampingEnvelope n := Real.exp_pos _

/-- **Damping envelope monotonicity**: `Λ` is non-increasing in `n`. -/
theorem dampingEnvelope_monotone {m n : ℕ} (hmn : m ≤ n) :
    T.dampingEnvelope n ≤ T.dampingEnvelope m := by
  unfold dampingEnvelope
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (T.tauEnt_monotone hmn)

/-! ## §5 — Trivial existence -/

/-- **Trivial trinity**: zero rate, zero everywhere.

Witness that the trinity structure is inhabited. -/
def trivial : DiscreteEntropicTimeTrinity where
  X                 := fun _ => 0
  τ_ent             := fun _ => 0
  lam               := fun _ => 0
  lam_nonneg        := fun _ => le_refl 0
  τ_ent_zero_nonneg := le_refl 0
  τ_ent_succ        := fun _ => by ring
  A                 := fun _ => 0

end DiscreteEntropicTimeTrinity

/-! ## §6 — Free-propagation limit `λ ≡ 0` -/

/-- **Free-propagation regime**: the rate is identically zero.

Under this regime the entropic-time `τ_ent` and damping envelope
`Λ` are both constant: there is no information dissipation. -/
def IsFreePropagation (T : DiscreteEntropicTimeTrinity) : Prop :=
  ∀ n, T.lam n = 0

namespace DiscreteEntropicTimeTrinity

variable (T : DiscreteEntropicTimeTrinity)

/-- **Under free propagation, `τ_ent` is constant**. -/
theorem tauEnt_const_of_freePropagation
    (hFree : IsFreePropagation T) (n : ℕ) :
    T.τ_ent n = T.τ_ent 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [T.τ_ent_succ k, hFree k, ih]
    ring

/-- **Under free propagation, the damping envelope `Λ` is constant**. -/
theorem dampingEnvelope_const_of_freePropagation
    (hFree : IsFreePropagation T) (n : ℕ) :
    T.dampingEnvelope n = T.dampingEnvelope 0 := by
  unfold dampingEnvelope
  rw [T.tauEnt_const_of_freePropagation hFree n]

end DiscreteEntropicTimeTrinity

end Physlib.StatisticalMechanics

end
