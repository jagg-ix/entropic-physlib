/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Lindblad.JumpFlowFiniteExp

/-!
# Partial-sum identification: `lindbladJumpFiniteExpSeries` is the `expSeries` partial sum

Pillar 13 of the closure-plan stack toward the full Lindblad
CP-semigroup theorem: identify the physlib-defined finite-truncated
series

 `lindbladJumpFiniteExpSeries t L_fn n
 := Σ_{k < n} (t^k / k!) · J^k` (from commit `b81e8ef9`)

with the **canonical partial sum of `NormedSpace.exp((t : ℂ) • J)`**:

 `Σ_{k < n} (k!)⁻¹ • ((t : ℂ) • J)^k`,

where `J^k` is the k-fold composition (Module.End monoid power).

This identification is the **algebraic bridge** to Mathlib's
matrix-exponential infrastructure: once the partial sums are
identified, the `n → ∞` limit goes through Mathlib's
`expSeries_sum_eq` / `NormedSpace.exp_eq_tsum` machinery and
gives `exp(t · J)` as the operator-norm limit.

## Contents

### §1 — Iterate equals monoid power

* **`lindbladJumpChannelIterate_eq_pow`** — the iterated jump
 channel `J^k_iter` equals the Monoid power `J^k` (from
 `Module.End.instMonoid`).

### §2 — Partial-sum identification

* **`lindbladJumpFiniteExpSeries_eq_expSeries_partialSum`** —
 the load-bearing identification:

 `lindbladJumpFiniteExpSeries t L_fn n
 = Σ_{k : Fin n} ((k.val.factorial : ℂ)⁻¹)
 • ((t : ℂ) • lindbladJumpChannel L_fn)^k.val`.

The right-hand side is the n-th partial sum of `NormedSpace.exp`
applied to `(t : ℂ) • lindbladJumpChannel L_fn`.

## Connection to the full Lindblad theorem

Combined with:
* `lindbladJumpFiniteExpSeries_isCompletelyPositive` (commit `b81e8ef9`):
 each partial sum is CP;
* `isCompletelyPositive_of_pointwise_tendsto` (commit `6482f326`):
 CP is closed under pointwise tendsto;
* Mathlib's `NormedSpace.exp_eq_tsum` (when applicable):
 partial sums converge to `NormedSpace.exp` in operator norm;

we obtain `(NormedSpace.exp ((t : ℂ) • lindbladJumpChannel L_fn)).IsCompletelyPositive`
for `t ≥ 0`. The final composition is the Lindblad CP-semigroup
theorem for the multi-jump exponential.

## Scope

* This file provides the **algebraic identification**; the
 operator-norm convergence of the partial sums to
 `NormedSpace.exp` requires Mathlib's algebra typeclass setup
 on `MatrixMap d d ℂ` (specifically `Module.End ℂ (Matrix d d ℂ)`
 as a normed algebra). For finite-dim matrices, this
 infrastructure exists in
 `Mathlib.Analysis.Normed.Algebra.Exponential` but its
 application is downstream.

## References

* Lindblad 1976 *Commun. Math. Phys.* 48, 119 — Theorem 1.
* `Mathlib.Algebra.Group.Action.Defs.smul_pow` — `(t • J)^n = t^n • J^n`.
* `Mathlib.Algebra.Module.LinearMap.End` —
 `Module.End.instMonoid` (composition = monoid mul).
* `Physlib.QuantumMechanics.Lindblad.JumpFlowFiniteExp`
 (commit `b81e8ef9`) — `lindbladJumpFiniteExpSeries`.

-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Lindblad

open Matrix Complex

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]

/-! ## §1 — Iterate equals Module.End monoid power -/

/-- **The iterated jump channel `J^k_iter` equals the Module.End
monoid power `J^k`**.

In `Module.End R M` with composition as multiplication and
`LinearMap.id` as one (commit `Module.End.instMonoid`), the
Monoid power `x^k` is defined by

  `x^0 := 1 = LinearMap.id`,
  `x^{k+1} := x * x^k = LinearMap.comp x x^k`.

This matches our `lindbladJumpChannelIterate` definition exactly,
so they coincide by induction on `k`. -/
theorem lindbladJumpChannelIterate_eq_pow
    (L_fn : ι → Matrix d d ℂ) (k : ℕ) :
    lindbladJumpChannelIterate L_fn k
      = (lindbladJumpChannel L_fn)^k := by
  induction k with
  | zero =>
    unfold lindbladJumpChannelIterate
    rfl
  | succ n ih =>
    unfold lindbladJumpChannelIterate
    rw [ih]
    rw [pow_succ']
    rfl

/-! ## §2 — Partial-sum identification -/

/-- **:`lindbladJumpFiniteExpSeries` is the `expSeries`
partial sum**.

  `lindbladJumpFiniteExpSeries t L_fn n
    = ∑ k : Fin n, ((k.val.factorial : ℂ)⁻¹)
                      • ((t : ℂ) • lindbladJumpChannel L_fn)^k.val`.

The right-hand side is the n-th partial sum of `NormedSpace.exp`
applied to `(t : ℂ) • lindbladJumpChannel L_fn` (Mathlib's
exponential power series).

**Algebraic core**: each summand transforms as
`(t^k / k! : ℂ) • J^k_iter = ((k!)⁻¹) • t^k • J^k = ((k!)⁻¹) • (t • J)^k`,
using `smul_pow` for the last step. -/
theorem lindbladJumpFiniteExpSeries_eq_expSeries_partialSum
    (t : ℝ) (L_fn : ι → Matrix d d ℂ) (n : ℕ) :
    lindbladJumpFiniteExpSeries t L_fn n
      = ∑ k : Fin n,
          ((k.val.factorial : ℂ)⁻¹) •
            (((t : ℂ)) • lindbladJumpChannel L_fn)^k.val := by
  unfold lindbladJumpFiniteExpSeries
  apply Finset.sum_congr rfl
  intro k _
  -- Goal: ((t^k.val / k.val.factorial : ℝ) : ℂ) • J^k_iter
  --     = ((k.val.factorial : ℂ)⁻¹) • ((t : ℂ) • J)^k.val
  rw [lindbladJumpChannelIterate_eq_pow]
  -- Use smul_pow: (t • J)^k = t^k • J^k
  rw [smul_pow]
  -- Goal: ((t^k.val / k.val.factorial : ℝ) : ℂ) • J^k.val
  --     = ((k.val.factorial : ℂ)⁻¹) • ((t : ℂ)^k.val • J^k.val)
  rw [smul_smul]
  congr 1
  -- Goal: ((t^k.val / k.val.factorial : ℝ) : ℂ)
  --     = (k.val.factorial : ℂ)⁻¹ * (t : ℂ)^k.val
  push_cast
  ring

end Physlib.QuantumMechanics.Lindblad

end
