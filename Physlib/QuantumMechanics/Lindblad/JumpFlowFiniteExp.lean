/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Lindblad.LindbladCPTP

/-!
# Finite-truncated exponential series of the Lindblad jump channel is CP

CP-series-closure proof: the finite-truncated power series

  `Σ_{k=0}^{n-1} (t^k / k!) · J^k`

for the multi-jump Kraus channel `J[L](ρ) = Σ_j L_j · ρ · L_j^†` is
**completely positive** for every `t ≥ 0` and every `n ∈ ℕ`.

This is the **polynomial-in-time CP content** of the Lindblad
jump-flow exponential `exp(t · ℒ_J)`, leveraging the QuantumInfo
CP-closure infrastructure:

* `IsCompletelyPositive.id` — identity is CP,
* `IsCompletelyPositive.comp` — composition of CP is CP,
* `IsCompletelyPositive.smul` (with `0 ≤ x`) — non-negative
  scaling preserves CP,
* `IsCompletelyPositive.finset_sum` — finite sums of CP are CP,
* `lindbladJumpChannel_isCompletelyPositive` (commit `48ddc88d`) —
  the jump channel itself is CP.

## Strategy

1. Iterated composition `J^k := J ∘ J ∘ ... ∘ J` (k times) is CP
   by induction on `k`, using `IsCompletelyPositive.id` (base) and
   `IsCompletelyPositive.comp` (step).

2. Each truncation term `(t^k / k!) · J^k`:
   * `J^k` is CP by (1),
   * `t^k / k!` is non-negative when `t ≥ 0`,
   * `(t^k / k!) · J^k` is CP by `IsCompletelyPositive.smul`.

3. The full finite series `Σ_{k=0}^{n-1} (t^k / k!) · J^k`:
   * sum of CP maps is CP by `IsCompletelyPositive.finset_sum`.

## Where this stops short of the full Lindblad CP theorem

The finite-truncated series is CP for every `n`.  Taking
`n → ∞` should give the matrix exponential
`exp(t · ℒ_J) = lim_{n→∞} Σ_{k=0}^{n-1} (t·ℒ_J)^k / k!` by
`Mathlib.Analysis.Normed.Algebra.Exponential`.

To conclude `exp(t · ℒ_J).IsCompletelyPositive` from the finite-
truncation CP property requires **closure of the CP cone under
operator-norm limits** in the algebra of `MatrixMap d d ℂ`.  This
closure step requires:

* A `NormedRing` / `NormedAlgebra` structure on
  `MatrixMap d d ℂ` (operator norm on linear endomorphisms),
* A closedness theorem `IsClosed {Φ | Φ.IsCompletelyPositive}`,
* Identification of `NormedSpace.exp (t · J)` as the tsum of the
  series.

These are downstream analytic steps; this commit provides the
**combinatorial CP-series content** which is the load-bearing
piece for the limit argument.

## Contents

### §1 — Iterated CP composition

* `lindbladJumpChannelIterate L_fn k` — `J[L]^k` as iterated
  composition.
* `lindbladJumpChannelIterate_isCompletelyPositive` — `J^k` is CP
  for every `k`.

### §2 — Finite-truncated exponential series

* `lindbladJumpFiniteExpSeries t L_fn n`
  `:= Σ_{k=0}^{n-1} (t^k / k!) · J^k`.
* **`lindbladJumpFiniteExpSeries_isCompletelyPositive`** — the
  theorem: `Σ_{k=0}^{n-1} (t^k / k!) · J^k` is CP for `t ≥ 0`.

## References

* Lindblad 1976 *Commun. Math. Phys.* 48, 119 — Theorem 1
  (CP-semigroup characterisation).
* `QuantumInfo.Channels.Unbundled.IsCompletelyPositive` — closure
  theorems (`id`, `comp`, `add`, `smul`, `finset_sum`, `zero`).
* `Physlib.QuantumMechanics.Lindblad.LindbladCPTP` (commit
  `48ddc88d`) — `lindbladJumpChannel_isCompletelyPositive`.

-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Lindblad

open Matrix Complex MatrixMap
open scoped ComplexOrder

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]

/-! ## §1 — Iterated CP composition of the jump channel -/

/-- **Iterated Lindblad jump channel** `J[L]^k` as `k`-fold
linear-map composition:

  `J^0 := id`,
  `J^{k+1} := J ∘ J^k`. -/
def lindbladJumpChannelIterate
    (L_fn : ι → Matrix d d ℂ) : ℕ → MatrixMap d d ℂ
  | 0 => LinearMap.id
  | n + 1 =>
    LinearMap.comp (lindbladJumpChannel L_fn)
      (lindbladJumpChannelIterate L_fn n)

/-- **Iterated jump channel is completely positive** for every
`k ∈ ℕ`.

Proof by induction:
* Base (`k = 0`): identity is CP (`IsCompletelyPositive.id`).
* Step: `J^{k+1} = J ∘ J^k` is CP by composition closure
  (`IsCompletelyPositive.comp`), since both `J` and `J^k` are CP. -/
theorem lindbladJumpChannelIterate_isCompletelyPositive
    (L_fn : ι → Matrix d d ℂ) (k : ℕ) :
    (lindbladJumpChannelIterate L_fn k).IsCompletelyPositive := by
  induction k with
  | zero =>
    unfold lindbladJumpChannelIterate
    exact MatrixMap.IsCompletelyPositive.id
  | succ n ih =>
    unfold lindbladJumpChannelIterate
    exact MatrixMap.IsCompletelyPositive.comp ih
      (lindbladJumpChannel_isCompletelyPositive L_fn)

/-! ## §2 — Finite-truncated exponential series of the jump channel -/

/-- **Finite-truncated exponential series** of the multi-jump
Kraus channel:

  `Σ_{k=0}^{n-1} (t^k / k!) · J^k`,

the polynomial-in-time approximation to `exp(t · J[L])` using `n`
truncation terms. -/
def lindbladJumpFiniteExpSeries
    (t : ℝ) (L_fn : ι → Matrix d d ℂ) (n : ℕ) :
    MatrixMap d d ℂ :=
  ∑ k : Fin n,
    ((((t : ℝ)^k.val / (k.val.factorial : ℝ)) : ℝ) : ℂ) •
      lindbladJumpChannelIterate L_fn k.val

/-- **The complex scalar `(t^k / k!) : ℂ` is non-negative**
under `ComplexOrder` when `t ≥ 0`.

Direct from `Complex.ofReal_nonneg` and non-negativity of
`t^k / k!` as a real number. -/
theorem t_pow_div_factorial_nonneg
    {t : ℝ} (h_nonneg : 0 ≤ t) (k : ℕ) :
    (0 : ℂ) ≤ ((t^k / k.factorial : ℝ) : ℂ) := by
  rw [Complex.zero_le_real]
  apply div_nonneg
  · exact pow_nonneg h_nonneg k
  · exact_mod_cast Nat.factorial_pos k |>.le

/-- **:finite-truncated exponential series of the
Lindblad jump channel is completely positive** for `t ≥ 0`.

  `(Σ_{k=0}^{n-1} (t^k / k!) · J^k).IsCompletelyPositive`.

**Proof**: each summand `(t^k / k!) · J^k` is CP because:
* `J^k` is CP by `lindbladJumpChannelIterate_isCompletelyPositive`,
* the scalar `t^k / k!` is non-negative (real and `≥ 0`),
* non-negative scaling preserves CP by `IsCompletelyPositive.smul`.

The full sum is CP by `IsCompletelyPositive.finset_sum`.

This is the **polynomial-in-time CP content** of the Lindblad
jump-flow exponential — the load-bearing combinatorial step.
The full `exp(t · J[L]).IsCompletelyPositive` follows by passing
to the `n → ∞` limit, which requires the analytic closure of CP
under operator-norm limits (downstream). -/
theorem lindbladJumpFiniteExpSeries_isCompletelyPositive
    {t : ℝ} (h_nonneg : 0 ≤ t)
    (L_fn : ι → Matrix d d ℂ) (n : ℕ) :
    (lindbladJumpFiniteExpSeries t L_fn n).IsCompletelyPositive := by
  unfold lindbladJumpFiniteExpSeries
  apply MatrixMap.IsCompletelyPositive.finset_sum
  intro k
  apply MatrixMap.IsCompletelyPositive.smul
  · exact lindbladJumpChannelIterate_isCompletelyPositive L_fn k.val
  · exact t_pow_div_factorial_nonneg h_nonneg k.val

/-! ## §3 — Specialisation at `n = 0` and `n = 1` -/

/-- **`n = 0` truncation: zero map**.

  `Σ_{k=0}^{-1} ... = 0`,

the empty sum.  Note: the zero map is CP
(`IsCompletelyPositive.zero`), so this is consistent. -/
theorem lindbladJumpFiniteExpSeries_zero_eq
    (t : ℝ) (L_fn : ι → Matrix d d ℂ) :
    lindbladJumpFiniteExpSeries t L_fn 0 = 0 := by
  unfold lindbladJumpFiniteExpSeries
  simp

/-- **`n = 1` truncation: identity**.

  `Σ_{k=0}^{0} (t^k / k!) · J^k = (1 / 0!) · J^0 = id`,

the identity map.  Independent of `t`. -/
theorem lindbladJumpFiniteExpSeries_one_eq
    (t : ℝ) (L_fn : ι → Matrix d d ℂ) :
    lindbladJumpFiniteExpSeries t L_fn 1 = LinearMap.id := by
  unfold lindbladJumpFiniteExpSeries lindbladJumpChannelIterate
  simp

end Physlib.QuantumMechanics.Lindblad

end
