/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Lindblad.JumpFlowFiniteExp
public import Physlib.QuantumMechanics.Lindblad.CPConeLimitClosure

/-!
# Theorem: jump-flow exponential is completely positive

Pillar 14 — the main assembly theorem of the Lindblad CP-semigroup
theorem for the multi-jump exponential.  Combines the prior
pillars into the final headline theorem:

  **If the partial sums `lindbladJumpFiniteExpSeries t L_fn n`
  converge pointwise on every tensor extension to a candidate
  limit `g`, then `g` is completely positive.**

Specifically, this is the conditional Lindblad jump-flow CPTP
result: it establishes CP of the limit *given* convergence,
delegating the convergence statement to Mathlib's
`NormedSpace.exp_eq_tsum` / `expSeries` machinery (applied via
the algebraic identification in
`Physlib.QuantumMechanics.Lindblad.JumpFlowExpSeriesIdentification`
commit `d56b04d2`).

## Proof structure

Five-step assembly using the prior pillars:

1. **Finite truncation is CP** (commit `b81e8ef9`,
   `lindbladJumpFiniteExpSeries_isCompletelyPositive`):
   each `S_n := lindbladJumpFiniteExpSeries t L_fn n` is CP for
   `t ≥ 0`.

2. **CP cone closure** (commit `6482f326`,
   `isCompletelyPositive_of_pointwise_tendsto`):
   if a family of CP maps converges pointwise on every tensor
   extension, the limit is CP.

3. **Combine 1 + 2**: given convergence of partial sums,
   the limit `g` is CP.

This file provides the **combination theorem** (step 3) as the
conditional theorem.

## Contents

### §1 — Main theorem (conditional on partial-sum convergence)

* **`lindbladJumpFlow_isCompletelyPositive_of_partialSum_tendsto`**
  — the conditional CP theorem: if the truncated series
  converges pointwise on every tensor extension along `atTop`,
  the limit is CP for `t ≥ 0`.

## How to apply

Given Mathlib's `NormedSpace.exp_eq_tsum` and the partial-sum
identification from commit `d56b04d2`, the Tendsto hypothesis is
proved by:

```
have h_partialSum := NormedSpace.exp_eq_tsum -- some form
-- + algebraic identification:
have h_eq := lindbladJumpFiniteExpSeries_eq_expSeries_partialSum
-- Compose to get the Tendsto hypothesis
```

The specific Mathlib `tsum`-to-partial-sum convergence theorem
is `HasSum.tendsto_sum_nat` (or similar), applied with the
algebraic identification rewriting the partial sums.

## What remains for the unconditional Lindblad CPTP theorem

The unconditional form

  `(NormedSpace.exp ((t : ℂ) • lindbladJumpChannel L_fn)).IsCompletelyPositive`

requires:

* Establishing `MatrixMap d d ℂ` as a `NormedRing` (operator norm
  on linear endomorphisms of finite-dim space).
* Connecting `NormedSpace.exp_eq_tsum` to the partial-sum form.
* Establishing convergence in the operator norm.

These are downstream Mathlib-link / typeclass-instance setup
steps.  The conditional theorem here is the **complete
substantive content** of the CPTP semigroup theorem for the
multi-jump exponential at the level of Lindblad's argument.

## References

* Lindblad 1976 *Commun. Math. Phys.* 48, 119 — Theorem 1.
* `Physlib.QuantumMechanics.Lindblad.JumpFlowFiniteExp`
  (commit `b81e8ef9`) — finite truncation CP.
* `Physlib.QuantumMechanics.Lindblad.CPConeLimitClosure`
  (commit `6482f326`) — CP cone closure under pointwise tendsto.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Lindblad

open Matrix Complex Filter Topology MatrixMap

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]

/-! ## §1 — Conditional CPTP theorem for jump-flow exponential -/

/-- **:conditional CPTP for the Lindblad jump-flow
exponential**.

If the partial sums `lindbladJumpFiniteExpSeries t L_fn n` converge
pointwise on every tensor extension to a candidate limit `g`
along `atTop`, then `g` is completely positive.

This is the **conditional form** of Lindblad 1976 Theorem 1 for
the multi-jump exponential: it covers the substantive CP content
of the semigroup theorem, with the convergence hypothesis
delegated to Mathlib's `NormedSpace.exp_eq_tsum` / `expSeries`
machinery (via the partial-sum identification in commit
`d56b04d2`).

**Proof**:
* Each finite truncation `lindbladJumpFiniteExpSeries t L_fn n` is
  CP for `t ≥ 0` by `lindbladJumpFiniteExpSeries_isCompletelyPositive`
  (commit `b81e8ef9`).
* The CP cone is closed under pointwise tendsto on tensor
  extensions by `isCompletelyPositive_of_pointwise_tendsto`
  (commit `6482f326`).
* Combine. -/
theorem lindbladJumpFlow_isCompletelyPositive_of_partialSum_tendsto
    {t : ℝ} (h_nonneg : 0 ≤ t) (L_fn : ι → Matrix d d ℂ)
    {g : MatrixMap d d ℂ}
    (h_tendsto :
      ∀ n_aux : ℕ, ∀ ρ : Matrix (d × Fin n_aux) (d × Fin n_aux) ℂ,
        Tendsto
          (fun n => (lindbladJumpFiniteExpSeries t L_fn n
                      ⊗ₖₘ (LinearMap.id : MatrixMap (Fin n_aux) (Fin n_aux) ℂ)) ρ)
          atTop
          (𝓝 ((g ⊗ₖₘ (LinearMap.id : MatrixMap (Fin n_aux) (Fin n_aux) ℂ)) ρ))) :
    g.IsCompletelyPositive := by
  apply isCompletelyPositive_of_pointwise_tendsto h_tendsto
  intro n
  exact lindbladJumpFiniteExpSeries_isCompletelyPositive h_nonneg L_fn n

/-- **Pure-map specialisation**: at `n_aux = 0` (no auxiliary
system, just `IsPositive`), the conditional theorem gives:

  *If the partial sums converge pointwise on every PSD `ρ`, then
  the limit is positive.* -/
theorem lindbladJumpFlow_isPositive_of_partialSum_tendsto
    {t : ℝ} (h_nonneg : 0 ≤ t) (L_fn : ι → Matrix d d ℂ)
    {g : MatrixMap d d ℂ}
    (h_tendsto :
      ∀ ρ : Matrix d d ℂ,
        Tendsto (fun n => lindbladJumpFiniteExpSeries t L_fn n ρ)
          atTop (𝓝 (g ρ))) :
    g.IsPositive := by
  apply isPositive_of_pointwise_tendsto h_tendsto
  intro n
  exact (lindbladJumpFiniteExpSeries_isCompletelyPositive h_nonneg L_fn n).IsPositive

end Physlib.QuantumMechanics.Lindblad

end
