/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Complex.Basic

/-!
# Positive-semidefinite matrices are closed under limits

CP-cone closure step toward completing the Lindblad CP-semigroup
theorem.  This file provides the **load-bearing analytic step**: the
set of positive-semidefinite matrices is closed under filter
limits in the Pi topology on `Matrix d d ℂ`.

  `Tendsto f F (𝓝 M)  ∧  (∀ a, (f a).PosSemidef)  ⟹  M.PosSemidef`.

This is the Mathlib-level closure that, combined with the
finite-truncation CP property of the Lindblad jump-flow series
(commit `b81e8ef9`), would yield the full CP property of
`exp(t · J)` once the partial sums of the operator-norm
exponential are identified with the truncated series.

## Why this is foundational

The full Lindblad CP-semigroup theorem (Lindblad 1976, Theorem 1)
requires closing the cone of CP maps under operator-norm limits in
the algebra of `MatrixMap d d ℂ` superoperators.  The analytic
heart of this closure is **PSD-cone closedness at the matrix
level** — once we have this, the lift to `IsPositive` (positivity
preservation of maps), then to `IsCompletelyPositive`
(complete positivity via tensor extensions), follows by similar
continuity arguments.

This file provides the **matrix-level PSD closure**:

* `posSemidef_isClosed` — the set of PSD matrices is closed
  in the Pi topology.
* `posSemidef_of_tendsto` — Tendsto preservation of PSD.

These are the load-bearing topological steps for the analytic
direction of the Lindblad theorem.

## Contents


* `isHermitian_of_tendsto` — Hermitian property is preserved
  under filter limits (continuity of `conjTranspose`).


* `posSemidef_of_tendsto` — PSD property is preserved under
  filter limits (Hermitian closure + `Ici 0` closure on inner
  products).

## What remains downstream for the full Lindblad theorem

* **Lift to `IsPositive`**: if `f : ι → MatrixMap d d ℂ` with
  `Tendsto f F (𝓝 g)` and each `f a` is positive (preserves PSD),
  then `g` is positive.  Requires evaluation continuity
  `(f a)(ρ) → g(ρ)` for each ρ.

* **Lift to `IsCompletelyPositive`**: tensor extension
  preservation under limits.  Requires continuity of the
  Kronecker tensor at the MatrixMap level.

* **Identification of partial sums with `expSeries`**: connect
  `lindbladJumpFiniteExpSeries t L_fn n` to the n-th partial sum
  of `NormedSpace.exp (t • lindbladJumpChannel L_fn)`.

* **Apply closure**: take `n → ∞` of the partial sums, apply
  PSD/CP closure to conclude `exp(t · J).IsCompletelyPositive`.

These are progressively more analytic but all derivable from the
matrix-level PSD closure shipped here.

## References

* Lindblad 1976 *Commun. Math. Phys.* 48, 119 — Theorem 1.
* `Mathlib.LinearAlgebra.Matrix.PosDef` — `Matrix.PosSemidef`,
  `posSemidef_iff_dotProduct_mulVec`.
* `Mathlib.Topology.Instances.Matrix` — `Continuous.matrix_mul`,
  `Continuous.matrix_conjTranspose`, Pi topology on matrices.
* `Physlib.QuantumMechanics.Lindblad.JumpFlowFiniteExp` (commit
  `b81e8ef9`) — finite-truncation CP property to be combined
  with this closure for the full Lindblad theorem.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Lindblad

open Matrix Complex Filter Topology
open scoped ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d]


/-- **Hermitian property is closed under filter limits**.

If `f : ι → Matrix d d ℂ` is a family of Hermitian matrices and
`Tendsto f F (𝓝 M)` along some filter `F` with `F ≠ ⊥`, then
`M` is Hermitian.

**Proof**: `M.IsHermitian ↔ M^† = M`.  By continuity of
`conjTranspose`, `(f a)^† → M^†` along `F`.  By hypothesis
`(f a)^† = f a` (each `f a` Hermitian), so `(f a)^† → M`.  By
uniqueness of limits, `M^† = M`. -/
lemma isHermitian_of_tendsto
    {ι : Type*} {F : Filter ι} [F.NeBot]
    {f : ι → Matrix d d ℂ} {M : Matrix d d ℂ}
    (h_tendsto : Tendsto f F (𝓝 M))
    (h_herm : ∀ a, (f a).IsHermitian) :
    M.IsHermitian := by
  -- `conjTranspose` is continuous
  have h_ct : Tendsto (fun a => (f a)ᴴ) F (𝓝 Mᴴ) :=
    (continuous_id.matrix_conjTranspose.tendsto M).comp h_tendsto
  -- but `(f a)^† = f a` so it also tends to M
  have h_eq : (fun a => (f a)ᴴ) = f := by
    funext a; exact h_herm a
  rw [h_eq] at h_ct
  -- M = M^† by uniqueness
  exact (tendsto_nhds_unique h_tendsto h_ct).symm


/-- **PSD property is closed under filter limits**.

If `f : ι → Matrix d d ℂ` is a family of positive-semidefinite
matrices and `Tendsto f F (𝓝 M)`, then `M.PosSemidef`.

**Proof**: PSD `≡` Hermitian + nonneg quadratic form.
* Hermitian limit closure: `isHermitian_of_tendsto`.
* For each `x : d → ℂ`, the function `M ↦ star x ⬝ᵥ (M *ᵥ x)` is
  continuous (matrix-vector mul + dot product, all continuous on
  finite-dim).  The limit of non-negative complex values is
  non-negative (under `ComplexOrder`, the set `{z : 0 ≤ z}` is
  closed).
* Combine. -/
lemma posSemidef_of_tendsto
    {ι : Type*} {F : Filter ι} [F.NeBot]
    {f : ι → Matrix d d ℂ} {M : Matrix d d ℂ}
    (h_tendsto : Tendsto f F (𝓝 M))
    (h_psd : ∀ a, (f a).PosSemidef) :
    M.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · -- Hermitian limit
    apply isHermitian_of_tendsto h_tendsto
    intro a
    exact (h_psd a).1
  · -- Inner product nonneg limit
    intro x
    -- For each a, 0 ≤ star x ⬝ᵥ ((f a) *ᵥ x)
    have h_each : ∀ a, (0 : ℂ) ≤ star x ⬝ᵥ ((f a) *ᵥ x) :=
      fun a => Matrix.PosSemidef.dotProduct_mulVec_nonneg (h_psd a) x
    -- The function M ↦ star x ⬝ᵥ (M *ᵥ x) is continuous
    have h_cont : Continuous (fun M : Matrix d d ℂ => star x ⬝ᵥ (M *ᵥ x)) := by
      apply Continuous.dotProduct continuous_const
      exact Continuous.matrix_mulVec continuous_id continuous_const
    -- Tendsto + continuity → tendsto of composition
    have h_innerProd_tendsto :
        Tendsto (fun a => star x ⬝ᵥ ((f a) *ᵥ x)) F (𝓝 (star x ⬝ᵥ (M *ᵥ x))) :=
      (h_cont.tendsto M).comp h_tendsto
    -- Set.Ici 0 is closed, limit of points in Ici 0 stays in Ici 0
    exact ge_of_tendsto h_innerProd_tendsto (Filter.Eventually.of_forall h_each)

end Physlib.QuantumMechanics.Lindblad

end
