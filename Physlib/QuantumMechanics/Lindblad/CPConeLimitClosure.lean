/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Lindblad.PosSemidefLimitClosure
public import QuantumInfo.Channels.Unbundled

/-!
# CP-cone closure under filter limits — lift from PSD closure

Pillar 12 of the closure-plan stack toward the full Lindblad
CP-semigroup theorem.  Lifts the matrix-level PSD limit closure
(commit `240decd9`) to the **`MatrixMap` superoperator level**:

* `IsPositive` cone closure
* `IsCompletelyPositive` cone closure

These are the **superoperator-level analytic theorems** that
combine with the finite-truncation CP property (commit `b81e8ef9`)
and the partial-sum convergence (downstream Mathlib link, pillar
13) to yield the full `exp(t · J).IsCompletelyPositive` result.

## Strategy

Both lifts use **pointwise convergence** on evaluations, sidestepping
the topology question on `MatrixMap d d ℂ` itself.

For `IsPositive`:
* Given `f : ι → MatrixMap d d ℂ` and `g : MatrixMap d d ℂ` with
  `∀ ρ, Tendsto (fun a => f a ρ) F (𝓝 (g ρ))` (pointwise
  convergence on evaluations) and each `f a` positive,
* For any PSD `ρ`: `(f a) ρ` is PSD (positivity), `(f a) ρ → g ρ`
  (hypothesis), so `g ρ` is PSD by `posSemidef_of_tendsto`
  (commit `240decd9`).

For `IsCompletelyPositive`:
* Apply the same lift to each tensor extension `f ⊗ id_n`.

## Contents


* **`isPositive_of_pointwise_tendsto`** — `IsPositive` is
  preserved under pointwise filter convergence on evaluations.


* **`isCompletelyPositive_of_pointwise_tendsto`** — `IsCompletelyPositive`
  is preserved under pointwise filter convergence on all tensor
  extensions' evaluations.

## Connection to the Lindblad theorem

Combined with the finite-truncation CP property (commit
`b81e8ef9`), the **assembly for the Lindblad jump-flow theorem**
becomes:

```
1. Show NormedSpace.exp(t · J) is the operator-norm limit of
   the partial sums S_n := Σ_{k=0}^{n-1} (k!)⁻¹ • (t·J)^k.
   (Mathlib link: NormedSpace.exp_eq_tsum + tsum convergence.)

2. Identify S_n with lindbladJumpFiniteExpSeries t L_fn n.
   (Algebraic identity.)

3. Each S_n is CP (an earlier version).

4. Operator-norm convergence implies pointwise convergence on
   evaluations (continuity of evaluation maps in finite-dim).

5. By isCompletelyPositive_of_pointwise_tendsto (this commit):
   the limit NormedSpace.exp(t · J) is CP.
```

Step 1 (Mathlib link) and step 2 (algebraic) are the only
remaining downstream pieces for the full Lindblad jump-flow CP
main theorem.

## Honest scope

* These lifts work for **any filter `F` with `[F.NeBot]`** —
  general enough for sequence convergence (`atTop`), filter
  convergence to a point (`𝓝 g`), and combinations.

* The hypothesis is **pointwise convergence at every PSD `ρ`**.
  For CP, the convergence must hold on tensor extensions too.
  In the natural topology on `MatrixMap d d ℂ` (which is
  finite-dim, so any norm), pointwise convergence equals norm
  convergence, but the pointwise form is more flexible for
  applications.

## References

* Lindblad 1976 *Commun. Math. Phys.* 48, 119 — Theorem 1.
* `QuantumInfo.Channels.Unbundled.IsPositive`,
  `IsCompletelyPositive` (definitions).
* `Physlib.QuantumMechanics.Lindblad.PosSemidefLimitClosure`
  (commit `240decd9`) — matrix-level PSD closure.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Lindblad

open Matrix Complex Filter Topology MatrixMap
open scoped ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d]


/-- **:`IsPositive` is closed under pointwise filter
limits on evaluations**.

If `f : ι → MatrixMap d d ℂ` is a family of positive maps and
the evaluations `(f a)(ρ) → g(ρ)` along filter `F` for every PSD
`ρ`, then `g` is positive.

**Proof**: pick PSD `ρ`.  For each `a`, `(f a)(ρ)` is PSD by
positivity of `f a`.  The evaluations converge to `g(ρ)` by
hypothesis.  Apply `posSemidef_of_tendsto` (commit `240decd9`).

This is the **superoperator-level lift** of the matrix-level PSD
closure. -/
lemma isPositive_of_pointwise_tendsto
    {ι : Type*} {F : Filter ι} [F.NeBot]
    {f : ι → MatrixMap d d ℂ} {g : MatrixMap d d ℂ}
    (h_tendsto : ∀ ρ, Tendsto (fun a => f a ρ) F (𝓝 (g ρ)))
    (h_pos : ∀ a, (f a).IsPositive) :
    g.IsPositive := by
  intro ρ h_ρ_psd
  apply posSemidef_of_tendsto (h_tendsto ρ)
  intro a
  exact h_pos a h_ρ_psd


/-- **:`IsCompletelyPositive` is closed under pointwise
filter limits on all tensor extensions** evaluations.

If `f : ι → MatrixMap d d ℂ` is a family of CP maps and for every
auxiliary dimension `n` and every PSD `ρ : Matrix (d × Fin n) (d × Fin n) ℂ`,
the tensor-extension evaluations
`(f a ⊗ₖₘ id_n)(ρ) → (g ⊗ₖₘ id_n)(ρ)` along filter `F`, then `g`
is CP.

**Proof**: apply `isPositive_of_pointwise_tendsto` to each tensor
extension `f a ⊗ₖₘ id_n` at each fixed `n`.

This is the **full lift to the CP cone** — the last superoperator-
level analytic step toward closing the Lindblad CP-semigroup
theorem. -/
lemma isCompletelyPositive_of_pointwise_tendsto
    {ι : Type*} {F : Filter ι} [F.NeBot]
    {f : ι → MatrixMap d d ℂ} {g : MatrixMap d d ℂ}
    (h_tendsto :
      ∀ n : ℕ, ∀ ρ : Matrix (d × Fin n) (d × Fin n) ℂ,
        Tendsto (fun a => (f a ⊗ₖₘ (LinearMap.id : MatrixMap (Fin n) (Fin n) ℂ)) ρ)
          F (𝓝 ((g ⊗ₖₘ (LinearMap.id : MatrixMap (Fin n) (Fin n) ℂ)) ρ)))
    (h_cp : ∀ a, (f a).IsCompletelyPositive) :
    g.IsCompletelyPositive := by
  intro n
  apply isPositive_of_pointwise_tendsto (h_tendsto n)
  intro a
  exact h_cp a n

end Physlib.QuantumMechanics.Lindblad

end
