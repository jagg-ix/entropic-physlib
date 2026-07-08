/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.BadialiForwardBackwardDecomposition
public import Physlib.StatisticalMechanics.DiscreteEntropicTimeTrinity

/-!
# Bridge: Badiali Born density is the complex-action/entropic-time damping envelope

Third bridge in the analytic-gap closure
plan, after `BadialiToMadelung.lean` (Madelung polar form) and
`EquilibriumMatsubaraPeriod.lean` (thermal period).

**The load-bearing identification**:

The Badiali forward–backward decomposition produces a real-valued
Born density (paper Eq. 37):

 `μ(t, x) := φ(t, x) · φ̂(t, x) = |Ψ_Bd(t, x)|²`.

The complex-action/entropic-time discrete entropic-time trinity has a damping
envelope:

 `Λ(n) := exp(−τ_ent(n))`

with monotonically non-decreasing `τ_ent` so that `Λ ≤ 1` and
`Λ` is non-increasing — the **entropic-time arrow of time**.

If we **sample** `μ` at discrete times `t_n` and set

 `τ_ent(n) := −ln(μ(t_n, x))` (Shannon self-information)

then automatically

 `Λ(n) = exp(−τ_ent(n)) = exp(ln(μ(t_n, x))) = μ(t_n, x)`.

**The damping envelope literally IS the Born probability density**.

The structural conditions
* `τ_ent(n) ≥ 0` ⟺ `μ(t_n, x) ≤ 1` (normalisation),
* `τ_ent` non-decreasing ⟺ `μ` non-increasing (Badiali H-theorem
 at a fixed sampling point — paper Eq. 21 in pointwise reading),

connect the trinity's structural structures to Badiali's analytic
conditions, both **without** invoking the PDE-level H-theorem
machinery.

## Why this matters

The previous file `BadialiForwardBackwardDecomposition.lean`
proved `|Ψ_Bd|² = φ·φ̂` as an algebraic Born rule. The file
`BadialiToMadelung.lean` certified this is the same as the
Madelung Born rule. This file makes a *third* identification:
the Born density also IS the complex-action/entropic-time damping envelope — the
information-theoretic damping factor whose monotonicity *encodes
the arrow of time*.

Once this bridge is in place, downstream consumers can use the
existing `Physlib/StatisticalMechanics/DiscreteEntropicTimeTrinity`
machinery (damping bounds, entropic-time monotonicity, free-
propagation limit) on any Badiali forward–backward sampled
density — without further bridge work.

## Contents

### §1 — Trinity from a damping-envelope sequence

* `trinityFromDensitySequence` — constructor: given a positive,
 bounded-by-1, non-increasing density sequence `μ : ℕ → ℝ`,
 builds a `DiscreteEntropicTimeTrinity` whose `dampingEnvelope`
 equals `μ` and whose `τ_ent` is `−ln ∘ μ`.

* `trinityFromDensitySequence_dampingEnvelope_eq` — load-bearing
 identity: the trinity's damping envelope equals `μ` exactly.

### §2 — Bridge from sampled Badiali Born density

* `badialiBornDensitySampled` — convenience definition: the
 pointwise Born density `(φ φ̂)(n) = |Ψ_Bd(φ_n, φ̂_n)|²` of a
 sampled forward–backward pair.

* `badialiBornDensity_eq_normSq` — `μ_n = Complex.normSq Ψ_Bd_n`.

* **`badialiToTrinity_dampingEnvelope_eq_normSq`** — the load-
 bearing theorem: the complex-action/entropic-time damping envelope of the
 Badiali-derived trinity equals the Born probability density
 `|Ψ_Bd|²` exactly.

## Scope

This file uses the **pointwise** sampling convention. Badiali's
H-theorem (paper Eq. 21) is a **functional** statement about
`H(t) = −∫φ ln φ dx − ln V`. The pointwise interpretation
"`φ(t,x)` decreases at peaks during relaxation" is consistent
with the H-theorem but not equivalent to it. The functional
H-theorem is the Fisher-information coercivity statement deferred
to a separate Sobolev-equipped scope.

The bridge here delivers the **structural** entropic-time
machinery (damping bounds, monotonicity) certifying the
information-theoretic interpretation of `|Ψ_Bd|²` at the sampled
level. Phase-2 elevates this to the functional / PDE level.

## References

* Badiali 2005 *J. Phys. A* 38, 2835 §5 — H-theorem Eq. 21.
* `Physlib.StatisticalMechanics.DiscreteEntropicTimeTrinity`.
* `Physlib.QuantumMechanics.Schrodinger.BadialiForwardBackwardDecomposition`.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Schrodinger

open Real Physlib.StatisticalMechanics

/-! ## §1 — Trinity constructor from a density sequence -/

/-- **Trinity from a positive, bounded-by-1, non-increasing
density sequence**.

Given `μ : ℕ → ℝ` satisfying

* `h_pos     : ∀ n, 0 < μ n`,
* `h_le_one  : ∀ n, μ n ≤ 1`,
* `h_mono    : ∀ n, μ (n+1) ≤ μ n`,

constructs a `DiscreteEntropicTimeTrinity` with

* `τ_ent n := −ln(μ n)`     (Shannon self-information),
* `lam n   := ln(μ n) − ln(μ (n+1))` (information increment).

The damping envelope of this trinity equals `μ` exactly. -/
def trinityFromDensitySequence
    (μ : ℕ → ℝ)
    (h_pos : ∀ n, 0 < μ n)
    (h_le_one : ∀ n, μ n ≤ 1)
    (h_mono : ∀ n, μ (n+1) ≤ μ n) :
    DiscreteEntropicTimeTrinity where
  X                 := fun _ => 0
  τ_ent             := fun n => -Real.log (μ n)
  lam               := fun n => Real.log (μ n) - Real.log (μ (n+1))
  lam_nonneg        := fun n => by
    have hpos_n   : 0 < μ n := h_pos n
    have hpos_n1  : 0 < μ (n+1) := h_pos (n+1)
    have h_log_mono : Real.log (μ (n+1)) ≤ Real.log (μ n) :=
      Real.log_le_log hpos_n1 (h_mono n)
    linarith
  τ_ent_zero_nonneg := by
    show 0 ≤ -Real.log (μ 0)
    have h_log_le_zero : Real.log (μ 0) ≤ 0 :=
      Real.log_nonpos (le_of_lt (h_pos 0)) (h_le_one 0)
    linarith
  τ_ent_succ        := fun n => by
    show -Real.log (μ (n+1)) = -Real.log (μ n) + (Real.log (μ n) - Real.log (μ (n+1)))
    ring
  A                 := μ

/-- **Trinity damping envelope equals the density sequence**.

The load-bearing identity: the `trinityFromDensitySequence` was
constructed so that

  `dampingEnvelope n = exp(−τ_ent n) = exp(ln(μ n)) = μ n`.

This is the information-theoretic identification at the sampled
level. -/
theorem trinityFromDensitySequence_dampingEnvelope_eq
    (μ : ℕ → ℝ)
    (h_pos : ∀ n, 0 < μ n)
    (h_le_one : ∀ n, μ n ≤ 1)
    (h_mono : ∀ n, μ (n+1) ≤ μ n)
    (n : ℕ) :
    (trinityFromDensitySequence μ h_pos h_le_one h_mono).dampingEnvelope n = μ n := by
  unfold DiscreteEntropicTimeTrinity.dampingEnvelope
        trinityFromDensitySequence
  simp only
  -- Goal: Real.exp (-(- Real.log (μ n))) = μ n
  rw [neg_neg, Real.exp_log (h_pos n)]

/-! ## §2 — Badiali sampled Born density -/

/-- **Sampled Badiali Born density**: at step `n`, the
forward × backward product `(φ n) · (φ̂ n)`.

By Badiali Eq. 37, this is `|Ψ_Bd(φ n, φ̂ n)|²` — the Born
probability density at the sampled instant. -/
def badialiBornDensitySampled (φ φ_hat : ℕ → ℝ) (n : ℕ) : ℝ :=
  φ n * φ_hat n

/-- **Sampled Born density equals normSq of `badialiPsi`**.

Direct application of `badialiPsi_normSq` at each sample. -/
theorem badialiBornDensity_eq_normSq
    {φ φ_hat : ℕ → ℝ} (n : ℕ)
    (hφ : 0 < φ n) (hφ_hat : 0 < φ_hat n) :
    badialiBornDensitySampled φ φ_hat n
      = Complex.normSq (badialiPsi (φ n) (φ_hat n)) := by
  unfold badialiBornDensitySampled
  rw [badialiPsi_normSq hφ hφ_hat]

/-! ## §3 — Theorem: damping envelope IS Born probability -/

/-- **:the complex-action/entropic-time damping envelope equals the Badiali
Born density (and thus `|Ψ_Bd|²`)**.

Given a forward–backward sample sequence `(φ_n, φ̂_n)` with each
`φ_n · φ̂_n ∈ (0, 1]` and the **pointwise H-theorem hypothesis**
`(φ_{n+1} · φ̂_{n+1}) ≤ (φ_n · φ̂_n)` (Badiali Eq. 21 at the
sampling point during relaxation), the damping envelope of the
induced entropic-time trinity equals the Born probability density
`|Ψ_Bd|²` at every sample.

This is the **third Born-rule identification** for the Badiali
decomposition (the others: Badiali algebraic `badialiPsi_normSq`,
Madelung polar `badialiPsi_normSq_eq_madelungDensity`).

**Physical interpretation**: the information-theoretic damping
factor encoding the arrow of time in complex-action/entropic-time *is* the
quantum-mechanical Born probability density.  Forward–backward
forward-decreasing densities are exactly the regime where the
quantum probability acts as an entropic-time damping. -/
theorem badialiToTrinity_dampingEnvelope_eq_normSq
    (φ φ_hat : ℕ → ℝ)
    (hφ : ∀ n, 0 < φ n)
    (hφ_hat : ∀ n, 0 < φ_hat n)
    (h_le_one : ∀ n, badialiBornDensitySampled φ φ_hat n ≤ 1)
    (h_mono : ∀ n, badialiBornDensitySampled φ φ_hat (n+1)
                    ≤ badialiBornDensitySampled φ φ_hat n)
    (n : ℕ) :
    (trinityFromDensitySequence
        (badialiBornDensitySampled φ φ_hat)
        (fun k => mul_pos (hφ k) (hφ_hat k))
        h_le_one
        h_mono).dampingEnvelope n
      = Complex.normSq (badialiPsi (φ n) (φ_hat n)) := by
  rw [trinityFromDensitySequence_dampingEnvelope_eq]
  exact badialiBornDensity_eq_normSq n (hφ n) (hφ_hat n)

end Physlib.QuantumMechanics.Schrodinger

end
