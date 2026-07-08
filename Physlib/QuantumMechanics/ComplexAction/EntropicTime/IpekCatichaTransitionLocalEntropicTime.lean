/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsTransitionProbability

/-!
# The short-step transition probability and the local entropic-time clock (Ipek–Caticha)

Extends the entropic-dynamics short-step transition probability (`EntropicDynamicsTransitionProbability`, which
already includes the curved-space `√g` drift and variance, Eqs. 6–8) with the pieces specific to Ipek–Caticha
(arXiv:2006.05036): the **maximum-entropy completion of the square** taking the prior (Eq. 4) to the transition
(Eq. 6), the **drift + fluctuation decomposition** `Δχ = ⟨Δχ⟩ + Δw` (Eq. 7), and — the new ingredient for a
*curved-space, local* dynamics — the **local entropic-time clock** `α_x = 1/δξ⊥_x` (Eq. 12), under which the
fluctuation variance is the local proper time `δξ⊥/√g`, giving a Wiener process with a *position-dependent* clock.

* the **transition completes the prior square** `½α(Δχ−b)² = ½αΔχ² − αbΔχ + ½αb²` (`transition_completes_prior_square`)
 — the prior Gaussian `½αΔχ²` (Eq. 4) plus the linear drift-constraint term is the drifted transition action
 (Eq. 6), the maximum-entropy update;
* the **transition weight depends only on the fluctuation** `Δw = Δχ − b`: `P(b + Δw) = e^{−αΔw²/2}`
 (`edTransitionWeight_fluctuation`) — the generic change `Δχ = ⟨Δχ⟩ + Δw` (Eq. 7) with a zero-mean Gaussian
 fluctuation `Δw`;
* the **local entropic-time clock** `α = 1/δξ⊥` gives fluctuation variance `⟨Δw²⟩ = δξ⊥/√g`
 (`local_clock_variance`, Eq. 12) — the variance is the local proper time, so the fluctuations increase linearly
 with the local clock (`local_clock_variance_mono`), a Wiener process paced by a position-dependent `δξ⊥`.

So the curved-space entropic dynamics is a Brownian motion in the field with a *local* clock: the maximum-entropy
transition is the drifted Gaussian, the step is drift plus fluctuation, and the fluctuation variance is the local
proper time `δξ⊥/√g` — the defining Wiener property with a clock that ticks differently at each spatial point.

* **§A — the maximum-entropy completion of the square** (`transition_completes_prior_square`).
* **§B — the drift + fluctuation decomposition** (`edTransitionWeight_fluctuation`).
* **§C — the local entropic-time clock** (`entropicTimeMultiplier`, `local_clock_variance`,
 `local_clock_variance_mono`).

The completion of the square, the fluctuation form of the weight, and the local-clock variance
and its monotonicity are exact algebra, reusing `edEntropicAction`, `edTransitionWeight`, and
`edFluctuationVariance`. The functional maximum-entropy derivation, the foliation-invariance of `δξ⊥`, and the
field-theoretic Wiener process are the referenced content. No new axioms.

## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 4, 6, 7, 12; transition probability, local entropic time). Repo
 structure: `EntropicTime.EntropicDynamicsTransitionProbability` (`edTransitionWeight`, `edFluctuationVariance`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsTransitionProbability

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaTransitionLocalEntropicTime

/-! ## §A — the maximum-entropy completion of the square -/

/-- **[The transition completes the prior square] `½α(Δχ−b)² = ½αΔχ² − αbΔχ + ½αb²`.** The maximum-entropy update
takes the uninformative prior action `½αΔχ²` (Ipek–Caticha Eq. 4, the `b = 0` case) and the linear drift-constraint
term `−αbΔχ` into the drifted transition action `½α(Δχ−b)²` (Eq. 6) — completing the square is the maximum-entropy
step. -/
theorem transition_completes_prior_square (α b Δχ : ℝ) :
    edEntropicAction α b Δχ = edEntropicAction α 0 Δχ - α * b * Δχ + α * b ^ 2 / 2 := by
  unfold edEntropicAction
  ring

/-! ## §B — the drift + fluctuation decomposition -/

/-- **[The transition weight depends only on the fluctuation] `P(b + Δw) = e^{−αΔw²/2}`.** Writing the generic
change as `Δχ = ⟨Δχ⟩ + Δw = b + Δw` (Ipek–Caticha Eq. 7), the transition weight is a zero-mean Gaussian in the
fluctuation `Δw` alone — the drift `b` sets the peak, the fluctuation includes the spread. -/
theorem edTransitionWeight_fluctuation (α b Δw : ℝ) :
    edTransitionWeight α b (b + Δw) = Real.exp (-(α * Δw ^ 2 / 2)) := by
  unfold edTransitionWeight edEntropicAction
  congr 1
  ring

/-! ## §C — the local entropic-time clock -/

/-- **The local entropic-time multiplier** `α_x = 1/δξ⊥_x` (Ipek–Caticha Eq. 12) — the Lagrange multiplier is the
inverse local proper time, so that the fluctuation variance measures the local clock. -/
noncomputable def entropicTimeMultiplier (δξ : ℝ) : ℝ := 1 / δξ

/-- **[The local-clock fluctuation variance is the local proper time] `⟨Δw²⟩ = δξ⊥/√g`.** With the entropic-time
multiplier `α = 1/δξ⊥` (Eq. 12), the fluctuation variance `1/(√g α)` is the local proper time `δξ⊥` divided by the
surface density — the variance *is* the local clock, so equal variance increases mark equal `δξ⊥`. -/
theorem local_clock_variance (root_g δξ : ℝ) (hg : root_g ≠ 0) (hδξ : δξ ≠ 0) :
    edFluctuationVariance root_g (entropicTimeMultiplier δξ) = δξ / root_g := by
  unfold edFluctuationVariance entropicTimeMultiplier
  field_simp

/-- **[The fluctuations increase with the local clock] `δξ⊥` monotone.** For a positive surface density, the
fluctuation variance is monotone increasing in the local proper time `δξ⊥` — the defining Wiener/Brownian property,
here with a position-dependent local clock. -/
theorem local_clock_variance_mono (root_g : ℝ) (hg : 0 < root_g) {δξ₁ δξ₂ : ℝ} (h1 : 0 < δξ₁)
    (h : δξ₁ ≤ δξ₂) :
    edFluctuationVariance root_g (entropicTimeMultiplier δξ₁)
      ≤ edFluctuationVariance root_g (entropicTimeMultiplier δξ₂) := by
  rw [local_clock_variance root_g δξ₁ hg.ne' h1.ne',
    local_clock_variance root_g δξ₂ hg.ne' (by linarith)]
  gcongr

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaTransitionLocalEntropicTime

end
