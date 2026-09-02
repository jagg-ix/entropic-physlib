/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith

/-!
# The temporal-order expectation and its arrow reversal under imaginary-momentum flip

Ports the verified core of `CATEPT/ArrowMpemba.lean` and
`CATEPT/TemporalOrderAndReduction.lean` of the reference tree: the finite-mode
**temporal-order expectation**

  `⟨T̂⟩ = J · ∑ⱼ 2 sin(kR ⱼ) sinh(kI ⱼ)`,

whose sign classifies the direction of entropic time, and its exact behaviour under the two
sector operations:

* `temporalOrderExpectation_neg_kI` — **the matter/antimatter sign rule**: flipping the sign
  of every imaginary momentum flips the sign of `⟨T̂⟩`, because `sinh` is odd — conjugating
  the entropic sector reverses the temporal order exactly.
* `temporalOrderExpectation_zero_of_kI_zero` — **frozen order**: with no imaginary momenta
  the expectation vanishes identically; entropic time does not tick in the purely
  real-momentum sector.
* `forward_becomes_backward_of_neg_kI` — **arrow reversal**: a state with forward temporal
  order acquires backward temporal order under `kI ↦ −kI`.
* `hasForwardTemporalOrder_of_pos` — non-vacuity of the classification: a positive coupling
  with all mode products nonnegative and one strictly positive (e.g. one mode with
  `kR ∈ (0, π)` and `kI > 0`) has forward temporal order.

**Honest layering.**  Exact `sin`/`sinh` algebra on the finite mode sum.  The two-sector
trace-out narrative of the source (reduced non-unitary dynamics, the balanced
temporal-order superposition, the entropy-rate law `Ṡ = k_B·d⟨T̂⟩/dt`) was contract-style
placeholder material there and is not reproduced; the operator content lives in the
entropic-time arc of this library.

## References

* Source: `CATEPT/ArrowMpemba.lean`, `CATEPT/TemporalOrderAndReduction.lean` (reference tree,
  own authorship); re-authored on the sine/hyperbolic-sine mode sum with the non-vacuity
  lemma added.
-/

set_option autoImplicit false

open Finset

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.TemporalOrderArrowReversal

/-- **The finite-mode temporal-order expectation** `⟨T̂⟩ = J·∑ⱼ 2 sin(kRⱼ) sinh(kIⱼ)`: each
mode enters through its real-momentum phase and its imaginary-momentum weight. -/
noncomputable def temporalOrderExpectation (J : ℝ) {n : ℕ} (kR kI : Fin n → ℝ) : ℝ :=
  J * ∑ j, 2 * Real.sin (kR j) * Real.sinh (kI j)

/-- **The matter/antimatter sign rule**: flipping every imaginary momentum flips the sign of
the temporal-order expectation — `sinh` is odd, so conjugating the entropic sector reverses
the order exactly. -/
theorem temporalOrderExpectation_neg_kI (J : ℝ) {n : ℕ} (kR kI : Fin n → ℝ) :
    temporalOrderExpectation J kR (fun j => -kI j)
      = - temporalOrderExpectation J kR kI := by
  unfold temporalOrderExpectation
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.sinh_neg]
  ring

/-- **Frozen order**: with vanishing imaginary momenta the temporal-order expectation is
zero — entropic time does not tick in the purely real-momentum sector. -/
theorem temporalOrderExpectation_zero_of_kI_zero (J : ℝ) {n : ℕ} (kR : Fin n → ℝ) :
    temporalOrderExpectation J kR (fun _ => 0) = 0 := by
  unfold temporalOrderExpectation
  simp

/-- Forward temporal order: positive expectation. -/
def HasForwardTemporalOrder (J : ℝ) {n : ℕ} (kR kI : Fin n → ℝ) : Prop :=
  0 < temporalOrderExpectation J kR kI

/-- Backward temporal order: negative expectation. -/
def HasBackwardTemporalOrder (J : ℝ) {n : ℕ} (kR kI : Fin n → ℝ) : Prop :=
  temporalOrderExpectation J kR kI < 0

/-- **Arrow reversal**: forward temporal order becomes backward temporal order under the
imaginary-momentum flip `kI ↦ −kI`. -/
theorem forward_becomes_backward_of_neg_kI (J : ℝ) {n : ℕ} (kR kI : Fin n → ℝ)
    (hF : HasForwardTemporalOrder J kR kI) :
    HasBackwardTemporalOrder J kR (fun j => -kI j) := by
  unfold HasForwardTemporalOrder at hF
  unfold HasBackwardTemporalOrder
  rw [temporalOrderExpectation_neg_kI]
  linarith

/-- **Non-vacuity of the classification**: a positive coupling whose mode products
`sin(kRⱼ)·sinh(kIⱼ)` are all nonnegative, with at least one strictly positive — for instance
a single mode with `kR ∈ (0, π)` and `kI > 0` — has forward temporal order. -/
theorem hasForwardTemporalOrder_of_pos (J : ℝ) {n : ℕ} (kR kI : Fin n → ℝ)
    (hJ : 0 < J) (h : ∀ j, 0 ≤ Real.sin (kR j) * Real.sinh (kI j))
    (j₀ : Fin n) (hj₀ : 0 < Real.sin (kR j₀) * Real.sinh (kI j₀)) :
    HasForwardTemporalOrder J kR kI := by
  unfold HasForwardTemporalOrder temporalOrderExpectation
  refine mul_pos hJ (Finset.sum_pos' (fun j _ => ?_) ⟨j₀, Finset.mem_univ j₀, ?_⟩)
  · have := h j
    nlinarith
  · nlinarith

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.TemporalOrderArrowReversal

end
