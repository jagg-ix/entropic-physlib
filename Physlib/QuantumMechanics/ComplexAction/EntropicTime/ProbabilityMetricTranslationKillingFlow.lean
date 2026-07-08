/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative
public import Mathlib.MeasureTheory.Group.Integral

/-!
# The CDF-translation Killing flow: an isometry of the Cramér and 1-Wasserstein metrics

Links the CDF probability metrics (`CramerDistanceCDFMetric`) to the **Killing-flow** structure of
`AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative`. A `KillingFlow` there is a one-parameter group of
structure-preserving automorphisms `π_s` (`π_0 = id`, cocycle `π_{s+t} = π_s ∘ π_t`) — the algebraic form of a
metric isometry. Its geometric realization on the probability manifold is the **CDF-translation flow**
`(𝒯_s F)(x) = F(x − s)` (translating a distribution by `s`): it is a one-parameter group *and* an **isometry** of the
Cramér and 1-Wasserstein metrics, which is exactly the **sum invariance** (property (I)) of Bellemare et al. for a
constant shift.

* the **translation is a one-parameter group** `𝒯_0 = id`, `𝒯_{s+t} = 𝒯_s ∘ 𝒯_t` (`cdfTranslate_zero`,
 `cdfTranslate_add`) — the cocycle structure of a `KillingFlow`;
* the **translation is an isometry of the Cramér distance** `l_2²(𝒯_s P, 𝒯_s Q) = l_2²(P, Q)`
 (`cramerDistance_translation_invariant`) and of the **1-Wasserstein distance** `w_1(𝒯_s P, 𝒯_s Q) = w_1(P, Q)`
 (`wasserstein1Distance_translation_invariant`) — from the translation invariance of Lebesgue measure
 (`integral_sub_right_eq_self`); this is the sum invariance `d(A + X, A + Y) = d(X, Y)` of the ideal metric.

So the CDF-translation flow is the **metric Killing flow** of the probability manifold: a one-parameter group
(the cocycle of `KillingFlow`) that preserves the Cramér and Wasserstein distances (an isometry), the geometric
counterpart of the algebraic bracket-preserving `KillingFlow` (`killingFlow_preserves_bracket`). Sum invariance of
the probability metric *is* a Killing symmetry.

* **§A — the CDF-translation one-parameter group** (`cdfTranslate`, `cdfTranslate_zero`, `cdfTranslate_add`).
* **§B — the translation is an isometry (sum invariance)** (`cramerDistance_translation_invariant`,
 `wasserstein1Distance_translation_invariant`).

The one-parameter-group laws and the metric invariances are exact algebra / measure-theoretic
translation invariance, reusing `cramerDistance`, `wasserstein1Distance`, and `integral_sub_right_eq_self`. The full
`KillingFlow` instance on the function ring and the scale-sensitivity (property (S)) are the referenced content;
here the translation Killing flow and its metric isometry are proved. No new axioms.

## References

* M.G. Bellemare et al., arXiv:1705.10743 (property (I) sum invariance); B.S. Kay, R.M. Wald (Killing flow). Repo
 structures: `EntropicTime.CramerDistanceCDFMetric`,
 `AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative` (`KillingFlow`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric
open MeasureTheory

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.ProbabilityMetricTranslationKillingFlow

/-! ## §A — the CDF-translation one-parameter group -/

/-- **The CDF-translation flow** `(𝒯_s F)(x) = F(x − s)` — translating a distribution by `s` (shifting its
cumulative distribution function), the geometric Killing flow of the probability manifold. -/
def cdfTranslate (s : ℝ) (F : ℝ → ℝ) : ℝ → ℝ := fun x => F (x - s)

/-- **[The translation at `0` is the identity] `𝒯_0 = id`.** -/
theorem cdfTranslate_zero (F : ℝ → ℝ) : cdfTranslate 0 F = F := by
  funext x
  simp [cdfTranslate]

/-- **[The translation flow is a one-parameter group] `𝒯_{s+t} = 𝒯_s ∘ 𝒯_t`.** The cocycle law of a `KillingFlow`:
translating by `s + t` is translating by `t` then by `s`. -/
theorem cdfTranslate_add (s t : ℝ) (F : ℝ → ℝ) :
    cdfTranslate (s + t) F = cdfTranslate s (cdfTranslate t F) := by
  funext x
  simp only [cdfTranslate]
  congr 1
  ring

/-! ## §B — the translation is an isometry (sum invariance) -/

/-- **[The translation is an isometry of the Cramér distance] `l_2²(𝒯_s P, 𝒯_s Q) = l_2²(P, Q)`.** Shifting both
distributions by the same constant `s` preserves the Cramér distance — the sum invariance `d(A+X, A+Y) = d(X, Y)`
(Bellemare et al. property (I)), from the translation invariance of Lebesgue measure. The CDF-translation is a
metric Killing flow. -/
theorem cramerDistance_translation_invariant (F_P F_Q : ℝ → ℝ) (s : ℝ) :
    cramerDistance (cdfTranslate s F_P) (cdfTranslate s F_Q) = cramerDistance F_P F_Q := by
  unfold cramerDistance cdfTranslate
  exact integral_sub_right_eq_self (fun x => (F_P x - F_Q x) ^ 2) s

/-- **[The translation is an isometry of the 1-Wasserstein distance] `w_1(𝒯_s P, 𝒯_s Q) = w_1(P, Q)`.** The
1-Wasserstein / `l_1` distance is likewise sum invariant under a constant shift — a Killing isometry of the
probability metric. -/
theorem wasserstein1Distance_translation_invariant (F_P F_Q : ℝ → ℝ) (s : ℝ) :
    wasserstein1Distance (cdfTranslate s F_P) (cdfTranslate s F_Q) = wasserstein1Distance F_P F_Q := by
  unfold wasserstein1Distance cdfTranslate
  exact integral_sub_right_eq_self (fun x => |F_P x - F_Q x|) s

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.ProbabilityMetricTranslationKillingFlow

end
