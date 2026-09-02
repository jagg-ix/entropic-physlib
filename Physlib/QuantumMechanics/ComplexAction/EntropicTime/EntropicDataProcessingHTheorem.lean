/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality
public import Mathlib.Algebra.BigOperators.Field
/- ZIL-BEGIN -/
public meta import Zil
/- ZIL-END -/

/-!
# The entropic H-theorem: relative entropy decreases under coarse-graining (data processing)

The **time / coarse-graining monotonicity** of the entropic-time program — the companion to the
scale-monotonicity of the entropic c-theorem (`EntropicCTheorem`). Building on the Gibbs inequality
(`RelativeEntropyGibbsInequality.klDivergence_nonneg`), we derive:

* the **log-sum inequality** (`logSumInequality`)

    `(Σᵢ aᵢ) log((Σᵢaᵢ)/(Σᵢbᵢ)) ≤ Σᵢ aᵢ log(aᵢ/bᵢ)`,

  the workhorse of information theory, obtained here directly from `D(ã‖b̃) ≥ 0` for the normalized
  distributions `ãᵢ = aᵢ/Σa`, `b̃ᵢ = bᵢ/Σb`;

* the **data-processing / H-theorem inequality** (`relativeEntropy_marginal_le`)

    `D(p_X‖q_X) ≤ D(p_XY‖q_XY)`,

  relative entropy never increases under marginalization (a deterministic coarse-graining channel) —
  applying the log-sum inequality row by row. Coarse-graining loses information: the divergence to a
  reference distribution can only shrink, which is exactly the arrow-of-time / second-law statement for
  entropic evolution (a Markov step `p ↦ pT` toward a stationary `π` is such a channel, so
  `D(pₜ₊₁‖π) ≤ D(pₜ‖π)`).

* **§A — the log-sum inequality** (`logSumInequality`).
* **§B — data processing / H-theorem** (`relativeEntropy_marginal_le`).

## References

* Standard information theory (Cover–Thomas, the log-sum inequality and the data-processing inequality).
  Companion to `EntropicTime.RelativeEntropyGibbsInequality` (the `D ≥ 0` it rests on) and
  `EntropicCTheorem` (the scale-monotonicity counterpart).
-/

set_option autoImplicit false

open Finset

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDataProcessingHTheorem

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality

variable {ι : Type*} [Fintype ι]

/-! ### §A — the log-sum inequality -/

/-- **[Log-sum inequality]** `(Σaᵢ) log((Σaᵢ)/(Σbᵢ)) ≤ Σ aᵢ log(aᵢ/bᵢ)` for `aᵢ ≥ 0`, `bᵢ > 0`,
`Σaᵢ > 0`. Derived from the Gibbs inequality `D(ã‖b̃) ≥ 0` applied to the normalized distributions. -/
theorem logSumInequality [Nonempty ι] (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i)
    (hA : 0 < ∑ i, a i) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) ≤ ∑ i, a i * Real.log (a i / b i) := by
  have hB : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  set A := ∑ i, a i with hA_def
  set B := ∑ i, b i with hB_def
  have hgibbs : 0 ≤ klDivergence (fun i => a i / A) (fun i => b i / B) :=
    klDivergence_nonneg _ _ (fun i => div_nonneg (ha i) hA.le) (fun i => div_pos (hb i) hB)
      (by rw [← Finset.sum_div, ← hA_def]; exact div_self (ne_of_gt hA))
      (by rw [← Finset.sum_div, ← hB_def]; exact div_self (ne_of_gt hB))
  rw [klDivergence] at hgibbs
  have hterm : ∀ i, a i / A * Real.log (a i / A / (b i / B))
      = a i * Real.log (a i / b i) / A + a i * Real.log (B / A) / A := by
    intro i
    rcases (ha i).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [show a i / A / (b i / B) = a i / b i * (B / A) by field_simp,
          Real.log_mul (ne_of_gt (div_pos h (hb i))) (ne_of_gt (div_pos hB hA))]
      field_simp
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
      ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_mul, ← hA_def] at hgibbs
  rw [mul_comm A (Real.log (B / A)), mul_div_assoc, div_self (ne_of_gt hA), mul_one] at hgibbs
  have hSA : A * ((∑ i, a i * Real.log (a i / b i)) / A) = ∑ i, a i * Real.log (a i / b i) := by
    field_simp
  have hmul : 0 ≤ A * ((∑ i, a i * Real.log (a i / b i)) / A + Real.log (B / A)) :=
    mul_nonneg hA.le hgibbs
  rw [mul_add, hSA] at hmul
  have hlogAB : Real.log (A / B) = -Real.log (B / A) := by rw [← Real.log_inv, inv_div]
  rw [hlogAB, mul_neg]
  linarith [hmul]

/-! ### §B — data processing / H-theorem -/

/-- **[Data-processing / H-theorem: relative entropy decreases under marginalization]**
`D(p_X‖q_X) ≤ D(p_XY‖q_XY)`. Coarse-graining the joint `(X,Y)`-distributions to their `X`-marginals never
increases the relative entropy — the log-sum inequality applied row by row. This is the arrow-of-time /
second-law monotonicity: a Markov (channel) step toward a reference distribution can only shrink the
divergence. -/
theorem relativeEntropy_marginal_le {κ : Type*} [Fintype κ] [Nonempty κ]
    (p q : ι → κ → ℝ) (hp : ∀ i j, 0 ≤ p i j) (hq : ∀ i j, 0 < q i j)
    (hpX : ∀ i, 0 < ∑ j, p i j) :
    (∑ i, (∑ j, p i j) * Real.log ((∑ j, p i j) / (∑ j, q i j)))
      ≤ ∑ i, ∑ j, p i j * Real.log (p i j / q i j) :=
  Finset.sum_le_sum (fun i _ => logSumInequality (p i) (q i) (hp i) (hq i) (hpX i))

/- ZIL-BEGIN -/

zil attach logSumInequality where
  supported_by @ "lean:klDivergence_nonneg",
  formalizes @ "claim:log-sum-inequality-from-the-gibbs-inequality-on-normalized-distributions",
  epistemic_status @ "consistency-identity",
  requires @ "claim:discrete-relative-entropy-is-nonnegative-gibbs-inequality-second-law-master-bound",
  caveat @ "claim:classical-log-sum-inequality-over-a-fintype-not-the-operator-or-measure-theoretic-version"

zil attach relativeEntropy_marginal_le where
  supported_by @ "lean:logSumInequality",
  formalizes @ "claim:relative-entropy-decreases-under-marginalization-data-processing-h-theorem-arrow-of-time",
  epistemic_status @ "consistency-identity",
  requires @ "claim:log-sum-inequality-from-the-gibbs-inequality-on-normalized-distributions",
  caveat @ "claim:deterministic-coarse-graining-marginalization-channel-classical-not-the-quantum-data-processing-inequality"

zil_file_contract physlib.entropicDataProcessingHTheorem where
  promises "The entropic H-theorem / data-processing monotonicity of the entropic-time program. The log-sum inequality (logSumInequality), derived directly from the Gibbs inequality applied to the normalized distributions, forces relative entropy to never increase under marginalization (relativeEntropy_marginal_le, D(p_X‖q_X) ≤ D(p_XY‖q_XY)). This is the time / coarse-graining monotonicity dual to the entropic c-theorem's scale-monotonicity: a Markov step toward a stationary reference can only shrink the divergence, D(p_{t+1}‖π) ≤ D(p_t‖π) -- the arrow-of-time / second-law statement for entropic evolution."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence_nonneg",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDataProcessingHTheorem.logSumInequality"]
  forbids_substitutes ["any operator-level or quantum data-processing inequality -- this is the classical marginalization (deterministic coarse-graining) channel",
    "calling the marginalization special case the full stochastic-channel data-processing inequality"]
  witnessed_by [logSumInequality, relativeEntropy_marginal_le]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDataProcessingHTheorem
