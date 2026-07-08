/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussLipschitzExtension
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Johnson–Lindenstrauss Lemma 3 — the `ε`-net / packing cardinality bound `(1 + 4/ε)ⁿ`

Formalizes **Lemma 3** of Johnson–Lindenstrauss (*Extensions of Lipschitz mappings into a Hilbert space*, Contemp.
Math. 26 (1984)): the unit sphere `S(Y)` of an `n`-dimensional Banach space admits an `ε`-net of cardinality at
most `(1 + 4/ε)ⁿ`. The proof is the **volume packing argument**, built here directly from Mathlib's Haar
ball-volume scaling: an `ε`-separated set `M` in the closed unit ball gives pairwise-disjoint balls
`closedBall y (ε/4)` (`y ∈ M`), all contained in `closedBall 0 (1 + ε/4)`, so

`card M · μ(closedBall 0 (ε/4)) ≤ μ(closedBall 0 (1 + ε/4))`,

and since `μ(closedBall 0 r) = rⁿ · μ(closedBall 0 1)` (`addHaar_real_closedBall'`), dividing by the positive,
finite `μ(closedBall 0 1)` gives `card M · (ε/4)ⁿ ≤ (1 + ε/4)ⁿ`, i.e.
`card M ≤ ((1 + ε/4)/(ε/4))ⁿ = (1 + 4/ε)ⁿ`.

Because a **maximal** `ε`-separated set is automatically an `ε`-net, this packing bound is exactly Lemma 3. In
Mathlib's language the left side is the `packingNumber` of the sphere (`Topology.MetricSpace.CoveringNumbers`);
here it is proved as an explicit `Finset.card` bound.

* **§A — the packing cardinality bound** (`separated_card_le_pow`): any `ε`-separated `Finset` in the closed unit
 ball has cardinality `≤ (1 + 4/ε)ⁿ`.

The bound is a genuine measure-theoretic theorem, built from Mathlib's Haar ball-volume
scaling (`MeasureTheory.Measure.addHaar_real_closedBall'`), disjoint-union additivity (`measure_biUnion_finset`),
and monotonicity (`measure_mono`) — all present in the repository. Only the passage "maximal `ε`-separated ⟹
`ε`-net" (elementary) and the identification with the abstract `packingNumber` are left as the connecting remarks;
the quantitative content — the `(1 + 4/ε)ⁿ` cardinality bound — is proved. No new axioms.

## References

* W.B. Johnson, J. Lindenstrauss, Contemp. Math. 26 (1984) 189 (Lemma 3). Repo dependencies:
 `MeasureTheory.Measure.addHaar_real_closedBall'` (ball-volume scaling), `measure_biUnion_finset`. Companion:
 `AdSCFT.JohnsonLindenstraussLipschitzExtension`.

No new axioms.
-/

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure Metric Set Module
open scoped ENNReal

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussEpsilonNetPacking

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-! ## §A — the packing cardinality bound -/

-- the Haar measure `μ` is only a proof device: the bound is measure-independent, so we `include` it
include μ

/-- **[Johnson–Lindenstrauss Lemma 3 — the `ε`-net / packing cardinality bound] `card M ≤ (1 + 4/ε)ⁿ`.** Any
`ε`-separated finite set `M` in the closed unit ball of an `n`-dimensional real normed space has cardinality at
most `(1 + 4/ε)ⁿ`, `n = finrank ℝ E`. Proof: the balls `closedBall y (ε/4)` (`y ∈ M`) are pairwise disjoint (`M`
is `ε`-separated and `ε/4 + ε/4 = ε/2 < ε`) and all lie in `closedBall 0 (1 + ε/4)` (centers have norm `≤ 1`), so
`card M · μ(closedBall 0 (ε/4)) ≤ μ(closedBall 0 (1 + ε/4))`; the Haar scaling `μ(closedBall 0 r) = rⁿ μ(closedBall
0 1)` and division by the positive finite unit-ball measure give the bound. A maximal such `M` is an `ε`-net, so
this is Lemma 3. -/
theorem separated_card_le_pow {ε : ℝ} (hε : 0 < ε) (M : Finset E)
    (hM : ∀ x ∈ M, ‖x‖ ≤ 1) (hsep : ∀ x ∈ M, ∀ y ∈ M, x ≠ y → ε ≤ ‖x - y‖) :
    (M.card : ℝ) ≤ (1 + 4 / ε) ^ (finrank ℝ E) := by
  have hεne : ε ≠ 0 := hε.ne'
  have hε4 : (0 : ℝ) < ε / 4 := by positivity
  -- the (ε/4)-balls around points of `M` are pairwise disjoint
  have hdisj : (↑M : Set E).PairwiseDisjoint (fun y => closedBall y (ε / 4)) := by
    intro x hx y hy hxy
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro z hzx hzy
    rw [mem_closedBall] at hzx hzy
    have hxz : dist x z ≤ ε / 4 := by rw [dist_comm]; exact hzx
    have htri : dist x y ≤ dist x z + dist z y := dist_triangle x z y
    have hd : ε ≤ dist x y := by
      rw [dist_eq_norm]; exact hsep x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hxy
    linarith
  -- they all lie in the ball of radius `1 + ε/4`
  have hsub : (⋃ y ∈ M, closedBall y (ε / 4)) ⊆ closedBall (0 : E) (1 + ε / 4) := by
    apply Set.iUnion₂_subset
    intro y hyM z hz
    rw [mem_closedBall] at hz ⊢
    have hy1 : dist y 0 ≤ 1 := by rw [dist_zero_right]; exact hM y hyM
    calc dist z 0 ≤ dist z y + dist y 0 := dist_triangle z y 0
      _ ≤ ε / 4 + 1 := by linarith
      _ = 1 + ε / 4 := by ring
  -- volume comparison
  have hunion : μ (⋃ y ∈ M, closedBall y (ε / 4)) = ∑ y ∈ M, μ (closedBall y (ε / 4)) :=
    measure_biUnion_finset hdisj (fun y _ => measurableSet_closedBall)
  have hsum : ∑ y ∈ M, μ (closedBall y (ε / 4)) = (M.card : ℝ≥0∞) * μ (closedBall (0 : E) (ε / 4)) := by
    rw [Finset.sum_congr rfl (fun y _ => addHaar_closedBall_center μ y (ε / 4)), Finset.sum_const,
      nsmul_eq_mul]
  have hle : (M.card : ℝ≥0∞) * μ (closedBall (0 : E) (ε / 4)) ≤ μ (closedBall (0 : E) (1 + ε / 4)) := by
    calc (M.card : ℝ≥0∞) * μ (closedBall (0 : E) (ε / 4))
        = μ (⋃ y ∈ M, closedBall y (ε / 4)) := by rw [hunion, hsum]
      _ ≤ μ (closedBall (0 : E) (1 + ε / 4)) := measure_mono hsub
  -- pass to real measures and use the Haar scaling `μ(ball r) = rⁿ · μ(ball 1)`
  have hfinL : (M.card : ℝ≥0∞) * μ (closedBall (0 : E) (ε / 4)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_closedBall_lt_top.ne
  have hlereal := (ENNReal.toReal_le_toReal hfinL measure_closedBall_lt_top.ne).mpr hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hlereal
  simp only [← MeasureTheory.measureReal_def] at hlereal
  rw [addHaar_real_closedBall' μ 0 hε4.le,
    addHaar_real_closedBall' μ 0 (by positivity : (0 : ℝ) ≤ 1 + ε / 4), ← mul_assoc] at hlereal
  have hV : 0 < μ.real (closedBall (0 : E) 1) := by
    rw [MeasureTheory.measureReal_def]
    exact ENNReal.toReal_pos (measure_closedBall_pos μ 0 one_pos).ne' measure_closedBall_lt_top.ne
  have hstep : (M.card : ℝ) * (ε / 4) ^ (finrank ℝ E) ≤ (1 + ε / 4) ^ (finrank ℝ E) :=
    le_of_mul_le_mul_right hlereal hV
  -- rearrange to the `(1 + 4/ε)ⁿ` form
  have hpow : (0 : ℝ) < (ε / 4) ^ (finrank ℝ E) := by positivity
  have hfrac : (1 + ε / 4) ^ (finrank ℝ E) / (ε / 4) ^ (finrank ℝ E) = (1 + 4 / ε) ^ (finrank ℝ E) := by
    rw [← div_pow]; congr 1; field_simp; ring
  rw [← hfrac]
  exact (le_div_iff₀ hpow).mpr hstep

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussEpsilonNetPacking

end
