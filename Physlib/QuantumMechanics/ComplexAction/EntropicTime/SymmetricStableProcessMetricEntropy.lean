/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The symmetric stable process pseudo-metric as an `Lᵖ` metric, and its metric entropy (Nolan 1989)

Formalizes the exact-algebra cores of the metric apparatus of Nolan, *Continuity of Symmetric Stable Processes*,
J. Multivariate Anal. 29 (1989) 84. A symmetric `p`-stable process `X = {X(t), t ∈ T}` with stochastic integral
representation `X(t) = ∫_U f(t,u) W_m(du)` has a **natural pseudo-metric** (Nolan §3),

`d_X(t,s) = (−log E exp(i(X(t) − X(s))))^{1/p} = ‖f(t,·) − f(s,·)‖_{Lᵖ(U,𝒰,m)}`,

the last equality from the stable characteristic function `E exp(i∑ aⱼX(tⱼ)) = exp(−‖∑ aⱼf(tⱼ,·)‖ᵖ_{Lᵖ})`
(Nolan (1.2)). So `d_X` is exactly the `Lᵖ` norm of the kernel difference — the same `Lᵖ`-distance-of-a-difference
structure as the Cramér / 1-Wasserstein CDF distances of `EntropicTime.CramerDistanceCDFMetric`. This module proves:

* the **stable pseudo-metric is the `Lᵖ`-norm pullback of the kernel** and satisfies the pseudo-metric axioms —
 vanishing on the diagonal (`stableDist_self`), symmetry (`stableDist_comm`), the triangle inequality
 (`stableDist_triangle`, from Minkowski in the `1 ≤ p` normed case), and non-negativity (`stableDist_nonneg`);
 equivalently it is `PseudoMetricSpace.induced` along the kernel map `f : T → Lᵖ`;
* the **metric entropy** `H_q(ε) = (log N(d;ε))^{1/q}` (Nolan §3, `metricEntropy`), monotone in the covering count
 `N` (`metricEntropy_mono`) and non-negative (`metricEntropy_nonneg`), with `q` the **dual index** of `p`,
 `1/p + 1/q = 1` (`conjugate_index`). Here `N(d;ε)` is the covering number — Mathlib's
 `Topology.MetricSpace.CoveringNumbers.coveringNumber` — the count of `d`-balls of radius `ε` covering `T`.

* **§A — the stable pseudo-metric** (`stableDist`, `stableDist_self`, `stableDist_comm`, `stableDist_triangle`,
 `stableDist_nonneg`).
* **§B — the metric entropy and the dual index** (`metricEntropy`, `metricEntropy_mono`, `metricEntropy_nonneg`,
 `conjugate_index`).
* **§C — the metric entropy integral** `J_q(d;δ) = ∫₀^δ H_q(d;ε) dε` (Nolan §3, `metricEntropyIntegral`), the
 Dudley-type integral controlling continuity in Theorem 3(ii) and Proposition 4: it vanishes at `δ = 0`
 (`metricEntropyIntegral_zero`), is non-negative (`metricEntropyIntegral_nonneg`), and is monotone in the cutoff
 `δ` (`metricEntropyIntegral_mono`).
* **§D — metric entropy under holographic / JL dimensional reduction** (`metricEntropy_le_dimensional_reduction`):
 the covering number `N(d_X;ε)` is the same object bounded by the Johnson–Lindenstrauss / holographic packing bound
 `(1+4/ε)ⁿ`, so an `n`-dimensionally-reduced stable process has metric entropy `≤ (n·log(1+4/ε))^{1/q}`.

The pseudo-metric axioms, the entropy monotonicity/non-negativity, the dual-index identity, and
the entropy-integral properties are exact algebra / integration (norm / `Real.log` / `Real.rpow` /
`intervalIntegral`). The deep probabilistic content is the *referenced* part, not
re-derived: the stable characteristic function and the representation-independence of `d_X` (Nolan (1.2)–(1.3)), the
sample-path continuity trichotomy (Theorem 1), the metric-entropy sufficiency and the stable Dudley–Fernique
conjecture (Theorem 3), and continuity-at-a-point (Theorem 5) — all of which require the stable-noise stochastic
integral and sample-path machinery. No new axioms.

## References

* J.P. Nolan, *Continuity of Symmetric Stable Processes*, J. Multivariate Anal. 29 (1989) 84 (§1–§3). Repo
 companions: `EntropicTime.CramerDistanceCDFMetric` (the `Lᵖ` CDF distances),
 `Topology.MetricSpace.CoveringNumbers` (`coveringNumber` = `N(d;ε)`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.SymmetricStableProcessMetricEntropy

/-! ## §A — the stable pseudo-metric `d_X(t,s) = ‖f(t,·) − f(s,·)‖_{Lᵖ}` -/

section StableMetric

variable {T : Type*} {V : Type*} [SeminormedAddCommGroup V]

/-- The **symmetric-stable process pseudo-metric** `d_X(t,s) = ‖f(t,·) − f(s,·)‖_{Lᵖ}` (Nolan §3), realized as the
`Lᵖ`-norm pullback of the kernel map `f : T → Lᵖ` (`V` a seminormed group standing for `Lᵖ(U,𝒰,m)`). By the stable
characteristic function it equals `(−log E exp(i(X(t)−X(s))))^{1/p}`, and is representation-independent. -/
def stableDist (f : T → V) (t s : T) : ℝ := ‖f t - f s‖

/-- **[The stable pseudo-metric vanishes on the diagonal] `d_X(t,t) = 0`.** -/
theorem stableDist_self (f : T → V) (t : T) : stableDist f t t = 0 := by
  simp [stableDist]

/-- **[The stable pseudo-metric is symmetric] `d_X(t,s) = d_X(s,t)`.** -/
theorem stableDist_comm (f : T → V) (t s : T) : stableDist f t s = stableDist f s t := by
  simp [stableDist, norm_sub_rev]

/-- **[The stable pseudo-metric satisfies the triangle inequality] `d_X(t,r) ≤ d_X(t,s) + d_X(s,r)`.** From the
Minkowski inequality (the norm triangle inequality of `Lᵖ`, `1 ≤ p`): telescoping `f t − f r = (f t − f s) +
(f s − f r)` and `norm_add_le`. So `d_X` is a genuine pseudo-metric on the index set `T`, namely
`PseudoMetricSpace.induced` along the kernel map. -/
theorem stableDist_triangle (f : T → V) (t s r : T) :
    stableDist f t r ≤ stableDist f t s + stableDist f s r := by
  simp only [stableDist]
  calc ‖f t - f r‖ = ‖(f t - f s) + (f s - f r)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖f t - f s‖ + ‖f s - f r‖ := norm_add_le _ _

/-- **[The stable pseudo-metric is non-negative] `0 ≤ d_X(t,s)`.** -/
theorem stableDist_nonneg (f : T → V) (t s : T) : 0 ≤ stableDist f t s := norm_nonneg _

end StableMetric

/-! ## §B — the metric entropy `H_q(ε) = (log N(d;ε))^{1/q}` and the dual index `1/p + 1/q = 1` -/

/-- The **metric entropy** `H_q(ε) = (log N)^{1/q}` (Nolan §3), a function of the covering count `N = N(d;ε)` (the
minimum number of `d`-balls of radius `ε` covering `T`, i.e. Mathlib's `coveringNumber`) and the dual index `q`.
Written with the real power `Real.rpow`. -/
noncomputable def metricEntropy (q N : ℝ) : ℝ := (Real.log N) ^ (1 / q)

/-- **[The metric entropy is monotone in the covering count] `N₁ ≤ N₂ ⟹ H_q(N₁) ≤ H_q(N₂)`.** For `q > 0` and
covering counts `≥ 1`, a larger covering number gives larger metric entropy — the entropy grows with the
`ε`-complexity of `T` (and, since the covering number decreases as `ε` grows, `H_q(ε)` decreases in `ε`). -/
theorem metricEntropy_mono {q : ℝ} (hq : 0 < q) {N₁ N₂ : ℝ} (h1 : 1 ≤ N₁) (h : N₁ ≤ N₂) :
    metricEntropy q N₁ ≤ metricEntropy q N₂ := by
  unfold metricEntropy
  exact Real.rpow_le_rpow (Real.log_nonneg h1) (Real.log_le_log (by linarith) h) (by positivity)

/-- **[The metric entropy is non-negative] `0 ≤ H_q(N)`.** For covering count `N ≥ 1`. -/
theorem metricEntropy_nonneg {q N : ℝ} (hN : 1 ≤ N) : 0 ≤ metricEntropy q N :=
  Real.rpow_nonneg (Real.log_nonneg hN) _

/-- **[The metric-entropy index is the Hölder dual of the stability index] `1/p + 1/q = 1`.** Nolan §3 takes `q` to
be the dual index of `p` (`p⁻¹ + q⁻¹ = 1`, `q = p/(p−1)`); the metric entropy `H_q` and the stable pseudo-metric
`d_X` (an `Lᵖ` object) are paired through this Hölder duality. -/
theorem conjugate_index {p q : ℝ} (hp : 1 < p) (hq : q = p / (p - 1)) : 1 / p + 1 / q = 1 := by
  subst hq
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  field_simp
  ring

/-! ## §C — the metric entropy integral `J_q(d;δ) = ∫₀^δ H_q(d;ε) dε` -/

open MeasureTheory in
/-- The **metric entropy integral** `J_q(d;δ) = ∫₀^δ H_q(d;ε) dε` (Nolan §3), the Dudley-type integral of the
scale-entropy function `H : ε ↦ H_q(d;ε)` up to the cutoff `δ`. Its finiteness `J_q(d;δ) < ∞` is the sufficient
condition for path continuity in Theorem 3(ii) and the modulus-of-continuity bound of Proposition 4. -/
noncomputable def metricEntropyIntegral (H : ℝ → ℝ) (δ : ℝ) : ℝ := ∫ ε in (0 : ℝ)..δ, H ε

/-- **[The metric entropy integral vanishes at the origin] `J_q(d;0) = 0`.** -/
theorem metricEntropyIntegral_zero (H : ℝ → ℝ) : metricEntropyIntegral H 0 = 0 := by
  unfold metricEntropyIntegral
  exact intervalIntegral.integral_same

/-- **[The metric entropy integral is non-negative] `0 ≤ J_q(d;δ)`.** For `0 ≤ δ` and a non-negative scale-entropy
function on `[0,δ]` (the metric entropy `H_q ≥ 0`, `metricEntropy_nonneg`), the Dudley integral is non-negative. -/
theorem metricEntropyIntegral_nonneg (H : ℝ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hH : ∀ ε ∈ Set.Icc (0 : ℝ) δ, 0 ≤ H ε) : 0 ≤ metricEntropyIntegral H δ :=
  intervalIntegral.integral_nonneg hδ hH

/-- **[The metric entropy integral is monotone in the cutoff] `δ₁ ≤ δ₂ ⟹ J_q(d;δ₁) ≤ J_q(d;δ₂)`.** Extending the
integration cutoff over a range where the scale-entropy is non-negative only increases the Dudley integral (given
interval-integrability), so `J_q(d;·)` grows with `δ`. -/
theorem metricEntropyIntegral_mono (H : ℝ → ℝ) {δ₁ δ₂ : ℝ} (h12 : δ₁ ≤ δ₂)
    (h1 : IntervalIntegrable H MeasureTheory.volume 0 δ₁)
    (h2 : IntervalIntegrable H MeasureTheory.volume δ₁ δ₂)
    (hH : ∀ ε ∈ Set.Icc δ₁ δ₂, 0 ≤ H ε) :
    metricEntropyIntegral H δ₁ ≤ metricEntropyIntegral H δ₂ := by
  unfold metricEntropyIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hnn : 0 ≤ ∫ ε in δ₁..δ₂, H ε := intervalIntegral.integral_nonneg h12 hH
  linarith

/-! ## §D — metric entropy under holographic / Johnson–Lindenstrauss dimensional reduction -/

/-- **[Metric entropy under dimensional reduction] `H_q(N) ≤ (n·log(1+4/ε))^{1/q}` when `N ≤ (1+4/ε)ⁿ`.** When the
`ε`-covering count `N = N(d_X;ε)` of the stable pseudo-metric space is controlled by the Johnson–Lindenstrauss /
holographic dimensional-reduction packing bound `(1+4/ε)ⁿ` — the `ε`-net cardinality of an `n`-dimensionally-reduced
index set (`AdSCFT.JohnsonLindenstraussEpsilonNetPacking.separated_card_le_pow`, where holography is the exact
`ε = 0` distance-preserving case, `holographic_reduction_is_exact_JL`) — the metric entropy is at most
`(n·log(1+4/ε))^{1/q}`, growing linearly in the reduced dimension `n`. So a stable process whose index set is
holographically / distance-preservingly reduced to `n` dimensions has metric entropy — hence, through the Dudley
integral `J_q` (`metricEntropyIntegral`), its path-continuity modulus — controlled by that dimension. This is the
point of contact between Nolan's continuity apparatus (§A–§C) and the holographic dimensional-reduction arc. -/
theorem metricEntropy_le_dimensional_reduction {q : ℝ} (hq : 0 < q) {N ε : ℝ} (n : ℕ)
    (hN1 : 1 ≤ N) (hNbound : N ≤ (1 + 4 / ε) ^ n) :
    metricEntropy q N ≤ ((n : ℝ) * Real.log (1 + 4 / ε)) ^ (1 / q) := by
  calc metricEntropy q N ≤ metricEntropy q ((1 + 4 / ε) ^ n) := metricEntropy_mono hq hN1 hNbound
    _ = (Real.log ((1 + 4 / ε) ^ n)) ^ (1 / q) := rfl
    _ = ((n : ℝ) * Real.log (1 + 4 / ε)) ^ (1 / q) := by rw [Real.log_pow]

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.SymmetricStableProcessMetricEntropy

end
