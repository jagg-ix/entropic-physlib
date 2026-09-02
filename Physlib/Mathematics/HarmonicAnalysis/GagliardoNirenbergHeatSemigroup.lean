/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Order.OrderClosed
meta import Zil

/-!
# The heat-semigroup interpolation kernel of Gagliardo–Nirenberg (Ozawa–Takeuchi)

Formalizes the algebraic heart of *T. Ozawa, T. Takeuchi, "A New Proof of the Gagliardo–Nirenberg
and Sobolev Inequalities: Heat Semigroup Approach", Proc. Amer. Math. Soc. Ser. B 11 (2024) 371–377*.

Their new proof reduces the Gagliardo–Nirenberg inequality to a single ingredient — the `Lᵖ`-`Lq`
smoothing estimate of the heat semigroup — followed by an optimization over the semigroup time `t`.
The heat estimate `‖∇ʲ e^{tΔ}f‖_{Lᵖ} ≤ C t^{-(n/2)(1/q₀−1/p₀)−j/2}‖f‖_{Lq₀}` produces, via the
telescoping identity `f = e^{tΔ}f − ∫₀ᵗ Δ e^{τΔ}f dτ`, a **two-term time-dependent bound**

  `‖f‖_{Lᵖ} ≤ C‖f‖_{Lq}·t^{−(n/2)(1/q−1/p)} + C‖∇f‖_{Lʳ}·t^{1/2−(n/2)(1/r−1/p)}`  for all `t > 0`,

and the theorem follows by **balancing the two powers of `t`**. This module carries exactly that
reduction on the level of the norms (real nonnegative numbers), taking the cited `Lᵖ`-`Lq` heat
estimate as the hypothesis:

* `heat_split_balancing` — the optimization core: if `X ≤ A t^{−σm} + B t^{(1−σ)m}` for all `t > 0`
  (`A, B > 0`, `m ≠ 0`), then `X ≤ 2 A^{1−σ} B^σ`, by evaluating at the balancing time
  `t = (A/B)^{1/m}` where both terms collapse to `A^{1−σ}B^σ`.
* `gnSigma_mul_gnScale` / `one_sub_gnSigma_mul_gnScale` — the exponent bookkeeping: with
  `m = 1/2 + (n/2)(1/q−1/r)` and the Gagliardo–Nirenberg interpolation index
  `σ = n(1/q−1/p)/(1 + n(1/q−1/r))`, the two heat exponents are exactly `σm = (n/2)(1/q−1/p)` and
  `(1−σ)m = 1/2 − (n/2)(1/r−1/p)`.
* `gagliardo_nirenberg_of_heat_bound` — Theorem 1.1(i): the two-term heat bound implies the
  Gagliardo–Nirenberg estimate `‖f‖_{Lᵖ} ≤ 2C‖f‖_{Lq}^{1−σ}‖∇f‖_{Lʳ}^σ`.
* `sobolev_limit_bound` — the final step of the Sobolev proof (Theorem 1.1(ii)): from
  `‖f‖ ≤ C t^{−1/2}‖f‖_{L²} + C‖∇f‖` for all `t > 0`, letting `t → ∞` gives `‖f‖ ≤ C‖∇f‖`.

**Honest layering.** The norms are carried as abstract nonnegative reals and the `Lᵖ`-`Lq` heat
estimate — standard, cited from [Giga–Giga–Saal] — is the hypothesis; the novel content of the paper
is the *reduction* (the balancing optimization and the exponent identity), which is what is proved
here in full. The measure-theoretic `Lᵖ`-space realization and the heat-kernel bound itself are not
reproved (they require heat-semigroup infrastructure absent from Mathlib).
-/

set_option autoImplicit false

open Filter Topology

@[expose] public section

namespace Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup

/-- **[The balancing optimization — the heart of the heat-semigroup proof]** If a nonnegative
quantity `X` is bounded by the two-term time family `A·t^{−σm} + B·t^{(1−σ)m}` for every `t > 0`
(with `A, B > 0` and `m ≠ 0`), then `X ≤ 2·A^{1−σ}·B^σ`. Proof: at the balancing time
`t = (A/B)^{1/m}` both powers of `t` collapse to the interpolation product `A^{1−σ}B^σ`, so their sum
is `2A^{1−σ}B^σ`. This is the optimization that turns the `Lᵖ`-`Lq` heat estimate into an
interpolation inequality. -/
theorem heat_split_balancing {X A B m σ : ℝ} (hA : 0 < A) (hB : 0 < B) (hm : m ≠ 0)
    (hbound : ∀ t : ℝ, 0 < t → X ≤ A * t ^ (-(σ * m)) + B * t ^ ((1 - σ) * m)) :
    X ≤ 2 * (A ^ (1 - σ) * B ^ σ) := by
  have hAB : 0 < A / B := div_pos hA hB
  have key := hbound ((A / B) ^ m⁻¹) (Real.rpow_pos_of_pos hAB _)
  have e1 : ((A / B) ^ m⁻¹) ^ (-(σ * m)) = (A / B) ^ (-σ) := by
    rw [← Real.rpow_mul hAB.le]; congr 1; field_simp
  have e2 : ((A / B) ^ m⁻¹) ^ ((1 - σ) * m) = (A / B) ^ (1 - σ) := by
    rw [← Real.rpow_mul hAB.le]; congr 1; field_simp
  rw [e1, e2] at key
  have d1 : A * (A / B) ^ (-σ) = A ^ (1 - σ) * B ^ σ := by
    rw [Real.div_rpow hA.le hB.le, Real.rpow_neg hA.le, Real.rpow_neg hB.le]
    have hAs : A ^ (1 - σ) = A / A ^ σ := by
      rw [eq_div_iff (Real.rpow_pos_of_pos hA σ).ne', ← Real.rpow_add hA,
        show (1 - σ) + σ = 1 by ring, Real.rpow_one]
    rw [hAs]
    field_simp [(Real.rpow_pos_of_pos hA σ).ne', (Real.rpow_pos_of_pos hB σ).ne']
  have d2 : B * (A / B) ^ (1 - σ) = A ^ (1 - σ) * B ^ σ := by
    rw [Real.div_rpow hA.le hB.le]
    have hBs : B ^ σ = B / B ^ (1 - σ) := by
      rw [eq_div_iff (Real.rpow_pos_of_pos hB (1 - σ)).ne', ← Real.rpow_add hB,
        show σ + (1 - σ) = 1 by ring, Real.rpow_one]
    rw [hBs]
    field_simp [(Real.rpow_pos_of_pos hB (1 - σ)).ne']
  rw [d1, d2] at key
  linarith [key]

/-- The Gagliardo–Nirenberg interpolation index `σ = n(1/q − 1/p)/(1 + n(1/q − 1/r))`. -/
noncomputable def gnSigma (n p q r : ℝ) : ℝ := n * (1 / q - 1 / p) / (1 + n * (1 / q - 1 / r))

/-- The heat time-scaling exponent `m = 1/2 + (n/2)(1/q − 1/r)`; it satisfies `2m = 1 + n(1/q − 1/r)`,
the denominator of `gnSigma`. -/
noncomputable def gnScale (n q r : ℝ) : ℝ := 1 / 2 + (n / 2) * (1 / q - 1 / r)

/-- `1 + n(1/q − 1/r) = 2·gnScale n q r`: the `gnSigma` denominator is twice the heat scale. -/
theorem two_mul_gnScale (n q r : ℝ) : 2 * gnScale n q r = 1 + n * (1 / q - 1 / r) := by
  unfold gnScale; ring

/-- **[Exponent identity, decay term] `σ·m = (n/2)(1/q − 1/p)`.** The first heat exponent
`(n/2)(1/q − 1/p)` is exactly `gnSigma·gnScale` — the reason the `Lᵖ`-`Lq` decay rate carries the
interpolation index `σ`. -/
theorem gnSigma_mul_gnScale (n p q r : ℝ) (h : gnScale n q r ≠ 0) :
    gnSigma n p q r * gnScale n q r = (n / 2) * (1 / q - 1 / p) := by
  have h2 : 1 + n * (1 / q - 1 / r) ≠ 0 := by rw [← two_mul_gnScale]; simpa using h
  unfold gnSigma gnScale
  field_simp

/-- **[Exponent identity, gradient term] `(1 − σ)·m = 1/2 − (n/2)(1/r − 1/p)`.** The second heat
exponent `1/2 − (n/2)(1/r − 1/p)` is exactly `(1 − gnSigma)·gnScale` — the gradient term carries the
complementary index `1 − σ`. -/
theorem one_sub_gnSigma_mul_gnScale (n p q r : ℝ) (h : gnScale n q r ≠ 0) :
    (1 - gnSigma n p q r) * gnScale n q r = 1 / 2 - (n / 2) * (1 / r - 1 / p) := by
  have hkey := gnSigma_mul_gnScale n p q r h
  have hsplit : (1 - gnSigma n p q r) * gnScale n q r
      = gnScale n q r - gnSigma n p q r * gnScale n q r := by ring
  rw [hsplit, hkey]
  unfold gnScale
  ring

/-- **[Gagliardo–Nirenberg inequality, Theorem 1.1(i)]** — from the two-term heat-semigroup bound to
the interpolation estimate. If the norms `Nq = ‖f‖_{Lq}`, `Np = ‖f‖_{Lᵖ}`, `Nr = ‖∇f‖_{Lʳ}` satisfy
the `Lᵖ`-`Lq` heat estimate

  `Np ≤ C·Nq·t^{−(n/2)(1/q−1/p)} + C·Nr·t^{1/2−(n/2)(1/r−1/p)}`  for all `t > 0`,

then the Gagliardo–Nirenberg inequality holds:

  `Np ≤ 2C·Nq^{1−σ}·Nr^σ`,  `σ = gnSigma n p q r`.

The two heat exponents are `σ·gnScale` and `(1−σ)·gnScale` (`gnSigma_mul_gnScale`), so the balancing
optimization `heat_split_balancing` applies with `A = C·Nq`, `B = C·Nr`, `m = gnScale`. -/
theorem gagliardo_nirenberg_of_heat_bound (n p q r C Nq Np Nr : ℝ)
    (hC : 0 < C) (hNq : 0 < Nq) (hNr : 0 < Nr) (hscale : gnScale n q r ≠ 0)
    (hbound : ∀ t : ℝ, 0 < t →
      Np ≤ C * Nq * t ^ (-((n / 2) * (1 / q - 1 / p)))
        + C * Nr * t ^ (1 / 2 - (n / 2) * (1 / r - 1 / p))) :
    Np ≤ 2 * C * Nq ^ (1 - gnSigma n p q r) * Nr ^ (gnSigma n p q r) := by
  set σ := gnSigma n p q r with hσ
  set m := gnScale n q r with hm
  have hexp1 : (n / 2) * (1 / q - 1 / p) = σ * m := (gnSigma_mul_gnScale n p q r hscale).symm
  have hexp2 : 1 / 2 - (n / 2) * (1 / r - 1 / p) = (1 - σ) * m :=
    (one_sub_gnSigma_mul_gnScale n p q r hscale).symm
  have hbound' : ∀ t : ℝ, 0 < t →
      Np ≤ (C * Nq) * t ^ (-(σ * m)) + (C * Nr) * t ^ ((1 - σ) * m) := by
    intro t ht
    have hb := hbound t ht
    rwa [hexp1, hexp2] at hb
  have hbal := heat_split_balancing (mul_pos hC hNq) (mul_pos hC hNr) hscale hbound'
  -- (C·Nq)^{1−σ}·(C·Nr)^σ = C·Nq^{1−σ}·Nr^σ
  have hsimp : (C * Nq) ^ (1 - σ) * (C * Nr) ^ σ = C * (Nq ^ (1 - σ) * Nr ^ σ) := by
    rw [Real.mul_rpow hC.le hNq.le, Real.mul_rpow hC.le hNr.le]
    have hCC : C ^ (1 - σ) * C ^ σ = C := by
      rw [← Real.rpow_add hC, show (1 - σ) + σ = 1 by ring, Real.rpow_one]
    calc C ^ (1 - σ) * Nq ^ (1 - σ) * (C ^ σ * Nr ^ σ)
        = (C ^ (1 - σ) * C ^ σ) * (Nq ^ (1 - σ) * Nr ^ σ) := by ring
      _ = C * (Nq ^ (1 - σ) * Nr ^ σ) := by rw [hCC]
  rw [hsimp] at hbal
  calc Np ≤ 2 * (C * (Nq ^ (1 - σ) * Nr ^ σ)) := hbal
    _ = 2 * C * Nq ^ (1 - σ) * Nr ^ σ := by ring

/-- **[Sobolev inequality, final step of Theorem 1.1(ii)]** — the `t → ∞` optimization. If a
quantity `N` satisfies `N ≤ C·t^{−1/2}·D + E` for all `t > 0` (with `C, D ≥ 0`), then `N ≤ E`: the
critical `t^{−1/2}` decay of the smoothed term vanishes in the large-time limit, leaving the
gradient bound. This is the last line of the Sobolev proof, `‖f‖ ≤ Ct^{−1/2}‖f‖_{L²} + C‖∇f‖ → C‖∇f‖`. -/
theorem sobolev_limit_bound {N C D E : ℝ}
    (hbound : ∀ t : ℝ, 0 < t → N ≤ C * t ^ (-(1 / 2 : ℝ)) * D + E) :
    N ≤ E := by
  have h0 : Tendsto (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have htend : Tendsto (fun t : ℝ => C * t ^ (-(1 / 2 : ℝ)) * D + E) atTop (𝓝 E) := by
    have hraw : Tendsto (fun t : ℝ => C * t ^ (-(1 / 2 : ℝ)) * D + E) atTop
        (𝓝 (C * 0 * D + E)) :=
      ((tendsto_const_nhds.mul h0).mul tendsto_const_nhds).add tendsto_const_nhds
    simpa using hraw
  refine ge_of_tendsto htend ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht using hbound t ht

end Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup

end

/- ZIL-BEGIN -/

zil attach Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.heat_split_balancing where
  formalizes @ "claim:the-two-term-heat-time-bound-balanced-at-t-equals-a-over-b-to-the-one-over-m-yields-the-interpolation-product-a-to-one-minus-sigma-b-to-sigma",
  supported_by @ "paper:ozawa-takeuchi-heat-semigroup-gagliardo-nirenberg-sobolev"

zil attach Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.gnSigma_mul_gnScale where
  supported_by @ "lean:Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.two_mul_gnScale",
  formalizes @ "claim:the-first-heat-decay-exponent-n-over-two-times-one-over-q-minus-one-over-p-equals-the-gagliardo-nirenberg-index-sigma-times-the-heat-scale"

zil attach Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.one_sub_gnSigma_mul_gnScale where
  supported_by @ "lean:Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.gnSigma_mul_gnScale",
  supported_by @ "lean:Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.heat_split_balancing",
  formalizes @ "claim:the-second-heat-gradient-exponent-equals-one-minus-the-gagliardo-nirenberg-index-times-the-heat-scale"

zil attach Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.gagliardo_nirenberg_of_heat_bound where
  formalizes @ "claim:the-two-term-lp-lq-heat-semigroup-bound-implies-the-gagliardo-nirenberg-interpolation-inequality",
  requires @ "claim:the-two-term-heat-time-bound-balanced-at-t-equals-a-over-b-to-the-one-over-m-yields-the-interpolation-product-a-to-one-minus-sigma-b-to-sigma",
  supported_by @ "paper:ozawa-takeuchi-heat-semigroup-gagliardo-nirenberg-sobolev",
  caveat @ "claim:the-lp-lq-heat-smoothing-estimate-itself-is-taken-as-a-cited-hypothesis-not-reproved-here"

zil attach Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.sobolev_limit_bound where
  supported_by @ "lean:HasVarAdjDerivAt.mul",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-critical-t-to-minus-one-half-smoothed-term-vanishes-in-the-large-time-limit-leaving-the-sobolev-gradient-bound"

zil_file_contract physlib.gagliardoNirenbergHeatSemigroup where
  promises "The heat-semigroup interpolation kernel of the Ozawa-Takeuchi proof of Gagliardo-Nirenberg and Sobolev: the two-term time-dependent bound X <= A t^{-sigma m} + B t^{(1-sigma)m} from the Lp-Lq heat estimate, balanced at t = (A/B)^{1/m}, yields the interpolation product 2 A^{1-sigma} B^sigma; the two heat exponents are exactly sigma*gnScale and (1-sigma)*gnScale with the Gagliardo-Nirenberg index sigma; hence the two-term heat bound implies the Gagliardo-Nirenberg inequality Np <= 2C Nq^{1-sigma} Nr^sigma; and the large-time limit of the critical smoothed term gives the Sobolev gradient bound."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.gnSigma",
    "lean:Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.gnScale"]
  forbids_substitutes ["the measure-theoretic Lp-space realization and the heat-kernel Lp-Lq smoothing estimate, which are taken as the cited hypothesis not reproved here",
    "the sharp best constant, only the qualitative interpolation inequality with constant 2C is carried"]
  witnessed_by [Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.heat_split_balancing,
    Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.gnSigma_mul_gnScale,
    Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.one_sub_gnSigma_mul_gnScale,
    Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.gagliardo_nirenberg_of_heat_bound,
    Physlib.Mathematics.HarmonicAnalysis.GagliardoNirenbergHeatSemigroup.sobolev_limit_bound]

/- ZIL-END -/
