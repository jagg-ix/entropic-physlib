/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution
public import Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
public import Physlib.Mathematics.LpAeConvergence
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
meta import Zil

/-!
# The Carleson problem: the Du–Zhang threshold, a.e. subsequence recovery, and the Sobolev ladder

Three structural aspects of Hickman's Bourbaki exposition of the Carleson problem (arXiv:2304.02507,
Problem 1.1, Theorems 1.2–1.3), building on the existing arc (`EuclideanL2FreeEvolution`,
`EuclideanSobolevFrequencyLocalization`) and welding in `Mathematics.LpAeConvergence`:

* **§A — the Carleson–Du–Zhang threshold exponent** `s_c(n) = n/(2(n+1))`: the sharp regularity index of the
  problem — a.e. convergence holds for `s > s_c(n)` (Du–Zhang 2019, Thm. 1.3) and fails for `s < s_c(n)`
  (Bourgain 2016, Thm. 1.2), with the endpoint open. We prove its structural arithmetic: `s_c(1) = 1/4`
  (Carleson 1980 / Dahlberg–Kenig 1982), strict monotonicity in `n`, the uniform bound `s_c(n) < 1/2`, the
  high-dimensional limit `s_c(n) → 1/2`, and that Du–Zhang strictly improves Bourgain's 2013 range
  `(2n−1)/(4n)` in every dimension `n ≥ 2`.
* **§B — almost-everywhere subsequence recovery for every `L²` datum**: for any `f ∈ L²(ℝⁿ)` (no Sobolev
  regularity at all) and any sequence `tₖ → 0`, some subsequence of `e^{i t_{φ(k)} Δ} f` converges to `f`
  almost everywhere — energy conservation + strong continuity (Eq. (4), (7) of the survey; the arc's
  `freeSchrodingerEvolution_tendsto_zero`) upgraded through `Mathematics.LpAeConvergence`
  (`ae_subseq_of_eLpNorm_tendsto`). This is the elementary a.e. statement the survey contrasts with
  Problem 1.1: the Carleson problem's difficulty is the *continuum* limit `t → 0₊` (Remark 1.4), not
  subsequences along null sequences.
* **§C — the Sobolev data ladder** `H^{s₂} ⊆ H^{s₁}` for `s₁ ≤ s₂` (`H⁰ = L²` is
  `hasSobolevRegularity_zero`): monotonicity of the Bessel-potential membership certificate, so the
  threshold of §A slices a genuinely nested family of data classes.

No maximal estimate, fractal energy estimate, counterexample construction, or the Du–Zhang analysis itself is
asserted — the ZIL contract records those as forbidden substitutes.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory
open scoped ENNReal
open Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution
open Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
open Physlib.Mathematics.LpAeConvergence

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Schrodinger.SchrodingerCarlesonThreshold

/-! ## §A The Carleson–Du–Zhang threshold exponent -/

/-- **The Carleson–Du–Zhang threshold** `s_c(n) = n/(2(n+1))` — the sharp Sobolev index of the Carleson
problem: a.e. convergence holds for `s > s_c(n)` (Du–Zhang) and fails for `s < s_c(n)` (Bourgain). -/
def carlesonExponent (n : ℕ) : ℝ := n / (2 * (n + 1))

/-- **[`s_c(1) = 1/4`]** the classical one-dimensional threshold of Carleson (1980, sufficiency) and
Dahlberg–Kenig (1982, necessity). -/
@[simp] theorem carlesonExponent_one : carlesonExponent 1 = 1 / 4 := by
  norm_num [carlesonExponent]

/-- **[`s_c(n) < 1/2`]** the threshold never reaches the trivial `H^{1/2}` index. -/
theorem carlesonExponent_lt_half (n : ℕ) : carlesonExponent n < 1 / 2 := by
  unfold carlesonExponent
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- **[`s_c` is strictly monotone]** the Carleson problem gets strictly harder in higher dimension. -/
theorem carlesonExponent_strictMono : StrictMono carlesonExponent := by
  intro m n hmn
  unfold carlesonExponent
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  push_cast
  have h : (m : ℝ) < n := by exact_mod_cast hmn
  nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n]

/-- **[`s_c(n) → 1/2`]** the high-dimensional limit of the threshold is the trivial index `1/2`. -/
theorem tendsto_carlesonExponent_atTop :
    Tendsto carlesonExponent atTop (nhds (1 / 2)) := by
  have hrw : carlesonExponent = fun n : ℕ => 1 / 2 - 1 / (2 * ((n : ℝ) + 1)) := by
    funext n
    unfold carlesonExponent
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [hrw]
  have hden : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)) atTop atTop := by
    apply Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) atTop (nhds 0) := by
    simpa [one_div, Function.comp_def, mul_inv, mul_comm] using tendsto_inv_atTop_zero.comp hden
  simpa using tendsto_const_nhds.sub hzero

/-- **The Bourgain (2013) multilinear range exponent** `(2n−1)/(4n)` — the pre-Du–Zhang sufficient range. -/
def bourgainMultilinearExponent (n : ℕ) : ℝ := (2 * n - 1) / (4 * n)

/-- **[Du–Zhang strictly improves Bourgain 2013] `s_c(n) < (2n−1)/(4n)` for `n ≥ 2`.** The Du–Zhang
threshold is strictly below the earlier multilinear range in every dimension where the problem was open. -/
theorem carlesonExponent_lt_bourgainMultilinear {n : ℕ} (hn : 2 ≤ n) :
    carlesonExponent n < bourgainMultilinearExponent n := by
  unfold carlesonExponent bourgainMultilinearExponent
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hn']


/-- **The sharp maximal Lebesgue exponent** `p(n) = 2(n+1)/n` — the Sobolev-embedding-critical target
exponent for the `H^s → L^p` Schrödinger maximal estimate (§3.2): `p(1) = 4` (Kenig–Ponce–Vega 1991),
`p(2) = 3` (Du–Guth–Li–Zhang 2018). -/
def maximalLebesgueExponent (n : ℕ) : ℝ := 2 * (n + 1) / n

/-- **[`p(1) = 4`]** the sharp one-dimensional maximal exponent of Kenig–Ponce–Vega (1991). -/
@[simp] theorem maximalLebesgueExponent_one : maximalLebesgueExponent 1 = 4 := by
  norm_num [maximalLebesgueExponent]

/-- **[`p(2) = 3`]** the sharp two-dimensional maximal exponent of Du–Guth–Li–Zhang (2018). -/
@[simp] theorem maximalLebesgueExponent_two : maximalLebesgueExponent 2 = 3 := by
  norm_num [maximalLebesgueExponent]

/-- **[Reciprocal duality] `s_c(n) · p(n) = 1`** — the Carleson–Du–Zhang threshold is exactly the reciprocal
of the sharp maximal Lebesgue exponent: the regularity index and the integrability index of the maximal
theory are inverse to each other. -/
theorem carlesonExponent_mul_maximalLebesgueExponent {n : ℕ} (hn : 1 ≤ n) :
    carlesonExponent n * maximalLebesgueExponent n = 1 := by
  unfold carlesonExponent maximalLebesgueExponent
  have h0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-! ## §B Almost-everywhere subsequence recovery for every `L²` datum -/

set_option maxHeartbeats 1000000 in
/-- **[a.e. subsequence recovery, Eq. (7) upgraded]** for every `f ∈ L²(ℝⁿ)` — no Sobolev regularity — and
every sequence of times `tₖ → 0`, there is a subsequence along which the Schrödinger evolution converges to
the initial datum almost everywhere. Energy conservation and strong `L²` continuity
(`freeSchrodingerEvolution_tendsto_zero`) composed with the a.e.-subsequence extraction of
`Mathematics.LpAeConvergence`. The Carleson problem (Problem 1.1) is the strictly harder *continuum* limit
`t → 0₊`; this subsequence statement is the elementary baseline it refines. -/
@[zil_claim physlib.carleson.aeSubsequenceRecovery,
  zil_concept physics.carlesonPointwiseConvergence, zil_requires assumptions.l2InitialDatum,
  zil_export]
theorem schrodinger_ae_subsequence_recovery {n : ℕ} (f : EuclideanL2 n)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        Tendsto (fun k => ⇑(freeSchrodingerEvolution (t (φ k)) f) x)
          atTop (nhds (⇑f x)) := by
  have hL2 : Tendsto (fun k => freeSchrodingerEvolution (t k) f) atTop (nhds f) :=
    (freeSchrodingerEvolution_tendsto_zero f).comp ht
  have heLp : Tendsto
      (fun k => eLpNorm (⇑(freeSchrodingerEvolution (t k) f) - ⇑f) 2 volume)
      atTop (nhds 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun k => freeSchrodingerEvolution (t k) f) f).mp hL2
  exact ae_subseq_of_eLpNorm_tendsto (p := 2) (μ := volume)
    (f := fun k => ⇑(freeSchrodingerEvolution (t k) f)) (g := ⇑f) (by norm_num)
    (fun k => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable f) heLp


/-- **[The Borel–Cantelli step of Corollary 3.2]** on the unit ball: if the maximal functions `Mₖ` of the
dyadic Schwartz differences satisfy the `L²` bound `‖Mₖ‖_{L²(B)} ≤ 4⁻ᵏ` — what the Du–Zhang maximal estimate
(Thm. 3.1) supplies from `‖fₖ − fₖ₋₁‖_{H^s} ≲ 2^{−2k}` — then the exceptional set `E` of Cor. 3.2 is null:
almost every point of the ball has *summable* maximal values, so the telescoping series converges absolutely
and uniformly in `t` a.e. The maximal estimate itself is a hypothesis, not proved. -/
@[zil_claim physlib.carleson.borelCantelliMaximalStep,
  zil_concept physics.carlesonPointwiseConvergence, zil_requires assumptions.duZhangMaximalBound,
  zil_export]
theorem schrodinger_borelCantelli_maximal_step {n : ℕ}
    (M : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hM : ∀ k, AEStronglyMeasurable (M k)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball 0 1)))
    (hbound : ∀ k, eLpNorm (M k) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball 0 1))
        ≤ (4⁻¹ : ℝ≥0∞) ^ k) :
    ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball 0 1)),
      Summable (fun k => ‖M k x‖) :=
  ae_summable_norm_of_eLpNorm_le_geometric hM hbound

/-! ## §C The Sobolev data ladder -/

/-- **[`H^{s₂} ⊆ H^{s₁}` for `s₁ ≤ s₂`]** the Bessel-potential membership certificate is monotone: higher
regularity data classes are nested inside lower ones (`H⁰ = L²` at the bottom,
`hasSobolevRegularity_zero`), so the Carleson threshold slices a genuinely nested family. -/
@[zil_claim physlib.carleson.sobolevLadderNested,
  zil_concept physics.carlesonPointwiseConvergence, zil_requires assumptions.besselPotentialScale,
  zil_export]
theorem hasSobolevRegularity_mono {n : ℕ} {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂)
    (f : EuclideanL2 n) (h : HasSobolevRegularity s₂ f) :
    HasSobolevRegularity s₁ f := by
  refine h.of_le (aestronglyMeasurable_weightedFourier s₁ f) (ae_of_all _ fun ξ => ?_)
  unfold weightedFourier
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (besselPotentialWeight_pos s₁ ξ), abs_of_pos (besselPotentialWeight_pos s₂ ξ)]
  exact besselPotentialWeight_mono hs ξ

/-! ## §D The continuum limit (Corollary 3.2 finished) and the energy slab (Eq. 16) -/

/-- **[Telescoping continuum limit, Weierstrass form]** a series of continuous-in-`t` functions with summable
uniform bounds has a continuous sum on `[0,1]`, and therefore a genuine *continuum* limit as `t → 0` within
`[0,1]`, equal to its value at `t = 0`. The analytic skeleton of Cor. 3.2: once the maximal values are
summable, the limit in Problem 1.1 is over the continuum, not merely subsequences. -/
theorem telescoping_continuum_limit {h : ℕ → ℝ → ℂ} {u : ℕ → ℝ}
    (hcont : ∀ k, ContinuousOn (h k) (Set.Icc (0 : ℝ) 1))
    (hu : Summable u)
    (hbound : ∀ k t, t ∈ Set.Icc (0 : ℝ) 1 → ‖h k t‖ ≤ u k) :
    ContinuousOn (fun t => ∑' k, h k t) (Set.Icc (0 : ℝ) 1)
      ∧ Tendsto (fun t => ∑' k, h k t) (nhdsWithin 0 (Set.Icc (0 : ℝ) 1))
          (nhds (∑' k, h k 0)) := by
  have hL : ContinuousOn (fun t => ∑' k, h k t) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_tsum hcont hu hbound
  exact ⟨hL, hL 0 (by norm_num)⟩

/-- **[Corollary 3.2, conditional skeleton] the a.e. continuum limit.** Given the Du–Zhang maximal `L²`
bounds at dyadic rates (hypothesis), pointwise domination of the telescoped evolutions `hₖ(x,·)` by the
maximal values, and continuity in time of each term (automatic for Schwartz data), almost every point of the
unit ball has a genuine continuum limit `t → 0` of the telescoped solution — the precise formalisation of the
limit in Theorem 1.3 (Remark 1.4). Assembles the Borel–Cantelli step with the Weierstrass telescoping
limit. -/
@[zil_claim physlib.carleson.aeContinuumLimit,
  zil_concept physics.carlesonPointwiseConvergence, zil_requires assumptions.duZhangMaximalBound,
  zil_export]
theorem schrodinger_ae_continuum_limit {n : ℕ}
    (M : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (h : ℕ → EuclideanSpace ℝ (Fin n) → ℝ → ℂ)
    (hM : ∀ k, AEStronglyMeasurable (M k)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball 0 1)))
    (hbound : ∀ k, eLpNorm (M k) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball 0 1))
        ≤ (4⁻¹ : ℝ≥0∞) ^ k)
    (hcont : ∀ k x, ContinuousOn (h k x) (Set.Icc (0 : ℝ) 1))
    (hdom : ∀ k x t, t ∈ Set.Icc (0 : ℝ) 1 → ‖h k x t‖ ≤ M k x) :
    ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball 0 1)),
      Tendsto (fun t => ∑' k, h k x t) (nhdsWithin 0 (Set.Icc (0 : ℝ) 1))
        (nhds (∑' k, h k x 0)) := by
  filter_upwards [schrodinger_borelCantelli_maximal_step M hM hbound] with x hx
  exact (telescoping_continuum_limit (fun k => hcont k x) hx
    (fun k t ht => (hdom k x t ht).trans
      ((le_abs_self _).trans_eq (Real.norm_eq_abs _).symm))).2

/-- **[Eq. (16): the space-time energy slab]** conservation of energy integrated over the time slab:
`∫_{−R}^{R} ‖e^{itΔ}f‖² dt = 2R·‖f‖²` — the exact identity behind the *fractal energy* terminology, and
the `α = n+1` face of the Du–Zhang fractal energy estimate (Thm. 3.7). -/
@[zil_claim physlib.carleson.spacetimeEnergySlab,
  zil_concept physics.carlesonPointwiseConvergence, zil_requires assumptions.l2InitialDatum,
  zil_export]
theorem spacetime_energy_slab {n : ℕ} (f : EuclideanL2 n) (R : ℝ) :
    (∫ t in (-R)..R, ‖freeSchrodingerEvolution t f‖ ^ 2) = 2 * R * ‖f‖ ^ 2 := by
  have hcongr : Set.EqOn (fun t => ‖freeSchrodingerEvolution t f‖ ^ 2)
      (fun _ => ‖f‖ ^ 2) (Set.uIcc (-R) R) := fun t _ => by
    simp only [norm_freeSchrodingerEvolution]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **[The fractal exponent at `α = n+1` is `1/2`]** `(n+1)/(2(n+1)) = 1/2` — the top-dimensional case of
the Thm. 3.7 power `R^{α/(2(n+1))}` is exactly the `R^{1/2}` of the energy slab (Eq. 16): the fractal energy
estimate interpolates down from conservation of energy. -/
theorem fractalExponent_top (n : ℕ) : (((n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) = 1 / 2 := by
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-! ## §E Native ZIL claim graph and file contract -/

zil attach schrodinger_ae_subsequence_recovery where
  formalizes @ "claim:l2-ae-subsequence-recovery-for-schrodinger-flow",
  requires @ "claim:euclidean-l2-free-schrodinger-strong-continuity",
  requires @ "definition:lp-ae-subsequence-extraction",
  supported_by @ "paper:hickman-2304.02507",
  caveat @ "claim:subsequence-along-null-sequences-not-the-continuum-limit"

zil attach hasSobolevRegularity_mono where
  formalizes @ "claim:sobolev-data-ladder-is-nested",
  requires @ "definition:bessel-potential-weight-monotone",
  supported_by @ "paper:hickman-2304.02507"

zil attach carlesonExponent_lt_bourgainMultilinear where
  formalizes @ "claim:du-zhang-threshold-strictly-improves-bourgain-2013-range",
  supported_by @ "paper:du-zhang-2019",
  supported_by @ "paper:bourgain-2013-multilinear",
  caveat @ "claim:threshold-arithmetic-not-the-du-zhang-analysis"

zil attach tendsto_carlesonExponent_atTop where
  formalizes @ "claim:carleson-threshold-tends-to-one-half",
  supported_by @ "paper:hickman-2304.02507"

zil_theorem_intent schrodinger_ae_subsequence_recovery where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerEvolution]

zil_theorem_intent hasSobolevRegularity_mono where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.HasSobolevRegularity]

zil_theorem_intent carlesonExponent_lt_bourgainMultilinear where
  at_level structural
  must_mention [carlesonExponent, bourgainMultilinearExponent]

zil_theorem_intent tendsto_carlesonExponent_atTop where
  at_level structural
  must_mention [carlesonExponent]

zil attach schrodinger_borelCantelli_maximal_step where
  formalizes @ "claim:borel-cantelli-step-of-corollary-3-2",
  requires @ "assumption:du-zhang-maximal-bound",
  requires @ "definition:chebyshev-borel-cantelli-geometric-engine",
  supported_by @ "paper:hickman-2304.02507",
  caveat @ "claim:maximal-estimate-is-hypothesis-not-theorem"

zil attach carlesonExponent_mul_maximalLebesgueExponent where
  formalizes @ "claim:threshold-is-reciprocal-of-maximal-lebesgue-exponent",
  supported_by @ "paper:kenig-ponce-vega-1991",
  supported_by @ "paper:du-guth-li-zhang-2018"

zil_theorem_intent schrodinger_borelCantelli_maximal_step where
  at_level bridge_theorem
  must_mention [MeasureTheory.eLpNorm, Summable, Metric.ball]

zil_theorem_intent carlesonExponent_mul_maximalLebesgueExponent where
  at_level structural
  must_mention [carlesonExponent, maximalLebesgueExponent]

zil attach schrodinger_ae_continuum_limit where
  formalizes @ "claim:corollary-3-2-conditional-ae-continuum-limit",
  requires @ "claim:borel-cantelli-step-of-corollary-3-2",
  requires @ "definition:weierstrass-telescoping-continuum-limit",
  supported_by @ "paper:hickman-2304.02507",
  caveat @ "claim:maximal-estimate-is-hypothesis-not-theorem"

zil attach spacetime_energy_slab where
  formalizes @ "claim:spacetime-energy-slab-identity",
  requires @ "definition:free-schrodinger-energy-conservation",
  supported_by @ "paper:du-zhang-2019",
  caveat @ "claim:alpha-top-face-not-the-fractal-energy-estimate"

zil_theorem_intent schrodinger_ae_continuum_limit where
  at_level bridge_theorem
  must_mention [Filter.Tendsto, nhdsWithin, tsum]

zil_theorem_intent spacetime_energy_slab where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerEvolution,
    intervalIntegral]

zil_file_contract physlib.carlesonThreshold where
  promises "The Carleson problem's structural layer: the Du-Zhang threshold exponent n/(2(n+1)) with its sharp arithmetic (value 1/4 at n=1, strict monotonicity, bound and limit 1/2, strict improvement over Bourgain's multilinear range), almost-everywhere subsequence recovery of every L2 datum from strong continuity plus a.e. extraction, and the nested Sobolev data ladder."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerCarlesonThreshold.carlesonExponent",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerEvolution",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.HasSobolevRegularity",
    "lean:Physlib.Mathematics.LpAeConvergence.ae_subseq_of_eLpNorm_tendsto"]
  forbids_substitutes ["the Du-Zhang fractal L2 restriction analysis or any maximal estimate",
    "Bourgain's counterexample construction",
    "the continuum-limit almost-everywhere convergence of Problem 1.1 from the subsequence statement",
    "an identification of the threshold arithmetic with the analytic theorems it indexes"]
  witnessed_by [schrodinger_ae_subsequence_recovery, hasSobolevRegularity_mono,
    carlesonExponent_lt_bourgainMultilinear, tendsto_carlesonExponent_atTop,
    schrodinger_borelCantelli_maximal_step, carlesonExponent_mul_maximalLebesgueExponent,
    schrodinger_ae_continuum_limit, spacetime_energy_slab]

#zil_formalization_lint physlib.carlesonThreshold

end Physlib.QuantumMechanics.Schrodinger.SchrodingerCarlesonThreshold
