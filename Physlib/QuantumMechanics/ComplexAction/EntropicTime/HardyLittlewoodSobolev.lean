/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.SpaceAndTime.Space.Norm.Basic
public import Physlib.SpaceAndTime.Space.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
meta import Zil

/-!
# The Hardy–Littlewood–Sobolev convolution inequality via the layer-cake / geometric core

The Hardy–Littlewood–Sobolev inequality bounds the bilinear Riesz–Newton kernel form
`∬ f(x)·g(y)/‖x−y‖^λ` by `L^p × L^q` norms of the sources. Its layer-cake proof, after writing the
kernel through its distribution function, reduces to a purely geometric estimate on the measure of
near-diagonal pairs. This module builds that route to completion for **indicator sources**:

* the **geometric core** `∫_A μ(B ∩ ball(x,r)) dx ≤ μ(ball(0,r))·μ(A)`
  (`lintegral_measure_inter_ball_le`) — a ball of radius `r` about any point meets a set in at most the
  ball's own (translation-invariant) measure — and its symmetric form
  (`lintegral_measure_inter_ball_le_min`);
* the **product-measure form** `(vol×vol)({(x,y)∈A×B : ‖x−y‖<r}) ≤ μ(ball(0,r))·μ(A)`
  (`prod_measure_near_diagonal_le`), lifting the core via Fubini — the direct layer-cake input;
* the **bilinear HLS inequality** `∬_{A×B} ‖x−y‖^{-λ} ≤ ∫₀^∞ μ(A)·min(μ(ball(0,t^{-1/λ})), μ(B)) dt`
  (`bilinearRieszForm_le`), obtained by feeding the geometric core through the layer-cake formula
  (`lintegral_eq_lintegral_meas_lt`) applied to the kernel's super-level sets;
* the **crossover optimization** `∫₀^∞ min(c·t^{-p}, V) dt = (p/(p−1))·c^{1/p}·V^{1−1/p}`
  (`integral_Ioi_min_rpow`), the closed-form evaluation of that right-hand integral (`p = n/λ`,
  `c = μ(ball(0,1))`, `V = μ(B)`);
* the **sharp inequality** `∬_{A×B} ‖x−y‖^{-λ} ≤ (3/(3−λ))·μ(ball(0,1))^{λ/3}·μ(B)^{1−λ/3}·μ(A)`
  (`bilinearRieszForm_le_sharp`), the recognizable `μ(A)·μ(B)^{1−λ/3}` power law, obtained by feeding the
  bilinear bound through the crossover value and bridging `ℝ≥0∞`↔Bochner via the ball-volume cube
  `μ(ball(0,ρ)) = ρ^3·μ(ball(0,1))` (`Measure.addHaar_ball`), for `0 < λ < 3` and finite sources.

The crossover integral (ball-cap `μ(ball)·μ(A)` at small radius versus total cap `μ(A)·μ(B)` at large
radius) is finite exactly for `λ < n`, and its sharp value gives the constant. Only the general-`L^p`
case remains — it needs the Marcinkiewicz interpolation / rearrangement machinery absent from Mathlib.
-/

set_option autoImplicit false

open MeasureTheory Metric
open scoped ENNReal Space

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev

/-- **[The geometric core of Hardy–Littlewood–Sobolev]** the near-diagonal measure bound
`∫_A μ(B ∩ ball(x,r)) dx ≤ μ(ball(0,r))·μ(A)`: integrating over `A` the measure of `B` inside the
radius-`r` ball about each point is at most the (translation-invariant) ball measure times `μ(A)`. This
is the heart of the layer-cake route to the HLS convolution inequality. -/
@[zil_level physical_theorem]
theorem lintegral_measure_inter_ball_le (A B : Set (Space 3)) (r : ℝ) :
    ∫⁻ x in A, volume (B ∩ Metric.ball x r) ≤
      volume (Metric.ball (0 : Space 3) r) * volume A := by
  calc ∫⁻ x in A, volume (B ∩ Metric.ball x r)
      ≤ ∫⁻ x in A, volume (Metric.ball x r) :=
        lintegral_mono fun x => measure_mono Set.inter_subset_right
    _ = ∫⁻ _ in A, volume (Metric.ball (0 : Space 3) r) := by
        simp_rw [Measure.addHaar_ball_center]
    _ = volume (Metric.ball (0 : Space 3) r) * volume A := by
        rw [setLIntegral_const]

/-- **[The symmetric near-diagonal bound]** by symmetry of `‖x−y‖`, the same estimate holds
integrating over `B`, so `∫_A μ(B ∩ ball(x,r)) dx ≤ μ(ball(0,r))·min(μA,μB)` follows by taking the
smaller of the two source measures. -/
@[zil_level physical_theorem]
theorem lintegral_measure_inter_ball_le_min (A B : Set (Space 3)) (r : ℝ) :
    ∫⁻ x in A, volume (B ∩ Metric.ball x r) ≤
      volume (Metric.ball (0 : Space 3) r) * volume A
    ∧ ∫⁻ x in A, volume (B ∩ Metric.ball x r) ≤ volume B * volume A := by
  refine ⟨lintegral_measure_inter_ball_le A B r, ?_⟩
  calc ∫⁻ x in A, volume (B ∩ Metric.ball x r)
      ≤ ∫⁻ _ in A, volume B :=
        lintegral_mono fun x => measure_mono Set.inter_subset_left
    _ = volume B * volume A := by rw [setLIntegral_const]

/-- The near-diagonal pair set `{(x,y) ∈ A×B : ‖x−y‖ < r}` sliced at `x` gives `B ∩ ball(x,r)`. -/
private theorem mk_preimage_near_diagonal (A B : Set (Space 3)) (r : ℝ) {x : Space 3}
    (hx : x ∈ A) :
    Prod.mk x ⁻¹' ((A ×ˢ B) ∩ {p : Space 3 × Space 3 | ‖p.1 - p.2‖ < r}) =
      B ∩ Metric.ball x r := by
  ext y
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_setOf_eq,
    Metric.mem_ball, dist_eq_norm]
  rw [norm_sub_rev]
  tauto

/-- **[The near-diagonal pair measure in product form]** the `volume × volume` measure of the
near-diagonal pair set `{(x,y) ∈ A×B : ‖x−y‖ < r}` is bounded by `μ(ball(0,r))·μ(A)`. This lifts the
geometric core to the product measure via Fubini (`Measure.prod_apply`) — the direct input to a
layer-cake proof of the HLS bilinear bound, which recovers `∬_{A×B} ‖x−y‖^{-λ}` by integrating this
against the kernel's distribution function. -/
@[zil_level physical_theorem]
theorem prod_measure_near_diagonal_le (A B : Set (Space 3)) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (r : ℝ) :
    (volume.prod volume) ((A ×ˢ B) ∩ {p : Space 3 × Space 3 | ‖p.1 - p.2‖ < r}) ≤
      volume (Metric.ball (0 : Space 3) r) * volume A := by
  have hker : MeasurableSet {p : Space 3 × Space 3 | ‖p.1 - p.2‖ < r} :=
    measurableSet_lt (by fun_prop) measurable_const
  rw [Measure.prod_apply ((hA.prod hB).inter hker)]
  calc ∫⁻ x, volume (Prod.mk x ⁻¹' ((A ×ˢ B) ∩ {p : Space 3 × Space 3 | ‖p.1 - p.2‖ < r}))
      = ∫⁻ x, A.indicator (fun x => volume (B ∩ Metric.ball x r)) x := by
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ A
        · rw [mk_preimage_near_diagonal A B r hx, Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx]
          convert measure_empty (μ := volume)
          ext y
          simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_empty_iff_false,
            iff_false, not_and]
          exact fun h => absurd h.1 hx
    _ = ∫⁻ x in A, volume (B ∩ Metric.ball x r) := lintegral_indicator hA _
    _ ≤ volume (Metric.ball (0 : Space 3) r) * volume A := lintegral_measure_inter_ball_le A B r

/-- The Riesz kernel super-level set `{p | t < ‖p.1−p.2‖^{-λ}}` at level `t > 0` is contained in the
near-diagonal set `{p | ‖p.1−p.2‖ < t^{-1/λ}}`: `t < d^{-λ} ⟹ d < t^{-1/λ}` for `d = ‖p.1−p.2‖ ≥ 0`. -/
private theorem restrict_meas_lt_le (A B : Set (Space 3)) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (lam : ℝ) (hlam : 0 < lam) {t : ℝ} (ht : 0 < t) :
    ((volume.prod volume).restrict (A ×ˢ B))
        {p : Space 3 × Space 3 | t < ‖p.1 - p.2‖ ^ (-lam)} ≤
      volume A * min (volume (Metric.ball (0 : Space 3) (t ^ (-lam⁻¹)))) (volume B) := by
  rw [Measure.restrict_apply' (hA.prod hB)]
  have hsub : {p : Space 3 × Space 3 | t < ‖p.1 - p.2‖ ^ (-lam)} ∩ (A ×ˢ B) ⊆
      (A ×ˢ B) ∩ {p : Space 3 × Space 3 | ‖p.1 - p.2‖ < t ^ (-lam⁻¹)} := by
    rintro ⟨x, y⟩ ⟨hlt, hAB⟩
    refine ⟨hAB, ?_⟩
    simp only [Set.mem_setOf_eq] at hlt ⊢
    have hd0 : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
    rcases eq_or_lt_of_le hd0 with hd | hd
    · rw [← hd, Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt hlam))] at hlt
      exact absurd hlt (not_lt.mpr ht.le)
    · rw [Real.rpow_neg hd0] at hlt
      have hdlam : (0 : ℝ) < ‖x - y‖ ^ lam := Real.rpow_pos_of_pos hd lam
      rw [lt_inv_comm₀ ht hdlam] at hlt
      have hkey := (Real.lt_rpow_inv_iff_of_pos hd0 (inv_nonneg.mpr ht.le) hlam).mpr hlt
      rwa [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at hkey
  calc (volume.prod volume) ({p : Space 3 × Space 3 | t < ‖p.1 - p.2‖ ^ (-lam)} ∩ (A ×ˢ B))
      ≤ (volume.prod volume)
          ((A ×ˢ B) ∩ {p : Space 3 × Space 3 | ‖p.1 - p.2‖ < t ^ (-lam⁻¹)}) := measure_mono hsub
    _ ≤ volume A * min (volume (Metric.ball (0 : Space 3) (t ^ (-lam⁻¹)))) (volume B) := by
        rcases le_total (volume (Metric.ball (0 : Space 3) (t ^ (-lam⁻¹)))) (volume B) with hmm | hmm
        · rw [min_eq_left hmm, mul_comm]
          exact prod_measure_near_diagonal_le A B hA hB _
        · rw [min_eq_right hmm]
          calc (volume.prod volume)
                ((A ×ˢ B) ∩ {p : Space 3 × Space 3 | ‖p.1 - p.2‖ < t ^ (-lam⁻¹)})
              ≤ (volume.prod volume) (A ×ˢ B) := measure_mono Set.inter_subset_left
            _ = volume A * volume B := Measure.prod_prod A B

/-- **[The bilinear Riesz–Newton form is bounded by the layer-cake integral — Hardy–Littlewood–Sobolev
via the geometric core]** for measurable sources `A`, `B` and `0 < λ`,

  `∬_{A×B} ‖x−y‖^{-λ} ≤ ∫₀^∞ μ(A)·min(μ(ball(0,t^{-1/λ})), μ(B)) dt`.

The bilinear Riesz kernel form is bounded, through the layer-cake formula (`lintegral_eq_lintegral_meas_lt`)
applied to the kernel's distribution function, by the radial integral of the near-diagonal measure — the
crossover between the ball-measure cap `μ(ball)·μ(A)` (small radius) and the total cap `μ(A)·μ(B)` (large
radius). This is the Hardy–Littlewood–Sobolev bilinear inequality for indicator sources, assembled from
the geometric core (`prod_measure_near_diagonal_le`). Optimizing the crossover integral against
`t^{-n/λ}` recovers the sharp power law `μ(A)·μ(B)^{1−λ/n}`; that final computation and the general-`L^p`
case (which needs the Marcinkiewicz interpolation absent from Mathlib) are separate steps. -/
@[zil_level physical_theorem]
theorem bilinearRieszForm_le (A B : Set (Space 3)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (lam : ℝ) (hlam : 0 < lam) :
    ∫⁻ p in A ×ˢ B, ENNReal.ofReal (‖p.1 - p.2‖ ^ (-lam)) ∂(volume.prod volume) ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), volume A *
        min (volume (Metric.ball (0 : Space 3) (t ^ (-lam⁻¹)))) (volume B) := by
  have hf_nn : 0 ≤ᵐ[(volume.prod volume).restrict (A ×ˢ B)]
      fun p : Space 3 × Space 3 => ‖p.1 - p.2‖ ^ (-lam) :=
    Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _
  have hf_mble : AEMeasurable (fun p : Space 3 × Space 3 => ‖p.1 - p.2‖ ^ (-lam))
      ((volume.prod volume).restrict (A ×ˢ B)) := by
    apply Measurable.aemeasurable
    fun_prop
  rw [lintegral_eq_lintegral_meas_lt ((volume.prod volume).restrict (A ×ˢ B)) hf_nn hf_mble]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact restrict_meas_lt_le A B hA hB lam hlam ht

/-- **[The crossover optimization — sharp power law of the Riesz radial integral]** for `c, V > 0` and
`p > 1`,

  `∫₀^∞ min(c·t^{−p}, V) dt = (p/(p−1))·c^{1/p}·V^{1−1/p}`.

This is the closed-form evaluation of the crossover integral appearing on the right of
`bilinearRieszForm_le` (with `p = n/λ = 3/λ`, `c = μ(ball(0,1))`, `V = μ(B)`): the near-diagonal cap `V`
governs small radii `t < t₀ := (c/V)^{1/p}` and the decaying ball cap `c·t^{−p}` governs large radii,
and the split at the crossover `c·t₀^{−p} = V` gives the sharp power `V^{1−1/p}`. The far piece is the
improper power integral (`integral_Ioi_rpow_of_lt`, convergent exactly for `p > 1`, i.e. `λ < n`); the
identity `c·t₀^{1−p} = V·t₀` collapses both pieces onto `V·t₀ = c^{1/p}·V^{1−1/p}`. Feeding this into
`bilinearRieszForm_le` yields the sharp Hardy–Littlewood–Sobolev bound `μ(A)·μ(B)^{1−λ/n}` for indicator
sources. -/
@[zil_level physical_theorem]
theorem integral_Ioi_min_rpow (c V p : ℝ) (hc : 0 < c) (hV : 0 < V) (hp : 1 < p) :
    ∫ t in Set.Ioi (0 : ℝ), min (c * t ^ (-p)) V = p / (p - 1) * c ^ p⁻¹ * V ^ (1 - p⁻¹) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  set t₀ : ℝ := (c / V) ^ p⁻¹ with ht₀def
  have ht₀ : 0 < t₀ := Real.rpow_pos_of_pos (div_pos hc hV) _
  -- crossover identity `c · t₀^{−p} = V`
  have hcross : c * t₀ ^ (-p) = V := by
    rw [ht₀def, ← Real.rpow_mul (div_pos hc hV).le, mul_neg, inv_mul_cancel₀ hp0.ne',
      Real.rpow_neg_one, inv_div, mul_div_assoc', mul_comm c V, mul_div_assoc,
      div_self hc.ne', mul_one]
  -- `V · t₀ = c^{1/p} · V^{1−1/p}`
  have hVt₀ : V * t₀ = c ^ p⁻¹ * V ^ (1 - p⁻¹) := by
    rw [ht₀def, Real.div_rpow hc.le hV.le, Real.rpow_sub hV, Real.rpow_one]
    ring
  have heq1 : Set.EqOn (fun t => min (c * t ^ (-p)) V) (fun _ => V) (Set.Ioc 0 t₀) := by
    intro t ht
    show min (c * t ^ (-p)) V = V
    refine min_eq_right ?_
    rw [← hcross]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ht.1 ht.2 (by linarith)) hc.le
  have heq2 : Set.EqOn (fun t => min (c * t ^ (-p)) V) (fun t => c * t ^ (-p)) (Set.Ioi t₀) := by
    intro t ht
    show min (c * t ^ (-p)) V = c * t ^ (-p)
    refine min_eq_left ?_
    rw [← hcross]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ht₀ (le_of_lt ht) (by linarith)) hc.le
  have hint1 : IntegrableOn (fun t => min (c * t ^ (-p)) V) (Set.Ioc 0 t₀) := by
    have hconst : IntegrableOn (fun _ : ℝ => V) (Set.Ioc 0 t₀) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    exact hconst.congr_fun heq1.symm measurableSet_Ioc
  have hint2 : IntegrableOn (fun t => min (c * t ^ (-p)) V) (Set.Ioi t₀) := by
    have hbase : IntegrableOn (fun t : ℝ => c * t ^ (-p)) (Set.Ioi t₀) :=
      Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (show (-p : ℝ) < -1 by linarith) ht₀) c
    exact hbase.congr_fun heq2.symm measurableSet_Ioi
  have hI1 : ∫ t in Set.Ioc (0 : ℝ) t₀, min (c * t ^ (-p)) V = V * t₀ := by
    rw [setIntegral_congr_fun measurableSet_Ioc heq1, setIntegral_const,
      Real.volume_real_Ioc_of_le ht₀.le, sub_zero, smul_eq_mul, mul_comm]
  have hI2 : ∫ t in Set.Ioi t₀, min (c * t ^ (-p)) V = V * t₀ / (p - 1) := by
    have hpow : ∫ t in Set.Ioi t₀, t ^ (-p) = -t₀ ^ (-p + 1) / (-p + 1) :=
      integral_Ioi_rpow_of_lt (by linarith) ht₀
    rw [setIntegral_congr_fun measurableSet_Ioi heq2, integral_const_mul, hpow]
    have hk : c * t₀ ^ (-p + 1) = V * t₀ := by
      rw [Real.rpow_add ht₀, Real.rpow_one, ← mul_assoc, hcross]
    rw [show c * (-t₀ ^ (-p + 1) / (-p + 1)) = -(c * t₀ ^ (-p + 1)) / (-p + 1) by ring, hk,
      show (-p : ℝ) + 1 = -(p - 1) by ring, neg_div_neg_eq]
  rw [← Set.Ioc_union_Ioi_eq_Ioi ht₀.le,
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint1 hint2, hI1, hI2,
    mul_assoc, ← hVt₀]
  field_simp
  ring

/-- The crossover integrand `min(c·t^{−p}, V)` is integrable on `(0,∞)` for `p > 1`: split at radius
`1`, bounded by the constant `V` on `(0,1]` and by the integrable tail `c·t^{−p}` on `(1,∞)`. -/
private theorem integrableOn_Ioi_min_rpow (c V p : ℝ) (hc : 0 < c) (hV : 0 < V) (hp : 1 < p) :
    IntegrableOn (fun t => min (c * t ^ (-p)) V) (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one (α := ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (integrableOn_const (C := V) (hs := measure_Ioc_lt_top.ne)) ?_ ?_
    · exact (Measurable.min (by fun_prop) measurable_const).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs,
        abs_of_nonneg (le_min (mul_nonneg hc.le (Real.rpow_nonneg ht.1.le _)) hV.le)]
      exact min_le_right _ _
  · refine Integrable.mono' (Integrable.const_mul
      (integrableOn_Ioi_rpow_of_lt (show (-p : ℝ) < -1 by linarith) one_pos) c) ?_ ?_
    · exact (Measurable.min (by fun_prop) measurable_const).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : (0 : ℝ) < t := lt_trans one_pos ht
      rw [Real.norm_eq_abs,
        abs_of_nonneg (le_min (mul_nonneg hc.le (Real.rpow_nonneg htpos.le _)) hV.le)]
      exact min_le_left _ _

/-- **[The sharp Hardy–Littlewood–Sobolev inequality for indicator sources]** for measurable `A`, `B` of
finite measure and `0 < λ < 3`,

  `∬_{A×B} ‖x−y‖^{-λ} ≤ (3/(3−λ))·μ(ball(0,1))^{λ/3}·μ(B)^{1−λ/3}·μ(A)`.

The fully assembled HLS bilinear inequality: the bilinear layer-cake bound (`bilinearRieszForm_le`) fed
through the sharp crossover value (`integral_Ioi_min_rpow`, with `p = n/λ = 3/λ`, `c = μ(ball(0,1))`,
`V = μ(B)`), bridged from `ℝ≥0∞` to the Bochner integral (`ofReal_integral_eq_lintegral_ofReal`) using
the ball-volume cube `μ(ball(0,r)) = r^3·μ(ball(0,1))` (`Measure.addHaar_ball`). This is the recognizable
`μ(A)·μ(B)^{1−λ/3}` power law. This module remains the sharp indicator-source layer. The repository's
separate maximal-function development now supplies the general-density Newtonian case; it does not
retroactively make this indicator constant a sharp constant for arbitrary densities. -/
@[zil_level physical_theorem]
theorem bilinearRieszForm_le_sharp (A B : Set (Space 3)) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAfin : volume A ≠ ∞) (hBfin : volume B ≠ ∞)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam3 : lam < 3) :
    ∫⁻ p in A ×ˢ B, ENNReal.ofReal (‖p.1 - p.2‖ ^ (-lam)) ∂(volume.prod volume) ≤
      ENNReal.ofReal (3 / (3 - lam) * (volume (Metric.ball (0 : Space 3) 1)).toReal ^ (lam / 3)
        * (volume B).toReal ^ (1 - lam / 3)) * volume A := by
  refine (bilinearRieszForm_le A B hA hB lam hlam0).trans ?_
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0∞) ≤ volume B) with hB0 | hBpos
  · have hz : ∀ t : ℝ, volume A *
        min (volume (Metric.ball (0 : Space 3) (t ^ (-lam⁻¹)))) (volume B) = 0 := fun t => by
      rw [← hB0, min_eq_right zero_le, mul_zero]
    rw [lintegral_congr hz, lintegral_zero]
    exact zero_le
  · have hlamne : lam ≠ 0 := hlam0.ne'
    have h3lamne : (3 : ℝ) - lam ≠ 0 := by linarith
    have hball1_fin : volume (Metric.ball (0 : Space 3) 1) ≠ ∞ := by
      rw [Space.volume_metricBall_three]; exact ENNReal.ofReal_ne_top
    have hball1_pos : 0 < volume (Metric.ball (0 : Space 3) 1) := by
      rw [Space.volume_metricBall_three]; exact ENNReal.ofReal_pos.mpr (by positivity)
    have hc : 0 < (volume (Metric.ball (0 : Space 3) 1)).toReal :=
      ENNReal.toReal_pos hball1_pos.ne' hball1_fin
    have hV : 0 < (volume B).toReal := ENNReal.toReal_pos hBpos.ne' hBfin
    have hp : 1 < 3 / lam := (one_lt_div hlam0).mpr (by linarith)
    have hmono : Monotone ENNReal.ofReal := fun _ _ h => ENNReal.ofReal_le_ofReal h
    have hcube : ∀ {t : ℝ}, 0 < t →
        volume (Metric.ball (0 : Space 3) (t ^ (-lam⁻¹)))
          = ENNReal.ofReal ((volume (Metric.ball (0 : Space 3) 1)).toReal * t ^ (-(3 / lam))) := by
      intro t ht
      have hr : (0 : ℝ) ≤ t ^ (-lam⁻¹) := Real.rpow_nonneg ht.le _
      rw [Measure.addHaar_ball volume 0 hr, Space.finrank_eq_dim,
        ← Real.rpow_natCast (t ^ (-lam⁻¹)) 3, ← Real.rpow_mul ht.le,
        show (-lam⁻¹ * ((3 : ℕ) : ℝ)) = -(3 / lam) by push_cast; rw [div_eq_mul_inv]; ring,
        ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hball1_fin, mul_comm]
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun t => min ((volume (Metric.ball (0 : Space 3) 1)).toReal * t ^ (-(3 / lam)))
          ((volume B).toReal) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact le_min (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg ht.le _))
        ENNReal.toReal_nonneg
    have hlint : ∫⁻ t in Set.Ioi (0 : ℝ),
          min (volume (Metric.ball (0 : Space 3) (t ^ (-lam⁻¹)))) (volume B)
        = ENNReal.ofReal (3 / (3 - lam) * (volume (Metric.ball (0 : Space 3) 1)).toReal ^ (lam / 3)
            * (volume B).toReal ^ (1 - lam / 3)) := by
      rw [show (3 / (3 - lam) * (volume (Metric.ball (0 : Space 3) 1)).toReal ^ (lam / 3)
            * (volume B).toReal ^ (1 - lam / 3) : ℝ)
          = ∫ t in Set.Ioi (0 : ℝ),
              min ((volume (Metric.ball (0 : Space 3) 1)).toReal * t ^ (-(3 / lam)))
                ((volume B).toReal) from ?_]
      · rw [ofReal_integral_eq_lintegral_ofReal
          (integrableOn_Ioi_min_rpow _ _ (3 / lam) hc hV hp) hnn]
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [hcube ht, hmono.map_min, ENNReal.ofReal_toReal hBfin]
      · rw [integral_Ioi_min_rpow _ _ (3 / lam) hc hV hp]
        simp only [inv_div]
        have hd : (3 : ℝ) / lam - 1 ≠ 0 := by
          rw [show (3 : ℝ) / lam - 1 = (3 - lam) / lam by field_simp]
          exact div_ne_zero h3lamne hlamne
        rw [show (3 / lam) / (3 / lam - 1) = 3 / (3 - lam) by
          rw [div_eq_div_iff hd h3lamne]; field_simp]
    rw [lintegral_const_mul' (volume A)
        (fun t => min (volume (Metric.ball (0 : Space 3) (t ^ (-lam⁻¹)))) (volume B)) hAfin,
      hlint]
    exact le_of_eq (mul_comm _ _)

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev.lintegral_measure_inter_ball_le where
  formalizes @ "claim:the-geometric-core-of-the-hardy-littlewood-sobolev-convolution-inequality-the-near-diagonal-measure-bound-the-integral-over-a-of-the-measure-of-b-intersect-the-radius-r-ball-about-each-point-is-at-most-the-translation-invariant-ball-measure-times-the-measure-of-a",
  supported_by @ "lean:MeasureTheory.Measure.addHaar_ball_center"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev.bilinearRieszForm_le where
  formalizes @ "claim:the-hardy-littlewood-sobolev-bilinear-inequality-for-indicator-sources-the-bilinear-riesz-newton-kernel-form-the-double-integral-of-norm-x-minus-y-to-the-minus-lambda-over-a-cross-b-is-bounded-through-the-layer-cake-formula-by-the-radial-integral-of-mu-a-times-the-min-of-the-ball-measure-cap-and-the-total-measure-cap",
  supported_by @ "lean:MeasureTheory.lintegral_eq_lintegral_meas_lt",
  caveat @ "claim:the-bilinear-hls-inequality-is-proven-for-indicator-sources-the-general-lp-case-requires-the-marcinkiewicz-interpolation-machinery-absent-from-mathlib"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev.integral_Ioi_min_rpow where
  formalizes @ "claim:the-crossover-optimization-the-improper-radial-integral-over-t-in-zero-infinity-of-the-min-of-c-times-t-to-the-minus-p-and-v-equals-p-over-p-minus-one-times-c-to-the-one-over-p-times-v-to-the-one-minus-one-over-p-the-closed-form-sharp-value-of-the-crossover-integral-in-the-hardy-littlewood-sobolev-bound",
  supported_by @ "lean:integral_Ioi_rpow_of_lt"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev.bilinearRieszForm_le_sharp where
  formalizes @ "claim:the-sharp-hardy-littlewood-sobolev-inequality-for-indicator-sources-the-double-integral-of-norm-x-minus-y-to-the-minus-lambda-over-a-cross-b-is-at-most-three-over-three-minus-lambda-times-the-measure-of-the-unit-ball-to-the-lambda-over-three-times-the-measure-of-b-to-the-one-minus-lambda-over-three-times-the-measure-of-a-the-recognizable-mu-a-times-mu-b-power-law",
  supported_by @ "lean:MeasureTheory.Measure.addHaar_ball",
  supported_by @ "lean:MeasureTheory.ofReal_integral_eq_lintegral_ofReal",
  caveat @ "claim:the-sharp-constant-here-is-proven-for-indicator-sources-with-finite-measure-and-lambda-strictly-between-zero-and-three-the-separate-general-density-newtonian-hls-theorem-uses-an-explicit-maximal-function-constant-not-claimed-sharp"

zil_file_contract physlib.hardyLittlewoodSobolev where
  promises "The sharp Hardy-Littlewood-Sobolev convolution inequality for indicator sources, assembled via the layer-cake / geometric core. The HLS inequality bounds the bilinear Riesz-Newton kernel form over measurable sets through translation-invariant ball geometry and a sharp radial crossover integral. bilinearRieszForm_le_sharp is the fully assembled indicator theorem for zero less than lambda less than three. Honest current scope: this file's sharp constant is an indicator-source result. The repository now has a separate maximal-function and Marcinkiewicz development proving the general-density Newtonian lambda-one case with an explicit constant; that downstream constant is not claimed to be the sharp Lieb constant."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:MeasureTheory.Measure.addHaar_ball_center",
    "lean:MeasureTheory.setLIntegral_const",
    "lean:MeasureTheory.lintegral_eq_lintegral_meas_lt",
    "lean:MeasureTheory.Measure.prod_apply",
    "lean:integral_Ioi_rpow_of_lt",
    "lean:MeasureTheory.Measure.addHaar_ball",
    "lean:MeasureTheory.ofReal_integral_eq_lintegral_ofReal"]
  forbids_substitutes ["a fixed-center ball, whereas the estimate uses translation invariance over all centers x in A",
    "the downstream general-density Newtonian HLS theorem, whereas this file proves the sharp indicator-source inequality via the layer-cake and geometric core",
    "a divergent or non-sharp crossover integral, whereas integral_Ioi_min_rpow gives the finite sharp closed form valid exactly for p greater than one",
    "an unconstrained exponent, whereas the sharp inequality holds for lambda strictly between zero and three with finite source measures"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev.lintegral_measure_inter_ball_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev.lintegral_measure_inter_ball_le_min,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev.prod_measure_near_diagonal_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev.bilinearRieszForm_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev.integral_Ioi_min_rpow,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodSobolev.bilinearRieszForm_le_sharp]

/- ZIL-END -/
