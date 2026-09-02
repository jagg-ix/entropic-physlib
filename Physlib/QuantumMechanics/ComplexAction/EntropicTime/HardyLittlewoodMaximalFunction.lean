/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.SpaceAndTime.Space.Norm.Basic
public import Physlib.SpaceAndTime.Space.Integrals.Basic
public import Physlib.SpaceAndTime.Space.Module
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
meta import Zil

/-!
# The Hardy–Littlewood maximal function

This module builds the centered Hardy–Littlewood maximal function on `Space 3` and its basic
properties, as the foundation for a general-density Hardy–Littlewood–Sobolev inequality (Mathlib has no
maximal-function theory of its own — only the Vitali/Besicovitch covering lemmas this is built on).

  `maximalFunction f x = ⨆_{q>0 rational} (μ(ball(x,q)))⁻¹ · ∫_{ball(x,q)} f`.

Using **rational** radii keeps the supremum countable, so the maximal function is measurable by
`measurable_iSup` (`measurable_maximalFunction`). This file also proves the **local-average bounds**: the
average over a rational ball is at most `Mf` (`average_le_maximalFunction`), and the integral over an
arbitrary real ball is at most `8·μ(ball)·Mf` (`lintegral_ball_le_maximalFunction`, via a rational radius
in `(r,2r)`) — the estimate feeding the near-diagonal part of Hedberg's inequality.

The completed interpolation layer proves:

* weak `(1,1)` and its truncated form;
* the `Lᵖ` tail inequality and the genuine weak-`(p,p)` distribution estimate;
* almost-everywhere finiteness of `Mf` from finite `Lᵖ` mass alone;
* the strong `(p,p)` maximal inequality without a separate `L¹` premise;
* Hedberg's pointwise inequality and the general-density Newtonian HLS bound for every
  measurable `ρ ∈ L^(6/5)`.
-/

set_option autoImplicit false

open MeasureTheory Metric
open scoped ENNReal Space

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction

/-- The **centered Hardy–Littlewood maximal function** of `f : Space 3 → ℝ≥0∞`, as the supremum over
positive **rational** radii of the average of `f` on the ball of radius `q` about `x`. Rational radii
keep the supremum countable (hence measurable). -/
noncomputable def maximalFunction (f : Space 3 → ℝ≥0∞) (x : Space 3) : ℝ≥0∞ :=
  ⨆ (q : ℚ) (_ : 0 < q), (volume (Metric.ball x (q : ℝ)))⁻¹ * ∫⁻ y in Metric.ball x (q : ℝ), f y

/-- The average of `f` on a rational ball is at most the maximal function (immediate from the sup). -/
theorem average_le_maximalFunction (f : Space 3 → ℝ≥0∞) (x : Space 3) {q : ℚ} (hq : 0 < q) :
    (volume (Metric.ball x (q : ℝ)))⁻¹ * ∫⁻ y in Metric.ball x (q : ℝ), f y ≤ maximalFunction f x := by
  unfold maximalFunction
  exact le_iSup_of_le q (le_iSup_of_le hq le_rfl)

/-- **[Measurability of the maximal function]** the Hardy–Littlewood maximal function of a measurable
function is measurable — a countable supremum (over rational radii) of measurable averages. -/
@[zil_level physical_theorem]
theorem measurable_maximalFunction (f : Space 3 → ℝ≥0∞) (hf : Measurable f) :
    Measurable (maximalFunction f) := by
  unfold maximalFunction
  refine Measurable.iSup fun q => Measurable.iSup fun _ => ?_
  refine Measurable.mul ?_ ?_
  · have hcongr : (fun x : Space 3 => (volume (Metric.ball x (q : ℝ)))⁻¹)
        = fun _ => (volume (Metric.ball (0 : Space 3) (q : ℝ)))⁻¹ := by
      funext x; rw [Measure.addHaar_ball_center]
    rw [hcongr]; exact measurable_const
  · have huncurry : Measurable
        (Function.uncurry fun x y : Space 3 => (Metric.ball x (q : ℝ)).indicator f y) := by
      have hset : MeasurableSet {p : Space 3 × Space 3 | dist p.2 p.1 < (q : ℝ)} :=
        measurableSet_lt (by fun_prop) measurable_const
      exact Measurable.indicator (hf.comp measurable_snd) hset
    have hlp := huncurry.lintegral_prod_right (ν := volume)
    simpa only [lintegral_indicator, measurableSet_ball] using hlp

/-- **[The local-average bound]** the integral of `f` over an arbitrary real ball `ball(x,r)` is at
most `8·μ(ball(x,r))·Mf(x)`: pass to a rational radius `q ∈ (r, 2r)`, whose ball has measure at most
`8·μ(ball(x,r))`. This is the estimate feeding the near-diagonal part of Hedberg's inequality. -/
@[zil_level physical_theorem]
theorem lintegral_ball_le_maximalFunction (f : Space 3 → ℝ≥0∞) (x : Space 3) {r : ℝ} (hr : 0 < r) :
    ∫⁻ y in Metric.ball x r, f y ≤ 8 * volume (Metric.ball x r) * maximalFunction f x := by
  obtain ⟨q, hrq, hq2r⟩ := exists_rat_btwn (show r < 2 * r by linarith)
  have hq0 : (0 : ℝ) < q := lt_trans hr hrq
  have hqpos : 0 < q := by exact_mod_cast hq0
  have hball_pos : 0 < volume (Metric.ball x (q : ℝ)) := measure_ball_pos volume x hq0
  have hball_ne : volume (Metric.ball x (q : ℝ)) ≠ ∞ := measure_ball_lt_top.ne
  calc ∫⁻ y in Metric.ball x r, f y
      ≤ ∫⁻ y in Metric.ball x (q : ℝ), f y :=
        lintegral_mono_set (Metric.ball_subset_ball hrq.le)
    _ = volume (Metric.ball x (q : ℝ)) *
          ((volume (Metric.ball x (q : ℝ)))⁻¹ * ∫⁻ y in Metric.ball x (q : ℝ), f y) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hball_pos.ne' hball_ne, one_mul]
    _ ≤ volume (Metric.ball x (q : ℝ)) * maximalFunction f x :=
        mul_le_mul_of_nonneg_left (average_le_maximalFunction f x hqpos) zero_le
    _ ≤ 8 * volume (Metric.ball x r) * maximalFunction f x := by
        refine mul_le_mul_of_nonneg_right ?_ zero_le
        calc volume (Metric.ball x (q : ℝ))
            ≤ volume (Metric.ball x (2 * r)) := measure_mono (Metric.ball_subset_ball hq2r.le)
          _ = 8 * volume (Metric.ball x r) := by
              rw [Measure.addHaar_ball _ _ (by linarith : (0:ℝ) ≤ 2 * r),
                Measure.addHaar_ball _ _ hr.le, Space.finrank_eq_dim]
              rw [show ((2 * r) ^ (3 : ℕ) : ℝ) = 8 * r ^ (3 : ℕ) by ring,
                ENNReal.ofReal_mul (by norm_num), ← mul_assoc]
              norm_num

/-- At a point where `Mf(x) > t`, some rational ball has mean `> t`, i.e.
`t·μ(ball(x,q)) < ∫_{ball(x,q)} f` — the ball selected for the Vitali covering in the weak-(1,1) bound. -/
theorem exists_ball_of_lt_maximalFunction (f : Space 3 → ℝ≥0∞) {x : Space 3} {t : ℝ≥0∞}
    (hx : t < maximalFunction f x) :
    ∃ q : ℚ, 0 < q ∧ t * volume (Metric.ball x (q : ℝ)) < ∫⁻ y in Metric.ball x (q : ℝ), f y := by
  rw [maximalFunction, lt_iSup_iff] at hx
  obtain ⟨q, hq⟩ := hx
  rw [lt_iSup_iff] at hq
  obtain ⟨hq0, hlt⟩ := hq
  refine ⟨q, hq0, ?_⟩
  have hball_pos : 0 < volume (Metric.ball x (q : ℝ)) :=
    measure_ball_pos volume x (by exact_mod_cast hq0)
  have hball_ne : volume (Metric.ball x (q : ℝ)) ≠ ∞ := measure_ball_lt_top.ne
  have hmul := ENNReal.mul_lt_mul_right hball_pos.ne' hball_ne hlt
  rwa [← mul_assoc, ENNReal.mul_inv_cancel hball_pos.ne' hball_ne, one_mul, mul_comm] at hmul

/-- Monotonicity of the maximal function. -/
theorem maximalFunction_mono {f g : Space 3 → ℝ≥0∞} (h : f ≤ g) :
    maximalFunction f ≤ maximalFunction g := by
  intro x
  refine iSup_le fun q => iSup_le fun hq => ?_
  refine le_trans ?_ (average_le_maximalFunction g x hq)
  exact mul_le_mul_of_nonneg_left (lintegral_mono fun y => h y) zero_le

/-- Subadditivity of the maximal function: `M(f+g) ≤ Mf + Mg`. -/
theorem maximalFunction_add_le {f g : Space 3 → ℝ≥0∞} (hf : Measurable f) :
    maximalFunction (f + g) ≤ maximalFunction f + maximalFunction g := by
  intro x
  refine iSup_le fun q => iSup_le fun hq => ?_
  have hadd : ∫⁻ y in Metric.ball x (q : ℝ), (f + g) y
      = (∫⁻ y in Metric.ball x (q : ℝ), f y) + ∫⁻ y in Metric.ball x (q : ℝ), g y := by
    simp_rw [Pi.add_apply]
    exact lintegral_add_left hf _
  rw [hadd, mul_add]
  exact add_le_add (average_le_maximalFunction f x hq) (average_le_maximalFunction g x hq)

/-- If `f ≤ c` pointwise for a constant `c`, then `Mf ≤ c`: every ball average of `f` is `≤ c`. -/
theorem maximalFunction_le_const {f : Space 3 → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ y, f y ≤ c) :
    maximalFunction f ≤ fun _ => c := by
  intro x
  refine iSup_le fun q => iSup_le fun hq => ?_
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hball_pos : 0 < volume (Metric.ball x (q : ℝ)) := measure_ball_pos volume x hq0
  have hball_ne : volume (Metric.ball x (q : ℝ)) ≠ ∞ := measure_ball_lt_top.ne
  calc (volume (Metric.ball x (q : ℝ)))⁻¹ * ∫⁻ y in Metric.ball x (q : ℝ), f y
      ≤ (volume (Metric.ball x (q : ℝ)))⁻¹ * ∫⁻ _ in Metric.ball x (q : ℝ), c :=
        mul_le_mul_of_nonneg_left (lintegral_mono fun y => h y) zero_le
    _ = c := by
        rw [setLIntegral_const, ← mul_assoc, mul_comm (volume (Metric.ball x (q : ℝ)))⁻¹ c,
          mul_assoc, ENNReal.inv_mul_cancel hball_pos.ne' hball_ne, mul_one]

/-- **[The weak-(1,1) bound]** the Hardy–Littlewood maximal function satisfies the weak-type `(1,1)`
estimate `t·μ{Mf > t} ≤ 64·∫f`, via the Vitali covering theorem: cover the super-level set by balls of
mean `> t`, extract a disjoint subfamily whose `4×`-enlargements still cover, and sum. The constant `64`
is the enlargement factor `4³`. -/
@[zil_level physical_theorem]
theorem weak_1_1 (f : Space 3 → ℝ≥0∞) (hf : Measurable f) {t : ℝ≥0∞} (ht : 0 < t) (htop : t ≠ ∞) :
    t * volume {x | t < maximalFunction f x} ≤ 64 * ∫⁻ y, f y := by
  rcases eq_or_ne (∫⁻ y, f y) ∞ with hinf | hfin
  · rw [hinf, ENNReal.mul_top (by norm_num : (64 : ℝ≥0∞) ≠ 0)]; exact le_top
  classical
  set E := {x : Space 3 | t < maximalFunction f x} with hE
  -- select, for each point of E, a ball of mean > t
  have hsel : ∀ x : Space 3, x ∈ E → ∃ q : ℚ, 0 < q ∧
      t * volume (Metric.ball x (q : ℝ)) < ∫⁻ y in Metric.ball x (q : ℝ), f y :=
    fun x hx => exists_ball_of_lt_maximalFunction f hx
  set r : Space 3 → ℝ := fun x => if h : x ∈ E then ((hsel x h).choose : ℝ) else 0 with hr_def
  have hr_pos : ∀ x ∈ E, 0 < r x := by
    intro x hx; rw [hr_def]; simp only [hx, dif_pos]; exact_mod_cast (hsel x hx).choose_spec.1
  have hr_spec : ∀ x ∈ E,
      t * volume (Metric.ball x (r x)) < ∫⁻ y in Metric.ball x (r x), f y := by
    intro x hx; rw [hr_def]; simp only [hx, dif_pos]; exact (hsel x hx).choose_spec.2
  -- the radii are bounded (from the L¹ constraint `t·μ(ball) < ∫f`)
  have hball1_pos : 0 < (volume (Metric.ball (0 : Space 3) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hK_ne : (∫⁻ y, f y) / t ≠ ∞ := ENNReal.div_ne_top hfin ht.ne'
  set R : ℝ := (((∫⁻ y, f y) / t).toReal / (volume (Metric.ball (0 : Space 3) 1)).toReal)
    ^ (1 / 3 : ℝ) + 1 with hR_def
  have hr_bound : ∀ x ∈ E, r x ≤ R := by
    intro x hx
    have hrx_nn : 0 ≤ r x := (hr_pos x hx).le
    have hlt : t * volume (Metric.ball x (r x)) < ∫⁻ y, f y :=
      lt_of_lt_of_le (hr_spec x hx) (setLIntegral_le_lintegral _ _)
    have hvol_lt : volume (Metric.ball x (r x)) < (∫⁻ y, f y) / t := by
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl ht.ne') (Or.inl htop)]; rwa [mul_comm]
    have hcube : (r x) ^ 3 ≤
        ((∫⁻ y, f y) / t).toReal / (volume (Metric.ball (0 : Space 3) 1)).toReal := by
      rw [le_div_iff₀ hball1_pos]
      have heq : (r x) ^ 3 * (volume (Metric.ball (0 : Space 3) 1)).toReal
          = (volume (Metric.ball x (r x))).toReal := by
        rw [Measure.addHaar_ball _ _ hrx_nn, Space.finrank_eq_dim, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (pow_nonneg hrx_nn 3)]
      rw [heq]
      exact le_of_lt ((ENNReal.toReal_lt_toReal measure_ball_lt_top.ne hK_ne).mpr hvol_lt)
    have hbase_nn : (0 : ℝ) ≤
        ((∫⁻ y, f y) / t).toReal / (volume (Metric.ball (0 : Space 3) 1)).toReal := by positivity
    calc r x = ((r x) ^ 3) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_natCast (r x) 3, ← Real.rpow_mul hrx_nn]; norm_num
      _ ≤ (((∫⁻ y, f y) / t).toReal / (volume (Metric.ball (0 : Space 3) 1)).toReal) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hcube (by norm_num)
      _ ≤ R := by rw [hR_def]; linarith [Real.rpow_nonneg hbase_nn (1 / 3 : ℝ)]
  obtain ⟨u, huE, hu_disj, hu_cover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall E (fun x => x) r R hr_bound
      4 (by norm_num)
  -- E is covered by the 4×-enlarged balls
  have hEsub : E ⊆ ⋃ b ∈ u, Metric.closedBall b (4 * r b) := by
    intro a ha
    obtain ⟨b, hbu, hsub⟩ := hu_cover a ha
    exact Set.mem_biUnion hbu (hsub (Metric.mem_closedBall_self (hr_pos a ha).le))
  -- the disjoint subfamily is countable
  have hu_count : u.Countable := by
    have hcount := Measure.countable_meas_pos_of_disjoint_iUnion (μ := volume)
      (As := fun b : ↥u => Metric.closedBall (b : Space 3) (r b))
      (fun _ => measurableSet_closedBall)
      (fun i j hij => hu_disj i.2 j.2 (Subtype.coe_ne_coe.mpr hij))
    have huniv : {b : ↥u | 0 < volume (Metric.closedBall (b : Space 3) (r b))} = Set.univ := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact measure_closedBall_pos volume _ (hr_pos b.1 (huE b.2))
    rw [huniv] at hcount
    exact Set.countable_coe_iff.mp (Set.countable_univ_iff.mp hcount)
  -- the open balls (⊆ the disjoint closed balls) are disjoint
  have hball_disj : u.PairwiseDisjoint fun b => Metric.ball b (r b) :=
    hu_disj.mono fun b => Metric.ball_subset_closedBall
  have hball_spec : ∀ b ∈ u, t * volume (Metric.ball b (r b)) ≤ ∫⁻ y in Metric.ball b (r b), f y :=
    fun b hb => (hr_spec b (huE hb)).le
  calc t * volume E
      ≤ t * ∑' b : ↥u, volume (Metric.closedBall (b : Space 3) (4 * r b)) := by
        refine mul_le_mul_of_nonneg_left ((measure_mono hEsub).trans ?_) zero_le
        exact measure_biUnion_le volume hu_count _
    _ = 64 * ∑' b : ↥u, t * volume (Metric.ball (b : Space 3) (r b)) := by
        have hterm : ∀ b : ↥u, volume (Metric.closedBall (b : Space 3) (4 * r b))
            = 64 * volume (Metric.ball (b : Space 3) (r b)) := by
          intro b
          have hrb : 0 ≤ r b.1 := (hr_pos b.1 (huE b.2)).le
          rw [Measure.addHaar_closedBall_eq_addHaar_ball,
            Measure.addHaar_ball _ _ (by positivity : (0 : ℝ) ≤ 4 * r b.1),
            Measure.addHaar_ball _ _ hrb, Space.finrank_eq_dim,
            show ((4 * r b.1) ^ (3 : ℕ) : ℝ) = 64 * r b.1 ^ (3 : ℕ) by ring,
            ENNReal.ofReal_mul (by norm_num),
            show ENNReal.ofReal 64 = 64 from by norm_num, mul_assoc]
        simp_rw [hterm]
        rw [ENNReal.tsum_mul_left, ← mul_assoc, mul_comm t 64, mul_assoc, ← ENNReal.tsum_mul_left]
    _ ≤ 64 * ∑' b : ↥u, ∫⁻ y in Metric.ball (b : Space 3) (r b), f y := by
        gcongr with b
        exact hball_spec b.1 b.2
    _ = 64 * ∫⁻ y in ⋃ b ∈ u, Metric.ball b (r b), f y := by
        rw [← lintegral_biUnion hu_count (fun b _ => measurableSet_ball) hball_disj]
    _ ≤ 64 * ∫⁻ y, f y :=
        mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) zero_le

/-- **[The truncated weak-(1,1) bound]** `t·μ{Mf > t} ≤ 128·∫_{f > t/2} f`: split `f` at height `t/2`,
apply weak-(1,1) to the high part `f·𝟙_{f>t/2}` at level `t/2` (the low part contributes `≤ t/2` to `Mf`).
This is the Calderón–Zygmund estimate driving the strong-`L^p` bound. -/
theorem weak_1_1_truncation (f : Space 3 → ℝ≥0∞) (hf : Measurable f) {t : ℝ≥0∞} (ht : 0 < t)
    (htop : t ≠ ∞) :
    t * volume {x | t < maximalFunction f x} ≤ 128 * ∫⁻ y in {y | t / 2 < f y}, f y := by
  have hset : MeasurableSet {y : Space 3 | t / 2 < f y} := measurableSet_lt measurable_const hf
  set g := {y : Space 3 | t / 2 < f y}.indicator f with hg
  have hg_meas : Measurable g := hf.indicator hset
  have ht2 : (0 : ℝ≥0∞) < t / 2 := ENNReal.div_pos ht.ne' (by norm_num)
  have ht2top : t / 2 ≠ ∞ := ENNReal.div_ne_top htop (by norm_num)
  have hfgh : f = g + {y : Space 3 | f y ≤ t / 2}.indicator f := by
    funext y
    simp only [hg, Pi.add_apply, Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hy : t / 2 < f y
    · rw [if_pos hy, if_neg (not_le.mpr hy), add_zero]
    · rw [if_neg hy, if_pos (not_lt.mp hy), zero_add]
  have hh_le : {y : Space 3 | f y ≤ t / 2}.indicator f ≤ fun _ => t / 2 := by
    intro y
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hy : f y ≤ t / 2
    · rw [if_pos hy]; exact hy
    · rw [if_neg hy]; exact zero_le'
  have hsub : {x | t < maximalFunction f x} ⊆ {x | t / 2 < maximalFunction g x} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have hle : maximalFunction f x ≤ maximalFunction g x + t / 2 :=
      calc maximalFunction f x = maximalFunction (g + {y | f y ≤ t / 2}.indicator f) x := by
            rw [← hfgh]
        _ ≤ maximalFunction g x + maximalFunction ({y | f y ≤ t / 2}.indicator f) x :=
            maximalFunction_add_le hg_meas x
        _ ≤ maximalFunction g x + t / 2 := by
            gcongr
            exact maximalFunction_le_const hh_le x
    by_contra hcon
    push_neg at hcon
    exact absurd hx (not_lt.mpr (by
      calc maximalFunction f x ≤ maximalFunction g x + t / 2 := hle
        _ ≤ t / 2 + t / 2 := by gcongr
        _ = t := ENNReal.add_halves t))
  have h2 : t = 2 * (t / 2) := by
    rw [mul_comm, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  calc t * volume {x | t < maximalFunction f x}
      ≤ t * volume {x | t / 2 < maximalFunction g x} :=
        mul_le_mul_of_nonneg_left (measure_mono hsub) zero_le
    _ = 2 * (t / 2 * volume {x | t / 2 < maximalFunction g x}) := by rw [← mul_assoc, ← h2]
    _ ≤ 2 * (64 * ∫⁻ y, g y) :=
      mul_le_mul_of_nonneg_left (weak_1_1 g hg_meas ht2 ht2top) zero_le
    _ = 128 * ∫⁻ y in {y : Space 3 | t / 2 < f y}, f y := by
        rw [← mul_assoc, hg, lintegral_indicator hset]; norm_num

/-- The `Lᵖ` tail controls the truncated `L¹` mass:
`∫_{f>t} f ≤ t^(1-p) ∫ f^p`. This is the distributional bridge that removes the
auxiliary global `L¹` hypothesis from Marcinkiewicz interpolation. -/
theorem lintegral_tail_le_rpow (f : Space 3 → ℝ≥0∞) (hf : Measurable f)
    {t : ℝ≥0∞} (ht : 0 < t) (htop : t ≠ ∞)
    {p : ℝ} (hp : 1 < p) :
    ∫⁻ y in {y | t < f y}, f y ≤
      t ^ (1 - p) * ∫⁻ y, f y ^ p := by
  have hset : MeasurableSet {y : Space 3 | t < f y} :=
    measurableSet_lt measurable_const hf
  calc
    ∫⁻ y in {y | t < f y}, f y
        ≤ ∫⁻ y in {y | t < f y}, t ^ (1 - p) * f y ^ p := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hset] with y hy
          rcases eq_or_ne (f y) ∞ with hfty | hfty
          · rw [hfty]
            have ht0 : t ^ (1 - p) ≠ 0 := by
              simp [ENNReal.rpow_eq_zero_iff, ht.ne', htop,
                show 1 - p < 0 by linarith]
            simp [ht0, show (0 : ℝ) < p by linarith]
          · have hfy0 : f y ≠ 0 := ne_of_gt (ht.trans hy)
            have hmono : t ^ (p - 1) ≤ f y ^ (p - 1) :=
              ENNReal.rpow_le_rpow hy.le (by linarith)
            calc
              f y = (t ^ (1 - p) * t ^ (p - 1)) * f y := by
                rw [← ENNReal.rpow_add _ _ ht.ne' htop]
                norm_num
              _ = t ^ (1 - p) * (t ^ (p - 1) * f y) := by ring
              _ ≤ t ^ (1 - p) * (f y ^ (p - 1) * f y) := by
                gcongr
              _ = t ^ (1 - p) * f y ^ p := by
                congr 1
                calc
                  f y ^ (p - 1) * f y =
                      f y ^ (p - 1) * f y ^ (1 : ℝ) := by
                        rw [ENNReal.rpow_one]
                  _ = f y ^ ((p - 1) + 1) :=
                    (ENNReal.rpow_add (p - 1) 1 hfy0 hfty).symm
                  _ = f y ^ p := by ring_nf
    _ ≤ ∫⁻ y, t ^ (1 - p) * f y ^ p :=
      setLIntegral_le_lintegral _ _
    _ = t ^ (1 - p) * ∫⁻ y, f y ^ p := by
      rw [lintegral_const_mul _ (by fun_prop)]

/-- The powers generated by truncating at `t/2` cancel exactly:
`t^(p-1) (t/2)^(1-p) = 2^(p-1)`. -/
theorem rpow_truncation_cancel {t : ℝ≥0∞} (ht : 0 < t) (htop : t ≠ ∞)
    {p : ℝ} (hp : 1 < p) :
    t ^ (p - 1) * (t / 2) ^ (1 - p) = (2 : ℝ≥0∞) ^ (p - 1) := by
  have ht0 : t ≠ 0 := ht.ne'
  rw [show 1 - p = -(p - 1) by ring, ENNReal.rpow_neg]
  rw [ENNReal.div_rpow_of_nonneg _ _ (by linarith : 0 ≤ p - 1)]
  have htPow0 : t ^ (p - 1) ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, ht0, htop, show 0 < p - 1 by linarith]
  have htPowTop : t ^ (p - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) htop
  rw [div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl htPow0) (Or.inl htPowTop), inv_inv]
  calc
    t ^ (p - 1) * ((t ^ (p - 1))⁻¹ * 2 ^ (p - 1))
        = (t ^ (p - 1) * (t ^ (p - 1))⁻¹) * 2 ^ (p - 1) := by
            rw [mul_assoc]
    _ = 1 * 2 ^ (p - 1) := by
            rw [ENNReal.mul_inv_cancel]
            · exact htPow0
            · exact htPowTop
    _ = 2 ^ (p - 1) := one_mul _

/-- **Weak `(p,p)` distribution estimate.** Combining the truncated weak-`(1,1)`
bound with the `Lᵖ` tail estimate gives
`t^p μ{Mf>t} ≤ 128·2^(p-1)∫f^p`, with no `L¹` premise. -/
theorem weak_p_p (f : Space 3 → ℝ≥0∞) (hf : Measurable f)
    {t : ℝ≥0∞} (ht : 0 < t) (htop : t ≠ ∞)
    {p : ℝ} (hp : 1 < p) :
    t ^ p * volume {x | t < maximalFunction f x} ≤
      128 * (2 : ℝ≥0∞) ^ (p - 1) * ∫⁻ y, f y ^ p := by
  have htail := lintegral_tail_le_rpow f hf (t := t / 2) (p := p)
    (ENNReal.div_pos ht.ne' (by norm_num))
    (ENNReal.div_ne_top htop (by norm_num)) hp
  have hweak := weak_1_1_truncation f hf ht htop
  have ht0 : t ≠ 0 := ht.ne'
  calc
    t ^ p * volume {x | t < maximalFunction f x}
        = t ^ (p - 1) * (t * volume {x | t < maximalFunction f x}) := by
            rw [show p = (p - 1) + 1 by ring,
              ENNReal.rpow_add (p - 1) 1 ht0 htop, ENNReal.rpow_one]
            ring
    _ ≤ t ^ (p - 1) * (128 * ∫⁻ y in {y | t / 2 < f y}, f y) :=
      mul_le_mul_of_nonneg_left hweak zero_le
    _ ≤ t ^ (p - 1) * (128 * ((t / 2) ^ (1 - p) * ∫⁻ y, f y ^ p)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htail zero_le) zero_le
    _ = 128 * (2 : ℝ≥0∞) ^ (p - 1) * ∫⁻ y, f y ^ p := by
      rw [show t ^ (p - 1) * (128 * ((t / 2) ^ (1 - p) * ∫⁻ y, f y ^ p))
          = 128 * (t ^ (p - 1) * (t / 2) ^ (1 - p)) * ∫⁻ y, f y ^ p by ring,
        rpow_truncation_cancel ht htop hp]

/-- `Lᵖ` integrability with `p>0` makes an `ℝ≥0∞`-valued function finite almost
everywhere. -/
theorem ae_lt_top_of_lintegral_rpow_ne_top (f : Space 3 → ℝ≥0∞) (hf : Measurable f)
    {p : ℝ} (hp : 0 < p) (hfp : ∫⁻ y, f y ^ p ≠ ∞) :
    ∀ᵐ y, f y < ∞ := by
  have hpow : ∀ᵐ y, f y ^ p < ∞ :=
    ae_lt_top (by fun_prop) hfp
  filter_upwards [hpow] with y hy
  by_contra h
  have htop : f y = ∞ := top_le_iff.mp (not_lt.mp h)
  rw [htop] at hy
  simpa [ENNReal.top_rpow_of_pos hp] using hy

/-- **Almost-everywhere finiteness from `Lᵖ`, `p>1`.** The weak-`(p,p)`
distribution bound decays as `t⁻ᵖ`, so the infinite level set of `Mf` has zero
measure. This is the genuine weak-`Lᵖ` replacement for the former `L¹`
finiteness argument. -/
theorem maximalFunction_lt_top_ae_of_lintegral_rpow (f : Space 3 → ℝ≥0∞)
    (hf : Measurable f) {p : ℝ} (hp : 1 < p)
    (hfp : ∫⁻ y, f y ^ p ≠ ∞) :
    ∀ᵐ x, maximalFunction f x < ∞ := by
  rw [ae_iff]
  have hset : {x | ¬ maximalFunction f x < ∞} =
      {x | maximalFunction f x = ∞} := by
    ext x
    simp only [Set.mem_setOf_eq, not_lt, top_le_iff]
  rw [hset]
  let C : ℝ≥0∞ := 128 * (2 : ℝ≥0∞) ^ (p - 1) * ∫⁻ y, f y ^ p
  have hCtop : C ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · norm_num
      · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
    · exact hfp
  have hbound : ∀ n : ℕ, 1 ≤ n →
      volume {x | maximalFunction f x = ∞} ≤ C / ((n : ℝ≥0∞) ^ p) := by
    intro n hn
    have hnpos : (0 : ℝ≥0∞) < n := by exact_mod_cast hn
    have hntop : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
    have hnp0 : (n : ℝ≥0∞) ^ p ≠ 0 := by
      simp [ENNReal.rpow_eq_zero_iff, hnpos.ne', hntop, show 0 < p by linarith]
    have hnptop : (n : ℝ≥0∞) ^ p ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by linarith) hntop
    have hsub : {x | maximalFunction f x = ∞} ⊆
        {x | (n : ℝ≥0∞) < maximalFunction f x} :=
      fun x hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [hx]
        exact hntop.lt_top
    apply (measure_mono hsub).trans
    rw [ENNReal.le_div_iff_mul_le (Or.inl hnp0) (Or.inl hnptop)]
    calc
      volume {x | (n : ℝ≥0∞) < maximalFunction f x} * (n : ℝ≥0∞) ^ p
          = (n : ℝ≥0∞) ^ p *
              volume {x | (n : ℝ≥0∞) < maximalFunction f x} := mul_comm _ _
      _ ≤ C := weak_p_p f hf hnpos hntop hp
  have hinvpow : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) ^ p)⁻¹)
      Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.ennrpow_const p ENNReal.tendsto_inv_nat_nhds_zero
    simpa [ENNReal.inv_rpow, ENNReal.zero_rpow_of_pos (by linarith : 0 < p)] using h
  have htendsto : Filter.Tendsto (fun n : ℕ => C / ((n : ℝ≥0∞) ^ p))
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      ENNReal.Tendsto.const_mul hinvpow (Or.inr hCtop)
  exact le_antisymm
    (ge_of_tendsto htendsto (Filter.eventually_atTop.mpr ⟨1, hbound⟩)) zero_le'

/-- **[Almost-everywhere finiteness]** if `f ∈ L¹` then `Mf < ∞` a.e.: the super-level measures
`μ{Mf > n} ≤ 64·∫f / n → 0`, so `μ{Mf = ∞} = 0`. -/
theorem maximalFunction_lt_top_ae (f : Space 3 → ℝ≥0∞) (hf : Measurable f) (hf1 : ∫⁻ y, f y ≠ ∞) :
    ∀ᵐ x, maximalFunction f x < ∞ := by
  rw [ae_iff]
  have hset : {x | ¬ maximalFunction f x < ∞} = {x | maximalFunction f x = ∞} := by
    ext x; simp only [Set.mem_setOf_eq, not_lt, top_le_iff]
  rw [hset]
  have hbound : ∀ n : ℕ, 1 ≤ n →
      volume {x | maximalFunction f x = ∞} ≤ 64 * (∫⁻ y, f y) / (n : ℝ≥0∞) := by
    intro n hn
    have hnpos : (0 : ℝ≥0∞) < n := by exact_mod_cast hn
    have hntop : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
    have hsub : {x | maximalFunction f x = ∞} ⊆ {x | (n : ℝ≥0∞) < maximalFunction f x} :=
      fun x hx => by simp only [Set.mem_setOf_eq] at hx ⊢; rw [hx]; exact hntop.lt_top
    refine (measure_mono hsub).trans ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl hnpos.ne') (Or.inl hntop), mul_comm]
    exact weak_1_1 f hf hnpos hntop
  have htendsto : Filter.Tendsto (fun n : ℕ => 64 * (∫⁻ y, f y) / (n : ℝ≥0∞))
      Filter.atTop (nhds 0) := by
    have hcm := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.mul_ne_top (by norm_num : (64 : ℝ≥0∞) ≠ ∞) hf1))
    simp_rw [div_eq_mul_inv]
    simpa using hcm
  exact le_antisymm (ge_of_tendsto htendsto (Filter.eventually_atTop.mpr ⟨1, hbound⟩)) zero_le'

section StrongLp
open Set

/-- Power integral in `ℝ≥0∞` form: `∫₀^b t^(p-2) dt = b^(p-1)/(p-1)` for `p > 1`, `b ≥ 0`. Feeds the
inner radial integral of the strong-`(p,p)` bound. -/
theorem lintegral_Ioo_rpow_sub {b : ℝ} (hb : 0 ≤ b) {p : ℝ} (hp : 1 < p) :
    ∫⁻ t in Set.Ioo 0 b, ENNReal.ofReal (t ^ (p - 2)) =
      ENNReal.ofReal (b ^ (p - 1) / (p - 1)) := by
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · rw [← hb0]
    simp [Real.zero_rpow (show p - 1 ≠ 0 by linarith)]
  · have hf_nn : 0 ≤ᵐ[volume.restrict (Set.Ioo 0 b)] fun t => t ^ (p - 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact Real.rpow_nonneg ht.1.le _
    have hfi : IntegrableOn (fun t : ℝ => t ^ (p - 2)) (Set.Ioo 0 b) :=
      ((intervalIntegral.intervalIntegrable_rpow' (show (-1 : ℝ) < p - 2 by linarith)).1).mono_set
        Set.Ioo_subset_Ioc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hfi hf_nn]
    congr 1
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hb0.le,
      integral_rpow (Or.inl (show (-1 : ℝ) < p - 2 by linarith)),
      show p - 2 + 1 = p - 1 by ring, Real.zero_rpow (show p - 1 ≠ 0 by linarith), sub_zero]

/-- Joint measurability of the near-diagonal indicator `(t,y) ↦ 1[ofReal t/2 < f y]·f y` on the
product space, feeding the Tonelli exchange in `inner_tonelli`. -/
theorem indicator_prod_measurable (f : Space 3 → ℝ≥0∞) (hf : Measurable f) :
    Measurable (Function.uncurry fun (t : ℝ) (y : Space 3) =>
      Set.indicator {y' | ENNReal.ofReal t / 2 < f y'} f y) := by
  have hS : MeasurableSet {q : ℝ × Space 3 | ENNReal.ofReal q.1 / 2 < f q.2} :=
    measurableSet_lt (by fun_prop) (hf.comp measurable_snd)
  have heq : (Function.uncurry fun (t : ℝ) (y : Space 3) =>
      Set.indicator {y' | ENNReal.ofReal t / 2 < f y'} f y)
      = Set.indicator {q : ℝ × Space 3 | ENNReal.ofReal q.1 / 2 < f q.2} (fun q => f q.2) := by
    funext q
    simp only [Function.uncurry, Set.indicator_apply, Set.mem_setOf_eq]
  rw [heq]
  exact (hf.comp measurable_snd).indicator hS

/-- `a·a^(p-1) = a^p` for `a > 0`. -/
theorem rpow_one_add_aux {a : ℝ} (ha : 0 < a) {p : ℝ} : a * a ^ (p - 1) = a ^ p := by
  have h : a ^ p = a ^ ((1 : ℝ) + (p - 1)) := by rw [show (1 : ℝ) + (p - 1) = p by ring]
  rw [h, Real.rpow_add ha, Real.rpow_one]

/-- `a·(2a)^(p-1)/(p-1) = 2^(p-1)/(p-1)·a^p` for `a ≥ 0`, `p > 1`: collects the inner radial integral
into a clean `‖f‖^p` power. -/
theorem rpow_diagonal_aux {a : ℝ} (ha : 0 ≤ a) {p : ℝ} (hp : 1 < p) :
    a * (2 * a) ^ (p - 1) / (p - 1) = 2 ^ (p - 1) / (p - 1) * a ^ p := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · rw [← ha0]; simp [zero_mul, Real.zero_rpow (show (0 : ℝ) < p by linarith).ne']
  · rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha,
        show a * (2 ^ (p - 1) * a ^ (p - 1)) = 2 ^ (p - 1) * (a * a ^ (p - 1)) by ring,
        rpow_one_add_aux ha0]
    ring

/-- Tonelli + inner radial integral: after the layer-cake and weak-`(1,1)` substitution, the
double integral `∫∫ t^(p-2)·1[ofReal t/2 < f y]·f y` collapses (via Fubini–Tonelli and the power
integral `lintegral_Ioo_rpow_sub`) to `2^(p-1)/(p-1)·∫ f^p`. This is the exchange step of the
strong-`(p,p)` bound. -/
theorem inner_tonelli (f : Space 3 → ℝ≥0∞) (hf : Measurable f)
    (hf_lt : ∀ᵐ y, f y < ∞)
    {p : ℝ} (hp : 1 < p) :
    ∫⁻ t in Set.Ioi 0,
      ENNReal.ofReal (t ^ (p - 2)) * ∫⁻ y in {y | ENNReal.ofReal t / 2 < f y}, f y
      = ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * ∫⁻ y, (f y) ^ p := by
  have hstep : ∀ t : ℝ,
      ENNReal.ofReal (t ^ (p - 2)) * ∫⁻ y in {y | ENNReal.ofReal t / 2 < f y}, f y
      = ∫⁻ y, ENNReal.ofReal (t ^ (p - 2)) * Set.indicator {y | ENNReal.ofReal t / 2 < f y} f y := by
    intro t
    rw [lintegral_const_mul _ (hf.indicator (measurableSet_lt measurable_const hf)),
        lintegral_indicator (measurableSet_lt measurable_const hf)]
  simp_rw [hstep]
  have huncmeas : Measurable (Function.uncurry fun (t : ℝ) (y : Space 3) =>
      ENNReal.ofReal (t ^ (p - 2)) * Set.indicator {y | ENNReal.ofReal t / 2 < f y} f y) :=
    (by fun_prop : Measurable fun q : ℝ × Space 3 => ENNReal.ofReal (q.1 ^ (p - 2))).mul
      (indicator_prod_measurable f hf)
  rw [lintegral_lintegral_swap huncmeas.aemeasurable]
  have hJ : (fun y => ∫⁻ t in Set.Ioi 0,
      ENNReal.ofReal (t ^ (p - 2)) * Set.indicator {y' | ENNReal.ofReal t / 2 < f y'} f y)
      =ᵐ[volume] fun y => ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * (f y) ^ p := by
    filter_upwards [hf_lt] with y hy
    have hC_meas : MeasurableSet {t : ℝ | ENNReal.ofReal t / 2 < f y} :=
      measurableSet_lt (by fun_prop) measurable_const
    have hcond : ∀ t : ℝ, 0 < t → (ENNReal.ofReal t / 2 < f y ↔ t < 2 * (f y).toReal) := by
      intro t ht
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
          ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hy.ne]
      constructor <;> intro h <;> linarith
    have hset : {t | ENNReal.ofReal t / 2 < f y} ∩ Set.Ioi (0 : ℝ)
        = Set.Ioo 0 (2 * (f y).toReal) := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_setOf_eq, Set.mem_Ioo]
      constructor
      · rintro ⟨hlt, ht⟩; exact ⟨ht, (hcond t ht).mp hlt⟩
      · rintro ⟨ht, hlt⟩; exact ⟨(hcond t ht).mpr hlt, ht⟩
    have hig : ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t ^ (p - 2)) *
        Set.indicator {y' | ENNReal.ofReal t / 2 < f y'} f y
        = ∫⁻ t in Set.Ioi 0, Set.indicator {t | ENNReal.ofReal t / 2 < f y}
            (fun t => ENNReal.ofReal (t ^ (p - 2)) * f y) t := by
      refine lintegral_congr_ae (ae_of_all _ (fun t => ?_))
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      by_cases h : ENNReal.ofReal t / 2 < f y <;> simp [h]
    rw [hig, lintegral_indicator hC_meas, Measure.restrict_restrict hC_meas, hset,
        lintegral_mul_const _ (by fun_prop), lintegral_Ioo_rpow_sub (by positivity) hp]
    set a := (f y).toReal with ha
    have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
    have hfya : f y = ENNReal.ofReal a := (ENNReal.ofReal_toReal hy.ne).symm
    rw [hfya, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * a) ^ (p - 1) / (p - 1)),
        show (2 * a) ^ (p - 1) / (p - 1) * a = a * (2 * a) ^ (p - 1) / (p - 1) by ring,
        rpow_diagonal_aux ha0 hp, ENNReal.ofReal_rpow_of_nonneg ha0 (by linarith : (0 : ℝ) ≤ p),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ (p - 1) / (p - 1))]
  rw [lintegral_congr_ae hJ, lintegral_const_mul _ (by fun_prop)]

/-- **[Strong `(p,p)` bound]** for the Hardy–Littlewood maximal function: for `p > 1` and `f ∈ Lᵖ`,
`∫ (Mf)^p ≤ 128·p·2^(p-1)/(p-1) · ∫ f^p`. Marcinkiewicz interpolation of the weak-`(1,1)` estimate
(`weak_1_1_truncation`) against the trivial `L^∞` bound, executed by hand through the layer-cake
formula, the truncated weak bound, and the Tonelli exchange `inner_tonelli`. No global `L¹`
hypothesis is required: `weak_p_p` supplies almost-everywhere finiteness of `Mf`. -/
theorem lintegral_maximalFunction_rpow_le (f : Space 3 → ℝ≥0∞) (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) (hfp : ∫⁻ y, f y ^ p ≠ ∞) :
    ∫⁻ x, (maximalFunction f x) ^ p ≤
      ENNReal.ofReal (128 * p * 2 ^ (p - 1) / (p - 1)) * ∫⁻ y, (f y) ^ p := by
  have hf_lt : ∀ᵐ y, f y < ∞ :=
    ae_lt_top_of_lintegral_rpow_ne_top f hf (by linarith) hfp
  have hMf_lt : ∀ᵐ x, maximalFunction f x < ∞ :=
    maximalFunction_lt_top_ae_of_lintegral_rpow f hf hp hfp
  have step1 : ∫⁻ x, (maximalFunction f x) ^ p
      = ∫⁻ x, ENNReal.ofReal ((maximalFunction f x).toReal ^ p) := by
    apply lintegral_congr_ae
    filter_upwards [hMf_lt] with x hx
    show (maximalFunction f x) ^ p = ENNReal.ofReal ((maximalFunction f x).toReal ^ p)
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by linarith : (0 : ℝ) ≤ p),
        ENNReal.ofReal_toReal hx.ne]
  have hg_meas : Measurable (fun x => (maximalFunction f x).toReal) :=
    (measurable_maximalFunction f hf).ennreal_toReal
  have hg_nn : 0 ≤ᵐ[volume] fun x => (maximalFunction f x).toReal :=
    Filter.Eventually.of_forall (fun x => ENNReal.toReal_nonneg)
  have step2 := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := volume) hg_nn hg_meas.aemeasurable
    (show (0 : ℝ) < p by linarith)
  have hpt : ∀ t : ℝ, 0 < t →
      volume {x | t < (maximalFunction f x).toReal} * ENNReal.ofReal (t ^ (p - 1)) ≤
        128 * (ENNReal.ofReal (t ^ (p - 2)) * ∫⁻ y in {y | ENNReal.ofReal t / 2 < f y}, f y) := by
    intro t ht
    have hsub : {x | t < (maximalFunction f x).toReal}
        ⊆ {x | ENNReal.ofReal t < maximalFunction f x} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      rcases eq_or_ne (maximalFunction f x) ∞ with hinf | hinf
      · rw [hinf, ENNReal.toReal_top] at hx; exact absurd (ht.trans hx) (lt_irrefl 0)
      · rw [← ENNReal.ofReal_toReal hinf]
        exact (ENNReal.ofReal_lt_ofReal_iff (ht.trans hx)).mpr hx
    have hweak := weak_1_1_truncation f hf (ENNReal.ofReal_pos.mpr ht) ENNReal.ofReal_ne_top
    have hofReal : ENNReal.ofReal (t ^ (p - 1))
        = ENNReal.ofReal (t ^ (p - 2)) * ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), show p - 1 = (p - 2) + 1 by ring,
          Real.rpow_add ht, Real.rpow_one]
    calc volume {x | t < (maximalFunction f x).toReal} * ENNReal.ofReal (t ^ (p - 1))
        ≤ volume {x | ENNReal.ofReal t < maximalFunction f x} * ENNReal.ofReal (t ^ (p - 1)) :=
          mul_le_mul_of_nonneg_right (measure_mono hsub) zero_le
      _ = ENNReal.ofReal (t ^ (p - 2)) *
            (ENNReal.ofReal t * volume {x | ENNReal.ofReal t < maximalFunction f x}) := by
            rw [hofReal]; ring
      _ ≤ ENNReal.ofReal (t ^ (p - 2)) * (128 * ∫⁻ y in {y | ENNReal.ofReal t / 2 < f y}, f y) :=
          mul_le_mul_of_nonneg_left hweak zero_le
      _ = 128 * (ENNReal.ofReal (t ^ (p - 2)) *
            ∫⁻ y in {y | ENNReal.ofReal t / 2 < f y}, f y) := by ring
  have hHmeas : Measurable (fun t : ℝ =>
      ENNReal.ofReal (t ^ (p - 2)) * ∫⁻ y in {y | ENNReal.ofReal t / 2 < f y}, f y) := by
    have hg : Measurable (fun t : ℝ => ∫⁻ y in {y | ENNReal.ofReal t / 2 < f y}, f y) := by
      have heq : (fun t : ℝ => ∫⁻ y in {y | ENNReal.ofReal t / 2 < f y}, f y)
          = fun t : ℝ => ∫⁻ y, Set.indicator {y | ENNReal.ofReal t / 2 < f y} f y := by
        funext t; rw [lintegral_indicator (measurableSet_lt measurable_const hf)]
      rw [heq]
      exact (indicator_prod_measurable f hf).lintegral_prod_right'
    exact (by fun_prop : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (p - 2))).mul hg
  rw [step1, step2]
  calc ENNReal.ofReal p *
        ∫⁻ t in Set.Ioi 0,
          volume {x | t < (maximalFunction f x).toReal} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal p * ∫⁻ t in Set.Ioi 0,
          128 * (ENNReal.ofReal (t ^ (p - 2)) * ∫⁻ y in {y | ENNReal.ofReal t / 2 < f y}, f y) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hpt t ht
    _ = ENNReal.ofReal p * (128 * ∫⁻ t in Set.Ioi 0,
          ENNReal.ofReal (t ^ (p - 2)) * ∫⁻ y in {y | ENNReal.ofReal t / 2 < f y}, f y) := by
        rw [lintegral_const_mul 128 hHmeas]
    _ = ENNReal.ofReal p * (128 * (ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * ∫⁻ y, (f y) ^ p)) := by
        rw [inner_tonelli f hf hf_lt hp]
    _ = ENNReal.ofReal (128 * p * 2 ^ (p - 1) / (p - 1)) * ∫⁻ y, (f y) ^ p := by
        rw [← mul_assoc, ← mul_assoc]
        congr 1
        rw [show (128 : ℝ≥0∞) = ENNReal.ofReal 128 by simp,
            ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ p),
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ p * 128)]
        congr 1
        ring

end StrongLp

section Hedberg
open Set

/-- **Layer-cake (Cavalieri) representation of the Newtonian kernel**: `1/d = ∫_0^∞ 1[d<r]·r^(-2) dr`
for `d > 0`. This is the entry point to Hedberg's inequality: substituting it into
`∫_{ball} ρ(y)/‖x−y‖` and exchanging the order of integration turns the singular kernel into a
supremum of ball averages, which the maximal function controls. -/
theorem kernel_layercake {d : ℝ} (hd : 0 < d) :
    ENNReal.ofReal d⁻¹
    = ∫⁻ r in Set.Ioi (0 : ℝ), (Set.Ioi d).indicator (fun r => ENNReal.ofReal (r ^ (-2 : ℝ))) r := by
  have hInter : Set.Ioi d ∩ Set.Ioi (0 : ℝ) = Set.Ioi d := by
    ext r; simp only [Set.mem_inter_iff, Set.mem_Ioi, and_iff_left_iff_imp]; intro hr; linarith
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hInter,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (by norm_num) hd)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          exact Real.rpow_nonneg (hd.trans hr).le _),
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hd]
  congr 1
  rw [show (-2 : ℝ) + 1 = -1 by ring, Real.rpow_neg_one]
  ring

/-- Volume of a ball of radius `s` in `Space 3`. -/
theorem vol_ball_three (x : Space 3) {s : ℝ} (hs : 0 ≤ s) :
    volume (Metric.ball x s) = ENNReal.ofReal (4 / 3 * Real.pi * s ^ 3) := by
  rw [Measure.addHaar_ball _ x hs, Space.finrank_eq_dim, Space.volume_metricBall_three,
      ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- Two concentric balls intersect in the smaller. -/
theorem ball_inter_ball (x : Space 3) (R r : ℝ) :
    Metric.ball x R ∩ Metric.ball x r = Metric.ball x (min R r) := by
  ext y
  simp only [Set.mem_inter_iff, Metric.mem_ball, lt_min_iff]

/-- The radial integral behind the near bound: `∫_0^∞ r^(-2)·(min R r)^3 dr = 3R²/2`. -/
theorem radial_min_integral {R : ℝ} (hR : 0 < R) :
    ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ (-2 : ℝ) * min R r ^ 3)
    = ENNReal.ofReal (3 * R ^ 2 / 2) := by
  have hdisj : Disjoint (Set.Ioo (0 : ℝ) R) (Set.Ici R) := by
    rw [Set.disjoint_left]; rintro r ⟨_, hr2⟩ hr3
    exact absurd (Set.mem_Ici.mp hr3) (not_le.mpr hr2)
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioo 0 R ∪ Set.Ici R := by
    ext r; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
    constructor
    · intro hr; rcases lt_or_ge r R with h | h
      · exact Or.inl ⟨hr, h⟩
      · exact Or.inr h
    · rintro (⟨hr, _⟩ | hr)
      · exact hr
      · linarith
  rw [hsplit, lintegral_union measurableSet_Ici hdisj]
  have hIoo : ∫⁻ r in Set.Ioo (0 : ℝ) R, ENNReal.ofReal (r ^ (-2 : ℝ) * min R r ^ 3)
      = ENNReal.ofReal (R ^ 2 / 2) := by
    have he : Set.EqOn (fun r => ENNReal.ofReal (r ^ (-2 : ℝ) * min R r ^ 3))
        (fun r => ENNReal.ofReal (r ^ ((3 : ℝ) - 2))) (Set.Ioo 0 R) := by
      intro r hr
      simp only
      congr 1
      rw [min_eq_right hr.2.le, ← Real.rpow_natCast r 3, ← Real.rpow_add hr.1]
      norm_num
    rw [setLIntegral_congr_fun measurableSet_Ioo he,
        lintegral_Ioo_rpow_sub hR.le (by norm_num : (1 : ℝ) < 3)]
    congr 1
    rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hIci : ∫⁻ r in Set.Ici R, ENNReal.ofReal (r ^ (-2 : ℝ) * min R r ^ 3)
      = ENNReal.ofReal (R ^ 2) := by
    have he : Set.EqOn (fun r => ENNReal.ofReal (r ^ (-2 : ℝ) * min R r ^ 3))
        (fun r => ENNReal.ofReal (r ^ (-2 : ℝ) * R ^ 3)) (Set.Ici R) := by
      intro r hr
      simp only
      rw [min_eq_left (Set.mem_Ici.mp hr)]
    rw [setLIntegral_congr_fun measurableSet_Ici he, ← setLIntegral_congr Ioi_ae_eq_Ici,
      ← ofReal_integral_eq_lintegral_ofReal
        ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR).mul_const (R ^ 3))
        (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
            exact mul_nonneg (Real.rpow_nonneg (hR.trans hr).le _) (by positivity))]
    congr 1
    rw [integral_mul_const, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR,
        show (-2 : ℝ) + 1 = -1 by ring, Real.rpow_neg_one]
    field_simp
  rw [hIoo, hIci, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- **Hedberg near bound**: the singular part of the Riesz potential over a ball is controlled by
the maximal function, `∫_{ball(x,R)} ρ(y)/‖x−y‖ ≤ 16π·R²·Mρ(x)`. Substitute the kernel layer-cake,
exchange integration order, and on each radius the inner ball average is bounded by `Mρ(x)`; the
radial integral `radial_min_integral` collapses to `R²`. -/
theorem near_bound (ρ : Space 3 → ℝ≥0∞) (hρ : Measurable ρ) (x : Space 3) {R : ℝ} (hR : 0 < R) :
    ∫⁻ y in Metric.ball x R, ρ y * ENNReal.ofReal ‖x - y‖⁻¹
    ≤ ENNReal.ofReal (16 * Real.pi * R ^ 2) * maximalFunction ρ x := by
  have hane : ∀ᵐ y ∂(volume.restrict (Metric.ball x R)), y ≠ x := by
    apply ae_restrict_of_ae
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton x)] with y hy
    simpa using hy
  have hker : ∫⁻ y in Metric.ball x R, ρ y * ENNReal.ofReal ‖x - y‖⁻¹
      = ∫⁻ y in Metric.ball x R, ∫⁻ r in Set.Ioi (0 : ℝ),
          ρ y * (Set.Ioi ‖x - y‖).indicator (fun r => ENNReal.ofReal (r ^ (-2 : ℝ))) r := by
    apply lintegral_congr_ae
    filter_upwards [hane] with y hy
    rw [kernel_layercake (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hy))),
        lintegral_const_mul _
          ((by fun_prop : Measurable fun r : ℝ => ENNReal.ofReal (r ^ (-2 : ℝ))).indicator
            measurableSet_Ioi)]
  have hFmeas : Measurable (Function.uncurry fun (y : Space 3) (r : ℝ) =>
      ρ y * (Set.Ioi ‖x - y‖).indicator (fun r => ENNReal.ofReal (r ^ (-2 : ℝ))) r) := by
    have hset : MeasurableSet {p : Space 3 × ℝ | ‖x - p.1‖ < p.2} :=
      measurableSet_lt (by fun_prop) (by fun_prop)
    have hind : Measurable (fun p : Space 3 × ℝ =>
        (Set.Ioi ‖x - p.1‖).indicator (fun r => ENNReal.ofReal (r ^ (-2 : ℝ))) p.2) := by
      have heq : (fun p : Space 3 × ℝ =>
          (Set.Ioi ‖x - p.1‖).indicator (fun r => ENNReal.ofReal (r ^ (-2 : ℝ))) p.2)
          = Set.indicator {p : Space 3 × ℝ | ‖x - p.1‖ < p.2}
              (fun p => ENNReal.ofReal (p.2 ^ (-2 : ℝ))) := by
        funext p; simp [Set.indicator_apply, Set.mem_Ioi]
      rw [heq]
      exact (by fun_prop : Measurable fun p : Space 3 × ℝ =>
        ENNReal.ofReal (p.2 ^ (-2 : ℝ))).indicator hset
    exact (hρ.comp measurable_fst).mul hind
  rw [hker, lintegral_lintegral_swap hFmeas.aemeasurable]
  have hpr : ∀ r : ℝ, 0 < r →
      ∫⁻ y in Metric.ball x R,
          ρ y * (Set.Ioi ‖x - y‖).indicator (fun r => ENNReal.ofReal (r ^ (-2 : ℝ))) r
      ≤ ENNReal.ofReal (r ^ (-2 : ℝ)) *
          (8 * ENNReal.ofReal (4 / 3 * Real.pi * min R r ^ 3) * maximalFunction ρ x) := by
    intro r hr
    have hig : ∀ y, ρ y * (Set.Ioi ‖x - y‖).indicator (fun r => ENNReal.ofReal (r ^ (-2 : ℝ))) r
        = ENNReal.ofReal (r ^ (-2 : ℝ)) * (Metric.ball x r).indicator ρ y := by
      intro y
      by_cases h : ‖x - y‖ < r
      · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h),
            Set.indicator_of_mem (show y ∈ Metric.ball x r by
              rw [Metric.mem_ball', dist_eq_norm]; exact h), mul_comm]
      · rw [Set.indicator_of_notMem (fun hc => h (Set.mem_Ioi.mp hc)),
            Set.indicator_of_notMem (show y ∉ Metric.ball x r by
              rw [Metric.mem_ball', dist_eq_norm]; exact h), mul_zero, mul_zero]
    simp_rw [hig]
    rw [lintegral_const_mul _ (hρ.indicator measurableSet_ball),
        lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
        Set.inter_comm (Metric.ball x r) (Metric.ball x R), ball_inter_ball]
    have hmr : 0 < min R r := lt_min hR hr
    calc ENNReal.ofReal (r ^ (-2 : ℝ)) * ∫⁻ y in Metric.ball x (min R r), ρ y
        ≤ ENNReal.ofReal (r ^ (-2 : ℝ)) *
            (8 * volume (Metric.ball x (min R r)) * maximalFunction ρ x) :=
          mul_le_mul_of_nonneg_left (lintegral_ball_le_maximalFunction ρ x hmr) zero_le
      _ = ENNReal.ofReal (r ^ (-2 : ℝ)) *
            (8 * ENNReal.ofReal (4 / 3 * Real.pi * min R r ^ 3) * maximalFunction ρ x) := by
          rw [vol_ball_three x hmr.le]
  calc ∫⁻ r in Set.Ioi 0, ∫⁻ y in Metric.ball x R,
          ρ y * (Set.Ioi ‖x - y‖).indicator (fun r => ENNReal.ofReal (r ^ (-2 : ℝ))) r
      ≤ ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (r ^ (-2 : ℝ)) *
          (8 * ENNReal.ofReal (4 / 3 * Real.pi * min R r ^ 3) * maximalFunction ρ x) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact hpr r hr
    _ = 8 * maximalFunction ρ x * ENNReal.ofReal (4 / 3 * Real.pi) *
          ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (r ^ (-2 : ℝ) * min R r ^ 3) := by
        rw [← lintegral_const_mul _ (by fun_prop)]
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro r hr
        have h1 : ENNReal.ofReal (r ^ (-2 : ℝ)) * ENNReal.ofReal (4 / 3 * Real.pi * min R r ^ 3)
            = ENNReal.ofReal (4 / 3 * Real.pi) * ENNReal.ofReal (r ^ (-2 : ℝ) * min R r ^ 3) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _),
              ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 / 3 * Real.pi)]
          congr 1; ring
        calc ENNReal.ofReal (r ^ (-2 : ℝ)) *
              (8 * ENNReal.ofReal (4 / 3 * Real.pi * min R r ^ 3) * maximalFunction ρ x)
            = 8 * maximalFunction ρ x *
                (ENNReal.ofReal (r ^ (-2 : ℝ)) * ENNReal.ofReal (4 / 3 * Real.pi * min R r ^ 3)) := by
              ring
          _ = 8 * maximalFunction ρ x *
                (ENNReal.ofReal (4 / 3 * Real.pi) * ENNReal.ofReal (r ^ (-2 : ℝ) * min R r ^ 3)) := by
              rw [h1]
          _ = 8 * maximalFunction ρ x * ENNReal.ofReal (4 / 3 * Real.pi) *
                ENNReal.ofReal (r ^ (-2 : ℝ) * min R r ^ 3) := by ring
    _ = ENNReal.ofReal (16 * Real.pi * R ^ 2) * maximalFunction ρ x := by
        rw [radial_min_integral hR,
            show (8 : ℝ≥0∞) * maximalFunction ρ x * ENNReal.ofReal (4 / 3 * Real.pi) *
                ENNReal.ofReal (3 * R ^ 2 / 2)
              = (ENNReal.ofReal 8 * ENNReal.ofReal (4 / 3 * Real.pi) *
                  ENNReal.ofReal (3 * R ^ 2 / 2)) * maximalFunction ρ x from by
              rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by simp]; ring,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 8 * (4 / 3 * Real.pi))]
        congr 2
        ring

/-- The **far-field radial integral** `∫_{‖z‖≥R} ‖z‖^(-6) = (4π/3)·R^(-3)` in `Space 3`, obtained
from the radial change of variables `integral_fun_norm_addHaar` (`∫ f(‖z‖) = 3·vol(B₁)·∫₀^∞ r²f(r)`)
and the improper power integral `∫_R^∞ r^(-4) = R^(-3)/3`. Feeds the Hölder tail estimate in the far
part of Hedberg's inequality. -/
theorem far_radial_integral {R : ℝ} (hR : 0 < R) :
    ∫⁻ z in {z : Space 3 | R ≤ ‖z‖}, ENNReal.ofReal (‖z‖ ^ (-6 : ℝ))
    = ENNReal.ofReal (4 * Real.pi / 3 * R ^ (-3 : ℝ)) := by
  have hmeas : MeasurableSet {z : Space 3 | R ≤ ‖z‖} :=
    measurableSet_le measurable_const continuous_norm.measurable
  have h1 : ∫⁻ z in {z : Space 3 | R ≤ ‖z‖}, ENNReal.ofReal (‖z‖ ^ (-6 : ℝ))
      = ∫⁻ z : Space 3, ENNReal.ofReal (if R ≤ ‖z‖ then ‖z‖ ^ (-6 : ℝ) else 0) := by
    rw [← lintegral_indicator hmeas]
    apply lintegral_congr
    intro z
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs with h
    · rfl
    · rw [ENNReal.ofReal_zero]
  rw [h1]
  have hyEq : Set.EqOn (fun y : ℝ => y ^ (Module.finrank ℝ (Space 3) - 1) •
      (if R ≤ y then y ^ (-6 : ℝ) else 0)) ((Set.Ici R).indicator (fun y => y ^ (-4 : ℝ)))
      (Set.Ioi 0) := by
    intro y hy
    simp only [Space.finrank_eq_dim, Set.indicator_apply, Set.mem_Ici, smul_eq_mul]
    by_cases h : R ≤ y
    · rw [if_pos h, if_pos h, ← Real.rpow_natCast y (3 - 1), ← Real.rpow_add (mem_Ioi.mp hy)]
      norm_num
    · rw [if_neg h, if_neg h, mul_zero]
  have hIci : IntegrableOn (fun y : ℝ => y ^ (-4 : ℝ)) (Set.Ici R) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hR).congr_set_ae Ioi_ae_eq_Ici.symm
  have hyF : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ (Space 3) - 1) •
      (if R ≤ y then y ^ (-6 : ℝ) else 0)) (Set.Ioi 0) :=
    (integrableOn_congr_fun hyEq measurableSet_Ioi).mpr
      ((integrable_indicator_iff measurableSet_Ici).mpr hIci).integrableOn
  have hbridge : Integrable (fun z : Space 3 => if R ≤ ‖z‖ then ‖z‖ ^ (-6 : ℝ) else 0) volume := by
    rw [integrable_fun_norm_addHaar (μ := volume) (f := fun t => if R ≤ t then t ^ (-6 : ℝ) else 0)]
    exact hyF
  have hFnn : ∀ z : Space 3, 0 ≤ (if R ≤ ‖z‖ then ‖z‖ ^ (-6 : ℝ) else 0) := by
    intro z; split_ifs with h
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · rfl
  rw [← ofReal_integral_eq_lintegral_ofReal hbridge (Filter.Eventually.of_forall hFnn)]
  congr 1
  rw [integral_fun_norm_addHaar volume (fun t => if R ≤ t then t ^ (-6 : ℝ) else 0),
      Space.finrank_eq_dim, Space.volume_metricBall_three_real]
  have hInner : ∫ y in Set.Ioi (0 : ℝ), y ^ (3 - 1) • (if R ≤ y then y ^ (-6 : ℝ) else 0)
      = R ^ (-3 : ℝ) / 3 := by
    have heq : Set.EqOn (fun y : ℝ => y ^ (3 - 1) • (if R ≤ y then y ^ (-6 : ℝ) else 0))
        ((Set.Ici R).indicator (fun y => y ^ (-4 : ℝ))) (Set.Ioi 0) := by
      intro y hy
      simp only [Set.indicator_apply, Set.mem_Ici, smul_eq_mul]
      by_cases h : R ≤ y
      · rw [if_pos h, if_pos h, ← Real.rpow_natCast y (3 - 1), ← Real.rpow_add (mem_Ioi.mp hy)]
        norm_num
      · rw [if_neg h, if_neg h, mul_zero]
    calc ∫ y in Set.Ioi (0 : ℝ), y ^ (3 - 1) • (if R ≤ y then y ^ (-6 : ℝ) else 0)
        = ∫ y in Set.Ioi (0 : ℝ), (Set.Ici R).indicator (fun y => y ^ (-4 : ℝ)) y :=
          setIntegral_congr_fun measurableSet_Ioi heq
      _ = ∫ y in Set.Ioi (0 : ℝ) ∩ Set.Ici R, y ^ (-4 : ℝ) :=
          setIntegral_indicator measurableSet_Ici
      _ = ∫ y in Set.Ici R, y ^ (-4 : ℝ) := by
          rw [show Set.Ioi (0 : ℝ) ∩ Set.Ici R = Set.Ici R by
            ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici, and_iff_right_iff_imp]
            intro h; linarith]
      _ = ∫ y in Set.Ioi R, y ^ (-4 : ℝ) := (setIntegral_congr_set Ioi_ae_eq_Ici).symm
      _ = R ^ (-3 : ℝ) / 3 := by
          rw [integral_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hR,
              show (-4 : ℝ) + 1 = -3 by ring]
          ring
  rw [hInner]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- **Hedberg far bound**: the tail of the Riesz potential is controlled by the `L^{6/5}` norm,
`∫_{‖x−y‖≥R} ρ(y)/‖x−y‖ ≤ (∫ρ^{6/5})^{5/6}·(4π/3·R^{-3})^{1/6}`, by Hölder's inequality (conjugate
exponents `6/5` and `6`) against the far radial integral `far_radial_integral`. -/
theorem far_bound (ρ : Space 3 → ℝ≥0∞) (hρ : Measurable ρ) (x : Space 3) {R : ℝ} (hR : 0 < R) :
    ∫⁻ y in {y : Space 3 | R ≤ ‖x - y‖}, ρ y * ENNReal.ofReal ‖x - y‖⁻¹
    ≤ (∫⁻ y, (ρ y) ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 6)
      * ENNReal.ofReal ((4 * Real.pi / 3 * R ^ (-3 : ℝ)) ^ ((1 : ℝ) / 6)) := by
  have hSmeas : MeasurableSet {y : Space 3 | R ≤ ‖x - y‖} :=
    measurableSet_le measurable_const (by fun_prop)
  have hpq : (6 / 5 : ℝ).HolderConjugate 6 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hgm : AEMeasurable (fun y => ENNReal.ofReal ‖x - y‖⁻¹)
      (volume.restrict {y : Space 3 | R ≤ ‖x - y‖}) := by fun_prop
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict {y : Space 3 | R ≤ ‖x - y‖}) hpq hρ.aemeasurable hgm
  have hg6 : ∀ y : Space 3,
      (ENNReal.ofReal ‖x - y‖⁻¹) ^ (6 : ℝ) = ENNReal.ofReal (‖x - y‖ ^ (-6 : ℝ)) := by
    intro y
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0 : ℝ) ≤ 6)]
    congr 1
    rw [Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)]
  have htrans : ∫⁻ y in {y : Space 3 | R ≤ ‖x - y‖}, (ENNReal.ofReal ‖x - y‖⁻¹) ^ (6 : ℝ)
      = ENNReal.ofReal (4 * Real.pi / 3 * R ^ (-3 : ℝ)) := by
    simp_rw [hg6]
    rw [← far_radial_integral hR]
    rw [← lintegral_indicator hSmeas]
    rw [← lintegral_indicator (measurableSet_le measurable_const
          (by fun_prop : Measurable fun z : Space 3 => ‖z‖))]
    rw [← (measurePreserving_add_right volume (-x)).lintegral_comp
          ((by fun_prop : Measurable fun z : Space 3 => ENNReal.ofReal (‖z‖ ^ (-6 : ℝ))).indicator
            (measurableSet_le measurable_const (by fun_prop : Measurable fun z : Space 3 => ‖z‖)))]
    apply lintegral_congr
    intro y
    have hnorm : ‖y + -x‖ = ‖x - y‖ := by rw [← sub_eq_add_neg, norm_sub_rev]
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hnorm]
  refine le_trans hHolder ?_
  rw [show ENNReal.ofReal ((4 * Real.pi / 3 * R ^ (-3 : ℝ)) ^ ((1 : ℝ) / 6))
      = (ENNReal.ofReal (4 * Real.pi / 3 * R ^ (-3 : ℝ))) ^ ((1 : ℝ) / 6) from
      (ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)).symm, ← htrans]
  gcongr
  rw [show (1 : ℝ) / (6 / 5) = 5 / 6 by norm_num]
  gcongr
  exact Measure.restrict_le_self

/-- Optimization over the splitting radius: if `I ≤ A·R² + B·R^{-1/2}` for every `R > 0`, then
choosing `R = (B/A)^{2/5}` (where both terms balance) gives `I ≤ 2·A^{1/5}·B^{4/5}`. -/
theorem radius_optimization {I A B : ℝ≥0∞} (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hB0 : B ≠ 0) (hBtop : B ≠ ∞)
    (h : ∀ R : ℝ, 0 < R →
      I ≤ A * ENNReal.ofReal (R ^ 2) + B * ENNReal.ofReal (R ^ (-(1 : ℝ) / 2))) :
    I ≤ 2 * A ^ ((1 : ℝ) / 5) * B ^ ((4 : ℝ) / 5) := by
  have ha : 0 < A.toReal := ENNReal.toReal_pos hA0 hAtop
  have hb : 0 < B.toReal := ENNReal.toReal_pos hB0 hBtop
  set a := A.toReal with ha_def
  set b := B.toReal with hb_def
  have hba : 0 < b / a := div_pos hb ha
  set R := (b / a) ^ ((2 : ℝ) / 5) with hR_def
  have hR : 0 < R := Real.rpow_pos_of_pos hba _
  have hA_eq : A = ENNReal.ofReal a := (ENNReal.ofReal_toReal hAtop).symm
  have hB_eq : B = ENNReal.ofReal b := (ENNReal.ofReal_toReal hBtop).symm
  have hR2 : R ^ 2 = (b / a) ^ ((4 : ℝ) / 5) := by
    rw [hR_def, ← Real.rpow_natCast ((b / a) ^ ((2 : ℝ) / 5)) 2, ← Real.rpow_mul hba.le]
    norm_num
  have hRhalf : R ^ (-(1 : ℝ) / 2) = (b / a) ^ (-(1 : ℝ) / 5) := by
    rw [hR_def, ← Real.rpow_mul hba.le]
    norm_num
  have ha45 : (0 : ℝ) < a ^ ((4 : ℝ) / 5) := Real.rpow_pos_of_pos ha _
  have hb15 : (0 : ℝ) < b ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hb _
  have h1 : a * R ^ 2 = a ^ ((1 : ℝ) / 5) * b ^ ((4 : ℝ) / 5) := by
    rw [hR2, Real.div_rpow hb.le ha.le,
        show a ^ ((1 : ℝ) / 5) = a / a ^ ((4 : ℝ) / 5) by
          rw [show (1 : ℝ) / 5 = 1 - 4 / 5 by norm_num, Real.rpow_sub ha, Real.rpow_one]]
    field_simp
  have h2 : b * R ^ (-(1 : ℝ) / 2) = a ^ ((1 : ℝ) / 5) * b ^ ((4 : ℝ) / 5) := by
    rw [hRhalf, show -(1 : ℝ) / 5 = -((1 : ℝ) / 5) by norm_num, Real.rpow_neg hba.le,
        Real.div_rpow hb.le ha.le, inv_div,
        show b ^ ((4 : ℝ) / 5) = b / b ^ ((1 : ℝ) / 5) by
          rw [show (4 : ℝ) / 5 = 1 - 1 / 5 by norm_num, Real.rpow_sub hb, Real.rpow_one]]
    field_simp
  calc I ≤ A * ENNReal.ofReal (R ^ 2) + B * ENNReal.ofReal (R ^ (-(1 : ℝ) / 2)) := h R hR
    _ = ENNReal.ofReal (a * R ^ 2) + ENNReal.ofReal (b * R ^ (-(1 : ℝ) / 2)) := by
        rw [hA_eq, hB_eq, ← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_mul hb.le]
    _ = 2 * ENNReal.ofReal (a ^ ((1 : ℝ) / 5) * b ^ ((4 : ℝ) / 5)) := by
        rw [h1, h2, ← two_mul]
    _ = 2 * A ^ ((1 : ℝ) / 5) * B ^ ((4 : ℝ) / 5) := by
        rw [hA_eq, hB_eq,
            ENNReal.ofReal_rpow_of_nonneg ha.le (by norm_num : (0 : ℝ) ≤ 1 / 5),
            ENNReal.ofReal_rpow_of_nonneg hb.le (by norm_num : (0 : ℝ) ≤ 4 / 5),
            mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

/-- If `ρ` has nonvanishing integral, the maximal function is positive everywhere: the balls about
any point exhaust space, so some ball average is positive. -/
theorem maximalFunction_ne_zero (ρ : Space 3 → ℝ≥0∞) {x : Space 3}
    (hρ0 : ∫⁻ y, ρ y ≠ 0) : maximalFunction ρ x ≠ 0 := by
  intro hM
  apply hρ0
  have hball : ∀ q : ℚ, 0 < q → ∫⁻ y in Metric.ball x (q : ℝ), ρ y = 0 := by
    intro q hq
    have havg := average_le_maximalFunction ρ x hq
    rw [hM] at havg
    have h0 := le_zero_iff.mp havg
    have hvol : volume (Metric.ball x (q : ℝ)) ≠ ∞ := by
      rw [vol_ball_three x (Rat.cast_pos.mpr hq).le]
      exact ENNReal.ofReal_ne_top
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (ENNReal.inv_eq_zero.mp h) hvol
    · exact h
  have hcover : (Set.univ : Set (Space 3)) = ⋃ n : ℕ, Metric.ball x ((n : ℝ) + 1) := by
    ext y
    simp only [Set.mem_univ, true_iff, Set.mem_iUnion, Metric.mem_ball]
    exact ⟨⌊dist y x⌋₊, Nat.lt_floor_add_one _⟩
  have hzero : ∀ n : ℕ, ∫⁻ y in Metric.ball x ((n : ℝ) + 1), ρ y = 0 := by
    intro n
    have h := hball ((n : ℚ) + 1) (by positivity)
    rwa [show (((n : ℚ) + 1 : ℚ) : ℝ) = (n : ℝ) + 1 by push_cast; ring] at h
  have hle : ∫⁻ y, ρ y ≤ 0 :=
    calc ∫⁻ y, ρ y = ∫⁻ y in Set.univ, ρ y := (setLIntegral_univ ρ).symm
    _ = ∫⁻ y in ⋃ n : ℕ, Metric.ball x ((n : ℝ) + 1), ρ y := by rw [hcover]
    _ ≤ ∑' n : ℕ, ∫⁻ y in Metric.ball x ((n : ℝ) + 1), ρ y := lintegral_iUnion_le _ _
    _ = 0 := by simp [hzero]
  exact le_zero_iff.mp hle

/-- **Hedberg's pointwise inequality** for the Newtonian kernel in `Space 3`: the Riesz potential
is controlled by an interpolation of the maximal function and the `L^{6/5}` mass,
`I₂ρ(x) ≤ 2·(16π·Mρ(x))^{1/5}·(N^{5/6}·(4π/3)^{1/6})^{4/5}`, obtained by splitting at the
optimal radius `R = (B/A)^{2/5}` between the near bound (`near_bound`) and the far bound
(`far_bound`). -/
theorem hedberg_pointwise (ρ : Space 3 → ℝ≥0∞) (hρ : Measurable ρ) (x : Space 3)
    (hM0 : maximalFunction ρ x ≠ 0) (hMtop : maximalFunction ρ x ≠ ∞)
    (hN0 : ∫⁻ y, ρ y ^ ((6 : ℝ) / 5) ≠ 0) (hNtop : ∫⁻ y, ρ y ^ ((6 : ℝ) / 5) ≠ ∞) :
    ∫⁻ y, ρ y * ENNReal.ofReal ‖x - y‖⁻¹
      ≤ 2 * (ENNReal.ofReal (16 * Real.pi) * maximalFunction ρ x) ^ ((1 : ℝ) / 5)
        * ((∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 6)
            * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6))) ^ ((4 : ℝ) / 5) := by
  apply radius_optimization
  · exact mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' hM0
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMtop
  · refine mul_ne_zero (fun h => ?_) (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    rcases ENNReal.rpow_eq_zero_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hN0 h1
    · norm_num at h2
  · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hNtop)
      ENNReal.ofReal_ne_top
  intro R hR
  have hcompl : (Metric.ball x R)ᶜ = {y : Space 3 | R ≤ ‖x - y‖} := by
    ext y
    simp only [Set.mem_compl_iff, Metric.mem_ball, Set.mem_setOf_eq, not_lt, dist_eq_norm,
      norm_sub_rev y x]
  have hnear_eq : ENNReal.ofReal (16 * Real.pi * R ^ 2) * maximalFunction ρ x
      = ENNReal.ofReal (16 * Real.pi) * maximalFunction ρ x * ENNReal.ofReal (R ^ 2) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 16 * Real.pi)]
    ring
  have hfar_eq : (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 6)
        * ENNReal.ofReal ((4 * Real.pi / 3 * R ^ (-3 : ℝ)) ^ ((1 : ℝ) / 6))
      = (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 6)
          * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6))
          * ENNReal.ofReal (R ^ (-(1 : ℝ) / 2)) := by
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * Real.pi / 3)
          (Real.rpow_nonneg hR.le _),
        ← Real.rpow_mul hR.le, show (-3 : ℝ) * ((1 : ℝ) / 6) = -(1 : ℝ) / 2 by norm_num,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (4 * Real.pi / 3) ^ ((1 : ℝ) / 6)),
        mul_assoc]
  calc ∫⁻ y, ρ y * ENNReal.ofReal ‖x - y‖⁻¹
      = (∫⁻ y in Metric.ball x R, ρ y * ENNReal.ofReal ‖x - y‖⁻¹)
        + ∫⁻ y in (Metric.ball x R)ᶜ, ρ y * ENNReal.ofReal ‖x - y‖⁻¹ :=
        (lintegral_add_compl _ measurableSet_ball).symm
    _ = (∫⁻ y in Metric.ball x R, ρ y * ENNReal.ofReal ‖x - y‖⁻¹)
        + ∫⁻ y in {y : Space 3 | R ≤ ‖x - y‖}, ρ y * ENNReal.ofReal ‖x - y‖⁻¹ := by
        rw [hcompl]
    _ ≤ ENNReal.ofReal (16 * Real.pi * R ^ 2) * maximalFunction ρ x
        + (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 6)
            * ENNReal.ofReal ((4 * Real.pi / 3 * R ^ (-3 : ℝ)) ^ ((1 : ℝ) / 6)) :=
        add_le_add (near_bound ρ hρ x hR) (far_bound ρ hρ x hR)
    _ = ENNReal.ofReal (16 * Real.pi) * maximalFunction ρ x * ENNReal.ofReal (R ^ 2)
        + (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 6)
            * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6))
            * ENNReal.ofReal (R ^ (-(1 : ℝ) / 2)) := by
        rw [hnear_eq, hfar_eq]

/-- Sixth power of the Riesz potential integrates against `N^5`: raising Hedberg's pointwise
inequality to the sixth power turns `Mρ^{1/5}` into `Mρ^{6/5}`, whose integral the strong `(p,p)`
bound controls by `N`; the remaining factors contribute `N^4`. -/
theorem lintegral_riesz_sixth_power_le (ρ : Space 3 → ℝ≥0∞) (hρ : Measurable ρ)
    (hρ0 : ∫⁻ y, ρ y ≠ 0)
    (hNtop : ∫⁻ y, ρ y ^ ((6 : ℝ) / 5) ≠ ∞) :
    ∫⁻ x, (∫⁻ y, ρ y * ENNReal.ofReal ‖x - y‖⁻¹) ^ (6 : ℝ)
      ≤ (2 : ℝ≥0∞) ^ (6 : ℝ) * ENNReal.ofReal (16 * Real.pi) ^ ((6 : ℝ) / 5)
        * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6)) ^ ((24 : ℝ) / 5)
        * ENNReal.ofReal (128 * (6 / 5) * 2 ^ ((6 : ℝ) / 5 - 1) / ((6 : ℝ) / 5 - 1))
        * (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ (5 : ℝ) := by
  have hN0 : ∫⁻ y, ρ y ^ ((6 : ℝ) / 5) ≠ 0 := by
    intro h
    apply hρ0
    have hz := (lintegral_eq_zero_iff (by fun_prop)).mp h
    have hz' : ρ =ᵐ[volume] 0 := by
      filter_upwards [hz] with y hy
      simp only [Pi.zero_apply] at hy ⊢
      rcases ENNReal.rpow_eq_zero_iff.mp hy with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · norm_num at h2
    rw [lintegral_congr_ae hz']
    simp
  have hMmeas : Measurable (maximalFunction ρ) := measurable_maximalFunction ρ hρ
  have hpt : ∀ᵐ x, (∫⁻ y, ρ y * ENNReal.ofReal ‖x - y‖⁻¹) ^ (6 : ℝ)
      ≤ (2 : ℝ≥0∞) ^ (6 : ℝ) * ENNReal.ofReal (16 * Real.pi) ^ ((6 : ℝ) / 5)
        * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6)) ^ ((24 : ℝ) / 5)
        * (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ (4 : ℝ)
        * maximalFunction ρ x ^ ((6 : ℝ) / 5) := by
    filter_upwards [maximalFunction_lt_top_ae_of_lintegral_rpow ρ hρ
      (by norm_num : (1 : ℝ) < 6 / 5) hNtop] with x hx
    have h := hedberg_pointwise ρ hρ x (maximalFunction_ne_zero ρ hρ0) hx.ne hN0 hNtop
    calc (∫⁻ y, ρ y * ENNReal.ofReal ‖x - y‖⁻¹) ^ (6 : ℝ)
        ≤ (2 * (ENNReal.ofReal (16 * Real.pi) * maximalFunction ρ x) ^ ((1 : ℝ) / 5)
            * ((∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 6)
                * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6))) ^ ((4 : ℝ) / 5)) ^ (6 : ℝ) :=
          ENNReal.rpow_le_rpow h (by norm_num)
      _ = (2 : ℝ≥0∞) ^ (6 : ℝ) * ENNReal.ofReal (16 * Real.pi) ^ ((6 : ℝ) / 5)
            * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6)) ^ ((24 : ℝ) / 5)
            * (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ (4 : ℝ)
            * maximalFunction ρ x ^ ((6 : ℝ) / 5) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6),
              ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6),
              ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
              show (1 : ℝ) / 5 * 6 = 6 / 5 by norm_num,
              show (4 : ℝ) / 5 * 6 = 24 / 5 by norm_num,
              ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6 / 5),
              ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 24 / 5),
              ← ENNReal.rpow_mul, show (5 : ℝ) / 6 * (24 / 5) = 4 by norm_num]
          ring
  have hN45 : (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ (4 : ℝ) * (∫⁻ y, ρ y ^ ((6 : ℝ) / 5))
      = (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ (5 : ℝ) := by
    nth_rewrite 2 [← ENNReal.rpow_one (∫⁻ y, ρ y ^ ((6 : ℝ) / 5))]
    rw [← ENNReal.rpow_add _ _ hN0 hNtop]
    norm_num
  calc ∫⁻ x, (∫⁻ y, ρ y * ENNReal.ofReal ‖x - y‖⁻¹) ^ (6 : ℝ)
      ≤ ∫⁻ x, (2 : ℝ≥0∞) ^ (6 : ℝ) * ENNReal.ofReal (16 * Real.pi) ^ ((6 : ℝ) / 5)
          * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6)) ^ ((24 : ℝ) / 5)
          * (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ (4 : ℝ)
          * maximalFunction ρ x ^ ((6 : ℝ) / 5) := lintegral_mono_ae hpt
    _ = (2 : ℝ≥0∞) ^ (6 : ℝ) * ENNReal.ofReal (16 * Real.pi) ^ ((6 : ℝ) / 5)
          * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6)) ^ ((24 : ℝ) / 5)
          * (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ (4 : ℝ)
          * ∫⁻ x, maximalFunction ρ x ^ ((6 : ℝ) / 5) := by
        rw [lintegral_const_mul _ (by fun_prop)]
    _ ≤ (2 : ℝ≥0∞) ^ (6 : ℝ) * ENNReal.ofReal (16 * Real.pi) ^ ((6 : ℝ) / 5)
          * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6)) ^ ((24 : ℝ) / 5)
          * (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ (4 : ℝ)
          * (ENNReal.ofReal (128 * (6 / 5) * 2 ^ ((6 : ℝ) / 5 - 1) / ((6 : ℝ) / 5 - 1))
              * ∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) :=
        mul_le_mul_of_nonneg_left
          (lintegral_maximalFunction_rpow_le ρ hρ
            (by norm_num : (1 : ℝ) < 6 / 5) hNtop) zero_le
    _ = (2 : ℝ≥0∞) ^ (6 : ℝ) * ENNReal.ofReal (16 * Real.pi) ^ ((6 : ℝ) / 5)
          * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6)) ^ ((24 : ℝ) / 5)
          * ENNReal.ofReal (128 * (6 / 5) * 2 ^ ((6 : ℝ) / 5 - 1) / ((6 : ℝ) / 5 - 1))
          * (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ (5 : ℝ) := by
        rw [show (2 : ℝ≥0∞) ^ (6 : ℝ) * ENNReal.ofReal (16 * Real.pi) ^ ((6 : ℝ) / 5)
              * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6)) ^ ((24 : ℝ) / 5)
              * (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ (4 : ℝ)
              * (ENNReal.ofReal (128 * (6 / 5) * 2 ^ ((6 : ℝ) / 5 - 1) / ((6 : ℝ) / 5 - 1))
                  * ∫⁻ y, ρ y ^ ((6 : ℝ) / 5))
            = (2 : ℝ≥0∞) ^ (6 : ℝ) * ENNReal.ofReal (16 * Real.pi) ^ ((6 : ℝ) / 5)
              * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6)) ^ ((24 : ℝ) / 5)
              * ENNReal.ofReal (128 * (6 / 5) * 2 ^ ((6 : ℝ) / 5 - 1) / ((6 : ℝ) / 5 - 1))
              * ((∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ (4 : ℝ) * ∫⁻ y, ρ y ^ ((6 : ℝ) / 5))
            from by ring, hN45]

/-- The finite coefficient in the sixth-power Riesz-potential estimate.
Naming it once lets the bilinear HLS and downstream Newtonian-continuity
layers share the analytic constant without copying its expansion. -/
noncomputable def newtonianRieszSixthConstant : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (6 : ℝ)
    * ENNReal.ofReal (16 * Real.pi) ^ ((6 : ℝ) / 5)
    * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6)) ^ ((24 : ℝ) / 5)
    * ENNReal.ofReal
      (128 * (6 / 5) * 2 ^ ((6 : ℝ) / 5 - 1) / ((6 : ℝ) / 5 - 1))

lemma newtonianRieszSixthConstant_ne_top :
    newtonianRieszSixthConstant ≠ ∞ := by
  unfold newtonianRieszSixthConstant
  finiteness

/-- **Bilinear general-density Hardy--Littlewood--Sobolev estimate.**
For measurable `ρ, σ ∈ L^(6/5)(ℝ³)`, the mutual Newtonian form is bounded
by the `L^(6/5)` mass of `ρ` times the sixth-root Riesz-potential bound of
`σ`.  This is the non-diagonal estimate needed to control differences of
Hartree self-energies.  It follows directly from Hölder `(6/5,6)` and the
already-proved sixth-power Riesz estimate; no positivity or polarization
claim for signed real densities is inserted. -/
@[zil_level physical_theorem]
theorem lintegral_mutualInteraction_le
    (ρ σ : Space 3 → ℝ≥0∞) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hσtop : ∫⁻ y, σ y ^ ((6 : ℝ) / 5) ≠ ∞) :
    ∫⁻ x, ρ x * ∫⁻ y, σ y * ENNReal.ofReal ‖x - y‖⁻¹
      ≤ (∫⁻ x, ρ x ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 6)
        * (newtonianRieszSixthConstant
            * (∫⁻ y, σ y ^ ((6 : ℝ) / 5)) ^ (5 : ℝ))
          ^ ((1 : ℝ) / 6) := by
  by_cases hσ0 : ∫⁻ y, σ y = 0
  · have hz : σ =ᵐ[volume] 0 := (lintegral_eq_zero_iff hσ).mp hσ0
    have hpotential : ∀ x : Space 3,
        ∫⁻ y, σ y * ENNReal.ofReal ‖x - y‖⁻¹ = 0 := by
      intro x
      calc
        ∫⁻ y, σ y * ENNReal.ofReal ‖x - y‖⁻¹
            = ∫⁻ _y : Space 3, (0 : ℝ≥0∞) := by
                apply lintegral_congr_ae
                filter_upwards [hz] with y hy
                simp [hy]
        _ = 0 := by simp
    simp only [hpotential, mul_zero, lintegral_zero, zero_le]
  · have hI₂meas : Measurable
        (fun x : Space 3 => ∫⁻ y, σ y * ENNReal.ofReal ‖x - y‖⁻¹) := by
      apply Measurable.lintegral_prod_right
      exact (hσ.comp measurable_snd).mul
        (by fun_prop : Measurable fun p : Space 3 × Space 3 =>
          ENNReal.ofReal ‖p.1 - p.2‖⁻¹)
    have hpq : (6 / 5 : ℝ).HolderConjugate 6 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
      hρ.aemeasurable hI₂meas.aemeasurable
    have h6 := lintegral_riesz_sixth_power_le σ hσ hσ0 hσtop
    calc
      ∫⁻ x, ρ x * ∫⁻ y, σ y * ENNReal.ofReal ‖x - y‖⁻¹
          ≤ (∫⁻ x, ρ x ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 6)
            * (∫⁻ x, (∫⁻ y, σ y * ENNReal.ofReal ‖x - y‖⁻¹) ^ (6 : ℝ))
                ^ ((1 : ℝ) / 6) := by
              simpa [show (1 : ℝ) / (6 / 5) = 5 / 6 by norm_num] using hHolder
      _ ≤ (∫⁻ x, ρ x ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 6)
            * (newtonianRieszSixthConstant
                * (∫⁻ y, σ y ^ ((6 : ℝ) / 5)) ^ (5 : ℝ))
              ^ ((1 : ℝ) / 6) := by
          apply mul_le_mul_of_nonneg_left
          apply ENNReal.rpow_le_rpow _ (by norm_num)
          simpa [newtonianRieszSixthConstant] using h6
          exact zero_le

/-- **General-density Hardy–Littlewood–Sobolev inequality** for the Newtonian kernel in `Space 3`:
the self-interaction energy of any measurable density `ρ ∈ L^{6/5}` is controlled by its
`L^{6/5}` mass,
`∬ ρ(x)ρ(y)/‖x−y‖ ≤ C·(∫ρ^{6/5})^{5/3}`,
i.e. `≤ C·‖ρ‖_{6/5}²`. Hölder against the sixth-power bound of the Riesz potential, which in turn
rests on Hedberg's pointwise inequality and the strong `(p,p)` maximal-function estimate.
The previous auxiliary `L¹` hypothesis has been removed through `weak_p_p`. -/
theorem lintegral_selfInteraction_le (ρ : Space 3 → ℝ≥0∞) (hρ : Measurable ρ)
    (hNtop : ∫⁻ y, ρ y ^ ((6 : ℝ) / 5) ≠ ∞) :
    ∫⁻ x, ρ x * ∫⁻ y, ρ y * ENNReal.ofReal ‖x - y‖⁻¹
      ≤ ((2 : ℝ≥0∞) ^ (6 : ℝ) * ENNReal.ofReal (16 * Real.pi) ^ ((6 : ℝ) / 5)
          * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6)) ^ ((24 : ℝ) / 5)
          * ENNReal.ofReal (128 * (6 / 5) * 2 ^ ((6 : ℝ) / 5 - 1)
              / ((6 : ℝ) / 5 - 1))) ^ ((1 : ℝ) / 6)
        * (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 3) := by
  by_cases hρ0 : ∫⁻ y, ρ y = 0
  · have hz : ρ =ᵐ[volume] 0 := (lintegral_eq_zero_iff hρ).mp hρ0
    have hzz : (fun x => ρ x * ∫⁻ y, ρ y * ENNReal.ofReal ‖x - y‖⁻¹) =ᵐ[volume] 0 := by
      filter_upwards [hz] with x hx
      simp only [Pi.zero_apply] at hx ⊢
      rw [hx, zero_mul]
    rw [lintegral_congr_ae hzz]
    simp
  · have hN0 : ∫⁻ y, ρ y ^ ((6 : ℝ) / 5) ≠ 0 := by
      intro h
      apply hρ0
      have hz := (lintegral_eq_zero_iff (by fun_prop)).mp h
      have hz' : ρ =ᵐ[volume] 0 := by
        filter_upwards [hz] with y hy
        simp only [Pi.zero_apply] at hy ⊢
        rcases ENNReal.rpow_eq_zero_iff.mp hy with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact h1
        · norm_num at h2
      rw [lintegral_congr_ae hz']
      simp
    have hI₂meas : Measurable (fun x : Space 3 => ∫⁻ y, ρ y * ENNReal.ofReal ‖x - y‖⁻¹) := by
      apply Measurable.lintegral_prod_right
      exact (hρ.comp measurable_snd).mul
        (by fun_prop : Measurable fun p : Space 3 × Space 3 => ENNReal.ofReal ‖p.1 - p.2‖⁻¹)
    have hpq : (6 / 5 : ℝ).HolderConjugate 6 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hρ.aemeasurable
      hI₂meas.aemeasurable
    refine le_trans hHolder ?_
    rw [show (1 : ℝ) / (6 / 5) = 5 / 6 by norm_num]
    have h6 := lintegral_riesz_sixth_power_le ρ hρ hρ0 hNtop
    calc (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 6)
          * (∫⁻ x, (∫⁻ y, ρ y * ENNReal.ofReal ‖x - y‖⁻¹) ^ (6 : ℝ)) ^ ((1 : ℝ) / 6)
        ≤ (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 6)
          * (((2 : ℝ≥0∞) ^ (6 : ℝ) * ENNReal.ofReal (16 * Real.pi) ^ ((6 : ℝ) / 5)
              * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6)) ^ ((24 : ℝ) / 5)
              * ENNReal.ofReal (128 * (6 / 5) * 2 ^ ((6 : ℝ) / 5 - 1) / ((6 : ℝ) / 5 - 1)))
              * (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ (5 : ℝ)) ^ ((1 : ℝ) / 6) :=
          mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow h6 (by norm_num)) zero_le
      _ = ((2 : ℝ≥0∞) ^ (6 : ℝ) * ENNReal.ofReal (16 * Real.pi) ^ ((6 : ℝ) / 5)
            * ENNReal.ofReal ((4 * Real.pi / 3) ^ ((1 : ℝ) / 6)) ^ ((24 : ℝ) / 5)
            * ENNReal.ofReal (128 * (6 / 5) * 2 ^ ((6 : ℝ) / 5 - 1)
                / ((6 : ℝ) / 5 - 1))) ^ ((1 : ℝ) / 6)
          * (∫⁻ y, ρ y ^ ((6 : ℝ) / 5)) ^ ((5 : ℝ) / 3) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 6),
              ← ENNReal.rpow_mul, show (5 : ℝ) * (1 / 6) = 5 / 6 by norm_num,
              show ∀ X C : ℝ≥0∞, X ^ ((5 : ℝ) / 6) * (C * X ^ ((5 : ℝ) / 6))
                  = C * (X ^ ((5 : ℝ) / 6) * X ^ ((5 : ℝ) / 6)) from fun X C => by ring,
              ← ENNReal.rpow_add _ _ hN0 hNtop]
          norm_num

end Hedberg

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.HardyLittlewoodMaximalFunction

end
