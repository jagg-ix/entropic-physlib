/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.SpaceAndTime.Space.Integrals.Basic
public import Physlib.Mathematics.Distribution.SchwartzNuclear.SchwartzSlicing
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Zonal integration on the Euclidean two-sphere

This module proves the measure transport underlying axial, or zonal, integration on `S²`.
The proof uses `Measure.toSphere`, orthonormal-coordinate invariance of Lebesgue volume, Euclidean
Fubini slicing, and the existing exact area of a two-dimensional ball.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Pointwise Space

namespace Space

/-! ## A. Axial coordinates and solid cones -/

set_option backward.isDefEq.respectTransparency false in
/-- Fubini slicing of Euclidean space with the last coordinate as the outer integral. -/
lemma integral_euclidean_snoc_last (d : ℕ)
    (g : EuclideanSpace ℝ (Fin (d + 2)) → ℝ) (hg : Integrable g) :
    ∫ x, g x =
      ∫ t : ℝ, ∫ y : EuclideanSpace ℝ (Fin (d + 1)),
        g (GaussianField.euclideanSnoc (d + 1) y t) := by
  have hv := PiLp.volume_preserving_toLp (ι := Fin (d + 2))
  rw [← hv.integral_comp' (f := MeasurableEquiv.toLp 2 _)]
  set e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 2) => ℝ)
    (Fin.last (d + 1))).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 2) => ℝ)
      (Fin.last (d + 1))).symm _
  rw [← hem.integral_comp' (f := e)]
  set F : ℝ × (Fin (d + 1) → ℝ) → ℝ :=
    fun p => g ((MeasurableEquiv.toLp 2 _) (e p))
  have hint : Integrable F :=
    (hem.integrable_comp_emb e.measurableEmbedding).mpr
      ((hv.integrable_comp_emb (MeasurableEquiv.toLp 2 _).measurableEmbedding).mpr hg)
  rw [volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  have hv' := PiLp.volume_preserving_toLp (ι := Fin (d + 1))
  congr 1
  funext t
  rw [← hv'.integral_comp' (f := MeasurableEquiv.toLp 2 _)]
  congr 1
  funext y'
  show F (t, y') =
    g (GaussianField.euclideanSnoc (d + 1) ((MeasurableEquiv.toLp 2 _) y') t)
  simp only [F, e, MeasurableEquiv.piFinSuccAbove_symm_apply, MeasurableEquiv.toLp,
    MeasurableEquiv.coe_mk]
  congr 1
  ext i
  simp only [GaussianField.euclideanSnoc, WithLp.equiv_symm_apply]
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j
    simp [Fin.snoc_castSucc]

/-- The last Euclidean coordinate in dimension three. -/
def lastCoordinate3 (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  x (Fin.last 2)

lemma continuous_lastCoordinate3 : Continuous lastCoordinate3 := by
  unfold lastCoordinate3
  fun_prop

/-- The lower axial cap of the Euclidean unit two-sphere. -/
def lowerZonalCap3 (a : ℝ) : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  {n | lastCoordinate3 n.1 ≤ a}

/-- The open radial cone over `lowerZonalCap3 a`, truncated at unit radius. -/
def lowerZonalCone3 (a : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | x ≠ 0 ∧ ‖x‖ < 1 ∧ lastCoordinate3 x ≤ a * ‖x‖}

lemma measurableSet_lowerZonalCap3 (a : ℝ) : MeasurableSet (lowerZonalCap3 a) := by
  exact measurableSet_le (continuous_lastCoordinate3.comp continuous_subtype_val).measurable
    measurable_const

lemma measurableSet_lowerZonalCone3 (a : ℝ) : MeasurableSet (lowerZonalCone3 a) := by
  have hne : MeasurableSet {x : EuclideanSpace ℝ (Fin 3) | x ≠ 0} :=
    (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin 3))).compl
  have hnorm : MeasurableSet {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ < 1} :=
    measurableSet_lt continuous_norm.measurable measurable_const
  have hcoord : MeasurableSet
      {x : EuclideanSpace ℝ (Fin 3) | lastCoordinate3 x ≤ a * ‖x‖} :=
    measurableSet_le continuous_lastCoordinate3.measurable
      (continuous_const.mul continuous_norm).measurable
  exact hne.inter (hnorm.inter hcoord)

/-- The cone appearing in `Measure.toSphere_apply'` is the elementary norm-coordinate cone. -/
lemma Ioo_smul_lowerZonalCap3 (a : ℝ) :
    Set.Ioo (0 : ℝ) 1 •
        ((fun n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 => n.1) ''
          lowerZonalCap3 a) =
      lowerZonalCone3 a := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨n, hn, rfl⟩, rfl⟩
    have hnorm : ‖(r : ℝ) • (n : EuclideanSpace ℝ (Fin 3))‖ = r := by
      rw [norm_smul, mem_sphere_zero_iff_norm.mp n.2, mul_one, Real.norm_eq_abs,
        abs_of_pos hr.1]
    refine ⟨?_, by simpa [hnorm] using hr.2, ?_⟩
    · apply smul_ne_zero hr.1.ne'
      intro hnzero
      change (n.1 : EuclideanSpace ℝ (Fin 3)) = 0 at hnzero
      have := mem_sphere_zero_iff_norm.mp n.2
      rw [hnzero, norm_zero] at this
      norm_num at this
    · change lastCoordinate3 (r • n.1) ≤ a * ‖r • n.1‖
      rw [hnorm]
      change r * lastCoordinate3 n.1 ≤ a * r
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hn (le_of_lt hr.1)
  · rintro ⟨hx, hxnorm, hxcoord⟩
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
      ⟨‖x‖⁻¹ • x, by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']⟩
    refine ⟨‖x‖, ⟨hnorm, hxnorm⟩, n.1, ⟨n, ?_, rfl⟩, ?_⟩
    · change lastCoordinate3 (‖x‖⁻¹ • x) ≤ a
      change ‖x‖⁻¹ * lastCoordinate3 x ≤ a
      exact (inv_mul_le_iff₀ hnorm).2 (by simpa [mul_comm] using hxcoord)
    · simp [n, smul_smul, hnorm.ne']

/-! ## B. Euclidean cross-sections of a lower solid cone -/

/-- Radius of the planar section of the open unit ball at height `z`. -/
def unitBallSectionRadius (z : ℝ) : ℝ :=
  Real.sqrt (1 - z ^ 2)

lemma unitBallSectionRadius_sq {z : ℝ} (hz : z ∈ Set.Ioo (-1 : ℝ) 1) :
    unitBallSectionRadius z ^ 2 = 1 - z ^ 2 := by
  rw [unitBallSectionRadius, Real.sq_sqrt]
  nlinarith [hz.1, hz.2]

lemma euclideanSnoc_lastCoordinate3 (y : EuclideanSpace ℝ (Fin 2)) (z : ℝ) :
    lastCoordinate3 (GaussianField.euclideanSnoc 2 y z) = z := by
  simp only [lastCoordinate3, GaussianField.euclideanSnoc, WithLp.equiv_symm_apply]
  show (@Fin.snoc 2 (fun _ : Fin 3 => ℝ) (fun i : Fin 2 => y.ofLp i) z)
      (2 : Fin 3) = z
  rw [show (2 : Fin 3) = Fin.last 2 by rfl]
  exact @Fin.snoc_last 2 (fun _ : Fin 3 => ℝ) z (fun i : Fin 2 => y.ofLp i)

/-- Below the equatorial plane, every point of the unit-ball section belongs to a lower cap cone
whose height is nonnegative. -/
lemma lowerZonalCone3_section_neg {a z : ℝ} (ha : 0 ≤ a)
    (hz : z ∈ Set.Ioo (-1 : ℝ) 0) :
    {y : EuclideanSpace ℝ (Fin 2) |
        GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 a} =
      Metric.ball 0 (unitBallSectionRadius z) := by
  ext y
  have hzIoo : z ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hz.1, hz.2.trans (by norm_num)⟩
  have hradiusSq := unitBallSectionRadius_sq hzIoo
  have hradiusNonneg : 0 ≤ unitBallSectionRadius z := Real.sqrt_nonneg _
  have hsnocSq : ‖GaussianField.euclideanSnoc 2 y z‖ ^ 2 = ‖y‖ ^ 2 + z ^ 2 := by
    simpa using GaussianField.euclideanSnoc_norm_sq 1 y z
  rw [Set.mem_setOf_eq, lowerZonalCone3, Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]
  constructor
  · rintro ⟨_, hnorm, _⟩
    have hnormSq : ‖GaussianField.euclideanSnoc 2 y z‖ ^ 2 < 1 := by
      nlinarith [norm_nonneg (GaussianField.euclideanSnoc 2 y z)]
    rw [← sq_lt_sq₀ (norm_nonneg y) hradiusNonneg]
    nlinarith
  · intro hy
    have hynormSq : ‖y‖ ^ 2 < unitBallSectionRadius z ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg y) hradiusNonneg).2 hy
    have hnormSq : ‖GaussianField.euclideanSnoc 2 y z‖ ^ 2 < 1 := by
      nlinarith
    have hnorm : ‖GaussianField.euclideanSnoc 2 y z‖ < 1 := by
      nlinarith [norm_nonneg (GaussianField.euclideanSnoc 2 y z)]
    refine ⟨?_, hnorm, ?_⟩
    · intro hzero
      have := congrArg lastCoordinate3 hzero
      rw [euclideanSnoc_lastCoordinate3, lastCoordinate3] at this
      simp only [PiLp.zero_apply] at this
      exact hz.2.ne this
    · rw [euclideanSnoc_lastCoordinate3]
      exact le_trans hz.2.le (mul_nonneg ha (norm_nonneg _))

/-- Inner radius removed from a positive-height section of a lower cap cone. -/
def lowerZonalInnerRadius (a z : ℝ) : ℝ :=
  z * Real.sqrt (1 - a ^ 2) / a

lemma lowerZonalInnerRadius_nonneg {a z : ℝ} (ha : 0 < a) (hz : 0 ≤ z) :
    0 ≤ lowerZonalInnerRadius a z := by
  unfold lowerZonalInnerRadius
  positivity

lemma lowerZonalInnerRadius_sq {a z : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    lowerZonalInnerRadius a z ^ 2 = z ^ 2 * (1 - a ^ 2) / a ^ 2 := by
  have haSq : 0 ≤ 1 - a ^ 2 := by nlinarith
  unfold lowerZonalInnerRadius
  rw [div_pow, mul_pow, Real.sq_sqrt haSq]

/-- At positive height below the cap parameter, a lower cap cone cuts out the annulus between the
unit-ball section and the cone's inner radius. -/
lemma lowerZonalCone3_section_pos {a z : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hz : z ∈ Set.Ioo 0 a) :
    {y : EuclideanSpace ℝ (Fin 2) |
        GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 a} =
      Metric.ball 0 (unitBallSectionRadius z) \
        Metric.ball 0 (lowerZonalInnerRadius a z) := by
  ext y
  have hz1 : z < 1 := hz.2.trans ha1
  have hzIoo : z ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hz.1], hz1⟩
  have hradiusSq := unitBallSectionRadius_sq hzIoo
  have hradiusNonneg : 0 ≤ unitBallSectionRadius z := Real.sqrt_nonneg _
  have hinnerNonneg : 0 ≤ lowerZonalInnerRadius a z :=
    lowerZonalInnerRadius_nonneg ha hz.1.le
  have hinnerSq := lowerZonalInnerRadius_sq (z := z) ha ha1
  have hsnocSq : ‖GaussianField.euclideanSnoc 2 y z‖ ^ 2 = ‖y‖ ^ 2 + z ^ 2 := by
    simpa using GaussianField.euclideanSnoc_norm_sq 1 y z
  rw [Set.mem_setOf_eq, lowerZonalCone3, Set.mem_setOf_eq, Set.mem_sdiff,
    Metric.mem_ball, Metric.mem_ball]
  simp only [dist_zero_right]
  constructor
  · rintro ⟨_, hnorm, hcoord⟩
    have hnormSq : ‖GaussianField.euclideanSnoc 2 y z‖ ^ 2 < 1 := by
      nlinarith [norm_nonneg (GaussianField.euclideanSnoc 2 y z)]
    have hyOuter : ‖y‖ < unitBallSectionRadius z := by
      rw [← sq_lt_sq₀ (norm_nonneg y) hradiusNonneg]
      nlinarith
    have hcoord' : z ≤ a * ‖GaussianField.euclideanSnoc 2 y z‖ := by
      simpa [euclideanSnoc_lastCoordinate3] using hcoord
    have hcoordSq : z ^ 2 ≤
        (a * ‖GaussianField.euclideanSnoc 2 y z‖) ^ 2 :=
      (sq_le_sq₀ hz.1.le (mul_nonneg ha.le (norm_nonneg _))).2 hcoord'
    have hbase : z ^ 2 * (1 - a ^ 2) ≤ a ^ 2 * ‖y‖ ^ 2 := by
      nlinarith
    have hinnerSqLe : lowerZonalInnerRadius a z ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [hinnerSq]
      exact (div_le_iff₀ (sq_pos_of_pos ha)).2
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using hbase)
    refine ⟨hyOuter, ?_⟩
    exact not_lt_of_ge ((sq_le_sq₀ hinnerNonneg (norm_nonneg y)).1 hinnerSqLe)
  · rintro ⟨hyOuter, hyInner⟩
    have hyOuterSq : ‖y‖ ^ 2 < unitBallSectionRadius z ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg y) hradiusNonneg).2 hyOuter
    have hnormSq : ‖GaussianField.euclideanSnoc 2 y z‖ ^ 2 < 1 := by
      nlinarith
    have hnorm : ‖GaussianField.euclideanSnoc 2 y z‖ < 1 := by
      nlinarith [norm_nonneg (GaussianField.euclideanSnoc 2 y z)]
    have hinnerLe : lowerZonalInnerRadius a z ≤ ‖y‖ := le_of_not_gt hyInner
    have hinnerSqLe : lowerZonalInnerRadius a z ^ 2 ≤ ‖y‖ ^ 2 :=
      (sq_le_sq₀ hinnerNonneg (norm_nonneg y)).2 hinnerLe
    have hbase : z ^ 2 * (1 - a ^ 2) ≤ a ^ 2 * ‖y‖ ^ 2 := by
      rw [hinnerSq] at hinnerSqLe
      have := (div_le_iff₀ (sq_pos_of_pos ha)).1 hinnerSqLe
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hcoordSq : z ^ 2 ≤
        (a * ‖GaussianField.euclideanSnoc 2 y z‖) ^ 2 := by
      nlinarith
    have hcoord : z ≤ a * ‖GaussianField.euclideanSnoc 2 y z‖ :=
      (sq_le_sq₀ hz.1.le (mul_nonneg ha.le (norm_nonneg _))).1 hcoordSq
    refine ⟨?_, hnorm, ?_⟩
    · intro hzero
      have := congrArg lastCoordinate3 hzero
      rw [euclideanSnoc_lastCoordinate3, lastCoordinate3] at this
      simp only [PiLp.zero_apply] at this
      exact hz.1.ne' this
    · simpa [euclideanSnoc_lastCoordinate3] using hcoord

/-! ## C. Cross-section areas -/

lemma integral_indicator_ball_two (r : ℝ) (hr : 0 ≤ r) :
    ∫ y : EuclideanSpace ℝ (Fin 2),
        (Metric.ball 0 r).indicator (fun _ => (1 : ℝ)) y = Real.pi * r ^ 2 := by
  rw [integral_indicator_const (1 : ℝ) measurableSet_ball, smul_eq_mul, mul_one,
    measureReal_def,
    EuclideanSpace.volume_ball_fin_two]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal Real.pi_nonneg]
  ring

lemma integral_indicator_ball_sdiff_ball_two (r s : ℝ) (hs : 0 ≤ s) (hsr : s ≤ r) :
    ∫ y : EuclideanSpace ℝ (Fin 2),
        (Metric.ball 0 r \ Metric.ball 0 s).indicator (fun _ => (1 : ℝ)) y =
      Real.pi * (r ^ 2 - s ^ 2) := by
  rw [integral_indicator_const (1 : ℝ) (measurableSet_ball.diff measurableSet_ball),
    smul_eq_mul, mul_one, measureReal_sdiff]
  · rw [measureReal_def, measureReal_def, EuclideanSpace.volume_ball_fin_two,
      EuclideanSpace.volume_ball_fin_two]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal,
      ENNReal.toReal_ofReal Real.pi_nonneg, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hs, ENNReal.toReal_ofReal Real.pi_nonneg]
    · ring
    · exact le_trans hs hsr
  · exact Metric.ball_subset_ball hsr
  · exact measurableSet_ball

/-- The planar annulus in a positive cone section has a polynomial area. -/
lemma lowerZonalCone3_section_pos_integral {a z : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hz : z ∈ Set.Ioo 0 a) :
    ∫ y : EuclideanSpace ℝ (Fin 2),
        (lowerZonalCone3 a).indicator (fun _ => (1 : ℝ))
          (GaussianField.euclideanSnoc 2 y z) =
      Real.pi * (1 - z ^ 2 / a ^ 2) := by
  have hzIoo : z ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hz.1], hz.2.trans ha1⟩
  have houterNonneg : 0 ≤ unitBallSectionRadius z := Real.sqrt_nonneg _
  have hinnerNonneg : 0 ≤ lowerZonalInnerRadius a z :=
    lowerZonalInnerRadius_nonneg ha hz.1.le
  have hinnerLeOuter : lowerZonalInnerRadius a z ≤ unitBallSectionRadius z := by
    have hzSq : z ^ 2 < a ^ 2 := (sq_lt_sq₀ hz.1.le ha.le).2 hz.2
    rw [← sq_le_sq₀ hinnerNonneg houterNonneg, lowerZonalInnerRadius_sq ha ha1,
      unitBallSectionRadius_sq hzIoo]
    apply (div_le_iff₀ (sq_pos_of_pos ha)).2
    nlinarith
  change ∫ y : EuclideanSpace ℝ (Fin 2),
      {y | GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 a}.indicator
        (fun _ => (1 : ℝ)) y = _
  rw [lowerZonalCone3_section_pos ha ha1 hz]
  rw [integral_indicator_ball_sdiff_ball_two _ _ hinnerNonneg hinnerLeOuter,
    unitBallSectionRadius_sq hzIoo, lowerZonalInnerRadius_sq ha ha1]
  field_simp
  ring

lemma lowerZonalCone3_section_neg_integral {a z : ℝ} (ha : 0 ≤ a)
    (hz : z ∈ Set.Ioo (-1 : ℝ) 0) :
    ∫ y : EuclideanSpace ℝ (Fin 2),
        (lowerZonalCone3 a).indicator (fun _ => (1 : ℝ))
          (GaussianField.euclideanSnoc 2 y z) =
      Real.pi * (1 - z ^ 2) := by
  change ∫ y : EuclideanSpace ℝ (Fin 2),
      {y | GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 a}.indicator
        (fun _ => (1 : ℝ)) y = _
  rw [lowerZonalCone3_section_neg ha hz]
  calc
    _ = Real.pi * unitBallSectionRadius z ^ 2 :=
      integral_indicator_ball_two (unitBallSectionRadius z) (Real.sqrt_nonneg _)
    _ = _ := by rw [unitBallSectionRadius_sq ⟨hz.1, hz.2.trans (by norm_num)⟩]

lemma lowerZonalCone3_section_empty {a z : ℝ} (ha : 0 < a) (hz0 : z ≠ 0)
    (hneg : z ∉ Set.Ioo (-1 : ℝ) 0) (hpos : z ∉ Set.Ioo 0 a) :
    {y : EuclideanSpace ℝ (Fin 2) |
        GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 a} = ∅ := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, hnorm, hcoord⟩
  have hzNormLe : ‖z‖ ≤ ‖GaussianField.euclideanSnoc 2 y z‖ :=
    GaussianField.euclideanSnoc_norm_ge_right 1 y z
  have hzAbs : |z| < 1 := by simpa [Real.norm_eq_abs] using hzNormLe.trans_lt hnorm
  have hzBounds : -1 < z ∧ z < 1 := (abs_lt.mp hzAbs)
  have hcoord' : z ≤ a * ‖GaussianField.euclideanSnoc 2 y z‖ := by
    simpa [euclideanSnoc_lastCoordinate3] using hcoord
  have hmul : a * ‖GaussianField.euclideanSnoc 2 y z‖ < a := by
    simpa using mul_lt_mul_of_pos_left hnorm ha
  have hza : z < a := hcoord'.trans_lt hmul
  rcases lt_or_gt_of_ne hz0 with hzlt | hzgt
  · exact hneg ⟨hzBounds.1, hzlt⟩
  · exact hpos ⟨hzgt, hza⟩

/-- Almost every planar section of a positive lower cap cone is one of the two explicit disk or
annulus sections. -/
lemma lowerZonalCone3_section_integral_ae {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᵐ z ∂(volume : Measure ℝ),
      (∫ y : EuclideanSpace ℝ (Fin 2),
          (lowerZonalCone3 a).indicator (fun _ => (1 : ℝ))
            (GaussianField.euclideanSnoc 2 y z)) =
        (Set.Ioo (-1 : ℝ) 0).indicator (fun z => Real.pi * (1 - z ^ 2)) z +
        (Set.Ioo 0 a).indicator (fun z => Real.pi * (1 - z ^ 2 / a ^ 2)) z := by
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with z hz0
  by_cases hneg : z ∈ Set.Ioo (-1 : ℝ) 0
  · have hnotPos : z ∉ Set.Ioo 0 a := fun hz => (not_lt_of_ge hz.1.le) hneg.2
    rw [lowerZonalCone3_section_neg_integral ha.le hneg]
    simp [hneg, hnotPos]
  · by_cases hpos : z ∈ Set.Ioo 0 a
    · rw [lowerZonalCone3_section_pos_integral ha ha1 hpos]
      simp [hneg, hpos]
    · have hempty := lowerZonalCone3_section_empty ha hz0 hneg hpos
      change ∫ y : EuclideanSpace ℝ (Fin 2),
          {y | GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 a}.indicator
            (fun _ => (1 : ℝ)) y = _
      rw [hempty]
      simp [hneg, hpos]

lemma integral_Ioo_pi_one_sub_sq :
    ∫ z in Set.Ioo (-1 : ℝ) 0, Real.pi * (1 - z ^ 2) = 2 * Real.pi / 3 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0)]
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun _ : ℝ => Real.pi * 1).intervalIntegrable (-1) 0)
      ((by fun_prop : Continuous fun z : ℝ => Real.pi * z ^ 2).intervalIntegrable (-1) 0),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_pow]
  ring

lemma integral_Ioo_pi_one_sub_sq_div {a : ℝ} (ha : 0 < a) :
    ∫ z in Set.Ioo 0 a, Real.pi * (1 - z ^ 2 / a ^ 2) = 2 * Real.pi * a / 3 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha.le]
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun _ : ℝ => Real.pi * 1).intervalIntegrable 0 a)
      ((by fun_prop : Continuous fun z : ℝ => Real.pi * (z ^ 2 / a ^ 2)).intervalIntegrable 0 a),
    intervalIntegral.integral_const]
  rw [show (fun z : ℝ => Real.pi * (z ^ 2 / a ^ 2)) =
      fun z => (Real.pi / a ^ 2) * z ^ 2 by
    funext z
    ring]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  field_simp
  ring

lemma integrable_lowerZonalCone3_indicator (a : ℝ) :
    Integrable ((lowerZonalCone3 a).indicator (fun _ => (1 : ℝ))) := by
  have hsubset : lowerZonalCone3 a ⊆
      Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro x hx
    simpa [Metric.mem_ball] using hx.2.1
  have hball : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ))
      (Metric.ball 0 1) := integrableOn_const (measure_ball_lt_top.ne)
  exact (hball.mono_set hsubset).integrable_indicator (measurableSet_lowerZonalCone3 a)

/-- The cone over the lower cap of height `a ∈ (0,1)` has the expected solid-cone volume. -/
lemma lowerZonalCone3_volumeReal_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (lowerZonalCone3 a) =
      2 * Real.pi * (1 + a) / 3 := by
  let g : EuclideanSpace ℝ (Fin 3) → ℝ :=
    (lowerZonalCone3 a).indicator (fun _ => (1 : ℝ))
  have hg : Integrable g := integrable_lowerZonalCone3_indicator a
  have hneg : Integrable
      ((Set.Ioo (-1 : ℝ) 0).indicator (fun z => Real.pi * (1 - z ^ 2))) :=
    ((by fun_prop : Continuous fun z : ℝ => Real.pi * (1 - z ^ 2)).integrableOn_Icc
      |>.mono_set Set.Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
  have hpos : Integrable
      ((Set.Ioo 0 a).indicator (fun z => Real.pi * (1 - z ^ 2 / a ^ 2))) :=
    ((by fun_prop : Continuous fun z : ℝ => Real.pi * (1 - z ^ 2 / a ^ 2)).integrableOn_Icc
      |>.mono_set Set.Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
  calc
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (lowerZonalCone3 a) =
        ∫ x, g x := by
      symm
      simpa [g, smul_eq_mul] using
        (integral_indicator_const (1 : ℝ) (measurableSet_lowerZonalCone3 a))
    _ = ∫ z : ℝ, ∫ y : EuclideanSpace ℝ (Fin 2),
          g (GaussianField.euclideanSnoc 2 y z) :=
      integral_euclidean_snoc_last 1 g hg
    _ = ∫ z : ℝ,
        (Set.Ioo (-1 : ℝ) 0).indicator (fun z => Real.pi * (1 - z ^ 2)) z +
        (Set.Ioo 0 a).indicator (fun z => Real.pi * (1 - z ^ 2 / a ^ 2)) z :=
      integral_congr_ae (lowerZonalCone3_section_integral_ae ha ha1)
    _ = (∫ z in Set.Ioo (-1 : ℝ) 0, Real.pi * (1 - z ^ 2)) +
        ∫ z in Set.Ioo 0 a, Real.pi * (1 - z ^ 2 / a ^ 2) := by
      rw [integral_add hneg hpos, integral_indicator measurableSet_Ioo,
        integral_indicator measurableSet_Ioo]
    _ = _ := by
      rw [integral_Ioo_pi_one_sub_sq, integral_Ioo_pi_one_sub_sq_div ha]
      ring

/-- The `toSphere` measure of a positive-height lower cap is `2π(1+a)`. -/
lemma toSphere_lowerZonalCap3_real_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere.real (lowerZonalCap3 a) =
      2 * Real.pi * (1 + a) := by
  rw [measureReal_def, Measure.toSphere_apply' _ (measurableSet_lowerZonalCap3 a),
    Ioo_smul_lowerZonalCap3 a]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  change 3 * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (lowerZonalCone3 a) = _
  rw [lowerZonalCone3_volumeReal_pos ha ha1]
  ring

/-! ## D. Negative-height caps -/

lemma lowerZonalCone3_neg_section_full {b z : ℝ} (hb : 0 < b)
    (hz : z ∈ Set.Ioo (-1 : ℝ) (-b)) :
    {y : EuclideanSpace ℝ (Fin 2) |
        GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 (-b)} =
      Metric.ball 0 (unitBallSectionRadius z) := by
  ext y
  have hzIoo : z ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hz.1, hz.2.trans (by linarith)⟩
  have hradiusSq := unitBallSectionRadius_sq hzIoo
  have hradiusNonneg : 0 ≤ unitBallSectionRadius z := Real.sqrt_nonneg _
  have hsnocSq : ‖GaussianField.euclideanSnoc 2 y z‖ ^ 2 = ‖y‖ ^ 2 + z ^ 2 := by
    simpa using GaussianField.euclideanSnoc_norm_sq 1 y z
  rw [Set.mem_setOf_eq, lowerZonalCone3, Set.mem_setOf_eq, Metric.mem_ball,
    dist_zero_right]
  constructor
  · rintro ⟨_, hnorm, _⟩
    have hnormSq : ‖GaussianField.euclideanSnoc 2 y z‖ ^ 2 < 1 := by
      nlinarith [norm_nonneg (GaussianField.euclideanSnoc 2 y z)]
    rw [← sq_lt_sq₀ (norm_nonneg y) hradiusNonneg]
    nlinarith
  · intro hy
    have hySq : ‖y‖ ^ 2 < unitBallSectionRadius z ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg y) hradiusNonneg).2 hy
    have hnormSq : ‖GaussianField.euclideanSnoc 2 y z‖ ^ 2 < 1 := by nlinarith
    have hnorm : ‖GaussianField.euclideanSnoc 2 y z‖ < 1 := by
      nlinarith [norm_nonneg (GaussianField.euclideanSnoc 2 y z)]
    refine ⟨?_, hnorm, ?_⟩
    · intro hzero
      have := congrArg lastCoordinate3 hzero
      rw [euclideanSnoc_lastCoordinate3, lastCoordinate3] at this
      simp only [PiLp.zero_apply] at this
      exact (by linarith [hz.2, hb] : z ≠ 0) this
    · rw [euclideanSnoc_lastCoordinate3]
      have hmul : -b < (-b) * ‖GaussianField.euclideanSnoc 2 y z‖ := by
        nlinarith [norm_nonneg (GaussianField.euclideanSnoc 2 y z)]
      exact hz.2.le.trans hmul.le

lemma lowerZonalCone3_neg_section_inner {b z : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hz : z ∈ Set.Ioo (-b) 0) :
    {y : EuclideanSpace ℝ (Fin 2) |
        GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 (-b)} =
      Metric.closedBall 0 (lowerZonalInnerRadius b (-z)) := by
  ext y
  have hsPos : 0 < -z := neg_pos.mpr hz.2
  have hsLt : -z < b := by linarith [hz.1]
  have hinnerNonneg : 0 ≤ lowerZonalInnerRadius b (-z) :=
    lowerZonalInnerRadius_nonneg hb hsPos.le
  have hinnerSq := lowerZonalInnerRadius_sq (z := -z) hb hb1
  have hsnocSq : ‖GaussianField.euclideanSnoc 2 y z‖ ^ 2 = ‖y‖ ^ 2 + z ^ 2 := by
    simpa using GaussianField.euclideanSnoc_norm_sq 1 y z
  rw [Set.mem_setOf_eq, lowerZonalCone3, Set.mem_setOf_eq, Metric.mem_closedBall,
    dist_zero_right]
  constructor
  · rintro ⟨_, _, hcoord⟩
    have hcoord' : b * ‖GaussianField.euclideanSnoc 2 y z‖ ≤ -z := by
      rw [euclideanSnoc_lastCoordinate3] at hcoord
      linarith
    have hcoordSq : (b * ‖GaussianField.euclideanSnoc 2 y z‖) ^ 2 ≤ (-z) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg hb.le (norm_nonneg _)) hsPos.le).2 hcoord'
    have hbase : b ^ 2 * ‖y‖ ^ 2 ≤ z ^ 2 * (1 - b ^ 2) := by nlinarith
    have hySq : ‖y‖ ^ 2 ≤ lowerZonalInnerRadius b (-z) ^ 2 := by
      rw [hinnerSq]
      apply (le_div_iff₀ (sq_pos_of_pos hb)).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
    exact (sq_le_sq₀ (norm_nonneg y) hinnerNonneg).1 hySq
  · intro hy
    have hySq : ‖y‖ ^ 2 ≤ lowerZonalInnerRadius b (-z) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg y) hinnerNonneg).2 hy
    rw [hinnerSq] at hySq
    have hbase : b ^ 2 * ‖y‖ ^ 2 ≤ z ^ 2 * (1 - b ^ 2) := by
      have := (le_div_iff₀ (sq_pos_of_pos hb)).1 hySq
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hcoordSq : (b * ‖GaussianField.euclideanSnoc 2 y z‖) ^ 2 ≤ (-z) ^ 2 := by
      nlinarith
    have hcoord' : b * ‖GaussianField.euclideanSnoc 2 y z‖ ≤ -z :=
      (sq_le_sq₀ (mul_nonneg hb.le (norm_nonneg _)) hsPos.le).1 hcoordSq
    have hzSq : z ^ 2 < b ^ 2 := by
      have := (sq_lt_sq₀ hsPos.le hb.le).2 hsLt
      simpa using this
    have hnormSq : ‖GaussianField.euclideanSnoc 2 y z‖ ^ 2 < 1 := by
      nlinarith [sq_pos_of_pos hb]
    have hnorm : ‖GaussianField.euclideanSnoc 2 y z‖ < 1 := by
      nlinarith [norm_nonneg (GaussianField.euclideanSnoc 2 y z)]
    refine ⟨?_, hnorm, ?_⟩
    · intro hzero
      have := congrArg lastCoordinate3 hzero
      rw [euclideanSnoc_lastCoordinate3, lastCoordinate3] at this
      simp only [PiLp.zero_apply] at this
      exact hz.2.ne this
    · rw [euclideanSnoc_lastCoordinate3]
      linarith

lemma integral_indicator_closedBall_two (r : ℝ) (hr : 0 ≤ r) :
    ∫ y : EuclideanSpace ℝ (Fin 2),
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r).indicator
          (fun _ => (1 : ℝ)) y =
      Real.pi * r ^ 2 := by
  rw [integral_indicator_const (1 : ℝ) measurableSet_closedBall, smul_eq_mul, mul_one,
    measureReal_def, EuclideanSpace.volume_closedBall_fin_two]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal Real.pi_nonneg]
  ring

lemma lowerZonalCone3_neg_section_full_integral {b z : ℝ} (hb : 0 < b)
    (hz : z ∈ Set.Ioo (-1 : ℝ) (-b)) :
    (∫ y : EuclideanSpace ℝ (Fin 2),
        (lowerZonalCone3 (-b)).indicator (fun _ => (1 : ℝ))
          (GaussianField.euclideanSnoc 2 y z)) =
      Real.pi * (1 - z ^ 2) := by
  rw [show (fun y : EuclideanSpace ℝ (Fin 2) =>
      (lowerZonalCone3 (-b)).indicator (fun _ => (1 : ℝ))
        (GaussianField.euclideanSnoc 2 y z)) =
      {y | GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 (-b)}.indicator
        (fun _ => (1 : ℝ)) by
    funext y
    simp only [Set.indicator, Set.mem_ofPred_eq]]
  rw [lowerZonalCone3_neg_section_full hb hz,
    integral_indicator_ball_two (unitBallSectionRadius z)
      (Real.sqrt_nonneg _), unitBallSectionRadius_sq]
  exact ⟨hz.1, hz.2.trans (by linarith [hb])⟩

lemma lowerZonalCone3_neg_section_inner_integral {b z : ℝ} (hb : 0 < b)
    (hb1 : b < 1) (hz : z ∈ Set.Ioo (-b) 0) :
    (∫ y : EuclideanSpace ℝ (Fin 2),
        (lowerZonalCone3 (-b)).indicator (fun _ => (1 : ℝ))
          (GaussianField.euclideanSnoc 2 y z)) =
      Real.pi * (z ^ 2 * (1 - b ^ 2) / b ^ 2) := by
  rw [show (fun y : EuclideanSpace ℝ (Fin 2) =>
      (lowerZonalCone3 (-b)).indicator (fun _ => (1 : ℝ))
        (GaussianField.euclideanSnoc 2 y z)) =
      {y | GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 (-b)}.indicator
        (fun _ => (1 : ℝ)) by
    funext y
    simp only [Set.indicator, Set.mem_ofPred_eq]]
  rw [lowerZonalCone3_neg_section_inner hb hb1 hz,
    integral_indicator_closedBall_two (lowerZonalInnerRadius b (-z))
      (lowerZonalInnerRadius_nonneg hb (neg_nonneg.mpr hz.2.le)),
    lowerZonalInnerRadius_sq hb hb1]
  ring

lemma lowerZonalCone3_neg_section_empty {b z : ℝ} (hb : 0 < b)
    (_hz0 : z ≠ 0) (hzb : z ≠ -b)
    (hfull : z ∉ Set.Ioo (-1 : ℝ) (-b))
    (hinner : z ∉ Set.Ioo (-b) 0) :
    {y : EuclideanSpace ℝ (Fin 2) |
        GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 (-b)} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hcone := hy
  rw [Set.mem_setOf_eq, lowerZonalCone3, Set.mem_setOf_eq] at hcone
  have hnormPos : 0 < ‖GaussianField.euclideanSnoc 2 y z‖ :=
    norm_pos_iff.mpr hcone.1
  have hzNeg : z < 0 := by
    rw [euclideanSnoc_lastCoordinate3] at hcone
    nlinarith [mul_pos hb hnormPos]
  have hzLower : -1 < z := by
    have hzNorm : |z| ≤ ‖GaussianField.euclideanSnoc 2 y z‖ := by
      simpa [euclideanSnoc_lastCoordinate3] using
        GaussianField.euclideanSnoc_norm_ge_right 1 y z
    rw [abs_of_neg hzNeg] at hzNorm
    linarith [hcone.2.1]
  rcases lt_or_gt_of_ne hzb with hlt | hgt
  · exact hfull ⟨hzLower, hlt⟩
  · exact hinner ⟨hgt, hzNeg⟩

lemma lowerZonalCone3_neg_section_integral_ae {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∀ᵐ z : ℝ,
      (∫ y : EuclideanSpace ℝ (Fin 2),
          (lowerZonalCone3 (-b)).indicator (fun _ => (1 : ℝ))
            (GaussianField.euclideanSnoc 2 y z)) =
        (Set.Ioo (-1 : ℝ) (-b)).indicator (fun z => Real.pi * (1 - z ^ 2)) z +
        (Set.Ioo (-b) 0).indicator
          (fun z => Real.pi * (z ^ 2 * (1 - b ^ 2) / b ^ 2)) z := by
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) (0 : ℝ),
    Measure.ae_ne (volume : Measure ℝ) (-b)] with z hz0 hzb
  by_cases hfull : z ∈ Set.Ioo (-1 : ℝ) (-b)
  · rw [lowerZonalCone3_neg_section_full_integral hb hfull]
    simp [hfull, not_lt_of_ge hfull.2.le]
  · by_cases hinner : z ∈ Set.Ioo (-b) 0
    · rw [lowerZonalCone3_neg_section_inner_integral hb hb1 hinner]
      simp [hfull, hinner]
    · have hempty := lowerZonalCone3_neg_section_empty hb hz0 hzb hfull hinner
      rw [show (fun y : EuclideanSpace ℝ (Fin 2) =>
          (lowerZonalCone3 (-b)).indicator (fun _ => (1 : ℝ))
            (GaussianField.euclideanSnoc 2 y z)) =
          {y | GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 (-b)}.indicator
            (fun _ => (1 : ℝ)) by
        funext y
        simp only [Set.indicator, Set.mem_ofPred_eq], hempty]
      simp [hfull, hinner]

lemma integral_Ioo_neg_one_neg_pi_one_sub_sq {b : ℝ} (_hb : 0 < b) (hb1 : b < 1) :
    ∫ z in Set.Ioo (-1 : ℝ) (-b), Real.pi * (1 - z ^ 2) =
      Real.pi * (2 / 3 - b + b ^ 3 / 3) := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith : (-1 : ℝ) ≤ -b)]
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun _ : ℝ => Real.pi * 1).intervalIntegrable (-1) (-b))
      ((by fun_prop : Continuous fun z : ℝ => Real.pi * z ^ 2).intervalIntegrable (-1) (-b)),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_pow]
  ring

lemma integral_Ioo_neg_inner_pi {b : ℝ} (hb : 0 < b) :
    ∫ z in Set.Ioo (-b) 0,
        Real.pi * (z ^ 2 * (1 - b ^ 2) / b ^ 2) =
      Real.pi * b * (1 - b ^ 2) / 3 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith : -b ≤ (0 : ℝ))]
  rw [show (fun z : ℝ => Real.pi * (z ^ 2 * (1 - b ^ 2) / b ^ 2)) =
      fun z => (Real.pi * (1 - b ^ 2) / b ^ 2) * z ^ 2 by
    funext z
    ring]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  field_simp
  ring

/-- The cone over a negative-height lower cap has volume `2π(1-b)/3`. -/
lemma lowerZonalCone3_volumeReal_neg {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (lowerZonalCone3 (-b)) =
      2 * Real.pi * (1 - b) / 3 := by
  let g : EuclideanSpace ℝ (Fin 3) → ℝ :=
    (lowerZonalCone3 (-b)).indicator (fun _ => (1 : ℝ))
  have hg : Integrable g := integrable_lowerZonalCone3_indicator (-b)
  have hfull : Integrable
      ((Set.Ioo (-1 : ℝ) (-b)).indicator (fun z => Real.pi * (1 - z ^ 2))) :=
    ((by fun_prop : Continuous fun z : ℝ => Real.pi * (1 - z ^ 2)).integrableOn_Icc
      |>.mono_set Set.Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
  have hinner : Integrable
      ((Set.Ioo (-b) 0).indicator
        (fun z => Real.pi * (z ^ 2 * (1 - b ^ 2) / b ^ 2))) :=
    ((by fun_prop : Continuous fun z : ℝ =>
        Real.pi * (z ^ 2 * (1 - b ^ 2) / b ^ 2)).integrableOn_Icc
      |>.mono_set Set.Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
  calc
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (lowerZonalCone3 (-b)) =
        ∫ x, g x := by
      symm
      simpa [g, smul_eq_mul] using
        (integral_indicator_const (1 : ℝ) (measurableSet_lowerZonalCone3 (-b)))
    _ = ∫ z : ℝ, ∫ y : EuclideanSpace ℝ (Fin 2),
          g (GaussianField.euclideanSnoc 2 y z) :=
      integral_euclidean_snoc_last 1 g hg
    _ = ∫ z : ℝ,
        (Set.Ioo (-1 : ℝ) (-b)).indicator (fun z => Real.pi * (1 - z ^ 2)) z +
        (Set.Ioo (-b) 0).indicator
          (fun z => Real.pi * (z ^ 2 * (1 - b ^ 2) / b ^ 2)) z :=
      integral_congr_ae (lowerZonalCone3_neg_section_integral_ae hb hb1)
    _ = (∫ z in Set.Ioo (-1 : ℝ) (-b), Real.pi * (1 - z ^ 2)) +
        ∫ z in Set.Ioo (-b) 0,
          Real.pi * (z ^ 2 * (1 - b ^ 2) / b ^ 2) := by
      rw [integral_add hfull hinner, integral_indicator measurableSet_Ioo,
        integral_indicator measurableSet_Ioo]
    _ = _ := by
      rw [integral_Ioo_neg_one_neg_pi_one_sub_sq hb hb1,
        integral_Ioo_neg_inner_pi hb]
      ring

/-- The `toSphere` measure of a negative-height lower cap is `2π(1-b)`. -/
lemma toSphere_lowerZonalCap3_real_neg {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere.real (lowerZonalCap3 (-b)) =
      2 * Real.pi * (1 - b) := by
  rw [measureReal_def, Measure.toSphere_apply' _ (measurableSet_lowerZonalCap3 (-b)),
    Ioo_smul_lowerZonalCap3 (-b)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  change 3 * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real
      (lowerZonalCone3 (-b)) = _
  rw [lowerZonalCone3_volumeReal_neg hb hb1]
  ring

/-! ## E. Equator and endpoint caps -/

lemma lowerZonalCone3_zero_section_empty {z : ℝ} (hz0 : z ≠ 0)
    (hneg : z ∉ Set.Ioo (-1 : ℝ) 0) :
    {y : EuclideanSpace ℝ (Fin 2) |
        GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 0} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  rw [Set.mem_setOf_eq, lowerZonalCone3, Set.mem_setOf_eq] at hy
  have hzNonpos : z ≤ 0 := by
    rw [euclideanSnoc_lastCoordinate3] at hy
    simpa using hy.2.2
  have hzNeg : z < 0 := lt_of_le_of_ne hzNonpos hz0
  have hzNorm : |z| ≤ ‖GaussianField.euclideanSnoc 2 y z‖ :=
    GaussianField.euclideanSnoc_norm_ge_right 1 y z
  rw [abs_of_neg hzNeg] at hzNorm
  exact hneg ⟨by linarith [hy.2.1], hzNeg⟩

lemma lowerZonalCone3_zero_section_integral_ae :
    ∀ᵐ z : ℝ,
      (∫ y : EuclideanSpace ℝ (Fin 2),
          (lowerZonalCone3 0).indicator (fun _ => (1 : ℝ))
            (GaussianField.euclideanSnoc 2 y z)) =
        (Set.Ioo (-1 : ℝ) 0).indicator (fun z => Real.pi * (1 - z ^ 2)) z := by
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) (0 : ℝ)] with z hz0
  by_cases hneg : z ∈ Set.Ioo (-1 : ℝ) 0
  · rw [lowerZonalCone3_section_neg_integral (a := 0) (by norm_num) hneg]
    simp [hneg]
  · have hempty := lowerZonalCone3_zero_section_empty hz0 hneg
    rw [show (fun y : EuclideanSpace ℝ (Fin 2) =>
        (lowerZonalCone3 0).indicator (fun _ => (1 : ℝ))
          (GaussianField.euclideanSnoc 2 y z)) =
        {y | GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 0}.indicator
          (fun _ => (1 : ℝ)) by
      funext y
      simp only [Set.indicator, Set.mem_ofPred_eq], hempty]
    simp [hneg]

lemma lowerZonalCone3_volumeReal_zero :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (lowerZonalCone3 0) =
      2 * Real.pi / 3 := by
  let g : EuclideanSpace ℝ (Fin 3) → ℝ :=
    (lowerZonalCone3 0).indicator (fun _ => (1 : ℝ))
  have hg : Integrable g := integrable_lowerZonalCone3_indicator 0
  calc
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (lowerZonalCone3 0) =
        ∫ x, g x := by
      symm
      simpa [g, smul_eq_mul] using
        (integral_indicator_const (1 : ℝ) (measurableSet_lowerZonalCone3 0))
    _ = ∫ z : ℝ, ∫ y : EuclideanSpace ℝ (Fin 2),
          g (GaussianField.euclideanSnoc 2 y z) :=
      integral_euclidean_snoc_last 1 g hg
    _ = ∫ z : ℝ,
        (Set.Ioo (-1 : ℝ) 0).indicator (fun z => Real.pi * (1 - z ^ 2)) z :=
      integral_congr_ae lowerZonalCone3_zero_section_integral_ae
    _ = ∫ z in Set.Ioo (-1 : ℝ) 0, Real.pi * (1 - z ^ 2) := by
      rw [integral_indicator measurableSet_Ioo]
    _ = _ := integral_Ioo_pi_one_sub_sq

lemma toSphere_lowerZonalCap3_real_zero :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere.real (lowerZonalCap3 0) =
      2 * Real.pi := by
  rw [measureReal_def, Measure.toSphere_apply' _ (measurableSet_lowerZonalCap3 0),
    Ioo_smul_lowerZonalCap3 0]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  change 3 * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real
      (lowerZonalCone3 0) = _
  rw [lowerZonalCone3_volumeReal_zero]
  ring

lemma lowerZonalCone3_neg_one_section_subset (z : ℝ) :
    {y : EuclideanSpace ℝ (Fin 2) |
        GaussianField.euclideanSnoc 2 y z ∈ lowerZonalCone3 (-1)} ⊆ {0} := by
  intro y hy
  rw [Set.mem_setOf_eq, lowerZonalCone3, Set.mem_setOf_eq] at hy
  have hcoord : z ≤ -‖GaussianField.euclideanSnoc 2 y z‖ := by
    simpa [euclideanSnoc_lastCoordinate3] using hy.2.2
  have hzNeg : z < 0 := lt_of_le_of_ne (hcoord.trans (neg_nonpos.mpr (norm_nonneg _))) <| by
    intro hz
    subst z
    have := hy.2.2
    simp [euclideanSnoc_lastCoordinate3] at this
    exact hy.1 this
  have hzNorm : -z ≤ ‖GaussianField.euclideanSnoc 2 y z‖ := by
    simpa [abs_of_neg hzNeg] using GaussianField.euclideanSnoc_norm_ge_right 1 y z
  have hnorm : ‖GaussianField.euclideanSnoc 2 y z‖ = -z := by linarith
  have hsnocSq := GaussianField.euclideanSnoc_norm_sq 1 y z
  have : ‖y‖ ^ 2 = 0 := by nlinarith
  simpa [Set.mem_singleton_iff, norm_eq_zero] using (sq_eq_zero_iff.mp this)

lemma lowerZonalCone3_neg_one_section_integral (z : ℝ) :
    (∫ y : EuclideanSpace ℝ (Fin 2),
        (lowerZonalCone3 (-1)).indicator (fun _ => (1 : ℝ))
          (GaussianField.euclideanSnoc 2 y z)) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [Measure.ae_ne (volume : Measure (EuclideanSpace ℝ (Fin 2))) 0] with y hy
  have hnot : GaussianField.euclideanSnoc 2 y z ∉ lowerZonalCone3 (-1) := by
    intro hmem
    exact hy (lowerZonalCone3_neg_one_section_subset z hmem)
  simp [Set.indicator_of_notMem hnot]

lemma lowerZonalCone3_volumeReal_neg_one :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (lowerZonalCone3 (-1)) = 0 := by
  let g : EuclideanSpace ℝ (Fin 3) → ℝ :=
    (lowerZonalCone3 (-1)).indicator (fun _ => (1 : ℝ))
  have hg : Integrable g := integrable_lowerZonalCone3_indicator (-1)
  calc
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (lowerZonalCone3 (-1)) =
        ∫ x, g x := by
      symm
      simpa [g, smul_eq_mul] using
        (integral_indicator_const (1 : ℝ) (measurableSet_lowerZonalCone3 (-1)))
    _ = ∫ z : ℝ, ∫ y : EuclideanSpace ℝ (Fin 2),
          g (GaussianField.euclideanSnoc 2 y z) :=
      integral_euclidean_snoc_last 1 g hg
    _ = 0 := by
      simp only [g, lowerZonalCone3_neg_one_section_integral, integral_zero]

lemma toSphere_lowerZonalCap3_real_neg_one :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere.real (lowerZonalCap3 (-1)) = 0 := by
  rw [measureReal_def, Measure.toSphere_apply' _ (measurableSet_lowerZonalCap3 (-1)),
    Ioo_smul_lowerZonalCap3 (-1)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  change 3 * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real
      (lowerZonalCone3 (-1)) = 0
  rw [lowerZonalCone3_volumeReal_neg_one]
  ring

lemma lowerZonalCap3_eq_empty {a : ℝ} (ha : a < -1) : lowerZonalCap3 a = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro n hn
  rw [lowerZonalCap3, Set.mem_setOf_eq] at hn
  have hlast : -1 ≤ lastCoordinate3 n.1 := by
    have hcoord : |lastCoordinate3 n.1| ≤ ‖n.1‖ := by
      have hle := GaussianField.euclideanSnoc_norm_ge_right 1
        (GaussianField.euclideanInit 2 n.1) (lastCoordinate3 n.1)
      have hrecon := congrArg norm (GaussianField.euclideanSnoc_init_last 2 n.1)
      simpa [lastCoordinate3] using hle.trans_eq hrecon
    rw [mem_sphere_zero_iff_norm.mp n.2] at hcoord
    exact (neg_le_of_abs_le hcoord)
  linarith

lemma lowerZonalCap3_eq_univ {a : ℝ} (ha : 1 ≤ a) : lowerZonalCap3 a = Set.univ := by
  apply Set.eq_univ_of_forall
  intro n
  rw [lowerZonalCap3, Set.mem_setOf_eq]
  have hcoord : |lastCoordinate3 n.1| ≤ ‖n.1‖ := by
    have hle := GaussianField.euclideanSnoc_norm_ge_right 1
      (GaussianField.euclideanInit 2 n.1) (lastCoordinate3 n.1)
    have hrecon := congrArg norm (GaussianField.euclideanSnoc_init_last 2 n.1)
    simpa [lastCoordinate3] using hle.trans_eq hrecon
  rw [mem_sphere_zero_iff_norm.mp n.2] at hcoord
  exact (le_trans (le_abs_self _) hcoord).trans ha

lemma toSphere_real_univ_three :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere.real Set.univ =
      4 * Real.pi := by
  rw [Measure.toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  ring

/-- Closed-form distribution function of the last coordinate on the Euclidean two-sphere. -/
lemma toSphere_lowerZonalCap3_real (a : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere.real (lowerZonalCap3 a) =
      if a < -1 then 0 else if a < 1 then 2 * Real.pi * (1 + a) else 4 * Real.pi := by
  by_cases hlow : a < -1
  · rw [if_pos hlow, lowerZonalCap3_eq_empty hlow]
    simp
  rw [if_neg hlow]
  by_cases hhigh : a < 1
  · rw [if_pos hhigh]
    rcases lt_trichotomy a 0 with ha | rfl | ha
    · by_cases haNegOne : a = -1
      · subst a
        simpa using toSphere_lowerZonalCap3_real_neg_one
      · have hb : 0 < -a := neg_pos.mpr ha
        have hbNe : -a ≠ 1 := by
          intro h
          apply haNegOne
          linarith
        have hbLt : -a < 1 := lt_of_le_of_ne (by linarith) hbNe
        convert toSphere_lowerZonalCap3_real_neg hb hbLt using 1 <;> ring
    · simpa using toSphere_lowerZonalCap3_real_zero
    · exact toSphere_lowerZonalCap3_real_pos ha hhigh
  · rw [if_neg hhigh, lowerZonalCap3_eq_univ (le_of_not_gt hhigh),
      toSphere_real_univ_three]

/-! ## F. The spherical-coordinate pushforward -/

/-- The uniform height measure on `[-1,1]`, with the azimuthal factor `2π`. -/
def zonalHeightMeasure3 : Measure ℝ :=
  ENNReal.ofReal (2 * Real.pi) • volume.restrict (Set.Icc (-1 : ℝ) 1)

lemma zonalHeightMeasure3_Iic_real (a : ℝ) :
    zonalHeightMeasure3.real (Set.Iic a) =
      if a < -1 then 0 else if a < 1 then 2 * Real.pi * (1 + a) else 4 * Real.pi := by
  rw [zonalHeightMeasure3, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi),
    measureReal_restrict_apply measurableSet_Iic]
  by_cases hlow : a < -1
  · rw [if_pos hlow]
    have hinter : Set.Iic a ∩ Set.Icc (-1 : ℝ) 1 = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false]
      exact iff_false_intro fun hx => by linarith
    rw [hinter]
    simp
  rw [if_neg hlow]
  by_cases hhigh : a < 1
  · rw [if_pos hhigh]
    have hinter : Set.Iic a ∩ Set.Icc (-1 : ℝ) 1 = Set.Icc (-1) a := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor <;> intro hx
      · exact ⟨hx.2.1, hx.1⟩
      · exact ⟨hx.2, hx.1, hx.2.trans hhigh.le⟩
    rw [hinter, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ a - (-1))]
    ring
  · rw [if_neg hhigh]
    have hinter : Set.Iic a ∩ Set.Icc (-1 : ℝ) 1 = Set.Icc (-1) 1 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor <;> intro hx
      · exact hx.2
      · exact ⟨hx.2.trans (le_of_not_gt hhigh), hx⟩
    rw [hinter, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 - (-1))]
    ring

lemma lastCoordinate3_preimage_Iic (a : ℝ) :
    (fun n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      lastCoordinate3 n.1) ⁻¹' Set.Iic a = lowerZonalCap3 a := rfl

/-- The last coordinate pushes spherical surface measure on `S²` to `2π` times Lebesgue
measure on `[-1,1]`. This is the measure-theoretic spherical-coordinate formula. -/
theorem map_lastCoordinate3_toSphere :
    Measure.map
        (fun n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
          lastCoordinate3 n.1)
        (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere =
      zonalHeightMeasure3 := by
  letI : IsFiniteMeasure zonalHeightMeasure3 := by
    constructor
    simp [zonalHeightMeasure3, Real.volume_Icc]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (by simp)) (by simp)
  apply Measure.ext_of_Iic
  intro a
  apply (measureReal_eq_measureReal_iff).mp
  have hmeas : Measurable
      (fun n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
        lastCoordinate3 n.1) :=
    (continuous_lastCoordinate3.comp continuous_subtype_val).measurable
  rw [map_measureReal_apply hmeas measurableSet_Iic,
    lastCoordinate3_preimage_Iic, toSphere_lowerZonalCap3_real,
    zonalHeightMeasure3_Iic_real]

/-- Integrating a measurable function of the last coordinate over `S²` is the same as
integrating it against the uniform height measure. -/
theorem integral_comp_lastCoordinate3_toSphere (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f zonalHeightMeasure3) :
    (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        f (lastCoordinate3 n.1)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) =
      ∫ t : ℝ, f t ∂zonalHeightMeasure3 := by
  rw [← map_lastCoordinate3_toSphere]
  have hf' : AEStronglyMeasurable f
      (Measure.map
        (fun n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
          lastCoordinate3 n.1)
        (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) := by
    rw [map_lastCoordinate3_toSphere]
    exact hf
  exact (integral_map
    (continuous_lastCoordinate3.comp continuous_subtype_val).measurable.aemeasurable hf').symm

/-- For an interval-integrable scalar function, spherical zonal integration is exactly
`2π` times its interval integral on `[-1,1]`. -/
theorem integral_comp_lastCoordinate3_toSphere_eq_intervalIntegral (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (-1) 1) :
    (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        f (lastCoordinate3 n.1)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) =
      2 * Real.pi * ∫ t in (-1 : ℝ)..1, f t := by
  have hmeas : AEStronglyMeasurable f zonalHeightMeasure3 := by
    rw [zonalHeightMeasure3]
    have hfi : IntegrableOn f (Set.Icc (-1 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp hf
    exact hfi.aestronglyMeasurable.smul_measure _
  rw [integral_comp_lastCoordinate3_toSphere f hmeas, zonalHeightMeasure3,
    integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi), smul_eq_mul]
  rw [← restrict_Ioc_eq_restrict_Icc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

/-! ## G. Basis-independent use on `Space 3` -/

/-- Last coordinate relative to an orthonormal frame of physical three-space. -/
def basisLastCoordinate3 (b : OrthonormalBasis (Fin 3) ℝ (Space 3))
    (x : Space 3) : ℝ :=
  lastCoordinate3 (b.repr x)

lemma basisLastCoordinate3_smul
    (b : OrthonormalBasis (Fin 3) ℝ (Space 3)) (r : ℝ) (x : Space 3) :
    basisLastCoordinate3 b (r • x) = r * basisLastCoordinate3 b x := by
  simp [basisLastCoordinate3, lastCoordinate3]

def basisLowerZonalCap3 (b : OrthonormalBasis (Fin 3) ℝ (Space 3)) (a : ℝ) :
    Set (Metric.sphere (0 : Space 3) 1) :=
  {n | basisLastCoordinate3 b n.1 ≤ a}

def basisLowerZonalCone3 (b : OrthonormalBasis (Fin 3) ℝ (Space 3)) (a : ℝ) :
    Set (Space 3) :=
  {x | x ≠ 0 ∧ ‖x‖ < 1 ∧ basisLastCoordinate3 b x ≤ a * ‖x‖}

lemma measurableSet_basisLowerZonalCap3
    (b : OrthonormalBasis (Fin 3) ℝ (Space 3)) (a : ℝ) :
    MeasurableSet (basisLowerZonalCap3 b a) := by
  exact measurableSet_le
    ((continuous_lastCoordinate3.comp b.repr.continuous).comp continuous_subtype_val).measurable
    measurable_const

lemma measurableSet_basisLowerZonalCone3
    (b : OrthonormalBasis (Fin 3) ℝ (Space 3)) (a : ℝ) :
    MeasurableSet (basisLowerZonalCone3 b a) := by
  have hne : MeasurableSet ({0}ᶜ : Set (Space 3)) :=
    MeasurableSet.compl (measurableSet_singleton (0 : Space 3))
  have hnorm : MeasurableSet {x : Space 3 | ‖x‖ < 1} :=
    measurableSet_lt continuous_norm.measurable measurable_const
  have hcoord : MeasurableSet
      {x : Space 3 | basisLastCoordinate3 b x ≤ a * ‖x‖} :=
    measurableSet_le (continuous_lastCoordinate3.comp b.repr.continuous).measurable
      (continuous_const.mul continuous_norm).measurable
  exact hne.inter (hnorm.inter hcoord)

lemma Ioo_smul_basisLowerZonalCap3
    (b : OrthonormalBasis (Fin 3) ℝ (Space 3)) (a : ℝ) :
    Set.Ioo (0 : ℝ) 1 •
        ((fun n : Metric.sphere (0 : Space 3) 1 => n.1) '' basisLowerZonalCap3 b a) =
      basisLowerZonalCone3 b a := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨n, hn, rfl⟩, rfl⟩
    have hnorm : ‖(r : ℝ) • (n : Space 3)‖ = r := by
      rw [norm_smul, mem_sphere_zero_iff_norm.mp n.2, mul_one, Real.norm_eq_abs,
        abs_of_pos hr.1]
    refine ⟨?_, by simpa [hnorm] using hr.2, ?_⟩
    · apply smul_ne_zero hr.1.ne'
      intro hnzero
      change (n.1 : Space 3) = 0 at hnzero
      have := mem_sphere_zero_iff_norm.mp n.2
      rw [hnzero, norm_zero] at this
      norm_num at this
    · change basisLastCoordinate3 b (r • n.1) ≤ a * ‖r • n.1‖
      rw [hnorm, basisLastCoordinate3_smul]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hn (le_of_lt hr.1)
  · rintro ⟨hx, hxnorm, hxcoord⟩
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let n : Metric.sphere (0 : Space 3) 1 :=
      ⟨‖x‖⁻¹ • x, by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']⟩
    refine ⟨‖x‖, ⟨hnorm, hxnorm⟩, n.1, ⟨n, ?_, rfl⟩, ?_⟩
    · change basisLastCoordinate3 b (‖x‖⁻¹ • x) ≤ a
      rw [basisLastCoordinate3_smul]
      exact (inv_mul_le_iff₀ hnorm).2 (by simpa [mul_comm] using hxcoord)
    · simp [n, smul_smul, hnorm.ne']

lemma basisLowerZonalCone3_eq_preimage
    (b : OrthonormalBasis (Fin 3) ℝ (Space 3)) (a : ℝ) :
    basisLowerZonalCone3 b a = b.repr ⁻¹' lowerZonalCone3 a := by
  ext x
  simp [basisLowerZonalCone3, lowerZonalCone3, basisLastCoordinate3]

lemma basisLowerZonalCone3_volumeReal
    (b : OrthonormalBasis (Fin 3) ℝ (Space 3)) (a : ℝ) :
    (volume : Measure (Space 3)).real (basisLowerZonalCone3 b a) =
      (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (lowerZonalCone3 a) := by
  rw [basisLowerZonalCone3_eq_preimage]
  exact congrArg ENNReal.toReal
    (b.measurePreserving_repr.measure_preimage
      (measurableSet_lowerZonalCone3 a).nullMeasurableSet)

/-- Every orthonormal frame gives the same uniform coordinate distribution on the unit sphere. -/
lemma toSphere_basisLowerZonalCap3_real
    (b : OrthonormalBasis (Fin 3) ℝ (Space 3)) (a : ℝ) :
    (volume : Measure (Space 3)).toSphere.real (basisLowerZonalCap3 b a) =
      if a < -1 then 0 else if a < 1 then 2 * Real.pi * (1 + a) else 4 * Real.pi := by
  rw [measureReal_def, Measure.toSphere_apply' _ (measurableSet_basisLowerZonalCap3 b a),
    Ioo_smul_basisLowerZonalCap3 b a]
  simp only [Space.finrank_eq_dim, Nat.cast_ofNat]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  change 3 * (volume : Measure (Space 3)).real (basisLowerZonalCone3 b a) = _
  rw [basisLowerZonalCone3_volumeReal]
  have hstd := toSphere_lowerZonalCap3_real a
  rw [measureReal_def, Measure.toSphere_apply' _ (measurableSet_lowerZonalCap3 a),
    Ioo_smul_lowerZonalCap3 a] at hstd
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] at hstd
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hstd
  exact hstd

/-- The coordinate supplied by any orthonormal frame pushes physical-space spherical measure to
the same uniform height measure. -/
theorem map_basisLastCoordinate3_toSphere
    (b : OrthonormalBasis (Fin 3) ℝ (Space 3)) :
    Measure.map
        (fun n : Metric.sphere (0 : Space 3) 1 => basisLastCoordinate3 b n.1)
        (volume : Measure (Space 3)).toSphere = zonalHeightMeasure3 := by
  letI : IsFiniteMeasure zonalHeightMeasure3 := by
    constructor
    simp [zonalHeightMeasure3, Real.volume_Icc]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (by simp)) (by simp)
  apply Measure.ext_of_Iic
  intro a
  apply (measureReal_eq_measureReal_iff).mp
  have hmeas : Measurable
      (fun n : Metric.sphere (0 : Space 3) 1 => basisLastCoordinate3 b n.1) :=
    ((continuous_lastCoordinate3.comp b.repr.continuous).comp continuous_subtype_val).measurable
  rw [map_measureReal_apply hmeas measurableSet_Iic]
  change (volume : Measure (Space 3)).toSphere.real (basisLowerZonalCap3 b a) = _
  rw [toSphere_basisLowerZonalCap3_real, zonalHeightMeasure3_Iic_real]

theorem integral_comp_basisLastCoordinate3_toSphere_eq_intervalIntegral
    (b : OrthonormalBasis (Fin 3) ℝ (Space 3)) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (-1) 1) :
    (∫ n : Metric.sphere (0 : Space 3) 1,
        f (basisLastCoordinate3 b n.1) ∂(volume : Measure (Space 3)).toSphere) =
      2 * Real.pi * ∫ t in (-1 : ℝ)..1, f t := by
  have hfi : IntegrableOn f (Set.Icc (-1 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp hf
  have hmeas : AEStronglyMeasurable f zonalHeightMeasure3 := by
    rw [zonalHeightMeasure3]
    exact hfi.aestronglyMeasurable.smul_measure _
  have hmap : AEStronglyMeasurable f
      (Measure.map
        (fun n : Metric.sphere (0 : Space 3) 1 => basisLastCoordinate3 b n.1)
        (volume : Measure (Space 3)).toSphere) := by
    rw [map_basisLastCoordinate3_toSphere]
    exact hmeas
  have hcoordMeas : AEMeasurable
      (fun n : Metric.sphere (0 : Space 3) 1 => basisLastCoordinate3 b n.1)
      (volume : Measure (Space 3)).toSphere :=
    (((continuous_lastCoordinate3.comp b.repr.continuous).comp continuous_subtype_val).measurable
      |>.aemeasurable)
  have hchange :
      (∫ t : ℝ, f t ∂Measure.map
          (fun n : Metric.sphere (0 : Space 3) 1 => basisLastCoordinate3 b n.1)
          (volume : Measure (Space 3)).toSphere) =
        ∫ n : Metric.sphere (0 : Space 3) 1,
          f (basisLastCoordinate3 b n.1) ∂(volume : Measure (Space 3)).toSphere :=
    integral_map hcoordMeas hmap
  rw [← hchange,
    map_basisLastCoordinate3_toSphere, zonalHeightMeasure3, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi), smul_eq_mul]
  rw [← restrict_Ioc_eq_restrict_Icc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

/-- A unit vector in physical three-space can be chosen as the last vector of an orthonormal
frame. -/
lemma exists_orthonormalBasis_last_eq (axis : Space 3) (haxis : ‖axis‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ (Space 3), b (Fin.last 2) = axis := by
  let v : Fin 3 → Space 3 := fun _ => axis
  let s : Set (Fin 3) := {Fin.last 2}
  have hv : Orthonormal ℝ (s.restrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    change ‖axis‖ = 1
    exact haxis
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b, hb (Fin.last 2) (by simp [s])⟩

lemma basisLastCoordinate3_eq_inner
    (b : OrthonormalBasis (Fin 3) ℝ (Space 3)) (axis x : Space 3)
    (hb : b (Fin.last 2) = axis) :
    basisLastCoordinate3 b x = inner ℝ axis x := by
  rw [basisLastCoordinate3, lastCoordinate3, OrthonormalBasis.repr_apply_apply]
  change inner ℝ (b (Fin.last 2)) x = inner ℝ axis x
  rw [hb]

/-- Zonal integration on the physical unit sphere is independent of the selected unit axis. -/
theorem integral_comp_inner_unit_toSphere_eq_intervalIntegral
    (axis : Space 3) (haxis : ‖axis‖ = 1) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (-1) 1) :
    (∫ n : Metric.sphere (0 : Space 3) 1,
        f (inner ℝ axis n.1) ∂(volume : Measure (Space 3)).toSphere) =
      2 * Real.pi * ∫ t in (-1 : ℝ)..1, f t := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_last_eq axis haxis
  calc
    (∫ n : Metric.sphere (0 : Space 3) 1,
        f (inner ℝ axis n.1) ∂(volume : Measure (Space 3)).toSphere) =
        ∫ n : Metric.sphere (0 : Space 3) 1,
          f (basisLastCoordinate3 b n.1) ∂(volume : Measure (Space 3)).toSphere := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun n => by
        change f (inner ℝ axis n.1) = f (basisLastCoordinate3 b n.1)
        rw [basisLastCoordinate3_eq_inner b axis n.1 hb]
    _ = _ := integral_comp_basisLastCoordinate3_toSphere_eq_intervalIntegral b f hf

end Space

end
