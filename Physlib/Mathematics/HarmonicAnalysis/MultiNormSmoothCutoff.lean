/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock

/-!
# Smooth cutoffs subordinate to multi-norm frequency blocks

This module constructs an actual `C∞` cutoff for every rough coordinate shell
already identified with a multi-norm frequency block.  It reuses Mathlib's
bundled `ContDiffBump` and the exact shell theorem from
`MultiNormFrequencyBlock`.

The cutoff equals one on the original block.  Its support is contained in the
shell obtained by enlarging every upper exponent from `Lᵢ + 1/2` to `Lᵢ + 1`
and every dotted lower exponent from `Lᵢ - 1/2` to `Lᵢ - 1`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Metric
open scoped ContDiff

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormSmoothCutoff

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
variable [∀ i, HasContDiffBump (V i)]

open MultiNormDyadic MultiNormFrequencyBlock

/-! ## 1. Coordinate bump functions -/

def upperCoreRadius (L : ι → ℕ) (i : ι) : ℝ :=
  (2 : ℝ) ^ ((L i : ℝ) + 1 / 2)

def upperSupportRadius (L : ι → ℕ) (i : ι) : ℝ :=
  (2 : ℝ) ^ ((L i : ℝ) + 1)

def lowerZeroRadius (L : ι → ℕ) (i : ι) : ℝ :=
  (2 : ℝ) ^ ((L i : ℝ) - 1)

def lowerCoreRadius (L : ι → ℕ) (i : ι) : ℝ :=
  (2 : ℝ) ^ ((L i : ℝ) - 1 / 2)

lemma upperCoreRadius_pos (L : ι → ℕ) (i : ι) :
    0 < upperCoreRadius L i := by
  exact Real.rpow_pos_of_pos (by norm_num) _

lemma upperCoreRadius_lt_support (L : ι → ℕ) (i : ι) :
    upperCoreRadius L i < upperSupportRadius L i := by
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  linarith

lemma lowerZeroRadius_pos (L : ι → ℕ) (i : ι) :
    0 < lowerZeroRadius L i := by
  exact Real.rpow_pos_of_pos (by norm_num) _

lemma lowerZeroRadius_lt_core (L : ι → ℕ) (i : ι) :
    lowerZeroRadius L i < lowerCoreRadius L i := by
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  linarith

/-- Upper coordinate bump: one on the original upper ball and supported in
the ball with exponent padded by another half unit. -/
def upperBump (L : ι → ℕ) (i : ι) : ContDiffBump (0 : V i) :=
  ⟨upperCoreRadius L i, upperSupportRadius L i,
    upperCoreRadius_pos L i, upperCoreRadius_lt_support L i⟩

/-- Inner bump used to cut a hole in every dotted coordinate. -/
def lowerHoleBump (L : ι → ℕ) (i : ι) : ContDiffBump (0 : V i) :=
  ⟨lowerZeroRadius L i, lowerCoreRadius L i,
    lowerZeroRadius_pos L i, lowerZeroRadius_lt_core L i⟩

/-- One smooth coordinate factor.  Dotted coordinates carry both an upper
cutoff and an inner hole; undotted coordinates carry only the upper cutoff. -/
def smoothShellFactor (D : Set ι) (L : ι → ℕ) (i : ι) (x : V i) : ℝ :=
  by
    classical
    exact upperBump (V := V) L i x *
      if i ∈ D then (1 - lowerHoleBump (V := V) L i x) else 1

/-- Product cutoff on the dependent product of coordinate spaces. -/
def smoothBlockCutoff (D : Set ι) (L : ι → ℕ) (ξ : ∀ i, V i) : ℝ :=
  ∏ i, smoothShellFactor D L i (ξ i)

/-! ## 2. Smoothness and range -/

lemma contDiff_smoothShellFactor (D : Set ι) (L : ι → ℕ) (i : ι) :
    ContDiff ℝ ∞ (fun ξ : (∀ i, V i) => smoothShellFactor D L i (ξ i)) := by
  classical
  have hproj : ContDiff ℝ ∞ (fun ξ : (∀ i, V i) => ξ i) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := V) i).contDiff
  have hu : ContDiff ℝ ∞ (fun ξ : (∀ i, V i) => upperBump (V := V) L i (ξ i)) :=
    ((upperBump (V := V) L i).contDiff (n := ⊤)).comp hproj
  by_cases hi : i ∈ D
  · have hl : ContDiff ℝ ∞ (fun ξ : (∀ i, V i) => lowerHoleBump (V := V) L i (ξ i)) :=
      ((lowerHoleBump (V := V) L i).contDiff (n := ⊤)).comp hproj
    simpa [smoothShellFactor, hi] using hu.mul (contDiff_const.sub hl)
  · simpa [smoothShellFactor, hi] using hu

lemma contDiff_smoothBlockCutoff (D : Set ι) (L : ι → ℕ) :
    ContDiff ℝ ∞ (smoothBlockCutoff (V := V) D L) := by
  unfold smoothBlockCutoff
  exact contDiff_prod fun i _ => contDiff_smoothShellFactor D L i

lemma smoothShellFactor_nonneg (D : Set ι) (L : ι → ℕ) (i : ι) (x : V i) :
    0 ≤ smoothShellFactor D L i x := by
  classical
  by_cases hi : i ∈ D
  · rw [smoothShellFactor, if_pos hi]
    exact mul_nonneg (upperBump (V := V) L i).nonneg
      (sub_nonneg.mpr (lowerHoleBump (V := V) L i).le_one)
  · simpa [smoothShellFactor, hi] using (upperBump (V := V) L i).nonneg

lemma smoothShellFactor_le_one (D : Set ι) (L : ι → ℕ) (i : ι) (x : V i) :
    smoothShellFactor D L i x ≤ 1 := by
  classical
  by_cases hi : i ∈ D
  · rw [smoothShellFactor, if_pos hi]
    exact mul_le_one₀ (upperBump (V := V) L i).le_one
      (sub_nonneg.mpr (lowerHoleBump (V := V) L i).le_one)
      (sub_le_self 1 (lowerHoleBump (V := V) L i).nonneg)
  · simpa [smoothShellFactor, hi] using (upperBump (V := V) L i).le_one

lemma smoothBlockCutoff_mem_Icc (D : Set ι) (L : ι → ℕ) (ξ : ∀ i, V i) :
    smoothBlockCutoff D L ξ ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg fun i _ => smoothShellFactor_nonneg D L i (ξ i)
  · exact Finset.prod_le_one
      (fun i _ => smoothShellFactor_nonneg D L i (ξ i))
      (fun i _ => smoothShellFactor_le_one D L i (ξ i))

/-! ## 3. Core equality and support control -/

/-- The explicitly padded open shell containing the support of the cutoff. -/
def paddedCoordinateShell (D : Set ι) (L : ι → ℕ) : Set (∀ i, V i) :=
  {ξ | ∀ i,
    ‖ξ i‖ < upperSupportRadius L i ∧
      (i ∈ D → lowerZeroRadius L i < ‖ξ i‖)}

lemma smoothBlockCutoff_eq_one_of_mem_coordinateDyadicShell
    {D : Set ι} {L : ι → ℕ} {ξ : ∀ i, V i}
    (hξ : ξ ∈ coordinateDyadicShell D L) :
    smoothBlockCutoff D L ξ = 1 := by
  apply Finset.prod_eq_one
  intro i _hi
  have hu : upperBump (V := V) L i (ξ i) = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    simpa [Metric.mem_closedBall, upperBump, upperCoreRadius] using (hξ i).1
  by_cases hiD : i ∈ D
  · have hl : lowerHoleBump (V := V) L i (ξ i) = 0 := by
      apply ContDiffBump.zero_of_le_dist
      simpa [lowerHoleBump, lowerCoreRadius] using (hξ i).2 hiD
    simp [smoothShellFactor, hiD, hu, hl]
  · simp [smoothShellFactor, hiD, hu]

lemma support_smoothBlockCutoff_subset_paddedCoordinateShell
    (D : Set ι) (L : ι → ℕ) :
    Function.support (smoothBlockCutoff (V := V) D L) ⊆
      paddedCoordinateShell D L := by
  intro ξ hξ i
  have hfactor : smoothShellFactor D L i (ξ i) ≠ 0 := by
    apply (Finset.prod_ne_zero_iff.mp hξ) i
    exact Finset.mem_univ i
  have hu : upperBump (V := V) L i (ξ i) ≠ 0 := by
    intro hz
    simp [smoothShellFactor, hz] at hfactor
  have huSupport : ξ i ∈ Function.support (upperBump (V := V) L i) := hu
  have huBall : ξ i ∈ Metric.ball (0 : V i) (upperSupportRadius L i) := by
    rw [(upperBump (V := V) L i).support_eq] at huSupport
    simpa [upperBump] using huSupport
  refine ⟨by simpa [Metric.mem_ball] using huBall, ?_⟩
  intro hiD
  by_contra hnot
  have hle : ‖ξ i‖ ≤ lowerZeroRadius L i := le_of_not_gt hnot
  have hl : lowerHoleBump (V := V) L i (ξ i) = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    simpa [Metric.mem_closedBall, lowerHoleBump] using hle
  simp [smoothShellFactor, hiD, hl] at hfactor

/-- First smooth-multiplier capstone: the constructed cutoff is `C∞`, takes
values in `[0,1]`, equals one on the existing exact frequency block, and is
supported in its explicit half-scale padding. -/
lemma smoothBlockCutoff_subordinate_frequencyBlock
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hmax : IsMaximalDottedScale E D L) :
    ContDiff ℝ ∞ (smoothBlockCutoff (V := V) D L) ∧
    (∀ ξ : (∀ i, V i), smoothBlockCutoff D L ξ ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ ξ : (∀ i, V i), ξ ∈ frequencyBlock (V := V) D L →
      smoothBlockCutoff D L ξ = 1) ∧
    Function.support (smoothBlockCutoff (V := V) D L) ⊆
      paddedCoordinateShell (V := V) D L := by
  exact ⟨contDiff_smoothBlockCutoff (V := V) D L,
    smoothBlockCutoff_mem_Icc (V := V) D L,
    fun ξ hξ => smoothBlockCutoff_eq_one_of_mem_coordinateDyadicShell (V := V)
      ((mem_frequencyBlock_iff_coordinateDyadicShell E hD hmax ξ).1 hξ),
    support_smoothBlockCutoff_subset_paddedCoordinateShell (V := V) D L⟩

end MultiNormSmoothCutoff

end Physlib.Mathematics.HarmonicAnalysis
