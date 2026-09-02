/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTubePartition

/-!
# Frequency-space blocks from multi-norm logarithmic tubes

This module transports the completed logarithmic tube decomposition to
frequency space.  The paper's map is implemented as
`π(ξ)_i = log₂(max 1, ‖ξ_i‖)`, its `log₂⁺` convention.  The basic block is
then exactly `B_L = π⁻¹(T_L)`.

For a maximal scale in a nonempty canonical region, block membership is
proved equivalent to the explicit dyadic coordinate shell: every coordinate
has its tube upper bound and every dotted coordinate has the corresponding
annular lower bound.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormFrequencyBlock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]

open MultiNormMarkedPartition MultiNormDyadic

/-! ## 1. The positive logarithmic frequency map -/

/-- The paper's positive binary logarithmic norm
`π(ξ)_i = log₂⁺ ‖ξ_i‖ = log₂(max 1, ‖ξ_i‖)`. -/
def positiveLog2Norm (ξ : ∀ i, V i) : ι → ℝ :=
  fun i => Real.logb 2 (max 1 ‖ξ i‖)

/-- The positive logarithmic norm is coordinatewise nonnegative. -/
lemma positiveLog2Norm_nonneg (ξ : ∀ i, V i) (i : ι) :
    0 ≤ positiveLog2Norm ξ i := by
  apply Real.logb_nonneg (by norm_num)
  exact le_max_left 1 ‖ξ i‖

/-- An upper logarithmic bound with nonnegative exponent is exactly the
corresponding dyadic norm bound. -/
lemma positiveLog2Norm_le_iff {ξ : ∀ i, V i} {i : ι} {a : ℝ}
    (ha : 0 ≤ a) :
    positiveLog2Norm ξ i ≤ a ↔ ‖ξ i‖ ≤ (2 : ℝ) ^ a := by
  have hmaxpos : 0 < max 1 ‖ξ i‖ := zero_lt_one.trans_le (le_max_left _ _)
  rw [positiveLog2Norm, Real.logb_le_iff_le_rpow (by norm_num) hmaxpos]
  constructor
  · exact fun h => (le_max_right 1 ‖ξ i‖).trans h
  · intro h
    exact max_le
      (Real.one_le_rpow (by norm_num) ha)
      h

/-- A strictly positive lower logarithmic bound is exactly the corresponding
dyadic lower norm bound. -/
lemma le_positiveLog2Norm_iff {ξ : ∀ i, V i} {i : ι} {a : ℝ}
    (ha : 0 < a) :
    a ≤ positiveLog2Norm ξ i ↔ (2 : ℝ) ^ a ≤ ‖ξ i‖ := by
  have hmaxpos : 0 < max 1 ‖ξ i‖ := zero_lt_one.trans_le (le_max_left _ _)
  rw [positiveLog2Norm, Real.le_logb_iff_rpow_le (by norm_num) hmaxpos]
  constructor
  · intro h
    rcases max_cases 1 ‖ξ i‖ with hmax | hmax
    · rw [hmax.1] at h
      exact ((not_lt_of_ge h) (Real.one_lt_rpow (by norm_num) ha)).elim
    · simpa [hmax.1] using h
  · exact fun h => h.trans (le_max_right 1 ‖ξ i‖)

/-! ## 2. Basic frequency blocks -/

/-- The basic multi-norm frequency block `B_L = π⁻¹(T_L)`. -/
def frequencyBlock (D : Set ι) (L : ι → ℕ) : Set (∀ i, V i) :=
  {ξ | positiveLog2Norm ξ ∈ logTube D L}

/-- The explicit coordinate dyadic shell associated with a dotted set and
lattice apex. -/
def coordinateDyadicShell (D : Set ι) (L : ι → ℕ) : Set (∀ i, V i) :=
  {ξ | ∀ i,
    ‖ξ i‖ ≤ (2 : ℝ) ^ ((L i : ℝ) + 1 / 2) ∧
      (i ∈ D → (2 : ℝ) ^ ((L i : ℝ) - 1 / 2) ≤ ‖ξ i‖)}

/-- Dotted coordinates of a maximal scale in a nonempty region are positive
natural scales. -/
lemma dottedScale_pos
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    {i : ι} (hi : i ∈ D) : 0 < L i := by
  have hstrict :=
    (mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD _).1
      hmax.1 |>.2 i hi |>.1
  simpa [toLogPoint] using hstrict

/-! ## 3. Exact coordinate characterization -/

/-- A maximal logarithmic tube pulls back exactly to the expected coordinate
dyadic shell in frequency space. -/
lemma mem_frequencyBlock_iff_coordinateDyadicShell
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (ξ : ∀ i, V i) :
    ξ ∈ frequencyBlock D L ↔ ξ ∈ coordinateDyadicShell D L := by
  rw [frequencyBlock, logTube_eq_logTubeBox, logTubeBox]
  change (∀ i ∈ Set.univ, positiveLog2Norm ξ i ∈ logTubeInterval D L i) ↔ _
  constructor
  · intro h i
    have hiBox := h i (Set.mem_univ i)
    by_cases hiD : i ∈ D
    · rw [logTubeInterval, if_pos hiD, Set.mem_Icc] at hiBox
      have hLi : (1 : ℕ) ≤ L i := dottedScale_pos E hD hmax hiD
      have hlowerPos : 0 < (L i : ℝ) - 1 / 2 := by
        have hLiR : (1 : ℝ) ≤ L i := by exact_mod_cast hLi
        linarith
      rw [max_eq_right hlowerPos.le] at hiBox
      exact ⟨(positiveLog2Norm_le_iff (by positivity)).1 hiBox.2,
        fun _ => (le_positiveLog2Norm_iff hlowerPos).1 hiBox.1⟩
    · rw [logTubeInterval, if_neg hiD, Set.mem_Icc] at hiBox
      exact ⟨(positiveLog2Norm_le_iff (by positivity)).1 hiBox.2,
        fun h => (hiD h).elim⟩
  · intro h i _
    by_cases hiD : i ∈ D
    · rw [logTubeInterval, if_pos hiD, Set.mem_Icc]
      have hLi : (1 : ℕ) ≤ L i := dottedScale_pos E hD hmax hiD
      have hlowerPos : 0 < (L i : ℝ) - 1 / 2 := by
        have hLiR : (1 : ℝ) ≤ L i := by exact_mod_cast hLi
        linarith
      rw [max_eq_right hlowerPos.le]
      exact ⟨(le_positiveLog2Norm_iff hlowerPos).2 ((h i).2 hiD),
        (positiveLog2Norm_le_iff (by positivity)).2 (h i).1⟩
    · rw [logTubeInterval, if_neg hiD, Set.mem_Icc]
      exact ⟨positiveLog2Norm_nonneg ξ i,
        (positiveLog2Norm_le_iff (by positivity)).2 (h i).1⟩

/-- Target-one capstone: `B_L = π⁻¹(T_L)` is exactly the explicit product of
dyadic balls in undotted coordinates and dyadic annuli in dotted coordinates. -/
lemma frequencyBlock_eq_coordinateDyadicShell
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hmax : IsMaximalDottedScale E D L) :
    frequencyBlock (V := V) D L = coordinateDyadicShell (V := V) D L := by
  ext ξ
  exact mem_frequencyBlock_iff_coordinateDyadicShell E hD hmax ξ

end MultiNormFrequencyBlock

end Physlib.Mathematics.HarmonicAnalysis
