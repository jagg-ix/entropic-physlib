/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTubeColoring
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff

/-!
# Finite coloring of smooth multi-norm cutoff supports

The rough tube coloring cannot be applied unchanged after a smooth cutoff is
padded.  This module derives the enlarged overlap constant from the same
maximal-apex geometry, then constructs a new finite residue coloring whose
fibers have pairwise disjoint smooth supports.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormSmoothSupportColoring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
variable [∀ i, HasContDiffBump (V i)]

open MultiNormMarkedPartition MultiNormDyadic MultiNormSmoothCutoff

/-! ## 1. The padded overlap estimate -/

/-- Uniform apex bound for the half-scale padded smooth supports. -/
def paddedOverlapBound (E : StandardMultiNormMatrix ι) : ℝ :=
  1 + 2 * maxReciprocalEntry E

/-- One-sided apex comparison for a common point of two padded coordinate
shells. -/
lemma apex_lt_apex_add_paddedOverlapBound
    (E : StandardMultiNormMatrix ι)
    {D D' : Set ι} (hD : D.Nonempty) (hD' : D'.Nonempty)
    {L L' : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (hmax' : IsMaximalDottedScale E D' L')
    {ξ : ∀ i, V i} (hξ : ξ ∈ paddedCoordinateShell D L)
    (hξ' : ξ ∈ paddedCoordinateShell D' L') (i : ι) :
    (L i : ℝ) < (L' i : ℝ) + paddedOverlapBound E := by
  obtain ⟨⟨S, hmarks, hLS⟩, -⟩ :=
    (mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD _).1
      hmax.1
  have hprofile := hasMaximalFloorProfile_of_isMaximalDottedScale E hD hmax
    S hmarks hLS
  let k := S.mark i
  have hkD : k ∈ D := by
    rw [← hmarks]
    exact ⟨i, rfl⟩
  have hLi : (L i : ℝ) ≤ (L k : ℝ) / E k i := by
    have hx : 0 ≤ (L k : ℝ) / E k i :=
      div_nonneg (by positivity) (E.entry_pos _ _).le
    have hfloor := Nat.floor_le hx
    change (floorCoordinate E S L i : ℝ) ≤ _ at hfloor
    simpa [k, hprofile i] using hfloor
  have hpows :
      (2 : ℝ) ^ ((L k : ℝ) - 1) <
        (2 : ℝ) ^ ((L' k : ℝ) + 1) :=
    (hξ k).2 hkD |>.trans (hξ' k).1
  have hkexp : (L k : ℝ) - 1 < (L' k : ℝ) + 1 :=
    (Real.rpow_lt_rpow_left_iff (by norm_num)).1 hpows
  have hk : (L k : ℝ) < (L' k : ℝ) + 2 := by linarith
  have htransfer := maximalScale_div_lt_add_one E hD' hmax' k i
  calc
    (L i : ℝ) ≤ (L k : ℝ) / E k i := hLi
    _ < ((L' k : ℝ) + 2) / E k i :=
      (div_lt_div_iff_of_pos_right (E.entry_pos _ _)).2 hk
    _ = (L' k : ℝ) / E k i + 2 * (E k i)⁻¹ := by
      rw [add_div, div_eq_mul_inv]
      ring
    _ < (L' i : ℝ) + 1 + 2 * (E k i)⁻¹ := by linarith
    _ ≤ (L' i : ℝ) + paddedOverlapBound E := by
      unfold paddedOverlapBound
      have hinv := inv_entry_le_maxReciprocalEntry E k i
      linarith

lemma abs_apex_sub_apex_lt_of_paddedShell_inter
    (E : StandardMultiNormMatrix ι)
    {D D' : Set ι} (hD : D.Nonempty) (hD' : D'.Nonempty)
    {L L' : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (hmax' : IsMaximalDottedScale E D' L')
    {ξ : ∀ i, V i} (hξ : ξ ∈ paddedCoordinateShell D L)
    (hξ' : ξ ∈ paddedCoordinateShell D' L') (i : ι) :
    |(L i : ℝ) - (L' i : ℝ)| < paddedOverlapBound E := by
  rw [abs_lt]
  constructor
  · have h := apex_lt_apex_add_paddedOverlapBound
      E hD' hD hmax' hmax hξ' hξ i
    linarith
  · have h := apex_lt_apex_add_paddedOverlapBound
      E hD hD' hmax hmax' hξ hξ' i
    linarith

lemma scaleSupDistance_le_of_paddedShell_inter
    (E : StandardMultiNormMatrix ι)
    {D D' : Set ι} (hD : D.Nonempty) (hD' : D'.Nonempty)
    {L L' : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (hmax' : IsMaximalDottedScale E D' L')
    (hinter : (paddedCoordinateShell (V := V) D L ∩
      paddedCoordinateShell D' L').Nonempty) :
    scaleSupDistance L L' ≤ paddedOverlapBound E := by
  obtain ⟨ξ, hξ, hξ'⟩ := hinter
  exact Finset.sup'_le _ _ fun i _ =>
    (abs_apex_sub_apex_lt_of_paddedShell_inter
      E hD hD' hmax hmax' hξ hξ' i).le

/-! ## 2. A color adapted to the padded smooth supports -/

def smoothTubeColorModulus (E : StandardMultiNormMatrix ι) : ℕ :=
  ⌊paddedOverlapBound E⌋₊ + 1

lemma smoothTubeColorModulus_pos (E : StandardMultiNormMatrix ι) :
    0 < smoothTubeColorModulus E := by
  simp [smoothTubeColorModulus]

lemma paddedOverlapBound_lt_smoothTubeColorModulus
    (E : StandardMultiNormMatrix ι) :
    paddedOverlapBound E < (smoothTubeColorModulus E : ℝ) := by
  have hmax : 0 ≤ maxReciprocalEntry E := by
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    exact (inv_pos.mpr (E.entry_pos i i)).le.trans
      (inv_entry_le_maxReciprocalEntry E i i)
  have hnonneg : 0 ≤ paddedOverlapBound E := by
    unfold paddedOverlapBound
    linarith
  simpa [smoothTubeColorModulus] using
    Nat.lt_floor_add_one (paddedOverlapBound E)

abbrev SmoothTubeColor (E : StandardMultiNormMatrix ι) :=
  Finset ι × (ι → Fin (smoothTubeColorModulus E))

def smoothTubeColor (E : StandardMultiNormMatrix ι)
    (A : MaximalTubeIndex E) : SmoothTubeColor E :=
  (dottedFinset A.dotted, fun i =>
    ⟨A.apex i % smoothTubeColorModulus E,
      Nat.mod_lt _ (smoothTubeColorModulus_pos E)⟩)

lemma dotted_eq_of_smoothTubeColor_eq
    (E : StandardMultiNormMatrix ι) {A B : MaximalTubeIndex E}
    (hcolor : smoothTubeColor E A = smoothTubeColor E B) :
    A.dotted = B.dotted := by
  apply Set.ext
  intro i
  have hi := congrArg (fun c : SmoothTubeColor E => i ∈ c.1) hcolor
  simp only [smoothTubeColor, dottedFinset, Finset.mem_filter,
    Finset.mem_univ, true_and] at hi
  exact ⟨fun h => hi ▸ h, fun h => hi.symm ▸ h⟩

lemma apex_mod_eq_of_smoothTubeColor_eq
    (E : StandardMultiNormMatrix ι) {A B : MaximalTubeIndex E}
    (hcolor : smoothTubeColor E A = smoothTubeColor E B) (i : ι) :
    A.apex i % smoothTubeColorModulus E =
      B.apex i % smoothTubeColorModulus E := by
  have hfun := congrArg Prod.snd hcolor
  exact congrArg Fin.val (congrFun hfun i)

/-! ## 3. Proper coloring of the actual smooth supports -/

lemma eq_of_smoothTubeColor_eq_of_support_inter
    (E : StandardMultiNormMatrix ι) {A B : MaximalTubeIndex E}
    (hcolor : smoothTubeColor E A = smoothTubeColor E B)
    (hinter : (Function.support
        (smoothBlockCutoff (V := V) A.dotted A.apex) ∩
      Function.support
        (smoothBlockCutoff (V := V) B.dotted B.apex)).Nonempty) :
    A = B := by
  have hD : A.dotted = B.dotted := dotted_eq_of_smoothTubeColor_eq E hcolor
  have hpadded : (paddedCoordinateShell (V := V) A.dotted A.apex ∩
      paddedCoordinateShell B.dotted B.apex).Nonempty := by
    obtain ⟨ξ, hξA, hξB⟩ := hinter
    exact ⟨ξ,
      support_smoothBlockCutoff_subset_paddedCoordinateShell
        A.dotted A.apex hξA,
      support_smoothBlockCutoff_subset_paddedCoordinateShell
        B.dotted B.apex hξB⟩
  have hdist := scaleSupDistance_le_of_paddedShell_inter E
    A.dotted_nonempty B.dotted_nonempty A.maximal B.maximal hpadded
  have hL : A.apex = B.apex := by
    by_contra hne
    have hne' : ∃ i, A.apex i ≠ B.apex i := by
      by_contra h
      push Not at h
      exact hne (funext h)
    obtain ⟨i, hi⟩ := hne'
    have hgap := modulus_le_abs_cast_sub_of_mod_eq
      (smoothTubeColorModulus_pos E)
      (apex_mod_eq_of_smoothTubeColor_eq E hcolor i) hi
    have hcoord : |(A.apex i : ℝ) - (B.apex i : ℝ)| ≤
        paddedOverlapBound E :=
      (Finset.le_sup'
        (fun j => |(A.apex j : ℝ) - (B.apex j : ℝ)|)
        (Finset.mem_univ i)).trans hdist
    exact (not_lt_of_ge hgap)
      (hcoord.trans_lt (paddedOverlapBound_lt_smoothTubeColorModulus E))
  exact MaximalTubeIndex.ext hD hL

/-- Second smooth-multiplier capstone: every fiber of the constructed color
map has pairwise disjoint supports for the actual `C∞` cutoffs. -/
lemma smoothTubeColor_fiber_pairwiseDisjoint
    (E : StandardMultiNormMatrix ι) (c : SmoothTubeColor E) :
    ({A : MaximalTubeIndex E | smoothTubeColor E A = c} : Set _).PairwiseDisjoint
      (fun A => Function.support
        (smoothBlockCutoff (V := V) A.dotted A.apex)) := by
  intro A hAc B hBc hne
  change Disjoint
    (Function.support (smoothBlockCutoff (V := V) A.dotted A.apex))
    (Function.support (smoothBlockCutoff (V := V) B.dotted B.apex))
  rw [Set.disjoint_left]
  intro ξ hξA hξB
  apply hne
  apply eq_of_smoothTubeColor_eq_of_support_inter (V := V) E
  · exact hAc.trans hBc.symm
  · exact ⟨ξ, hξA, hξB⟩

end MultiNormSmoothSupportColoring

end Physlib.Mathematics.HarmonicAnalysis
