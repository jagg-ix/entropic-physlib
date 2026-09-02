/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover
public import Mathlib.Topology.PartitionOfUnity

/-!
# Local finiteness of the global smooth multi-norm family

This module upgrades the completed pointwise frequency cover to the
neighborhood-level local finiteness needed for genuine infinite partitions.
It reuses the maximal-apex geometry and the explicit padded support shell.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormGlobalLocalFiniteness

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
variable [∀ i, HasContDiffBump (V i)]

open MultiNormMarkedPartition MultiNormDyadic MultiNormSmoothCutoff
  MultiNormGlobalFrequencyCover

/-! ## 1. Finite bounded-apex families -/

def boundedMaximalTubeCode (E : StandardMultiNormMatrix ι) (B : ℕ)
    (A : {A : MaximalTubeIndex E // ∀ i, A.apex i ≤ B}) :
    Finset ι × (ι → Fin (B + 1)) :=
  (dottedFinset A.1.dotted, fun i =>
    ⟨A.1.apex i, Nat.lt_succ_of_le (A.2 i)⟩)

lemma boundedMaximalTubeCode_injective
    (E : StandardMultiNormMatrix ι) (B : ℕ) :
    Function.Injective (boundedMaximalTubeCode E B) := by
  intro A C hcode
  apply Subtype.ext
  apply MaximalTubeIndex.ext
  · apply Set.ext
    intro i
    have hi := congrArg (fun p : Finset ι × (ι → Fin (B + 1)) => i ∈ p.1) hcode
    simpa [boundedMaximalTubeCode, dottedFinset] using hi
  · funext i
    have hfun := congrArg Prod.snd hcode
    exact congrArg Fin.val (congrFun hfun i)

lemma finite_boundedMaximalTubeIndex
    (E : StandardMultiNormMatrix ι) (B : ℕ) :
    {A : MaximalTubeIndex E | ∀ i, A.apex i ≤ B}.Finite := by
  exact Set.finite_coe_iff.mp <|
    Finite.of_injective (boundedMaximalTubeCode E B)
      (boundedMaximalTubeCode_injective E B)

/-! ## 2. A dotted apex controls every apex coordinate -/

lemma exists_dotted_apex_control
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hmax : IsMaximalDottedScale E D L) (i : ι) :
    ∃ k ∈ D, (L i : ℝ) ≤ (L k : ℝ) / E k i := by
  obtain ⟨⟨S, hmarks, hLS⟩, -⟩ :=
    (mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD _).1
      hmax.1
  have hprofile := hasMaximalFloorProfile_of_isMaximalDottedScale E hD hmax
    S hmarks hLS
  refine ⟨S.mark i, ?_, ?_⟩
  · rw [← hmarks]
    exact ⟨i, rfl⟩
  · have hx : 0 ≤ (L (S.mark i) : ℝ) / E (S.mark i) i :=
      div_nonneg (by positivity) (E.entry_pos _ _).le
    have hfloor := Nat.floor_le hx
    change (floorCoordinate E S L i : ℝ) ≤ _ at hfloor
    simpa [hprofile i] using hfloor

/-! ## 3. Neighborhood-level local finiteness -/

lemma locallyFinite_maximalSmoothSupports
    (E : StandardMultiNormMatrix ι) :
    LocallyFinite (fun A : MaximalTubeIndex E =>
      Function.support
        (smoothBlockCutoff (V := V) A.dotted A.apex)) := by
  intro ξ
  obtain ⟨N, hN⟩ := exists_nat_gt ‖ξ‖
  let r : ℝ := (2 : ℝ) ^ (N : ℝ)
  let B : ℕ := ⌈((N + 1 : ℕ) : ℝ) * maxReciprocalEntry E⌉₊
  refine ⟨Metric.ball (0 : ∀ i, V i) r, ?_, ?_⟩
  · apply Metric.isOpen_ball.mem_nhds
    rw [Metric.mem_ball, dist_zero_right]
    have hcast : ‖ξ‖ < (N : ℝ) := hN
    have hpowNat : N < 2 ^ N := N.lt_two_pow_self
    have hpow : (N : ℝ) < (2 : ℝ) ^ N := by exact_mod_cast hpowNat
    simpa [r, Real.rpow_natCast] using hcast.trans hpow
  · apply (finite_boundedMaximalTubeIndex E B).subset
    intro A hA i
    obtain ⟨η, hηsupport, hηball⟩ := hA
    have hηshell :=
      support_smoothBlockCutoff_subset_paddedCoordinateShell
        (V := V) A.dotted A.apex hηsupport
    obtain ⟨k, hkD, hik⟩ := exists_dotted_apex_control
      E A.dotted_nonempty A.maximal i
    have hkLower : (2 : ℝ) ^ ((A.apex k : ℝ) - 1) < ‖η k‖ :=
      (hηshell k).2 hkD
    have hηnorm : ‖η‖ < r := by
      simpa [Metric.mem_ball, dist_zero_left] using hηball
    have hkUpper : ‖η k‖ < r :=
      (norm_le_pi_norm η k).trans_lt hηnorm
    have hkExp : (A.apex k : ℝ) - 1 < (N : ℝ) := by
      exact (Real.rpow_lt_rpow_left_iff (x := 2)
        (y := (A.apex k : ℝ) - 1) (z := (N : ℝ)) (by norm_num)).1 <|
          by simpa [r] using hkLower.trans hkUpper
    have hkBound : (A.apex k : ℝ) < ((N + 1 : ℕ) : ℝ) := by
      norm_num at hkExp ⊢
      linarith
    have hrecip := inv_entry_le_maxReciprocalEntry E k i
    have hnonneg : 0 ≤ (A.apex k : ℝ) := by positivity
    have hiReal : (A.apex i : ℝ) ≤
        ((N + 1 : ℕ) : ℝ) * maxReciprocalEntry E := by
      calc
        (A.apex i : ℝ) ≤ (A.apex k : ℝ) / E k i := hik
        _ = (A.apex k : ℝ) * (E k i)⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ (A.apex k : ℝ) * maxReciprocalEntry E :=
          mul_le_mul_of_nonneg_left hrecip hnonneg
        _ ≤ ((N + 1 : ℕ) : ℝ) * maxReciprocalEntry E := by
          have hmaxNonneg : 0 ≤ maxReciprocalEntry E :=
            (inv_pos.mpr (E.entry_pos k i)).le.trans hrecip
          exact mul_le_mul_of_nonneg_right hkBound.le hmaxNonneg
    exact_mod_cast hiReal.trans (Nat.le_ceil _)

/-- The low block adds one support to the locally finite maximal family. -/
lemma locallyFinite_fullSmoothSupports
    (E : StandardMultiNormMatrix ι) :
    LocallyFinite (fun A : FullTubeIndex E =>
      Function.support (fullSmoothCutoff (V := V) A)) := by
  rw [locallyFinite_option]
  exact locallyFinite_maximalSmoothSupports (V := V) E

lemma finite_fullSmoothCutoffsAt
    (E : StandardMultiNormMatrix ι) (ξ : ∀ i, V i) :
    {A : FullTubeIndex E | fullSmoothCutoff A ξ ≠ 0}.Finite := by
  exact (locallyFinite_fullSmoothSupports (V := V) E).point_finite ξ

/-- First global capstone: the completed smooth family covers every frequency
point and is genuinely locally finite in a neighborhood of every point. -/
lemma globalSmoothCover_locallyFinite
    (E : StandardMultiNormMatrix ι) :
    LocallyFinite (fun A : FullTubeIndex E =>
      Function.support (fullSmoothCutoff (V := V) A)) ∧
    ∀ ξ : (∀ i, V i), ∃ A : FullTubeIndex E,
      fullSmoothCutoff A ξ = 1 := by
  exact ⟨locallyFinite_fullSmoothSupports (V := V) E,
    fun ξ => (fullFrequencyCover_and_cutoff_one (V := V) E ξ).imp
      fun _ h => h.2⟩

end MultiNormGlobalLocalFiniteness

end Physlib.Mathematics.HarmonicAnalysis
