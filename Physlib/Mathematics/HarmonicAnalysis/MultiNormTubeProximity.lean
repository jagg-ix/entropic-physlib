/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTubePartition
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormMaximalFloorCriterion

/-!
# Quantitative proximity and overlap bounds for multi-norm tubes

This module formalizes the discrete estimates behind Lemma 3.8(i) and (iv)
of Hejna--Nagel--Ricci, *Littlewood-Paley square functions and the local Hardy
space for Multi-Norm Structures on R^d* (arXiv:2507.09399).

The first result puts every maximal dyadic apex in the unit thickening of the
principal cone.  The second proves a uniform `ℓ∞` bound, depending only on the
standard matrix, for the apices of two intersecting maximal tubes.  The proof
reuses the exact tube boxes and the wall-robust maximal-floor criterion.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormDyadic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open MultiNormMarkedPartition

/-! ## 1. Maximal apices lie in a fixed thickening of the principal cone -/

/-- The paper's additive thickening
`Γ_δ(E) = {t : t_i / e(i,j) ≤ t_j + δ}` of the principal cone, including
the nonnegative-orthant condition. -/
def thickenedPrincipalCone (E : StandardMultiNormMatrix ι) (δ : ℝ) :
    Set (ι → ℝ) :=
  {t | (∀ i, 0 ≤ t i) ∧ ∀ i j, t i / E i j ≤ t j + δ}

/-- A maximal dyadic apex has weighted defect strictly less than one in
every ordered pair of coordinates.  This is the quantitative core of
Lemma 3.8(i). -/
lemma maximalScale_div_lt_add_one
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hmax : IsMaximalDottedScale E D L) (i j : ι) :
    (L i : ℝ) / E i j < (L j : ℝ) + 1 := by
  obtain ⟨⟨S, hmarks, hLS⟩, -⟩ :=
    (mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD _).1
      hmax.1
  have hprofile := hasMaximalFloorProfile_of_isMaximalDottedScale E hD hmax
    S hmarks hLS
  let p : S.MarkedIndex := ⟨S.mark i, ⟨i, rfl⟩⟩
  let q : S.MarkedIndex := ⟨S.mark j, ⟨j, rfl⟩⟩
  have hLi : (L i : ℝ) ≤ (L (S.mark i) : ℝ) / E (S.mark i) i := by
    have hx : 0 ≤ (L (S.mark i) : ℝ) / E (S.mark i) i :=
      div_nonneg (by positivity) (E.entry_pos _ _).le
    have hfloor := Nat.floor_le hx
    change (floorCoordinate E S L i : ℝ) ≤ _ at hfloor
    simpa [hprofile i] using hfloor
  have hLj : (L (S.mark j) : ℝ) / E (S.mark j) j < (L j : ℝ) + 1 := by
    have hfloor := Nat.lt_floor_add_one
      ((L (S.mark j) : ℝ) / E (S.mark j) j)
    change _ < (floorCoordinate E S L j : ℝ) + 1 at hfloor
    simpa [hprofile j] using hfloor
  have hpq : (L (S.mark i) : ℝ) ≤
      (E (S.mark i) j / E (S.mark j) j) * (L (S.mark j) : ℝ) := by
    calc
      (L (S.mark i) : ℝ) ≤ S.tau E p q * (L (S.mark j) : ℝ) :=
        S.cone_mark_le_tau_mul hLS p q
      _ ≤ (E (S.mark i) j / E (S.mark j) j) *
          (L (S.mark j) : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (S.tau_le_ratio E p q rfl) (by positivity)
  have hratio : E (S.mark i) j /
      (E (S.mark i) i * E i j) ≤ 1 := by
    exact (div_le_one (mul_pos (E.entry_pos _ _) (E.entry_pos _ _))).2
      (E.multiplicative_triangle (S.mark i) i j)
  have hcoeff :
      (E (S.mark i) j / E (S.mark j) j) /
          (E (S.mark i) i * E i j) ≤ 1 / E (S.mark j) j := by
    rw [show (E (S.mark i) j / E (S.mark j) j) /
          (E (S.mark i) i * E i j) =
        (E (S.mark i) j / (E (S.mark i) i * E i j)) /
          E (S.mark j) j by ring]
    exact (div_le_div_iff_of_pos_right (E.entry_pos _ _)).2 hratio
  have hmiddle : (L i : ℝ) / E i j ≤
      (L (S.mark j) : ℝ) / E (S.mark j) j := by
    calc
      (L i : ℝ) / E i j ≤
          ((L (S.mark i) : ℝ) / E (S.mark i) i) / E i j :=
        (div_le_div_iff_of_pos_right (E.entry_pos _ _)).2 hLi
      _ = (L (S.mark i) : ℝ) /
          (E (S.mark i) i * E i j) := by rw [div_div]
      _ ≤ ((E (S.mark i) j / E (S.mark j) j) *
          (L (S.mark j) : ℝ)) /
          (E (S.mark i) i * E i j) :=
        (div_le_div_iff_of_pos_right
          (mul_pos (E.entry_pos _ _) (E.entry_pos _ _))).2 hpq
      _ = ((E (S.mark i) j / E (S.mark j) j) /
          (E (S.mark i) i * E i j)) * (L (S.mark j) : ℝ) := by ring
      _ ≤ (1 / E (S.mark j) j) * (L (S.mark j) : ℝ) := by
        exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = (L (S.mark j) : ℝ) / E (S.mark j) j := by ring
  exact hmiddle.trans_lt hLj

/-- Every maximal apex lies in the unit additive thickening `Γ₁(E)`.
Unlike an existential metric statement, this records every coordinate defect
that later multiplier estimates need. -/
lemma maximalScale_mem_thickenedPrincipalCone_one
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hmax : IsMaximalDottedScale E D L) :
    toLogPoint L ∈ thickenedPrincipalCone E 1 := by
  refine ⟨fun i => by simp [toLogPoint], ?_⟩
  intro i j
  simpa [toLogPoint] using (maximalScale_div_lt_add_one E hD hmax i j).le

/-! ## 2. Intersecting maximal tubes have uniformly close apices -/

/-- The largest reciprocal matrix entry.  It is finite because the index
type is finite and positive because every standard-matrix entry is positive. -/
def maxReciprocalEntry (E : StandardMultiNormMatrix ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun ij : ι × ι => (E ij.1 ij.2)⁻¹)

/-- Every reciprocal entry is controlled by `maxReciprocalEntry`. -/
lemma inv_entry_le_maxReciprocalEntry
    (E : StandardMultiNormMatrix ι) (i j : ι) :
    (E i j)⁻¹ ≤ maxReciprocalEntry E := by
  exact Finset.le_sup' (fun ij : ι × ι => (E ij.1 ij.2)⁻¹)
    (Finset.mem_univ (i, j))

/-- Every coordinate of a tube point lies below its apex plus one half. -/
lemma le_apex_add_half_of_mem_logTube
    {D : Set ι} {L : ι → ℕ} {t : ι → ℝ}
    (ht : t ∈ logTube D L) (i : ι) :
    t i ≤ (L i : ℝ) + 1 / 2 := by
  rw [logTube_eq_logTubeBox, logTubeBox, Set.mem_pi] at ht
  have hti := ht i (Set.mem_univ i)
  by_cases hi : i ∈ D
  · rw [logTubeInterval, if_pos hi, Set.mem_Icc] at hti
    exact hti.2
  · rw [logTubeInterval, if_neg hi, Set.mem_Icc] at hti
    exact hti.2

/-- At a dotted coordinate, a tube point lies above the apex minus one half. -/
lemma apex_sub_half_le_of_mem_logTube
    {D : Set ι} {L : ι → ℕ} {t : ι → ℝ}
    (ht : t ∈ logTube D L) {i : ι} (hi : i ∈ D) :
    (L i : ℝ) - 1 / 2 ≤ t i := by
  rw [logTube_eq_logTubeBox, logTubeBox, Set.mem_pi] at ht
  have hti := ht i (Set.mem_univ i)
  rw [logTubeInterval, if_pos hi, Set.mem_Icc] at hti
  exact (le_max_right 0 ((L i : ℝ) - 1 / 2)).trans hti.1

/-- One-sided apex comparison for intersecting maximal tubes.  The marked
coordinate of the first apex is close to the common tube point, while the
unit thickening estimate transfers that control to the second apex. -/
lemma apex_lt_apex_add_overlapBound
    (E : StandardMultiNormMatrix ι)
    {D D' : Set ι} (hD : D.Nonempty) (hD' : D'.Nonempty)
    {L L' : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (hmax' : IsMaximalDottedScale E D' L')
    {t : ι → ℝ} (ht : t ∈ logTube D L) (ht' : t ∈ logTube D' L')
    (i : ι) :
    (L i : ℝ) < (L' i : ℝ) + 1 + maxReciprocalEntry E := by
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
  have hk : (L k : ℝ) ≤ (L' k : ℝ) + 1 := by
    have hlower := apex_sub_half_le_of_mem_logTube ht hkD
    have hupper := le_apex_add_half_of_mem_logTube ht' k
    linarith
  have htransfer := maximalScale_div_lt_add_one E hD' hmax' k i
  calc
    (L i : ℝ) ≤ (L k : ℝ) / E k i := hLi
    _ ≤ ((L' k : ℝ) + 1) / E k i :=
      (div_le_div_iff_of_pos_right (E.entry_pos _ _)).2 hk
    _ = (L' k : ℝ) / E k i + (E k i)⁻¹ := by
      rw [add_div, one_div]
    _ < (L' i : ℝ) + 1 + (E k i)⁻¹ := by linarith
    _ ≤ (L' i : ℝ) + 1 + maxReciprocalEntry E := by
      gcongr
      exact inv_entry_le_maxReciprocalEntry E k i

/-- Coordinatewise form of Lemma 3.8(iv): intersecting maximal tubes have
uniformly close apices. -/
lemma abs_apex_sub_apex_lt_of_logTube_inter
    (E : StandardMultiNormMatrix ι)
    {D D' : Set ι} (hD : D.Nonempty) (hD' : D'.Nonempty)
    {L L' : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (hmax' : IsMaximalDottedScale E D' L')
    {t : ι → ℝ} (ht : t ∈ logTube D L) (ht' : t ∈ logTube D' L')
    (i : ι) :
    |(L i : ℝ) - (L' i : ℝ)| < 1 + maxReciprocalEntry E := by
  rw [abs_lt]
  constructor
  · have h := apex_lt_apex_add_overlapBound E hD' hD hmax' hmax ht' ht i
    linarith
  · have h := apex_lt_apex_add_overlapBound E hD hD' hmax hmax' ht ht' i
    linarith

/-- The `ℓ∞` distance between two real-valued scale vectors. -/
def scaleSupDistance (L L' : ι → ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => |(L i : ℝ) - (L' i : ℝ)|)

/-- Lemma 3.8(iv), in its paper-level `ℓ∞` form: if two maximal logarithmic
tubes intersect, their apices are at distance at most a constant depending
only on `E`. -/
lemma scaleSupDistance_le_of_logTube_inter
    (E : StandardMultiNormMatrix ι)
    {D D' : Set ι} (hD : D.Nonempty) (hD' : D'.Nonempty)
    {L L' : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (hmax' : IsMaximalDottedScale E D' L')
    (hinter : (logTube D L ∩ logTube D' L').Nonempty) :
    scaleSupDistance L L' ≤ 1 + maxReciprocalEntry E := by
  obtain ⟨t, ht, ht'⟩ := hinter
  exact Finset.sup'_le _ _ fun i _ =>
    (abs_apex_sub_apex_lt_of_logTube_inter E hD hD' hmax hmax' ht ht' i).le

/-- Capstone for the two quantitative parts of Lemma 3.8 established here:
all maximal apices lie in `Γ₁(E)`, and intersecting maximal tubes have
matrix-uniformly bounded `ℓ∞` apex distance. -/
lemma maximalScale_proximity_and_intersectingTube_bound
    (E : StandardMultiNormMatrix ι) :
    (∀ (D : Set ι), D.Nonempty → ∀ L : ι → ℕ,
      IsMaximalDottedScale E D L →
        toLogPoint L ∈ thickenedPrincipalCone E 1) ∧
    (∀ (D D' : Set ι), D.Nonempty → D'.Nonempty →
      ∀ (L L' : ι → ℕ), IsMaximalDottedScale E D L →
        IsMaximalDottedScale E D' L' →
        (logTube D L ∩ logTube D' L').Nonempty →
          scaleSupDistance L L' ≤ 1 + maxReciprocalEntry E) := by
  exact ⟨fun _ hD _ hmax =>
      maximalScale_mem_thickenedPrincipalCone_one E hD hmax,
    fun _ _ hD hD' _ _ hmax hmax' hinter =>
      scaleSupDistance_le_of_logTube_inter E hD hD' hmax hmax' hinter⟩

end MultiNormDyadic

end Physlib.Mathematics.HarmonicAnalysis
