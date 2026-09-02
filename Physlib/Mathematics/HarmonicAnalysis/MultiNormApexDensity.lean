/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTubeProximity

/-!
# Density and meet proximity for maximal multi-norm scales

This module completes the lattice-proximity content of Lemma 3.8(ii)--(iii)
in Hejna--Nagel--Ricci, *Littlewood-Paley square functions and the local Hardy
space for Multi-Norm Structures on R^d* (arXiv:2507.09399).

Every nonnegative point of the principal cone is uniformly close to a maximal
dyadic apex.  Moreover, the coordinatewise minimum of two maximal apices is
within `ℓ∞` distance one of another maximal apex.  The construction reuses the
canonical dotted-region partition and its unique maximal-apex theorem.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormDyadic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open MultiNormMarkedPartition

/-! ## 1. Rounding and the empty canonical region -/

/-- The canonical dotted set is nonempty: it is the range of the mark map of
the canonical marked partition. -/
lemma canonicalDottedSet_nonempty
    (E : StandardMultiNormMatrix ι) (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (canonicalDottedSet E t ht).Nonempty := by
  rw [canonicalDottedSet, minimalDottedSet]
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  exact ⟨(minimalMarkedPartition E t
    (admitsMarkedCone_of_nonnegative E t ht)).mark i, ⟨i, rfl⟩⟩

/-- The empty canonical dotted region consists exactly of the origin. -/
lemma mem_dottedRegion_empty_iff_eq_zero
    (E : StandardMultiNormMatrix ι) (t : ι → ℝ) :
    t ∈ dottedRegion E ∅ ↔ t = 0 := by
  constructor
  · rintro ⟨ht, hcase⟩
    rcases hcase with ⟨hzero, -⟩ | ⟨-, hcanonical⟩
    · exact hzero
    · have hne := canonicalDottedSet_nonempty E t ht
      rw [hcanonical] at hne
      exact (Set.not_nonempty_empty hne).elim
  · rintro rfl
    exact zero_mem_dottedRegion_empty E

/-- The origin is the maximal apex of the empty dotted region. -/
lemma zero_isMaximalDottedScale_empty (E : StandardMultiNormMatrix ι) :
    IsMaximalDottedScale E ∅ (0 : ι → ℕ) := by
  have hlog : toLogPoint (0 : ι → ℕ) = (0 : ι → ℝ) := by
    funext i
    change ((0 : ℕ) : ℝ) = 0
    norm_num
  refine ⟨hlog ▸ zero_mem_dottedRegion_empty E, ?_⟩
  intro j _hj hinc
  have hzero := (mem_dottedRegion_empty_iff_eq_zero E _).1 hinc
  have hj := congrFun hzero j
  simp [toLogPoint, increment] at hj

/-- Nearest-half-integer rounding places every nonnegative point in its
closed logarithmic unit cell. -/
lemma mem_logCell_nearestCellIndex {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i) :
    t ∈ logCell (nearestCellIndex t) := by
  intro i
  have hx : 0 ≤ t i + 1 / 2 := by linarith [ht i]
  have hfloor := Nat.floor_le hx
  have hnext := Nat.lt_floor_add_one (t i + 1 / 2)
  change ((nearestCellIndex t i : ℕ) : ℝ) ≤ t i + 1 / 2 at hfloor
  change t i + 1 / 2 < ((nearestCellIndex t i : ℕ) : ℝ) + 1 at hnext
  exact ⟨ht i, by linarith, by linarith⟩

/-! ## 2. Thickened cones and maximal lattice apices -/

/-- Coordinatewise minimum of two natural-valued scale vectors. -/
def scaleInf (L L' : ι → ℕ) : ι → ℕ := fun i => min (L i) (L' i)

/-- A common additive thickening of the principal cone is closed under
coordinatewise minimum, as used in the proof of Lemma 3.8(iii). -/
lemma thickenedPrincipalCone_scaleInf
    (E : StandardMultiNormMatrix ι) {δ : ℝ} {L L' : ι → ℕ}
    (hL : toLogPoint L ∈ thickenedPrincipalCone E δ)
    (hL' : toLogPoint L' ∈ thickenedPrincipalCone E δ) :
    toLogPoint (scaleInf L L') ∈ thickenedPrincipalCone E δ := by
  refine ⟨fun i => by simp [toLogPoint, scaleInf], ?_⟩
  intro i j
  have hiL : (scaleInf L L' i : ℝ) / E i j ≤ (L i : ℝ) / E i j := by
    apply (div_le_div_iff_of_pos_right (E.entry_pos _ _)).2
    exact_mod_cast min_le_left (L i) (L' i)
  have hiL' : (scaleInf L L' i : ℝ) / E i j ≤ (L' i : ℝ) / E i j := by
    apply (div_le_div_iff_of_pos_right (E.entry_pos _ _)).2
    exact_mod_cast min_le_right (L i) (L' i)
  calc
    (scaleInf L L' i : ℝ) / E i j ≤
        min ((L j : ℝ) + δ) ((L' j : ℝ) + δ) :=
      le_min (hiL.trans (hL.2 i j)) (hiL'.trans (hL'.2 i j))
    _ = (scaleInf L L' j : ℝ) + δ := by
      rw [min_add_add_right]
      congr 1
      exact_mod_cast rfl

/-- Any lattice point in `Γ_δ(E)` lies within `δ` of a maximal apex in its
canonical dotted region.  This includes the origin through the empty region. -/
lemma exists_maximalApex_near_thickenedLattice
    (E : StandardMultiNormMatrix ι) {δ : ℝ} (hδ : 0 ≤ δ)
    (M : ι → ℕ) (hM : toLogPoint M ∈ thickenedPrincipalCone E δ) :
    ∃ (D : Set ι) (L : ι → ℕ),
      IsMaximalDottedScale E D L ∧
      M ∈ tubeIndexSet D L ∧
      scaleSupDistance M L ≤ δ := by
  by_cases hzero : M = 0
  · subst M
    refine ⟨∅, 0, zero_isMaximalDottedScale_empty E,
      self_mem_tubeIndexSet ∅ 0, ?_⟩
    simpa [scaleSupDistance] using hδ
  · have hMnonneg : ∀ i, 0 ≤ toLogPoint M i := fun i => by simp [toLogPoint]
    let D := canonicalDottedSet E (toLogPoint M) hMnonneg
    have hD : D.Nonempty := canonicalDottedSet_nonempty E _ hMnonneg
    have hMD : toLogPoint M ∈ dottedRegion E D :=
      mem_dottedRegion_canonical E _ hMnonneg (by
        intro h
        apply hzero
        funext i
        have hi := congrFun h i
        change (M i : ℝ) = 0 at hi
        exact Nat.cast_eq_zero.mp hi)
    obtain ⟨L, hL, -⟩ := existsUnique_maximalApex E hD hMD
    refine ⟨D, L, hL.1, hL.2, ?_⟩
    obtain ⟨⟨S, hmarks, hLS⟩, -⟩ :=
      (mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus E hD _).1
        hL.1.1
    have hprofile := hasMaximalFloorProfile_of_isMaximalDottedScale E hD hL.1
      S hmarks hLS
    apply Finset.sup'_le
    intro i _hi
    have hML : M i ≤ L i := le_apex_of_mem_tubeIndexSet hL.2 i
    let k := S.mark i
    have hkD : k ∈ D := by
      rw [← hmarks]
      exact ⟨i, rfl⟩
    have hk : M k = L k := hL.2.1 k hkD
    have hLi : (L i : ℝ) ≤ (L k : ℝ) / E k i := by
      have hx : 0 ≤ (L k : ℝ) / E k i :=
        div_nonneg (by positivity) (E.entry_pos _ _).le
      have hfloor := Nat.floor_le hx
      change (floorCoordinate E S L i : ℝ) ≤ _ at hfloor
      simpa [k, hprofile i] using hfloor
    have hbound : (L i : ℝ) ≤ (M i : ℝ) + δ := by
      calc
        (L i : ℝ) ≤ (L k : ℝ) / E k i := hLi
        _ = (M k : ℝ) / E k i := by rw [hk]
        _ ≤ (M i : ℝ) + δ := hM.2 k i
    change |(M i : ℝ) - (L i : ℝ)| ≤ δ
    have hML' : (M i : ℝ) ≤ (L i : ℝ) := by exact_mod_cast hML
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩

/-! ## 3. Principal-cone density and meet proximity -/

/-- The `ℓ∞` distance from a real logarithmic point to a natural-valued
dyadic scale. -/
def pointScaleSupDistance (t : ι → ℝ) (L : ι → ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => |t i - (L i : ℝ)|)

/-- Rounding a principal-cone point produces a lattice point in a controlled
thickening.  The constant comes only from the half-cell error and the largest
reciprocal matrix entry. -/
lemma nearestCellIndex_mem_thickenedPrincipalCone
    (E : StandardMultiNormMatrix ι) {t : ι → ℝ}
    (ht : ∀ i, 0 ≤ t i) (hcone : E.InPrincipalCone t) :
    toLogPoint (nearestCellIndex t) ∈
      thickenedPrincipalCone E ((1 + maxReciprocalEntry E) / 2) := by
  have hcell := mem_logCell_nearestCellIndex (ι := ι) ht
  refine ⟨fun i => by simp [toLogPoint], ?_⟩
  intro i j
  have hiLower := (hcell i).2.1
  have hjUpper := (hcell j).2.2
  have hprincipal : t i / E i j ≤ t j := by
    rw [div_le_iff₀ (E.entry_pos i j)]
    simpa [mul_comm] using hcone i j
  have hinv := inv_entry_le_maxReciprocalEntry E i j
  change (nearestCellIndex t i : ℝ) / E i j ≤
    (nearestCellIndex t j : ℝ) + (1 + maxReciprocalEntry E) / 2
  calc
    (nearestCellIndex t i : ℝ) / E i j ≤
        (t i + 1 / 2) / E i j :=
      (div_le_div_iff_of_pos_right (E.entry_pos _ _)).2 (by linarith)
    _ = t i / E i j + (1 / 2) * (E i j)⁻¹ := by field_simp
    _ ≤ t j + (1 / 2) * maxReciprocalEntry E := by gcongr
    _ ≤ (nearestCellIndex t j : ℝ) +
        (1 + maxReciprocalEntry E) / 2 := by linarith

/-- Lemma 3.8(ii): every nonnegative point of the principal cone is within a
matrix-uniform `ℓ∞` distance of a maximal dyadic apex. -/
lemma exists_maximalApex_near_principalCone
    (E : StandardMultiNormMatrix ι) {t : ι → ℝ}
    (ht : ∀ i, 0 ≤ t i) (hcone : E.InPrincipalCone t) :
    ∃ (D : Set ι) (L : ι → ℕ),
      IsMaximalDottedScale E D L ∧
      pointScaleSupDistance t L ≤ 1 + maxReciprocalEntry E := by
  let M := nearestCellIndex t
  let δ := (1 + maxReciprocalEntry E) / 2
  have hinvNonneg : 0 ≤ maxReciprocalEntry E := by
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    exact (inv_pos.mpr (E.entry_pos i i)).le.trans
      (inv_entry_le_maxReciprocalEntry E i i)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hM : toLogPoint M ∈ thickenedPrincipalCone E δ :=
    nearestCellIndex_mem_thickenedPrincipalCone E ht hcone
  obtain ⟨D, L, hmax, hMtube, hdist⟩ :=
    exists_maximalApex_near_thickenedLattice E hδ M hM
  refine ⟨D, L, hmax, ?_⟩
  have hcell : t ∈ logCell M := by
    simpa [M] using (mem_logCell_nearestCellIndex (ι := ι) ht)
  apply Finset.sup'_le
  intro i _hi
  have hround : |t i - (M i : ℝ)| ≤ 1 / 2 := by
    have hlower : (M i : ℝ) - 1 / 2 ≤ t i := (hcell i).2.1
    have hupper : t i ≤ (M i : ℝ) + 1 / 2 := (hcell i).2.2
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hiScale : |(M i : ℝ) - (L i : ℝ)| ≤ δ :=
    (Finset.le_sup' (fun j => |(M j : ℝ) - (L j : ℝ)|)
      (Finset.mem_univ i)).trans hdist
  calc
    |t i - (L i : ℝ)| ≤
        |t i - (M i : ℝ)| + |(M i : ℝ) - (L i : ℝ)| := by
      simpa [sub_eq_add_neg, add_assoc] using
        abs_add_le (t i - (M i : ℝ)) ((M i : ℝ) - (L i : ℝ))
    _ ≤ 1 / 2 + δ := add_le_add hround hiScale
    _ ≤ 1 + maxReciprocalEntry E := by dsimp [δ]; linarith

/-- Lemma 3.8(iii): the coordinatewise minimum of two maximal apices is
within `ℓ∞` distance one of a maximal apex. -/
lemma exists_maximalApex_near_scaleInf
    (E : StandardMultiNormMatrix ι)
    {D D' : Set ι} (hD : D.Nonempty) (hD' : D'.Nonempty)
    {L L' : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (hmax' : IsMaximalDottedScale E D' L') :
    ∃ (D'' : Set ι) (A : ι → ℕ),
      IsMaximalDottedScale E D'' A ∧
      scaleSupDistance (scaleInf L L') A ≤ 1 := by
  have hL := maximalScale_mem_thickenedPrincipalCone_one E hD hmax
  have hL' := maximalScale_mem_thickenedPrincipalCone_one E hD' hmax'
  have hinf := thickenedPrincipalCone_scaleInf E hL hL'
  obtain ⟨D'', A, hA, _hMA, hdist⟩ :=
    exists_maximalApex_near_thickenedLattice E zero_le_one (scaleInf L L') hinf
  exact ⟨D'', A, hA, hdist⟩

/-- A maximal apex in the empty dotted region is the origin. -/
lemma apex_eq_zero_of_isMaximalDottedScale_empty
    (E : StandardMultiNormMatrix ι) {L : ι → ℕ}
    (hmax : IsMaximalDottedScale E ∅ L) :
    L = 0 := by
  have hlog : toLogPoint L = (0 : ι → ℝ) :=
    (mem_dottedRegion_empty_iff_eq_zero E _).1 hmax.1
  funext i
  have hi := congrFun hlog i
  change (L i : ℝ) = 0 at hi
  exact Nat.cast_eq_zero.mp hi

/-- Lemma 3.8(iii), including the empty-region origin boundary case: the
coordinatewise minimum of any two maximal apices is within distance one of a
maximal apex. -/
lemma exists_maximalApex_near_scaleInf_general
    (E : StandardMultiNormMatrix ι)
    {D D' : Set ι} {L L' : ι → ℕ}
    (hmax : IsMaximalDottedScale E D L)
    (hmax' : IsMaximalDottedScale E D' L') :
    ∃ (D'' : Set ι) (A : ι → ℕ),
      IsMaximalDottedScale E D'' A ∧
      scaleSupDistance (scaleInf L L') A ≤ 1 := by
  by_cases hD : D.Nonempty
  · by_cases hD' : D'.Nonempty
    · exact exists_maximalApex_near_scaleInf E hD hD' hmax hmax'
    · have hD'eq : D' = ∅ := Set.not_nonempty_iff_eq_empty.mp hD'
      subst D'
      have hL' : L' = 0 := apex_eq_zero_of_isMaximalDottedScale_empty E hmax'
      subst L'
      refine ⟨∅, 0, zero_isMaximalDottedScale_empty E, ?_⟩
      simp [scaleSupDistance, scaleInf]
  · have hDeq : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hD
    subst D
    have hL : L = 0 := apex_eq_zero_of_isMaximalDottedScale_empty E hmax
    subst L
    refine ⟨∅, 0, zero_isMaximalDottedScale_empty E, ?_⟩
    simp [scaleSupDistance, scaleInf]

/-- Capstone completing the density and meet-proximity parts of Lemma 3.8. -/
lemma principalCone_density_and_maximalMeet_proximity
    (E : StandardMultiNormMatrix ι) :
    (∀ t : ι → ℝ, (∀ i, 0 ≤ t i) → E.InPrincipalCone t →
      ∃ (D : Set ι) (L : ι → ℕ),
        IsMaximalDottedScale E D L ∧
        pointScaleSupDistance t L ≤ 1 + maxReciprocalEntry E) ∧
    (∀ (D D' : Set ι) (L L' : ι → ℕ), IsMaximalDottedScale E D L →
        IsMaximalDottedScale E D' L' →
        ∃ (D'' : Set ι) (A : ι → ℕ),
          IsMaximalDottedScale E D'' A ∧
          scaleSupDistance (scaleInf L L') A ≤ 1) := by
  exact ⟨fun _ ht hcone => exists_maximalApex_near_principalCone E ht hcone,
    fun _ _ _ _ hmax hmax' =>
      exists_maximalApex_near_scaleInf_general E hmax hmax'⟩

end MultiNormDyadic

end Physlib.Mathematics.HarmonicAnalysis
