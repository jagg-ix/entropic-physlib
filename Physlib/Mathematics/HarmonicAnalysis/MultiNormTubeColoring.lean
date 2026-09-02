/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormApexDensity
public import Mathlib.Data.Fintype.BigOperators

/-!
# A canonical finite coloring of maximal multi-norm tubes

The overlap estimate from Lemma 3.8(iv) gives a coloring without an external
certificate.  A tube is colored by its dotted set and by every apex coordinate
modulo an integer strictly larger than the uniform overlap bound.  Two
intersecting tubes of the same color are therefore equal.

Consequently every color fiber is pairwise disjoint and only finitely many
maximal tubes can contain any fixed logarithmic point.  This is the finite
local-overlap mechanism needed before constructing smooth multiplier cells.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormDyadic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-! ## 1. Maximal-tube indices and their finite color type -/

/-- A maximal tube in a nonempty canonical dotted region. -/
structure MaximalTubeIndex (E : StandardMultiNormMatrix ι) where
  dotted : Set ι
  dotted_nonempty : dotted.Nonempty
  apex : ι → ℕ
  maximal : IsMaximalDottedScale E dotted apex

namespace MaximalTubeIndex

/-- The logarithmic tube represented by a maximal-tube index. -/
def tube {E : StandardMultiNormMatrix ι} (A : MaximalTubeIndex E) :
    Set (ι → ℝ) :=
  logTube A.dotted A.apex

@[ext] lemma ext {E : StandardMultiNormMatrix ι} {A B : MaximalTubeIndex E}
    (hD : A.dotted = B.dotted) (hL : A.apex = B.apex) : A = B := by
  cases A
  cases B
  simp_all

end MaximalTubeIndex

/-- One more than the natural floor of the real overlap bound. -/
def tubeColorModulus (E : StandardMultiNormMatrix ι) : ℕ :=
  ⌊1 + maxReciprocalEntry E⌋₊ + 1

lemma tubeColorModulus_pos (E : StandardMultiNormMatrix ι) :
    0 < tubeColorModulus E := by
  simp [tubeColorModulus]

/-- The real overlap bound is strictly smaller than the coloring modulus. -/
lemma overlapBound_lt_tubeColorModulus (E : StandardMultiNormMatrix ι) :
    1 + maxReciprocalEntry E < (tubeColorModulus E : ℝ) := by
  have hnonneg : 0 ≤ 1 + maxReciprocalEntry E := by
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    have hi : 0 ≤ maxReciprocalEntry E :=
      (inv_pos.mpr (E.entry_pos i i)).le.trans
        (inv_entry_le_maxReciprocalEntry E i i)
    linarith
  simpa [tubeColorModulus] using
    Nat.lt_floor_add_one (1 + maxReciprocalEntry E)

/-- Finite colors: the dotted subset and all coordinate residues. -/
abbrev TubeColor (E : StandardMultiNormMatrix ι) :=
  Finset ι × (ι → Fin (tubeColorModulus E))

/-- Convert a dotted subset into its finite characteristic set. -/
def dottedFinset (D : Set ι) : Finset ι :=
  by
    classical
    exact Finset.univ.filter fun i => i ∈ D

/-- The canonical residue color of a maximal tube. -/
def tubeColor (E : StandardMultiNormMatrix ι) (A : MaximalTubeIndex E) :
    TubeColor E :=
  (dottedFinset A.dotted, fun i =>
    ⟨A.apex i % tubeColorModulus E,
      Nat.mod_lt _ (tubeColorModulus_pos E)⟩)

/-! ## 2. Same-colored intersecting tubes coincide -/

/-- Distinct natural numbers with the same nonzero modulus differ in real
absolute value by at least that modulus. -/
lemma modulus_le_abs_cast_sub_of_mod_eq
    {a b N : ℕ} (_hN : 0 < N) (hmod : a % N = b % N) (hne : a ≠ b) :
    (N : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
  by_cases hab : a < b
  · have hdvd : N ∣ b - a :=
      (Nat.modEq_iff_dvd' hab.le).mp hmod
    have hgap : N ≤ b - a := Nat.le_of_dvd (Nat.sub_pos_of_lt hab) hdvd
    have hstep : a + N ≤ b := by omega
    have hstep' : (a : ℝ) + N ≤ b := by exact_mod_cast hstep
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hab.le))]
    linarith
  · have hba : b < a := by omega
    have hdvd : N ∣ a - b :=
      (Nat.modEq_iff_dvd' hba.le).mp hmod.symm
    have hgap : N ≤ a - b := Nat.le_of_dvd (Nat.sub_pos_of_lt hba) hdvd
    have hstep : b + N ≤ a := by omega
    have hstep' : (b : ℝ) + N ≤ a := by exact_mod_cast hstep
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hba.le))]
    linarith

/-- Equal colors determine equal dotted subsets. -/
lemma dotted_eq_of_tubeColor_eq
    (E : StandardMultiNormMatrix ι) {A B : MaximalTubeIndex E}
    (hcolor : tubeColor E A = tubeColor E B) :
    A.dotted = B.dotted := by
  apply Set.ext
  intro i
  have hi := congrArg (fun c : TubeColor E => i ∈ c.1) hcolor
  simp only [tubeColor, dottedFinset, Finset.mem_filter,
    Finset.mem_univ, true_and] at hi
  exact ⟨fun h => hi ▸ h, fun h => hi.symm ▸ h⟩

/-- Equal colors determine equal apex residues in every coordinate. -/
lemma apex_mod_eq_of_tubeColor_eq
    (E : StandardMultiNormMatrix ι) {A B : MaximalTubeIndex E}
    (hcolor : tubeColor E A = tubeColor E B) (i : ι) :
    A.apex i % tubeColorModulus E = B.apex i % tubeColorModulus E := by
  have hfun := congrArg Prod.snd hcolor
  exact congrArg Fin.val (congrFun hfun i)

/-- The canonical coloring is proper for tube intersection: two intersecting
maximal tubes carrying the same color are the same indexed tube. -/
lemma eq_of_tubeColor_eq_of_inter
    (E : StandardMultiNormMatrix ι) {A B : MaximalTubeIndex E}
    (hcolor : tubeColor E A = tubeColor E B)
    (hinter : (A.tube ∩ B.tube).Nonempty) :
    A = B := by
  have hD : A.dotted = B.dotted := dotted_eq_of_tubeColor_eq E hcolor
  have hdist := scaleSupDistance_le_of_logTube_inter E
    A.dotted_nonempty B.dotted_nonempty A.maximal B.maximal hinter
  have hL : A.apex = B.apex := by
    by_contra hne
    have hne' : ∃ i, A.apex i ≠ B.apex i := by
      by_contra h
      push Not at h
      exact hne (funext h)
    obtain ⟨i, hi⟩ := hne'
    have hgap := modulus_le_abs_cast_sub_of_mod_eq
      (tubeColorModulus_pos E) (apex_mod_eq_of_tubeColor_eq E hcolor i) hi
    have hcoord : |(A.apex i : ℝ) - (B.apex i : ℝ)| ≤
        1 + maxReciprocalEntry E :=
      (Finset.le_sup'
        (fun j => |(A.apex j : ℝ) - (B.apex j : ℝ)|)
        (Finset.mem_univ i)).trans hdist
    exact (not_lt_of_ge hgap)
      (hcoord.trans_lt (overlapBound_lt_tubeColorModulus E))
  exact MaximalTubeIndex.ext hD hL

/-! ## 3. Constructed color fibers and finite local overlap -/

/-- Every fiber of the canonical color map is a pairwise-disjoint family of
maximal logarithmic tubes. -/
lemma tubeColor_fiber_pairwiseDisjoint
    (E : StandardMultiNormMatrix ι) (c : TubeColor E) :
    ({A : MaximalTubeIndex E | tubeColor E A = c} : Set _).PairwiseDisjoint
      MaximalTubeIndex.tube := by
  intro A hAc B hBc hne
  change Disjoint A.tube B.tube
  rw [Set.disjoint_left]
  intro t htA htB
  apply hne
  apply eq_of_tubeColor_eq_of_inter E
  · exact hAc.trans hBc.symm
  · exact ⟨t, htA, htB⟩

/-- Maximal tubes containing a fixed logarithmic point, bundled as a type. -/
def TubesAtPoint (E : StandardMultiNormMatrix ι) (t : ι → ℝ) :=
  {A : MaximalTubeIndex E // t ∈ A.tube}

/-- The canonical color is injective on all maximal tubes containing a fixed
point. -/
lemma tubeColor_injective_atPoint
    (E : StandardMultiNormMatrix ι) (t : ι → ℝ) :
    Function.Injective
      (fun A : TubesAtPoint E t => tubeColor E A.1) := by
  intro A B hcolor
  apply Subtype.ext
  exact eq_of_tubeColor_eq_of_inter E hcolor ⟨t, A.2, B.2⟩

/-- Only finitely many maximal tubes contain any fixed logarithmic point. -/
lemma finite_tubesAtPoint
    (E : StandardMultiNormMatrix ι) (t : ι → ℝ) :
    Finite (TubesAtPoint E t) :=
  Finite.of_injective
    (fun A : TubesAtPoint E t => tubeColor E A.1)
    (tubeColor_injective_atPoint E t)

/-- Explicit local-overlap bound by the cardinality of the constructed finite
color type. -/
lemma natCard_tubesAtPoint_le_colorCard
    (E : StandardMultiNormMatrix ι) (t : ι → ℝ) :
    Nat.card (TubesAtPoint E t) ≤ Fintype.card (TubeColor E) := by
  letI : Finite (TubesAtPoint E t) := finite_tubesAtPoint E t
  simpa only [Nat.card_eq_fintype_card] using
    Nat.card_le_card_of_injective
      (fun A : TubesAtPoint E t => tubeColor E A.1)
      (tubeColor_injective_atPoint E t)

/-- Capstone: a matrix-determined finite coloring has disjoint fibers and
uniformly bounds the number of maximal tubes through every point. -/
lemma constructedTubeColoring_and_finiteLocalOverlap
    (E : StandardMultiNormMatrix ι) :
    (∀ c : TubeColor E,
      ({A : MaximalTubeIndex E | tubeColor E A = c} : Set _).PairwiseDisjoint
        MaximalTubeIndex.tube) ∧
    ∀ t : ι → ℝ,
      Finite (TubesAtPoint E t) ∧
      Nat.card (TubesAtPoint E t) ≤ Fintype.card (TubeColor E) := by
  exact ⟨tubeColor_fiber_pairwiseDisjoint E,
    fun t => ⟨finite_tubesAtPoint E t,
      natCard_tubesAtPoint_le_colorCard E t⟩⟩

end MultiNormDyadic

end Physlib.Mathematics.HarmonicAnalysis
