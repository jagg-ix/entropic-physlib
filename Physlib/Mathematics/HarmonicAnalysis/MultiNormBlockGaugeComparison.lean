/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock

/-!
# Block-gauge comparison for multi-norm frequency blocks

This module formalizes the valid block-gauge content behind Proposition 3.8.5
of Hejna--Nagel--Ricci.  A frequency block has an outer anisotropic gauge
bound at each active mark.  Conversely, coordinate-normalized block gauges,
together with the marked-coordinate annular lower bounds, imply membership in
the frequency block.

The reverse statement deliberately uses a floor-normalized gauge.  The
displayed proposition uses the same raw constant both for an anisotropic
upper bound and a marked-coordinate lower bound; on floor tie walls those two
requirements can conflict.  No such stronger boundary claim is made here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormBlockGaugeComparison

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]

open MultiNormMarkedPartition MultiNormDyadic MultiNormFrequencyBlock

/-! ## 1. Gauges on a marked block -/

/-- The physical multi-norm gauge restricted to the coordinates carried by
one active marked block. -/
def blockPhysicalGauge (E : StandardMultiNormMatrix ι)
    (S : MultiNormMarkedPartition ι) (k : S.MarkedIndex)
    (ξ : ∀ i, V i) : ℝ :=
  (S.blockFinset k.1).sup' (S.blockFinset_nonempty k)
    (fun i => ‖ξ i‖ ^ E k.1 i)

/-- The coordinate gauge normalized by the lattice floor scale in one marked
block.  Its unit ball is exactly the product of coordinate balls
`‖ξ_i‖ ≤ 2^(L_i)` on that block. -/
def floorNormalizedBlockGauge (S : MultiNormMarkedPartition ι)
    (L : ι → ℕ) (k : S.MarkedIndex) (ξ : ∀ i, V i) : ℝ :=
  (S.blockFinset k.1).sup' (S.blockFinset_nonempty k)
    (fun i => ‖ξ i‖ / (2 : ℝ) ^ (L i : ℝ))

/-- The finite comparison constant contributed by the half-width of the
dyadic shell in one marked block. -/
def blockGaugeConstant (E : StandardMultiNormMatrix ι)
    (S : MultiNormMarkedPartition ι) (k : S.MarkedIndex) : ℝ :=
  (S.blockFinset k.1).sup' (S.blockFinset_nonempty k)
    (fun i => (2 : ℝ) ^ (E k.1 i / 2))

/-- Every coordinate half-width factor is bounded by the block constant. -/
lemma halfWidth_le_blockGaugeConstant
    (E : StandardMultiNormMatrix ι) (S : MultiNormMarkedPartition ι)
    (k : S.MarkedIndex) {i : ι} (hi : S.mark i = k.1) :
    (2 : ℝ) ^ (E k.1 i / 2) ≤ blockGaugeConstant E S k := by
  exact Finset.le_sup'
    (fun j : ι => (2 : ℝ) ^ (E k.1 j / 2))
    ((S.mem_blockFinset_iff i k.1).2 hi)

/-! ## 2. The outer anisotropic estimate -/

/-- The floor equation bounds the exponentiated coordinate scale of every
coordinate in a marked block by the scale at its mark. -/
lemma exponent_mul_floorScale_le_markScale
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (S : MultiNormMarkedPartition ι) (hmarks : S.marks = D)
    (hLS : toLogPoint L ∈ S.cone E) (k : S.MarkedIndex)
    {i : ι} (hi : S.mark i = k.1) :
    E k.1 i * (L i : ℝ) ≤ L k.1 := by
  have hprofile :=
    hasMaximalFloorProfile_of_isMaximalDottedScale E hD hmax S hmarks hLS i
  have hnonneg : 0 ≤ (L k.1 : ℝ) / E k.1 i :=
    div_nonneg (by positivity) (E.entry_pos _ _).le
  have hfloor :
      (floorCoordinate E S L i : ℝ) ≤ (L k.1 : ℝ) / E k.1 i := by
    unfold floorCoordinate
    rw [hi]
    exact Nat.floor_le hnonneg
  calc
    E k.1 i * (L i : ℝ) = E k.1 i * floorCoordinate E S L i := by rw [hprofile]
    _ ≤ E k.1 i * ((L k.1 : ℝ) / E k.1 i) :=
      mul_le_mul_of_nonneg_left hfloor (E.entry_pos _ _).le
    _ = L k.1 := mul_div_cancel₀ _ (E.entry_pos k.1 i).ne'

/-- A coordinate upper shell bound yields the physical-gauge term required
by the marked-block comparison. -/
lemma coordinate_rpow_le_blockConstant_mul_scale
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (S : MultiNormMarkedPartition ι) (hmarks : S.marks = D)
    (hLS : toLogPoint L ∈ S.cone E) (k : S.MarkedIndex)
    {ξ : ∀ i, V i} {i : ι} (hi : S.mark i = k.1)
    (hupper : ‖ξ i‖ ≤ (2 : ℝ) ^ ((L i : ℝ) + 1 / 2)) :
    ‖ξ i‖ ^ E k.1 i ≤
      blockGaugeConstant E S k * (2 : ℝ) ^ (L k.1 : ℝ) := by
  have hscale := exponent_mul_floorScale_le_markScale
    E hD hmax S hmarks hLS k hi
  have hhalf := halfWidth_le_blockGaugeConstant E S k hi
  calc
    ‖ξ i‖ ^ E k.1 i
        ≤ ((2 : ℝ) ^ ((L i : ℝ) + 1 / 2)) ^ E k.1 i :=
      Real.rpow_le_rpow (norm_nonneg _) hupper (E.entry_pos _ _).le
    _ = (2 : ℝ) ^ (((L i : ℝ) + 1 / 2) * E k.1 i) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ (2 : ℝ) ^ ((L k.1 : ℝ) + E k.1 i / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith
    _ = (2 : ℝ) ^ (E k.1 i / 2) * (2 : ℝ) ^ (L k.1 : ℝ) := by
      rw [show (L k.1 : ℝ) + E k.1 i / 2 = E k.1 i / 2 + L k.1 by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ blockGaugeConstant E S k * (2 : ℝ) ^ (L k.1 : ℝ) :=
      mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg (by norm_num) _)

/-- Every exact frequency block satisfies the paper's reusable outer
anisotropic block-gauge estimate. -/
lemma blockPhysicalGauge_le_of_mem_frequencyBlock
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (S : MultiNormMarkedPartition ι) (hmarks : S.marks = D)
    (hLS : toLogPoint L ∈ S.cone E) {ξ : ∀ i, V i}
    (hξ : ξ ∈ frequencyBlock D L) (k : S.MarkedIndex) :
    blockPhysicalGauge E S k ξ ≤
      blockGaugeConstant E S k * (2 : ℝ) ^ (L k.1 : ℝ) := by
  rw [blockPhysicalGauge, Finset.sup'_le_iff]
  intro i hi
  exact coordinate_rpow_le_blockConstant_mul_scale E hD hmax S hmarks hLS k
    ((S.mem_blockFinset_iff i k.1).1 hi)
    ((mem_frequencyBlock_iff_coordinateDyadicShell E hD hmax ξ).1 hξ i).1

/-! ## 3. Correct floor-normalized reverse inclusion -/

/-- A normalized block-gauge unit bound gives the unpadded coordinate scale
bound on every coordinate in the marked block. -/
lemma norm_le_floorScale_of_floorNormalizedBlockGauge_le_one
    (S : MultiNormMarkedPartition ι) (L : ι → ℕ)
    (k : S.MarkedIndex) (ξ : ∀ i, V i)
    (h : floorNormalizedBlockGauge S L k ξ ≤ 1)
    {i : ι} (hi : S.mark i = k.1) :
    ‖ξ i‖ ≤ (2 : ℝ) ^ (L i : ℝ) := by
  have hterm : ‖ξ i‖ / (2 : ℝ) ^ (L i : ℝ) ≤ 1 :=
    (Finset.le_sup' _ ((S.mem_blockFinset_iff i k.1).2 hi)).trans h
  exact (div_le_one (Real.rpow_pos_of_pos (by norm_num) _)).1 hterm

/-- Corrected reverse inclusion: unit floor-normalized gauges on all marked
blocks, plus their annular lower bounds, place a frequency in `B_L`. -/
lemma mem_frequencyBlock_of_normalizedBlockGauges
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (S : MultiNormMarkedPartition ι) (hmarks : S.marks = D)
    (ξ : ∀ i, V i)
    (hgauge : ∀ k : S.MarkedIndex,
      floorNormalizedBlockGauge S L k ξ ≤ 1)
    (hlower : ∀ k : S.MarkedIndex,
      (2 : ℝ) ^ ((L k.1 : ℝ) - 1 / 2) ≤ ‖ξ k.1‖) :
    ξ ∈ frequencyBlock D L := by
  apply (mem_frequencyBlock_iff_coordinateDyadicShell E hD hmax ξ).2
  intro i
  let k : S.MarkedIndex := ⟨S.mark i, ⟨i, rfl⟩⟩
  have hbase : ‖ξ i‖ ≤ (2 : ℝ) ^ (L i : ℝ) :=
    norm_le_floorScale_of_floorNormalizedBlockGauge_le_one S L k ξ
      (hgauge k) rfl
  have hpad : (2 : ℝ) ^ (L i : ℝ) ≤
      (2 : ℝ) ^ ((L i : ℝ) + 1 / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  refine ⟨hbase.trans hpad, ?_⟩
  intro hiD
  exact hlower ⟨i, hmarks.symm ▸ hiD⟩

/-! ## 4. Two-sided capstone -/

/-- Target-two capstone: exact frequency blocks obey the physical outer
estimate, while the floor-normalized product criterion gives a valid inner
inclusion without a tie-wall assumption. -/
lemma frequencyBlock_blockGauge_comparison
    (E : StandardMultiNormMatrix ι) {D : Set ι} (hD : D.Nonempty)
    {L : ι → ℕ} (hmax : IsMaximalDottedScale E D L)
    (S : MultiNormMarkedPartition ι) (hmarks : S.marks = D)
    (hLS : toLogPoint L ∈ S.cone E) :
    (∀ (ξ : ∀ i, V i), ξ ∈ frequencyBlock D L →
      ∀ k : S.MarkedIndex,
        blockPhysicalGauge E S k ξ ≤
          blockGaugeConstant E S k * (2 : ℝ) ^ (L k.1 : ℝ)) ∧
    (∀ (ξ : ∀ i, V i),
      (∀ k : S.MarkedIndex, floorNormalizedBlockGauge S L k ξ ≤ 1) →
      (∀ k : S.MarkedIndex,
        (2 : ℝ) ^ ((L k.1 : ℝ) - 1 / 2) ≤ ‖ξ k.1‖) →
      ξ ∈ frequencyBlock D L) := by
  exact ⟨fun ξ hξ k =>
      blockPhysicalGauge_le_of_mem_frequencyBlock
        E hD hmax S hmarks hLS hξ k,
    fun ξ hgauge hlower =>
      mem_frequencyBlock_of_normalizedBlockGauges
        E hD hmax S hmarks ξ hgauge hlower⟩

end MultiNormBlockGaugeComparison

end Physlib.Mathematics.HarmonicAnalysis
