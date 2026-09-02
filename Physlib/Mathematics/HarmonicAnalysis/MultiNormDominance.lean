/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGeometry

/-!
# Dominance and marked blocks for multi-norm geometry

This module formalizes the dominance mechanism underlying Section 3.1 of
A. Hejna, A. Nagel, and F. Ricci, *Littlewood-Paley square functions and the
local Hardy space for Multi-Norm Structures on R^d* (arXiv:2507.09399).

For logarithmic block sizes `t`, coordinate `k` dominates the `i`-th
frequency gauge when

`t j / e(j,i) ≤ t k / e(k,i)`

for every coordinate `j`. The standard-matrix triangle inequality implies
the paper's key transfer principle: if `k` dominates any gauge, then `k`
also dominates its own gauge. Strict dominants are unique.

An assignment choosing a strict dominant for every gauge is consequently
idempotent. Its fibers are therefore naturally marked by fixed points,
which supplies the algebraic substrate of the paper's marked partitions.
This module does not assert existence of strict dominants on singular
tie loci, construct the cones `Γ_S`, or construct dyadic frequency tubes.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

namespace StandardMultiNormMatrix

/-! # A. Logarithmic frequency gauges and dominance -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The logarithmic frequency gauge
`n̂_i(t) = max_j t_j / e(j,i)` used in the paper's dominance analysis. -/
def logFrequencyGauge (E : StandardMultiNormMatrix ι)
    (i : ι) (t : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => t j / E j i)

/-- Coordinate `k` is dominant in the `i`-th logarithmic frequency gauge
at `t` when its weighted coordinate is at least every other one. -/
def Dominates (E : StandardMultiNormMatrix ι)
    (k i : ι) (t : ι → ℝ) : Prop :=
  ∀ j, t j / E j i ≤ t k / E k i

/-- Coordinate `k` is strictly dominant in the `i`-th logarithmic frequency
gauge at `t` when every different coordinate has strictly smaller weight. -/
def StrictlyDominates (E : StandardMultiNormMatrix ι)
    (k i : ι) (t : ι → ℝ) : Prop :=
  ∀ ⦃j⦄, j ≠ k → t j / E j i < t k / E k i

omit [Fintype ι] [Nonempty ι] in
/-- Strict dominance implies dominance after allowing equality at the
dominant coordinate itself. -/
lemma StrictlyDominates.dominates
    (E : StandardMultiNormMatrix ι) {k i : ι} {t : ι → ℝ}
    (h : E.StrictlyDominates k i t) :
    E.Dominates k i t := by
  intro j
  by_cases hj : j = k
  · simp [hj]
  · exact (h hj).le

/-- A dominant coordinate realizes the logarithmic frequency gauge. -/
lemma logFrequencyGauge_eq_of_dominates
    (E : StandardMultiNormMatrix ι) {k i : ι} {t : ι → ℝ}
    (h : E.Dominates k i t) :
    E.logFrequencyGauge i t = t k / E k i := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun j _ => h j
  · exact Finset.le_sup' (fun j => t j / E j i)
      (Finset.mem_univ k)

/-- Realizing the logarithmic frequency gauge is equivalent to dominance. -/
lemma dominates_iff_logFrequencyGauge_eq
    (E : StandardMultiNormMatrix ι) {k i : ι} {t : ι → ℝ} :
    E.Dominates k i t ↔
      E.logFrequencyGauge i t = t k / E k i := by
  constructor
  · exact E.logFrequencyGauge_eq_of_dominates
  · intro h j
    exact (Finset.le_sup' (fun q => t q / E q i)
      (Finset.mem_univ j)).trans_eq h

/-! # B. The dominance-transfer principle -/

omit [Fintype ι] [Nonempty ι] in
/-- The matrix triangle inequality compares the weight used by gauge `i`
with the weight used by gauge `k`. -/
lemma weightedCoordinate_le_transfer
    (E : StandardMultiNormMatrix ι) {j k i : ι} {t : ι → ℝ}
    (ht : 0 ≤ t j) :
    t j / E j k ≤ (t j / E j i) * E k i := by
  rw [div_mul_eq_mul_div, div_le_div_iff₀
    (E.entry_pos j k) (E.entry_pos j i)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left
      (E.multiplicative_triangle j k i) ht

omit [Fintype ι] [Nonempty ι] in
/-- Paper Lemma 3.1(1), non-strict form: a coordinate dominant in any
logarithmic frequency gauge is also dominant in its own gauge. -/
lemma dominates_self_of_dominates
    (E : StandardMultiNormMatrix ι) {k i : ι} {t : ι → ℝ}
    (ht : ∀ j, 0 ≤ t j) (h : E.Dominates k i t) :
    E.Dominates k k t := by
  intro j
  calc
    t j / E j k ≤ (t j / E j i) * E k i :=
      E.weightedCoordinate_le_transfer (ht j)
    _ ≤ (t k / E k i) * E k i :=
      mul_le_mul_of_nonneg_right (h j) (E.entry_pos k i).le
    _ = t k / E k k := by
      rw [div_mul_cancel₀ _ (E.entry_pos k i).ne',
        E.diagonal, div_one]

omit [Fintype ι] [Nonempty ι] in
/-- Paper Lemma 3.1(1), strict form: strict dominance transfers to the
dominant coordinate's own logarithmic frequency gauge. -/
lemma strictlyDominates_self_of_strictlyDominates
    (E : StandardMultiNormMatrix ι) {k i : ι} {t : ι → ℝ}
    (ht : ∀ j, 0 ≤ t j) (h : E.StrictlyDominates k i t) :
    E.StrictlyDominates k k t := by
  intro j hj
  calc
    t j / E j k ≤ (t j / E j i) * E k i :=
      E.weightedCoordinate_le_transfer (ht j)
    _ < (t k / E k i) * E k i :=
      mul_lt_mul_of_pos_right (h hj) (E.entry_pos k i)
    _ = t k / E k k := by
      rw [div_mul_cancel₀ _ (E.entry_pos k i).ne',
        E.diagonal, div_one]

omit [Fintype ι] [Nonempty ι] in
/-- Two coordinates cannot both be strictly dominant in the same
logarithmic frequency gauge. -/
lemma strictlyDominant_unique
    (E : StandardMultiNormMatrix ι) {k l i : ι} {t : ι → ℝ}
    (hk : E.StrictlyDominates k i t)
    (hl : E.StrictlyDominates l i t) :
    k = l := by
  by_contra hkl
  have hlk : t l / E l i < t k / E k i := hk (Ne.symm hkl)
  have hkl' : t k / E k i < t l / E l i := hl hkl
  exact (not_lt_of_ge hlk.le) hkl'

/-! # C. Principal cone -/

/-- The principal standard-matrix cone
`Γ(E) = {t | t_i ≤ e(i,j)t_j for all i,j}`. -/
def InPrincipalCone (E : StandardMultiNormMatrix ι)
    (t : ι → ℝ) : Prop :=
  ∀ i j, t i ≤ E i j * t j

omit [Fintype ι] [Nonempty ι] in
/-- Membership in the principal cone is exactly diagonal dominance:
every coordinate dominates its matching logarithmic frequency gauge. -/
lemma inPrincipalCone_iff_diagonal_dominance
    (E : StandardMultiNormMatrix ι) (t : ι → ℝ) :
    E.InPrincipalCone t ↔ ∀ i, E.Dominates i i t := by
  constructor
  · intro h i j
    rw [E.diagonal, div_one]
    rw [div_le_iff₀ (E.entry_pos j i)]
    simpa [mul_comm] using h j i
  · intro h i j
    have hij := h j i
    rw [E.diagonal, div_one] at hij
    rw [div_le_iff₀ (E.entry_pos i j)] at hij
    simpa [mul_comm] using hij

/-! # D. Strict-dominance assignments and marked blocks -/

/-- A choice of one strict dominant coordinate for every logarithmic
frequency gauge. Its fibers model the blocks of a marked partition. -/
structure StrictDominanceAssignment
    (E : StandardMultiNormMatrix ι) (t : ι → ℝ) where
  owner : ι → ι
  owner_strictlyDominates :
    ∀ i, E.StrictlyDominates (owner i) i t

namespace StrictDominanceAssignment

/-- The block marked by `k` is the fiber of the dominant-coordinate
assignment over `k`. -/
def block {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (A : StrictDominanceAssignment E t) (k : ι) : Set ι :=
  {i | A.owner i = k}

omit [Fintype ι] [Nonempty ι] in
/-- Every chosen strict dominant is a fixed point of the owner map. This is
the algebraic reason its fibers carry canonical marked elements. -/
lemma owner_idempotent
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (A : StrictDominanceAssignment E t)
    (ht : ∀ j, 0 ≤ t j) (i : ι) :
    A.owner (A.owner i) = A.owner i := by
  exact E.strictlyDominant_unique
    (A.owner_strictlyDominates (A.owner i))
    (E.strictlyDominates_self_of_strictlyDominates
      ht (A.owner_strictlyDominates i))

omit [Fintype ι] [Nonempty ι] in
/-- The chosen mark of a gauge belongs to the block that it marks. -/
lemma owner_mem_block
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (A : StrictDominanceAssignment E t)
    (ht : ∀ j, 0 ≤ t j) (i : ι) :
    A.owner i ∈ A.block (A.owner i) :=
  A.owner_idempotent ht i

/-- Capstone for the marked-block substrate: every selected dominant realizes
its gauge, dominates its own gauge, and is an idempotent mark of its fiber. -/
lemma strictDominance_markedBlock_structure
    {E : StandardMultiNormMatrix ι} {t : ι → ℝ}
    (A : StrictDominanceAssignment E t)
    (ht : ∀ j, 0 ≤ t j) :
    ∀ i,
      E.logFrequencyGauge i t =
          t (A.owner i) / E (A.owner i) i ∧
      E.StrictlyDominates (A.owner i) (A.owner i) t ∧
      A.owner (A.owner i) = A.owner i ∧
      A.owner i ∈ A.block (A.owner i) := by
  intro i
  have hstrict := A.owner_strictlyDominates i
  exact ⟨E.logFrequencyGauge_eq_of_dominates hstrict.dominates,
    E.strictlyDominates_self_of_strictlyDominates ht hstrict,
    A.owner_idempotent ht i,
    A.owner_mem_block ht i⟩

end StrictDominanceAssignment

end StandardMultiNormMatrix

end Physlib.Mathematics.HarmonicAnalysis
