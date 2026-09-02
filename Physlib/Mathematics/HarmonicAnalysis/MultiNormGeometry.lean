/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Finset
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Matrix.Reflection

/-!
# Standard matrices and multi-norm dilation geometry

This module formalizes the foundational geometry from A. Hejna, A. Nagel, and
F. Ricci, *Littlewood-Paley square functions and the local Hardy space for
Multi-Norm Structures on R^d* (arXiv:2507.09399), equations (2.3) and (2.5a).

A standard matrix determines two blockwise dilation families and their
physical- and frequency-space homogeneous gauges. The implementation permits
each coordinate block to be an arbitrary real normed space, so it covers the
paper's product decomposition without flattening its blocks into unrelated
scalar coordinates.

The principal results prove the dilation group laws, exact degree-one
homogeneity of both gauges, and the paper's observation that every physical
and frequency gauge has the same unit ball. This is the geometric substrate
for later multi-norm frequency cells; it does not construct the paper's marked
partitions, tube decomposition, smooth Littlewood--Paley families, Hardy
spaces, or atomic decompositions.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.HarmonicAnalysis

/-! # A. Standard multi-norm matrices -/

/-- A positive matrix satisfying the paper's standard multi-norm conditions:
unit diagonal, multiplicative triangle inequality, and strict
nondegeneracy away from the diagonal. -/
structure StandardMultiNormMatrix (ι : Type*) [DecidableEq ι] where
  toMatrix : Matrix ι ι ℝ
  entry_pos : ∀ i j, 0 < toMatrix i j
  diagonal : ∀ i, toMatrix i i = 1
  multiplicative_triangle :
    ∀ i j k, toMatrix i k ≤ toMatrix i j * toMatrix j k
  strict_nondegenerate :
    ∀ {i j}, i ≠ j → 1 < toMatrix i j * toMatrix j i

namespace StandardMultiNormMatrix

instance {ι : Type*} [DecidableEq ι] :
    CoeFun (StandardMultiNormMatrix ι) (fun _ => ι → ι → ℝ) :=
  ⟨fun E => E.toMatrix⟩

/-- The first two standard-matrix conditions imply
`1 ≤ e(i,j)e(j,i)`; strict inequality is the additional nondegeneracy
condition when the indices differ. -/
lemma reciprocal_product_one_le {ι : Type*} [DecidableEq ι]
    (E : StandardMultiNormMatrix ι) (i j : ι) :
    1 ≤ E i j * E j i := by
  simpa [E.diagonal i] using E.multiplicative_triangle i j i

/-- The standard two-factor matrix with off-diagonal entries `a` and `b`.
Its only substantive compatibility condition is `1 < a*b`. -/
def twoFactor (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : 1 < a * b) : StandardMultiNormMatrix (Fin 2) where
  toMatrix := !![1, a; b, 1]
  entry_pos := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb]
  diagonal := by
    intro i
    fin_cases i <;> rfl
  multiplicative_triangle := by
    intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [Matrix.of_apply] <;>
      nlinarith [ha, hb, hab]
  strict_nondegenerate := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · simp at hij
    · exact hab
    · simpa [mul_comm] using hab
    · simp at hij

/-! # B. Physical and frequency dilation families -/

section Dilations

variable {ι : Type*} [DecidableEq ι]
variable {V : ι → Type*}
variable [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]

/-- The physical-space multi-norm dilation
`δ_t^i(x)_j = t^(1/e(i,j)) x_j`. -/
def physicalDilation (E : StandardMultiNormMatrix ι)
    (i : ι) (t : ℝ) (x : ∀ j, V j) : ∀ j, V j :=
  fun j => (t ^ (E i j)⁻¹) • x j

/-- The frequency-space multi-norm dilation
`δ̂_t^i(ξ)_j = t^(e(j,i)) ξ_j`. -/
def frequencyDilation (E : StandardMultiNormMatrix ι)
    (i : ι) (t : ℝ) (ξ : ∀ j, V j) : ∀ j, V j :=
  fun j => (t ^ E j i) • ξ j

@[simp] lemma physicalDilation_one (E : StandardMultiNormMatrix ι)
    (i : ι) (x : ∀ j, V j) :
    E.physicalDilation i 1 x = x := by
  funext j
  simp [physicalDilation]

@[simp] lemma frequencyDilation_one (E : StandardMultiNormMatrix ι)
    (i : ι) (ξ : ∀ j, V j) :
    E.frequencyDilation i 1 ξ = ξ := by
  funext j
  simp [frequencyDilation]

/-- Nonnegative physical dilation parameters compose multiplicatively. -/
lemma physicalDilation_mul (E : StandardMultiNormMatrix ι)
    (i : ι) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (x : ∀ j, V j) :
    E.physicalDilation i (s * t) x =
      E.physicalDilation i s (E.physicalDilation i t x) := by
  funext j
  simp only [physicalDilation, smul_smul]
  rw [Real.mul_rpow hs ht]

/-- Nonnegative frequency dilation parameters compose multiplicatively. -/
lemma frequencyDilation_mul (E : StandardMultiNormMatrix ι)
    (i : ι) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (ξ : ∀ j, V j) :
    E.frequencyDilation i (s * t) ξ =
      E.frequencyDilation i s (E.frequencyDilation i t ξ) := by
  funext j
  simp only [frequencyDilation, smul_smul]
  rw [Real.mul_rpow hs ht]

end Dilations

/-! # C. Homogeneous physical and frequency gauges -/

section Gauges

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*}
variable [∀ j, NormedAddCommGroup (V j)]

/-- The physical multi-norm gauge
`N_i(x) = max_j ‖x_j‖^(e(i,j))`. -/
def physicalGauge (E : StandardMultiNormMatrix ι)
    (i : ι) (x : ∀ j, V j) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun j => ‖x j‖ ^ E i j)

/-- The frequency multi-norm gauge
`N̂_i(ξ) = max_j ‖ξ_j‖^(1/e(j,i))`. -/
def frequencyGauge (E : StandardMultiNormMatrix ι)
    (i : ι) (ξ : ∀ j, V j) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun j => ‖ξ j‖ ^ (E j i)⁻¹)

/-- Every physical gauge has the common blockwise unit ball. -/
lemma physicalGauge_le_one_iff (E : StandardMultiNormMatrix ι)
    (i : ι) (x : ∀ j, V j) :
    E.physicalGauge i x ≤ 1 ↔ ∀ j, ‖x j‖ ≤ 1 := by
  unfold physicalGauge
  rw [Finset.sup'_le_iff]
  constructor
  · intro h j
    by_contra hj
    have hnorm : 1 < ‖x j‖ := lt_of_not_ge hj
    have hrpow : 1 < ‖x j‖ ^ E i j :=
      Real.one_lt_rpow hnorm (E.entry_pos i j)
    exact (not_lt_of_ge (h j (Finset.mem_univ j))) hrpow
  · intro h j hj
    exact Real.rpow_le_one (norm_nonneg _) (h j)
      (E.entry_pos i j).le

/-- Every frequency gauge has the common blockwise unit ball. -/
lemma frequencyGauge_le_one_iff (E : StandardMultiNormMatrix ι)
    (i : ι) (ξ : ∀ j, V j) :
    E.frequencyGauge i ξ ≤ 1 ↔ ∀ j, ‖ξ j‖ ≤ 1 := by
  unfold frequencyGauge
  rw [Finset.sup'_le_iff]
  constructor
  · intro h j
    by_contra hj
    have hnorm : 1 < ‖ξ j‖ := lt_of_not_ge hj
    have hexp : 0 < (E j i)⁻¹ := inv_pos.mpr (E.entry_pos j i)
    have hrpow : 1 < ‖ξ j‖ ^ (E j i)⁻¹ :=
      Real.one_lt_rpow hnorm hexp
    exact (not_lt_of_ge (h j (Finset.mem_univ j))) hrpow
  · intro h j hj
    exact Real.rpow_le_one (norm_nonneg _) (h j)
      (inv_pos.mpr (E.entry_pos j i)).le

lemma physicalGauge_unitBall_independent
    (E : StandardMultiNormMatrix ι) (i k : ι) (x : ∀ j, V j) :
    E.physicalGauge i x ≤ 1 ↔ E.physicalGauge k x ≤ 1 := by
  rw [E.physicalGauge_le_one_iff, E.physicalGauge_le_one_iff]

lemma frequencyGauge_unitBall_independent
    (E : StandardMultiNormMatrix ι) (i k : ι) (ξ : ∀ j, V j) :
    E.frequencyGauge i ξ ≤ 1 ↔ E.frequencyGauge k ξ ≤ 1 := by
  rw [E.frequencyGauge_le_one_iff, E.frequencyGauge_le_one_iff]

/-- Physical and frequency gauges share the same blockwise unit ball,
independently of the selected dilation families. -/
lemma physical_frequency_common_unitBall
    (E : StandardMultiNormMatrix ι) (i k : ι) (x : ∀ j, V j) :
    E.physicalGauge i x ≤ 1 ↔ E.frequencyGauge k x ≤ 1 := by
  rw [E.physicalGauge_le_one_iff, E.frequencyGauge_le_one_iff]

end Gauges

/-! # D. Degree-one gauge homogeneity -/

section Homogeneity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Type*}
variable [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]

/-- The physical gauge is homogeneous of degree one under its matching
physical dilation family. -/
lemma physicalGauge_dilation (E : StandardMultiNormMatrix ι)
    (i : ι) {t : ℝ} (ht : 0 < t) (x : ∀ j, V j) :
    E.physicalGauge i (E.physicalDilation i t x) =
      t * E.physicalGauge i x := by
  unfold physicalGauge
  rw [Finset.mul₀_sup' ht.le _ Finset.univ Finset.univ_nonempty]
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro j hj
  simp only [physicalDilation, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht _)]
  rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) (norm_nonneg _),
    ← Real.rpow_mul ht.le,
    inv_mul_cancel₀ (E.entry_pos i j).ne', Real.rpow_one]

/-- The frequency gauge is homogeneous of degree one under its matching
frequency dilation family. -/
lemma frequencyGauge_dilation (E : StandardMultiNormMatrix ι)
    (i : ι) {t : ℝ} (ht : 0 < t) (ξ : ∀ j, V j) :
    E.frequencyGauge i (E.frequencyDilation i t ξ) =
      t * E.frequencyGauge i ξ := by
  unfold frequencyGauge
  rw [Finset.mul₀_sup' ht.le _ Finset.univ Finset.univ_nonempty]
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro j hj
  simp only [frequencyDilation, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht _)]
  rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) (norm_nonneg _),
    ← Real.rpow_mul ht.le,
    mul_inv_cancel₀ (E.entry_pos j i).ne', Real.rpow_one]

/-- Capstone for the paper's foundational multi-norm geometry: the standard
matrix product bound, both dilation laws, degree-one gauge homogeneity, and
the shared physical/frequency unit ball. -/
lemma standardMultiNorm_dilationGauge_geometry
    (E : StandardMultiNormMatrix ι) (i k : ι)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x ξ : ∀ j, V j) :
    1 ≤ E i k * E k i ∧
    E.physicalDilation i (s * t) x =
      E.physicalDilation i s (E.physicalDilation i t x) ∧
    E.frequencyDilation i (s * t) ξ =
      E.frequencyDilation i s (E.frequencyDilation i t ξ) ∧
    E.physicalGauge i (E.physicalDilation i t x) =
      t * E.physicalGauge i x ∧
    E.frequencyGauge i (E.frequencyDilation i t ξ) =
      t * E.frequencyGauge i ξ ∧
    (E.physicalGauge i x ≤ 1 ↔ E.frequencyGauge k x ≤ 1) := by
  exact ⟨E.reciprocal_product_one_le i k,
    E.physicalDilation_mul i hs.le ht.le x,
    E.frequencyDilation_mul i hs.le ht.le ξ,
    E.physicalGauge_dilation i ht x,
    E.frequencyGauge_dilation i ht ξ,
    E.physical_frequency_common_unitBall i k x⟩

end Homogeneity

end StandardMultiNormMatrix

end Physlib.Mathematics.HarmonicAnalysis
