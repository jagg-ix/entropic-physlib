/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley

/-!
# Finite-overlap Euclidean Littlewood--Paley energy

This module extends the exact disjoint-cell result in
`EuclideanFiniteLittlewoodPaley` to a finite family admitting a spectral
coloring. Each color class consists of pairwise disjoint rough annuli, so the
previous exact Pythagorean theorem applies class by class. Regrouping the
finite sum by colors gives the bounded-overlap estimate

`∑ i, ‖P_i f‖² ≤ numberOfColors * ‖f‖²`.

The construction captures the finite-interaction principle used throughout
A. Hejna, A. Nagel, and F. Ricci, *Littlewood-Paley square functions and the
local Hardy space for Multi-Norm Structures on R^d* (arXiv:2507.09399), in
particular the bounded-neighbor support geometry surrounding Lemma 8.2.

The generic theorem accepts an explicit combinatorial certificate.  For the
standard dyadic radial annuli, however, the final section constructs the
certificate internally using parity of the scale index and exposes a
two-color Bessel theorem with no coloring premise.  This module does not claim
that the paper's smooth multi-norm multiplier cells have already been
constructed, nor does it prove an infinite square-function, `L¹`, Hardy-space,
Calderón-reproducing, or atomic-decomposition result.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform InnerProductSpace BigOperators

namespace Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley

open EuclideanL2FreeEvolution
open EuclideanSobolevFrequencyLocalization
open EuclideanFiniteLittlewoodPaley

/-! # A. Finite spectral colorings -/

/-- A finite spectral coloring: within each color fiber, the rough annular
frequency cells are pairwise disjoint. -/
def HasSpectralColoring {n : ℕ} {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (R : ι → ℝ) (color : ι → κ) : Prop :=
  ∀ a, SpectrallySeparated (n := n)
    (I.filter fun i => color i = a) R

/-- Every color fiber inherits the exact finite Pythagorean identity from the
disjoint-cell Littlewood--Paley layer. -/
lemma finiteOverlapLittlewoodPaley_coloredEnergy {n : ℕ}
    {ι κ : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (I : Finset ι) (R : ι → ℝ) (color : ι → κ)
    (hcolor : HasSpectralColoring (n := n) I R color)
    (f : EuclideanL2 n) :
    ∀ a : κ,
      ‖∑ i ∈ I.filter (fun i => color i = a),
          annularFrequencyProjection (R i) f‖ ^ 2 =
        ∑ i ∈ I.filter (fun i => color i = a),
          ‖annularFrequencyProjection (R i) f‖ ^ 2 := by
  intro a
  exact norm_sq_sum_annularFrequencyProjection
    (I.filter fun i => color i = a) R (hcolor a) f

/-! # B. Bounded-overlap square-sum estimate -/

/-- The finite rough Littlewood--Paley Bessel estimate with overlap controlled
by the number of spectral colors. -/
lemma finiteOverlapLittlewoodPaley_bessel {n : ℕ}
    {ι κ : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (I : Finset ι) (R : ι → ℝ) (color : ι → κ)
    (hcolor : HasSpectralColoring (n := n) I R color)
    (f : EuclideanL2 n) :
    ∑ i ∈ I, ‖annularFrequencyProjection (R i) f‖ ^ 2 ≤
      (Fintype.card κ : ℝ) * ‖f‖ ^ 2 := by
  rw [← Finset.sum_fiberwise I color
    (fun i => ‖annularFrequencyProjection (R i) f‖ ^ 2)]
  calc
    ∑ a : κ, ∑ i ∈ I with color i = a,
        ‖annularFrequencyProjection (R i) f‖ ^ 2 ≤
        ∑ _a : κ, ‖f‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact finiteLittlewoodPaley_bessel
        (I.filter fun i => color i = a) R (hcolor a) f
    _ = (Fintype.card κ : ℝ) * ‖f‖ ^ 2 := by
      simp

/-! # C. Capstone and free-flow covariance -/

/-- Capstone for finite-overlap rough frequency localization: exact energy in
every disjoint color fiber, a global Bessel estimate with the number of colors
as overlap constant, and covariance of every projection under free
Schrödinger evolution. -/
lemma finiteOverlapLittlewoodPaley_coloring_bessel {n : ℕ}
    {ι κ : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (I : Finset ι) (R : ι → ℝ) (color : ι → κ)
    (hcolor : HasSpectralColoring (n := n) I R color)
    (f : EuclideanL2 n) (t : ℝ) :
    (∀ a : κ,
      ‖∑ i ∈ I.filter (fun i => color i = a),
          annularFrequencyProjection (R i) f‖ ^ 2 =
        ∑ i ∈ I.filter (fun i => color i = a),
          ‖annularFrequencyProjection (R i) f‖ ^ 2) ∧
    ∑ i ∈ I, ‖annularFrequencyProjection (R i) f‖ ^ 2 ≤
      (Fintype.card κ : ℝ) * ‖f‖ ^ 2 ∧
    (∀ i ∈ I,
      annularFrequencyProjection (R i)
          (freeSchrodingerEvolution t f) =
        freeSchrodingerEvolution t
          (annularFrequencyProjection (R i) f)) := by
  exact ⟨finiteOverlapLittlewoodPaley_coloredEnergy
      I R color hcolor f,
    finiteOverlapLittlewoodPaley_bessel I R color hcolor f,
    fun i hi =>
      annularFrequencyProjection_commutes_evolution (R i) t f⟩

/-! # D. Constructed coloring for standard dyadic annuli -/

/-- The radius at dyadic scale `k`. -/
def dyadicAnnulusRadius (k : ℕ) : ℝ := (2 : ℝ) ^ k

/-- The parity color of a dyadic scale.  Two distinct scales of the same color
are separated by at least one intervening scale. -/
def dyadicAnnulusColor (k : ℕ) : Fin 2 :=
  ⟨k % 2, Nat.mod_lt _ (by omega)⟩

lemma dyadicAnnulusColor_mod_eq {a b : ℕ}
    (h : dyadicAnnulusColor a = dyadicAnnulusColor b) :
    a % 2 = b % 2 := by
  exact congrArg Fin.val h

/-- Distinct dyadic scales with the same parity have disjoint rough annuli. -/
lemma dyadicAnnulus_sameColor_disjoint {n a b : ℕ}
    (hcolor : dyadicAnnulusColor a = dyadicAnnulusColor b)
    (hab : a ≠ b) :
    Disjoint
      (frequencyAnnulus (n := n) (dyadicAnnulusRadius a))
      (frequencyAnnulus (n := n) (dyadicAnnulusRadius b)) := by
  have hmod := dyadicAnnulusColor_mod_eq hcolor
  by_cases hablt : a < b
  · have hstep : a + 1 ≤ b := by omega
    have hpow : (2 : ℝ) ^ (a + 1) ≤ (2 : ℝ) ^ b :=
      pow_le_pow_right₀ (by norm_num) hstep
    have hhalf : dyadicAnnulusRadius a ≤ dyadicAnnulusRadius b / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      simpa [dyadicAnnulusRadius, pow_succ] using hpow
    exact frequencyAnnulus_disjoint_of_le_half hhalf
  · have hbalt : b < a := by omega
    have hstep : b + 1 ≤ a := by omega
    have hpow : (2 : ℝ) ^ (b + 1) ≤ (2 : ℝ) ^ a :=
      pow_le_pow_right₀ (by norm_num) hstep
    have hhalf : dyadicAnnulusRadius b ≤ dyadicAnnulusRadius a / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      simpa [dyadicAnnulusRadius, pow_succ] using hpow
    exact (frequencyAnnulus_disjoint_of_le_half hhalf).symm

/-- Parity provides a spectral coloring for every finite family of standard
dyadic annuli; no external coloring certificate is required. -/
lemma hasSpectralColoring_dyadicAnnuli {n : ℕ} (I : Finset ℕ) :
    HasSpectralColoring (n := n) I dyadicAnnulusRadius dyadicAnnulusColor := by
  intro c
  unfold SpectrallySeparated
  intro a ha b hb hab
  change Disjoint
    (frequencyAnnulus (n := n) (dyadicAnnulusRadius a))
    (frequencyAnnulus (n := n) (dyadicAnnulusRadius b))
  apply dyadicAnnulus_sameColor_disjoint
  · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
  · exact hab

/-- Constructive two-color Littlewood--Paley capstone for standard dyadic
annuli.  Its statement contains no externally supplied coloring witness. -/
lemma finiteDyadicOverlapLittlewoodPaley_constructedColoring_bessel {n : ℕ}
    (I : Finset ℕ) (f : EuclideanL2 n) (t : ℝ) :
    (∀ a : Fin 2,
      ‖∑ i ∈ I.filter (fun i => dyadicAnnulusColor i = a),
          annularFrequencyProjection (dyadicAnnulusRadius i) f‖ ^ 2 =
        ∑ i ∈ I.filter (fun i => dyadicAnnulusColor i = a),
          ‖annularFrequencyProjection (dyadicAnnulusRadius i) f‖ ^ 2) ∧
    ∑ i ∈ I, ‖annularFrequencyProjection (dyadicAnnulusRadius i) f‖ ^ 2 ≤
      2 * ‖f‖ ^ 2 ∧
    (∀ i ∈ I,
      annularFrequencyProjection (dyadicAnnulusRadius i)
          (freeSchrodingerEvolution t f) =
        freeSchrodingerEvolution t
          (annularFrequencyProjection (dyadicAnnulusRadius i) f)) := by
  simpa using finiteOverlapLittlewoodPaley_coloring_bessel
    I dyadicAnnulusRadius dyadicAnnulusColor
      (hasSpectralColoring_dyadicAnnuli (n := n) I) f t

end Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley
