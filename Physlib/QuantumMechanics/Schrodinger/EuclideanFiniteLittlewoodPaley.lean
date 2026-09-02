/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization

/-!
# Finite Euclidean Littlewood--Paley orthogonality

This module supplies the finite `L²` orthogonality layer suggested by
A. Hejna, A. Nagel, and F. Ricci, *Littlewood-Paley square functions and the
local Hardy space for Multi-Norm Structures on R^d* (arXiv:2507.09399).

The paper uses smooth spectral projections supported near multi-norm frequency
cells and proves substantially stronger `L¹` square-function and local Hardy
space results. Here we reuse Physlib's existing rough annular projections and
formalize the exact disjoint-support precursor:

* separated annuli produce orthogonal Fourier cutoffs;
* Plancherel transfers that orthogonality to physical space;
* a finite separated family satisfies an exact Pythagorean identity;
* its square-sum satisfies the sharp `L²` Bessel bound;
* every member continues to commute with free Schrödinger evolution.

This does not formalize the paper's multi-norm exponent matrix, smooth
finite-overlap cells, `L¹` square-function equivalence, Calderón reproducing
formula, local `h¹_E` space, or atomic characterization.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter Topology MeasureTheory Set
open scoped FourierTransform ENNReal NNReal InnerProductSpace

namespace Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley

open EuclideanL2FreeEvolution
open EuclideanSobolevFrequencyLocalization

/-! # A. Separated rough frequency cells -/

/-- A sufficient radial separation condition for two rough frequency annuli
to be disjoint. -/
lemma frequencyAnnulus_disjoint_of_le_half {n : ℕ}
    {R S : ℝ} (hRS : R ≤ S / 2) :
    Disjoint
      (frequencyAnnulus (n := n) R)
      (frequencyAnnulus (n := n) S) := by
  rw [Set.disjoint_left]
  intro ξ hξR hξS
  exact (not_lt_of_ge hξS.1) (hξR.2.trans_le hRS)

/-- Fourier cutoffs on disjoint rough frequency cells are orthogonal in
frequency-space `L²`. -/
lemma inner_annularCutoff_eq_zero_of_disjoint {n : ℕ}
    {R S : ℝ}
    (hRS : Disjoint
      (frequencyAnnulus (n := n) R)
      (frequencyAnnulus (n := n) S))
    (g h : EuclideanL2 n) :
    ⟪annularCutoff R g, annularCutoff S h⟫_ℂ = 0 := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [
    annularCutoff_coeFn R g,
    annularCutoff_coeFn S h
  ] with ξ hR hS
  by_cases hξR : ξ ∈ frequencyAnnulus R
  · have hξS : ξ ∉ frequencyAnnulus S := by
      intro hmem
      exact Set.disjoint_left.1 hRS hξR hmem
    rw [hR, indicator_of_mem hξR, hS, indicator_of_notMem hξS]
    simp
  · rw [hR, indicator_of_notMem hξR]
    simp

/-! # B. Physical-space orthogonality through Plancherel -/

/-- Plancherel transfers disjoint Fourier support to orthogonality of the
physical-space annular projections. -/
lemma inner_annularFrequencyProjection_eq_zero_of_disjoint {n : ℕ}
    {R S : ℝ}
    (hRS : Disjoint
      (frequencyAnnulus (n := n) R)
      (frequencyAnnulus (n := n) S))
    (f g : EuclideanL2 n) :
    ⟪annularFrequencyProjection R f,
      annularFrequencyProjection S g⟫_ℂ = 0 := by
  rw [← MeasureTheory.Lp.inner_fourier_eq]
  simp only [annularFrequencyProjection,
    FourierInvPair.fourier_fourierInv_eq]
  exact inner_annularCutoff_eq_zero_of_disjoint hRS (𝓕 f) (𝓕 g)

/-- A rough Fourier cutoff is orthogonal to the part of its input lying
outside the cutoff cell. -/
lemma inner_annularCutoff_eq_inner_self {n : ℕ}
    (R : ℝ) (g : EuclideanL2 n) :
    ⟪annularCutoff R g, g⟫_ℂ =
      ⟪annularCutoff R g, annularCutoff R g⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [annularCutoff_coeFn R g] with ξ hcut
  by_cases hξ : ξ ∈ frequencyAnnulus R
  · rw [hcut, indicator_of_mem hξ]
  · rw [hcut, indicator_of_notMem hξ]
    simp

/-- The physical-space projection has the characteristic inner-product
identity of an orthogonal projection. -/
lemma inner_annularFrequencyProjection_eq_inner_self {n : ℕ}
    (R : ℝ) (f : EuclideanL2 n) :
    ⟪annularFrequencyProjection R f, f⟫_ℂ =
      ⟪annularFrequencyProjection R f,
        annularFrequencyProjection R f⟫_ℂ := by
  calc
    ⟪annularFrequencyProjection R f, f⟫_ℂ =
        ⟪𝓕 (annularFrequencyProjection R f), 𝓕 f⟫_ℂ := by
      symm
      exact MeasureTheory.Lp.inner_fourier_eq _ _
    _ = ⟪annularCutoff R (𝓕 f), 𝓕 f⟫_ℂ := by
      simp [annularFrequencyProjection]
    _ = ⟪annularCutoff R (𝓕 f), annularCutoff R (𝓕 f)⟫_ℂ :=
      inner_annularCutoff_eq_inner_self R (𝓕 f)
    _ = ⟪𝓕 (annularFrequencyProjection R f),
          𝓕 (annularFrequencyProjection R f)⟫_ℂ := by
      simp [annularFrequencyProjection]
    _ = ⟪annularFrequencyProjection R f,
          annularFrequencyProjection R f⟫_ℂ :=
      MeasureTheory.Lp.inner_fourier_eq _ _

/-! # C. Finite Littlewood--Paley energy -/

/-- A finite family of annular scales is spectrally separated when its rough
frequency cells are pairwise disjoint. -/
def SpectrallySeparated {n : ℕ} {ι : Type*}
    (I : Finset ι) (R : ι → ℝ) : Prop :=
  (I : Set ι).PairwiseDisjoint
    (fun i => frequencyAnnulus (n := n) (R i))

/-- Exact finite Pythagorean identity for separated annular projections. This
is the `L²` square-sum identity underlying the finite rough
Littlewood--Paley decomposition. -/
lemma norm_sq_sum_annularFrequencyProjection {n : ℕ}
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (R : ι → ℝ)
    (hI : SpectrallySeparated (n := n) I R)
    (f : EuclideanL2 n) :
    ‖∑ i ∈ I, annularFrequencyProjection (R i) f‖ ^ 2 =
      ∑ i ∈ I, ‖annularFrequencyProjection (R i) f‖ ^ 2 := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
      have htail : SpectrallySeparated (n := n) I R := by
        unfold SpectrallySeparated at hI ⊢
        intro i hi j hj hij
        exact hI (by simp [hi]) (by simp [hj]) hij
      have hinner :
          ⟪annularFrequencyProjection (R a) f,
            ∑ i ∈ I, annularFrequencyProjection (R i) f⟫_ℂ = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro i hi
        have hai : a ≠ i := by
          intro hai
          subst i
          exact ha hi
        unfold SpectrallySeparated at hI
        exact inner_annularFrequencyProjection_eq_zero_of_disjoint
          (hI (by simp) (by simp [hi]) hai) f f
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        ‖annularFrequencyProjection (R a) f +
            ∑ i ∈ I, annularFrequencyProjection (R i) f‖ ^ 2 =
            ‖annularFrequencyProjection (R a) f‖ ^ 2 +
              ‖∑ i ∈ I, annularFrequencyProjection (R i) f‖ ^ 2 := by
          simpa [pow_two] using
            norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
              (annularFrequencyProjection (R a) f)
              (∑ i ∈ I, annularFrequencyProjection (R i) f)
              hinner
        _ = ‖annularFrequencyProjection (R a) f‖ ^ 2 +
              ∑ i ∈ I, ‖annularFrequencyProjection (R i) f‖ ^ 2 := by
          rw [ih htail]

/-- The sum of finitely many separated annular projections is itself an
`L²` contraction. -/
lemma norm_sum_annularFrequencyProjection_le {n : ℕ}
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (R : ι → ℝ)
    (hI : SpectrallySeparated (n := n) I R)
    (f : EuclideanL2 n) :
    ‖∑ i ∈ I, annularFrequencyProjection (R i) f‖ ≤ ‖f‖ := by
  let q : EuclideanL2 n :=
    ∑ i ∈ I, annularFrequencyProjection (R i) f
  have hinner :
      ⟪q, f⟫_ℂ = ((‖q‖ ^ 2 : ℝ) : ℂ) := by
    dsimp [q]
    rw [sum_inner]
    calc
      ∑ i ∈ I, ⟪annularFrequencyProjection (R i) f, f⟫_ℂ =
          ∑ i ∈ I,
            ⟪annularFrequencyProjection (R i) f,
              annularFrequencyProjection (R i) f⟫_ℂ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact inner_annularFrequencyProjection_eq_inner_self (R i) f
      _ = ((∑ i ∈ I,
          ‖annularFrequencyProjection (R i) f‖ ^ 2 : ℝ) : ℂ) := by
        simp [inner_self_eq_norm_sq_to_K]
      _ = ((‖q‖ ^ 2 : ℝ) : ℂ) := by
        rw [norm_sq_sum_annularFrequencyProjection I R hI f]
  have hnorm :
      ‖q‖ ^ 2 ≤ ‖q‖ * ‖f‖ := by
    calc
      ‖q‖ ^ 2 = ‖⟪q, f⟫_ℂ‖ := by
        rw [hinner]
        simp
      _ ≤ ‖q‖ * ‖f‖ := norm_inner_le_norm q f
  by_cases hq : ‖q‖ = 0
  · simp [q, hq]
  · have hqpos : 0 < ‖q‖ :=
      lt_of_le_of_ne (norm_nonneg q) (Ne.symm hq)
    dsimp [q] at hnorm ⊢
    nlinarith

/-- Sharp finite Bessel inequality for separated annular projections. -/
lemma finiteLittlewoodPaley_bessel {n : ℕ}
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (R : ι → ℝ)
    (hI : SpectrallySeparated (n := n) I R)
    (f : EuclideanL2 n) :
    ∑ i ∈ I, ‖annularFrequencyProjection (R i) f‖ ^ 2 ≤
      ‖f‖ ^ 2 := by
  rw [← norm_sq_sum_annularFrequencyProjection I R hI f]
  have hnorm := norm_sum_annularFrequencyProjection_le I R hI f
  nlinarith [norm_nonneg (∑ i ∈ I,
    annularFrequencyProjection (R i) f), norm_nonneg f]

/-! # D. Capstone and Schrödinger covariance -/

/-- Capstone for the finite rough Littlewood--Paley layer: individual
contraction, pairwise orthogonality, exact Pythagorean energy, the sharp Bessel
bound, and covariance of every frequency cell under free Schrödinger
evolution. -/
lemma finiteLittlewoodPaley_orthogonality_bessel {n : ℕ}
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (R : ι → ℝ)
    (hI : SpectrallySeparated (n := n) I R)
    (f : EuclideanL2 n) (t : ℝ) :
    (∀ i ∈ I,
      ‖annularFrequencyProjection (R i) f‖ ≤ ‖f‖) ∧
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ⟪annularFrequencyProjection (R i) f,
        annularFrequencyProjection (R j) f⟫_ℂ = 0) ∧
    ‖∑ i ∈ I, annularFrequencyProjection (R i) f‖ ^ 2 =
      ∑ i ∈ I, ‖annularFrequencyProjection (R i) f‖ ^ 2 ∧
    ∑ i ∈ I, ‖annularFrequencyProjection (R i) f‖ ^ 2 ≤
      ‖f‖ ^ 2 ∧
    (∀ i ∈ I,
      annularFrequencyProjection (R i)
          (freeSchrodingerEvolution t f) =
        freeSchrodingerEvolution t
          (annularFrequencyProjection (R i) f)) := by
  refine ⟨?_, ?_, norm_sq_sum_annularFrequencyProjection I R hI f,
    finiteLittlewoodPaley_bessel I R hI f, ?_⟩
  · intro i hi
    exact norm_annularFrequencyProjection_le (R i) f
  · intro i hi j hj hij
    exact inner_annularFrequencyProjection_eq_zero_of_disjoint
      (hI hi hj hij) f f
  · intro i hi
    exact annularFrequencyProjection_commutes_evolution (R i) t f

end Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley
