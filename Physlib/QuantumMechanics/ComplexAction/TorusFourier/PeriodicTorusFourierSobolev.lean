/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Tactic.Linarith

/-!
# Periodic torus Fourier/Sobolev gap

This file ports the proved finite Fourier fragments from the helper tree
into the canonical physlib torus-Fourier layer.

The key result is the integer spectral gap for a nonzero periodic mode:
`1 ≤ ∑ᵢ kᵢ²`.  It gives a concrete `Tⁿ` Fourier Poincare estimate for
finite mode families and then links that estimate to the existing
Navier-Stokes Fourier hierarchy and torus triadic kernel.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib.QuantumMechanics.ComplexAction.TorusFourier.PeriodicTorusFourierSobolev

open NavierStokes.NSFieldFourierSobolevHierarchy
open TorusFourier.TriadicKernel

/-! ## Integer torus modes -/

/-- The integer square sum of a nonzero wave vector is at least one. -/
lemma integer_square_sum_ge_one {ι : Type*} [Fintype ι] (k : ι → ℤ) (hk : k ≠ 0) :
    (1 : ℤ) ≤ ∑ i : ι, k i ^ 2 := by
  classical
  have h_exists : ∃ i : ι, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext fun i => h i)
  rcases h_exists with ⟨i, hi⟩
  have hki_sq : (1 : ℤ) ≤ k i ^ 2 := by
    have h_abs : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
    nlinarith [sq_abs (k i)]
  exact le_trans hki_sq
    (Finset.single_le_sum (fun j _ => sq_nonneg (k j)) (Finset.mem_univ i))

/-- Real-valued version of the integer torus spectral gap. -/
lemma integer_square_sum_ge_one_real {ι : Type*} [Fintype ι] (k : ι → ℤ) (hk : k ≠ 0) :
    (1 : ℝ) ≤ ∑ i : ι, (k i : ℝ) ^ 2 := by
  classical
  have h_exists : ∃ i : ι, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext fun i => h i)
  rcases h_exists with ⟨i, hi⟩
  have h_abs_int : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
  have h_abs_real : (1 : ℝ) ≤ |(k i : ℝ)| := by
    exact_mod_cast h_abs_int
  have hki_sq : (1 : ℝ) ≤ (k i : ℝ) ^ 2 := by
    nlinarith [sq_abs (k i : ℝ)]
  exact le_trans hki_sq
    (Finset.single_le_sum (fun j _ => sq_nonneg ((k j : ℝ))) (Finset.mem_univ i))

/-- Squared wave number of a periodic integer Fourier mode. -/
def torusWaveNumberSq {ι : Type*} [Fintype ι] (k : ι → ℤ) : ℝ :=
  ∑ i : ι, (k i : ℝ) ^ 2

/-- The squared wave number is nonnegative. -/
lemma torusWaveNumberSq_nonneg {ι : Type*} [Fintype ι] (k : ι → ℤ) :
    0 ≤ torusWaveNumberSq k := by
  unfold torusWaveNumberSq
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Nonzero integer Fourier modes have squared wave number at least one. -/
lemma torusWaveNumberSq_ge_one {ι : Type*} [Fintype ι] (k : ι → ℤ) (hk : k ≠ 0) :
    1 ≤ torusWaveNumberSq k := by
  simpa [torusWaveNumberSq] using integer_square_sum_ge_one_real k hk

/-- The `H¹` Fourier weight of a single periodic mode and amplitude. -/
def fourierH1Weight {ι : Type*} [Fintype ι] (k : ι → ℤ) (amp : ℝ) : ℝ :=
  torusWaveNumberSq k * amp ^ 2

/-- The `H¹` Fourier weight is nonnegative. -/
lemma fourierH1Weight_nonneg {ι : Type*} [Fintype ι] (k : ι → ℤ) (amp : ℝ) :
    0 ≤ fourierH1Weight k amp := by
  exact mul_nonneg (torusWaveNumberSq_nonneg k) (sq_nonneg amp)

/-- A nonzero periodic mode controls the `L²` amplitude by its `H¹` Fourier weight. -/
lemma amplitude_sq_le_fourierH1Weight_of_nonzero {ι : Type*} [Fintype ι]
    (k : ι → ℤ) (hk : k ≠ 0) (amp : ℝ) :
    amp ^ 2 ≤ fourierH1Weight k amp := by
  have hgap : (1 : ℝ) ≤ torusWaveNumberSq k := torusWaveNumberSq_ge_one k hk
  calc
    amp ^ 2 = 1 * amp ^ 2 := by ring
    _ ≤ torusWaveNumberSq k * amp ^ 2 :=
        mul_le_mul_of_nonneg_right hgap (sq_nonneg amp)

/-! ## Finite periodic Fourier families -/

/-- A finite periodic Fourier family with integer wave vectors. -/
structure FiniteTorusFourierFamily (ι : Type*) [Fintype ι] where
  /-- Number of retained Fourier modes. -/
  N : ℕ
  /-- Integer wave vector of each retained mode. -/
  wave : Fin N → ι → ℤ
  /-- Real Fourier amplitude of each retained mode. -/
  amp : Fin N → ℝ

namespace FiniteTorusFourierFamily

variable {ι : Type*} [Fintype ι] (F : FiniteTorusFourierFamily ι)

/-- Finite `L²` energy of a periodic Fourier family. -/
def l2Energy : ℝ :=
  ∑ i : Fin F.N, F.amp i ^ 2

/-- Finite `H¹` seminorm of a periodic Fourier family. -/
def h1Seminorm : ℝ :=
  ∑ i : Fin F.N, fourierH1Weight (F.wave i) (F.amp i)

/-- The finite `L²` energy is nonnegative. -/
lemma l2Energy_nonneg : 0 ≤ F.l2Energy := by
  unfold l2Energy
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The finite `H¹` seminorm is nonnegative. -/
lemma h1Seminorm_nonneg : 0 ≤ F.h1Seminorm := by
  unfold h1Seminorm
  exact Finset.sum_nonneg fun i _ => fourierH1Weight_nonneg (F.wave i) (F.amp i)

/-- Finite torus Poincare inequality: if every retained mode is nonzero, `H⁰ ≤ H¹`. -/
lemma poincare (hNonzero : ∀ i : Fin F.N, F.wave i ≠ 0) :
    F.l2Energy ≤ F.h1Seminorm := by
  unfold l2Energy h1Seminorm
  exact Finset.sum_le_sum fun i _ =>
    amplitude_sq_le_fourierH1Weight_of_nonzero (F.wave i) (hNonzero i) (F.amp i)

/-- The integer torus gap and the existing NS Fourier hierarchy give the same Poincare pattern. -/
lemma poincare_and_nsHierarchy (hNonzero : ∀ i : Fin F.N, F.wave i ≠ 0)
    (v : NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier)
    (hfreq : ∀ i : Fin v.N, 1 ≤ v.freq i) :
    F.l2Energy ≤ F.h1Seminorm
      ∧ v.kineticEnergy ≤ v.enstrophy :=
  ⟨F.poincare hNonzero,
    NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.poincare v hfreq⟩

/-- The finite Poincare estimate is compatible with the concrete `T³` triadic kernel. -/
lemma poincare_and_triadic_cases (F : FiniteTorusFourierFamily (Fin 3))
    (hNonzero : ∀ i : Fin F.N, F.wave i ≠ 0)
    (wvec : Fin F.N → TorusWaveVec3) (k j l : Fin F.N) :
    F.l2Energy ≤ F.h1Seminorm
      ∧ (triadicKernelCoeff wvec k j l = 0 ∨
        triadicKernelCoeff wvec k j l =
          (waveVecDot3 (wvec k) (wvec j) : ℚ) / waveVecMagSq3 (wvec k)) :=
  ⟨F.poincare hNonzero, triadicKernelCoeff_cases wvec k j l⟩

end FiniteTorusFourierFamily

end Physlib.QuantumMechanics.ComplexAction.TorusFourier.PeriodicTorusFourierSobolev

end
