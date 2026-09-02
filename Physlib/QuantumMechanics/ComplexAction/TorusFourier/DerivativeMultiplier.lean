/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TorusFourier.PeriodicTorusFourierSobolev
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# Torus Fourier derivative multipliers

This file formalizes the finite spectral core behind the Fourier derivative
identity on a periodic torus.  For a mode `k : ι → ℤ`, differentiating the
Fourier basis in direction `i` multiplies the coefficient by
`2π i kᵢ`.  Summing squared directional multiplier weights gives exactly
`(2π)²` times the finite `H¹` Fourier seminorm from
`TorusFourier.PeriodicTorusFourierSobolev`.

The analytic theorem for smooth functions on `(ℝ/ℤ)³` additionally needs
Fubini/Parseval hypotheses.  This module provides the Lean-checked finite
algebraic layer that the Navier-Stokes Fourier hierarchy and torus triadic
kernel can use now.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Physlib.QuantumMechanics.ComplexAction.TorusFourier.DerivativeMultiplier

open TorusFourier.PeriodicTorusFourierSobolev
open TorusFourier.TriadicKernel

/-- The universal derivative scale `(2π)²`. -/
def derivativeScale : ℝ :=
  (2 * Real.pi) ^ 2

/-- Fourier derivative multiplier in direction `i`: `2π i kᵢ`. -/
def fourierDerivativeMultiplier {ι : Type*} (i : ι) (k : ι → ℤ) : ℂ :=
  ((2 * Real.pi * (k i : ℝ)) : ℂ) * Complex.I

/-- Directional derivative coefficient for a real Fourier amplitude. -/
def directionalDerivativeCoeff {ι : Type*} (i : ι) (k : ι → ℤ) (amp : ℝ) : ℂ :=
  fourierDerivativeMultiplier i k * (amp : ℂ)

/-- Squared directional derivative weight for one finite Fourier mode. -/
def directionalDerivativeWeight {ι : Type*} (i : ι) (k : ι → ℤ) (amp : ℝ) : ℝ :=
  derivativeScale * (k i : ℝ) ^ 2 * amp ^ 2

/-- The directional derivative weight is nonnegative. -/
lemma directionalDerivativeWeight_nonneg {ι : Type*} (i : ι) (k : ι → ℤ) (amp : ℝ) :
    0 ≤ directionalDerivativeWeight i k amp := by
  unfold directionalDerivativeWeight derivativeScale
  positivity

/-- The complex multiplier coefficient has the expected squared norm. -/
lemma norm_sq_directionalDerivativeCoeff {ι : Type*} (i : ι) (k : ι → ℤ) (amp : ℝ) :
    ‖directionalDerivativeCoeff i k amp‖ ^ 2 =
      directionalDerivativeWeight i k amp := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [directionalDerivativeCoeff, fourierDerivativeMultiplier, directionalDerivativeWeight,
    derivativeScale, Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal]
  ring

/-- A zero wave-vector component gives zero directional derivative weight. -/
@[simp]
lemma directionalDerivativeWeight_zero_component {ι : Type*} (i : ι) (k : ι → ℤ) (amp : ℝ)
    (hki : k i = 0) :
    directionalDerivativeWeight i k amp = 0 := by
  simp [directionalDerivativeWeight, hki]

variable {ι : Type*} [Fintype ι] (F : FiniteTorusFourierFamily ι)

/-- Directional derivative energy of a finite periodic Fourier family. -/
def finiteTorusDirectionalDerivativeEnergy (i : ι) : ℝ :=
  ∑ n : Fin F.N, directionalDerivativeWeight i (F.wave n) (F.amp n)

/-- Total gradient energy as the sum of all directional derivative weights. -/
def finiteTorusGradientEnergy : ℝ :=
  ∑ n : Fin F.N, ∑ i : ι, directionalDerivativeWeight i (F.wave n) (F.amp n)

/-- Directional derivative energy is nonnegative. -/
lemma finiteTorusDirectionalDerivativeEnergy_nonneg (i : ι) :
    0 ≤ finiteTorusDirectionalDerivativeEnergy F i := by
  unfold finiteTorusDirectionalDerivativeEnergy
  exact Finset.sum_nonneg fun n _ => directionalDerivativeWeight_nonneg i (F.wave n) (F.amp n)

/-- Total gradient energy is nonnegative. -/
lemma finiteTorusGradientEnergy_nonneg : 0 ≤ finiteTorusGradientEnergy F := by
  unfold finiteTorusGradientEnergy
  exact Finset.sum_nonneg fun n _ =>
    Finset.sum_nonneg fun i _ => directionalDerivativeWeight_nonneg i (F.wave n) (F.amp n)

/-- The total gradient energy is `(2π)²` times the finite `H¹` Fourier seminorm. -/
lemma finiteTorusGradientEnergy_eq_derivativeScale_mul_h1Seminorm :
    finiteTorusGradientEnergy F = derivativeScale * F.h1Seminorm := by
  unfold finiteTorusGradientEnergy
    TorusFourier.PeriodicTorusFourierSobolev.FiniteTorusFourierFamily.h1Seminorm
    directionalDerivativeWeight
    TorusFourier.PeriodicTorusFourierSobolev.fourierH1Weight
    TorusFourier.PeriodicTorusFourierSobolev.torusWaveNumberSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  calc
    ∑ i : ι, derivativeScale * (F.wave n i : ℝ) ^ 2 * F.amp n ^ 2
        = ∑ i : ι, derivativeScale * ((F.wave n i : ℝ) ^ 2 * F.amp n ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = derivativeScale * (∑ i : ι, (F.wave n i : ℝ) ^ 2 * F.amp n ^ 2) := by
          rw [Finset.mul_sum]
    _ = derivativeScale * ((∑ i : ι, (F.wave n i : ℝ) ^ 2) * F.amp n ^ 2) := by
          rw [Finset.sum_mul]

/-- Scaled finite Poincare inequality using derivative-multiplier gradient energy. -/
lemma derivativeScale_mul_l2Energy_le_finiteTorusGradientEnergy
    (hNonzero : ∀ n : Fin F.N, F.wave n ≠ 0) :
    derivativeScale * F.l2Energy ≤ finiteTorusGradientEnergy F := by
  rw [finiteTorusGradientEnergy_eq_derivativeScale_mul_h1Seminorm F]
  exact mul_le_mul_of_nonneg_left (F.poincare hNonzero) (by unfold derivativeScale; positivity)

/--
The derivative-multiplier gradient bound is compatible with the concrete
torus triadic kernel used by the finite Navier-Stokes Fourier hierarchy.
-/
lemma derivativeScale_poincare_and_triadic_cases
    (F : FiniteTorusFourierFamily (Fin 3))
    (hNonzero : ∀ n : Fin F.N, F.wave n ≠ 0)
    (wvec : Fin F.N → TorusWaveVec3) (k j l : Fin F.N) :
    derivativeScale * F.l2Energy ≤ finiteTorusGradientEnergy F
      ∧ (triadicKernelCoeff wvec k j l = 0 ∨
        triadicKernelCoeff wvec k j l =
          (waveVecDot3 (wvec k) (wvec j) : ℚ) / waveVecMagSq3 (wvec k)) :=
  ⟨derivativeScale_mul_l2Energy_le_finiteTorusGradientEnergy F hNonzero,
    triadicKernelCoeff_cases wvec k j l⟩

end Physlib.QuantumMechanics.ComplexAction.TorusFourier.DerivativeMultiplier

end
