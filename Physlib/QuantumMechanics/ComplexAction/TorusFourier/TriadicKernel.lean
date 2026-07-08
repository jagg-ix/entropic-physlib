/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic.Positivity

/-!
# Torus Fourier triadic kernel

This file provides a small concrete Fourier-mode kernel on `T³`.  The
coefficient is the usual triadic selection rule for torus Fourier modes:
it vanishes off resonance and equals a rational dot-product quotient on
resonant triples.

The module is intentionally independent of any one PDE or helper-repo
nomenclature.  Navier-Stokes Galerkin truncations, theta/Poisson mode
sums, and matrix-model Fourier reductions can all import the same kernel.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TorusFourier.TriadicKernel

/-! ## Wave-vector arithmetic on `T³` -/

/-- A Fourier wave vector on `T³`, represented as a triple of integers. -/
abbrev TorusWaveVec3 : Type := Fin 3 → ℤ

/-- Integer dot product of two torus wave vectors. -/
def waveVecDot3 (k j : TorusWaveVec3) : ℤ :=
  Finset.univ.sum fun i : Fin 3 => k i * j i

/-- Squared magnitude of a torus wave vector, valued in `ℚ`. -/
noncomputable def waveVecMagSq3 (k : TorusWaveVec3) : ℚ :=
  Finset.univ.sum fun i : Fin 3 => (k i : ℚ) ^ 2

/-- The squared magnitude is nonnegative. -/
theorem waveVecMagSq3_nonneg (k : TorusWaveVec3) : 0 ≤ waveVecMagSq3 k := by
  apply Finset.sum_nonneg
  intro i _
  positivity

/-- The zero wave vector has squared magnitude zero. -/
@[simp]
theorem waveVecMagSq3_zero : waveVecMagSq3 (fun _ => 0) = 0 := by
  simp [waveVecMagSq3]

/-- Wave-vector addition is componentwise. -/
@[simp]
theorem torusWaveVec3_add (k j : TorusWaveVec3) (i : Fin 3) :
    (k + j) i = k i + j i := rfl

/-! ## Concrete triadic kernel -/

/-- Concrete Fourier triadic kernel coefficient.

For modes `wvec : Fin N → TorusWaveVec3`, the coefficient for `(k,j,l)` is
`(wvec k · wvec j) / |wvec k|²` on resonant triples `wvec k = wvec j + wvec l`
and zero otherwise.
-/
noncomputable def triadicKernelCoeff {N : ℕ} (wvec : Fin N → TorusWaveVec3) :
    Fin N → Fin N → Fin N → ℚ :=
  fun k j l =>
    if wvec k = wvec j + wvec l then
      (waveVecDot3 (wvec k) (wvec j) : ℚ) / waveVecMagSq3 (wvec k)
    else 0

/-- Off-resonance vanishing of the torus triadic kernel. -/
theorem triadicKernelCoeff_off_resonance {N : ℕ} (wvec : Fin N → TorusWaveVec3)
    (k j l : Fin N) (h : wvec k ≠ wvec j + wvec l) :
    triadicKernelCoeff wvec k j l = 0 := by
  unfold triadicKernelCoeff
  exact if_neg h

/-- Resonant formula for the torus triadic kernel. -/
theorem triadicKernelCoeff_resonant {N : ℕ} (wvec : Fin N → TorusWaveVec3)
    (k j l : Fin N) (h : wvec k = wvec j + wvec l) :
    triadicKernelCoeff wvec k j l =
      (waveVecDot3 (wvec k) (wvec j) : ℚ) / waveVecMagSq3 (wvec k) := by
  unfold triadicKernelCoeff
  exact if_pos h

/-- Every triad is either off-resonant or has the resonant coefficient. -/
theorem triadicKernelCoeff_cases {N : ℕ} (wvec : Fin N → TorusWaveVec3) (k j l : Fin N) :
    triadicKernelCoeff wvec k j l = 0 ∨
      triadicKernelCoeff wvec k j l =
        (waveVecDot3 (wvec k) (wvec j) : ℚ) / waveVecMagSq3 (wvec k) := by
  by_cases h : wvec k = wvec j + wvec l
  · right
    exact triadicKernelCoeff_resonant wvec k j l h
  · left
    exact triadicKernelCoeff_off_resonance wvec k j l h

end Physlib.QuantumMechanics.ComplexAction.TorusFourier.TriadicKernel

end
