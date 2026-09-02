/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Schwartz kernels for the one-parameter Calderon decomposition

This module formalizes the first one-parameter mechanism in Section 4 of
Hejna--Nagel--Ricci.  A normalized compactly supported smooth bump is bundled
as a Schwartz map, its dyadic mass-preserving dilates are formed inside
Schwartz space, and consecutive differences give cancelling detail kernels.
The finite detail sum telescopes exactly to the last approximate identity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ContDiff SchwartzMap

namespace Physlib.Mathematics.HarmonicAnalysis

namespace MultiNormSchwartzKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## A. Normalized dyadic Schwartz kernels -/

/-- A normalized compactly supported smooth bump, bundled in Schwartz space. -/
def normalizedBumpSchwartz (φ : ContDiffBump (0 : E)) : 𝓢(E, ℝ) :=
  (φ.hasCompactSupport_normed (μ := volume)).toSchwartzMap
    (φ.contDiff_normed (μ := volume))

@[simp]
lemma normalizedBumpSchwartz_apply (φ : ContDiffBump (0 : E)) (x : E) :
    normalizedBumpSchwartz φ x = φ.normed volume x :=
  by simp [normalizedBumpSchwartz]

/-- The positive dyadic expansion factor used at resolution `n`. -/
def dyadicExpansion (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n

lemma dyadicExpansion_pos (n : ℕ) :
    0 < dyadicExpansion n := by
  simp [dyadicExpansion]

/-- Scalar expansion by `2^n`, bundled as a continuous linear equivalence. -/
def dyadicExpansionCLE (n : ℕ) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 (dyadicExpansion n) (dyadicExpansion_pos n).ne')

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
lemma dyadicExpansionCLE_apply (n : ℕ) (x : E) :
    dyadicExpansionCLE n x = dyadicExpansion n • x :=
  rfl

/-- The mass-preserving dyadic approximate-identity kernel
`2^(n dim E) φ(2^n x)`. -/
def dyadicApproximationKernel (φ : ContDiffBump (0 : E)) (n : ℕ) : 𝓢(E, ℝ) :=
  (dyadicExpansion n ^ Module.finrank ℝ E) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (dyadicExpansionCLE n) (normalizedBumpSchwartz φ)

@[simp]
lemma dyadicApproximationKernel_apply
    (φ : ContDiffBump (0 : E)) (n : ℕ) (x : E) :
    dyadicApproximationKernel φ n x =
      dyadicExpansion n ^ Module.finrank ℝ E *
        φ.normed volume (dyadicExpansion n • x) := by
  rfl

/-- Dyadic dilation preserves the unit mass of the normalized bump. -/
lemma integral_dyadicApproximationKernel
    (φ : ContDiffBump (0 : E)) (n : ℕ) :
    ∫ x, dyadicApproximationKernel φ n x = 1 := by
  simp_rw [dyadicApproximationKernel_apply]
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume
      (φ.normed volume) (dyadicExpansion n)
        (hR := (dyadicExpansion_pos n).le),
    φ.integral_normed]
  have hne : dyadicExpansion n ^ Module.finrank ℝ E ≠ 0 :=
    pow_ne_zero _ (dyadicExpansion_pos n).ne'
  simp [hne]

/-! ## B. Cancellation and finite telescoping -/

/-- The low-frequency kernel at level zero and consecutive dyadic detail
kernels at positive levels. -/
def dyadicDetailKernel (φ : ContDiffBump (0 : E)) : ℕ → 𝓢(E, ℝ)
  | 0 => dyadicApproximationKernel φ 0
  | n + 1 => dyadicApproximationKernel φ (n + 1) - dyadicApproximationKernel φ n

@[simp]
lemma dyadicDetailKernel_zero (φ : ContDiffBump (0 : E)) :
    dyadicDetailKernel φ 0 = dyadicApproximationKernel φ 0 :=
  rfl

@[simp]
lemma dyadicDetailKernel_succ (φ : ContDiffBump (0 : E)) (n : ℕ) :
    dyadicDetailKernel φ (n + 1) =
      dyadicApproximationKernel φ (n + 1) - dyadicApproximationKernel φ n :=
  rfl

/-- Every positive-level detail kernel has the order-one cancellation required
in the first step of Section 4. -/
lemma integral_dyadicDetailKernel_succ
    (φ : ContDiffBump (0 : E)) (n : ℕ) :
    ∫ x, dyadicDetailKernel φ (n + 1) x = 0 := by
  rw [dyadicDetailKernel_succ]
  simp only [sub_apply]
  rw [integral_sub
    (dyadicApproximationKernel φ (n + 1)).integrable
    (dyadicApproximationKernel φ n).integrable,
    integral_dyadicApproximationKernel,
    integral_dyadicApproximationKernel, sub_self]

/-- Every finite Section 4 detail sum telescopes to the last normalized
approximate-identity kernel. -/
lemma sum_range_dyadicDetailKernel (φ : ContDiffBump (0 : E)) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), dyadicDetailKernel φ n =
      dyadicApproximationKernel φ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show N.succ + 1 = (N + 1) + 1 by omega,
        Finset.sum_range_succ, ih]
      simp

/-- First Section 4 capstone: the kernels are genuine Schwartz maps, retain
unit mass at every dyadic resolution, have cancellation at every positive
detail level, and telescope exactly at every finite cutoff. -/
lemma dyadicSchwartzKernel_cancellation_telescope
    (φ : ContDiffBump (0 : E)) (N : ℕ) :
    (∫ x, dyadicApproximationKernel φ N x) = 1 ∧
    (∀ n : ℕ, ∫ x, dyadicDetailKernel φ (n + 1) x = 0) ∧
    (∑ n ∈ Finset.range (N + 1), dyadicDetailKernel φ n) =
      dyadicApproximationKernel φ N := by
  exact ⟨integral_dyadicApproximationKernel φ N,
    integral_dyadicDetailKernel_succ φ,
    sum_range_dyadicDetailKernel φ N⟩

end MultiNormSchwartzKernel

end Physlib.Mathematics.HarmonicAnalysis
