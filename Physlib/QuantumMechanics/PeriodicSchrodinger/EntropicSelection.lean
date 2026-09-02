/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.PeriodicSchrodinger.Isoenergetic
public import Physlib.QFT.Wick.Consistency

/-!
# Entropic selection of Bloch and resonant modes

This module connects periodic Schrödinger perturbation theory to the
complex-action and entropic-time program.

A squared spectral mismatch is used as a nonnegative imaginary-action penalty.
Its associated complex-action weight has modulus

`exp (-(spectral mismatch)² / hbar)`.

Thus exact free, resonant-matrix, or directional-reference matching has unit
modulus, while mismatched modes are contractively weighted. This is a
selection mechanism, not a replacement for the spectral approximation proof.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.PeriodicSchrodinger

open Physlib.QFT.Wick.Consistency

/-- Nonnegative squared mismatch between a true spectral value and a known
perturbative value. -/
def spectralMismatchPenalty
    (trueValue knownValue : ℝ) : ℝ :=
  (trueValue - knownValue) ^ 2

/-- Spectral mismatch penalty is nonnegative. -/
theorem spectralMismatchPenalty_nonneg
    (trueValue knownValue : ℝ) :
    0 ≤ spectralMismatchPenalty trueValue knownValue := by
  unfold spectralMismatchPenalty
  positivity

/-- The penalty vanishes exactly at spectral matching. -/
theorem spectralMismatchPenalty_eq_zero_iff
    (trueValue knownValue : ℝ) :
    spectralMismatchPenalty trueValue knownValue = 0 ↔
      trueValue = knownValue := by
  unfold spectralMismatchPenalty
  constructor
  · intro h
    nlinarith
  · rintro rfl
    ring

/-- Entropic-time cost of a spectral mismatch. -/
def spectralEntropicTime
    (trueValue knownValue hbar : ℝ) : ℝ :=
  spectralMismatchPenalty trueValue knownValue / hbar

/-- Complex-action selection weight for one spectral label. -/
def spectralSelectionWeight
    (phaseAction trueValue knownValue hbar : ℝ) : ℂ :=
  complexActionWeight phaseAction
    (spectralMismatchPenalty trueValue knownValue) hbar

/-- Exact modulus of the spectral-selection weight. -/
theorem norm_spectralSelectionWeight
    (phaseAction trueValue knownValue hbar : ℝ) :
    ‖spectralSelectionWeight phaseAction trueValue knownValue hbar‖ =
      Real.exp (-(spectralEntropicTime trueValue knownValue hbar)) := by
  unfold spectralSelectionWeight spectralEntropicTime
  exact norm_complexActionWeight phaseAction
    (spectralMismatchPenalty trueValue knownValue) hbar

/-- At exact spectral matching, the selection weight has unit modulus. -/
@[simp] theorem norm_spectralSelectionWeight_of_match
    (phaseAction value hbar : ℝ) :
    ‖spectralSelectionWeight phaseAction value value hbar‖ = 1 := by
  rw [norm_spectralSelectionWeight]
  simp [spectralEntropicTime, spectralMismatchPenalty]

/-- For positive `hbar`, every spectral-selection weight is contractive. -/
theorem norm_spectralSelectionWeight_le_one
    (phaseAction trueValue knownValue hbar : ℝ)
    (hhbar : 0 < hbar) :
    ‖spectralSelectionWeight phaseAction trueValue knownValue hbar‖ ≤ 1 := by
  rw [norm_spectralSelectionWeight, Real.exp_le_one_iff]
  exact neg_nonpos.mpr <|
    div_nonneg (spectralMismatchPenalty_nonneg trueValue knownValue)
      hhbar.le

/-- Diffraction mismatch penalty associated with a reciprocal displacement. -/
def diffractionPenalty {d : ℕ}
    (k b : Momentum d) : ℝ :=
  diffractionDefect k b ^ 2

/-- Diffraction penalty vanishes exactly on the diffraction hyperplane. -/
theorem diffractionPenalty_eq_zero_iff {d : ℕ}
    (k b : Momentum d) :
    diffractionPenalty k b = 0 ↔
      OnDiffractionHyperplane k b := by
  constructor
  · intro h
    apply (onDiffractionHyperplane_iff_defect_zero k b).2
    unfold diffractionPenalty at h
    nlinarith
  · intro h
    have hdefect : diffractionDefect k b = 0 :=
      (onDiffractionHyperplane_iff_defect_zero k b).1 h
    simp [diffractionPenalty, hdefect]

/-- Entropic-time cost assigned to diffraction mismatch. -/
def diffractionEntropicTime {d : ℕ}
    (k b : Momentum d) (hbar : ℝ) : ℝ :=
  diffractionPenalty k b / hbar

/-- Diffraction selection weight. -/
def diffractionSelectionWeight {d : ℕ}
    (phaseAction : ℝ) (k b : Momentum d) (hbar : ℝ) : ℂ :=
  complexActionWeight phaseAction (diffractionPenalty k b) hbar

/-- Exact modulus of diffraction selection. -/
theorem norm_diffractionSelectionWeight {d : ℕ}
    (phaseAction : ℝ) (k b : Momentum d) (hbar : ℝ) :
    ‖diffractionSelectionWeight phaseAction k b hbar‖ =
      Real.exp (-(diffractionEntropicTime k b hbar)) := by
  unfold diffractionSelectionWeight diffractionEntropicTime
  exact norm_complexActionWeight phaseAction (diffractionPenalty k b) hbar

/-- Exact diffraction points have unit selection weight. -/
theorem norm_diffractionSelectionWeight_of_resonance {d : ℕ}
    (phaseAction : ℝ) (k b : Momentum d) (hbar : ℝ)
    (hk : OnDiffractionHyperplane k b) :
    ‖diffractionSelectionWeight phaseAction k b hbar‖ = 1 := by
  rw [norm_diffractionSelectionWeight]
  have hp : diffractionPenalty k b = 0 :=
    (diffractionPenalty_eq_zero_iff k b).2 hk
  simp [diffractionEntropicTime, hp]

/-- A nonnegative global spectral penalty can be attached to every known-part
approximation order. -/
def expansionSelectionWeight {K : Type*}
    (A : ArbitraryOrderSpectralExpansion K)
    (order : ℕ) (phaseAction hbar : ℝ) (k : K) : ℂ :=
  spectralSelectionWeight phaseAction
    (A.actual k) (A.knownPart order k) hbar

end Physlib.QuantumMechanics.PeriodicSchrodinger

end
