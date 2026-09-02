/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.Vacuum
public import Physlib.SpaceAndTime.EntropicProperTime

/-!
# Complex action and entropic time for scalar Green functions

This file connects Rivers' scalar generating-functional construction to the
repository's complex-action and entropic-time program.

The load-bearing result is a normalization theorem. A constant shift
`S_I(phi) -> S_I(phi) + C` multiplies every path by the same nonzero scalar
`exp(-C/hbar)`. It changes the unnormalised partition and Green functions but
cancels exactly from every normalized expectation. Therefore:

* global vacuum phases and global imaginary-action offsets are normalization
  data, as in Rivers' removal of vacuum-to-vacuum diagrams;
* only a configuration-dependent imaginary action can change normalized Green
  functions or encode nontrivial entropic-time selection of histories;
* a global relative-entropy offset has modulus `exp(-D(rho||sigma))`, but also
  cancels from normalized correlations.

The file also reuses the existing entropic-weighted Wick theorem, showing that
Dyson--Wick contraction combinatorics is unchanged by the complex-action
weight and that the standard expansion is recovered by dividing out the
never-zero weight.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open MeasureTheory
open Physlib.QFT.PathIntegral
open Physlib.QFT.Wick.Consistency
open QuantumInfo.Finite
open FieldSpecification

variable {α : Type*} [MeasurableSpace α]

/-- Algebraic normalized expectation after multiplying both numerator and
partition by a global scalar. -/
def globallyWeightedNormalizedExpectation
    (m : MeasurePathIntegralModel α) (c : ℂ) (O : α → ℂ) : ℂ :=
  (c * m.unnormalizedExpectation O) / (c * m.partition)

/-- Every nonzero global path-weight factor cancels from normalized
expectations, including the case `partition = 0` under totalized division. -/
lemma globallyWeightedNormalizedExpectation_eq
    (m : MeasurePathIntegralModel α) (c : ℂ) (O : α → ℂ)
    (hc : c ≠ 0) :
    globallyWeightedNormalizedExpectation m c O =
      m.normalizedExpectation O := by
  unfold globallyWeightedNormalizedExpectation
    MeasurePathIntegralModel.normalizedExpectation
  by_cases hZ : m.partition = 0
  · simp [hZ]
  · field_simp [hc, hZ]

/-- Add a constant `C` to the imaginary action while retaining the same path
measure and real action. -/
def shiftImaginaryAction
    (m : MeasurePathIntegralModel α) (C : ℝ) (hC : 0 ≤ C) :
    MeasurePathIntegralModel α where
  μ := m.μ
  hbar := m.hbar
  hbar_pos := m.hbar_pos
  actionRe := m.actionRe
  actionIm := fun x => m.actionIm x + C
  measurable_actionRe := m.measurable_actionRe
  measurable_actionIm := m.measurable_actionIm.add_const C
  actionIm_nonneg := fun x => add_nonneg (m.actionIm_nonneg x) hC

/-- A constant imaginary-action shift factors pointwise as one global complex
weight. -/
lemma shiftImaginaryAction_weight
    (m : MeasurePathIntegralModel α) (C : ℝ) (hC : 0 ≤ C) (x : α) :
    (shiftImaginaryAction m C hC).weight x =
      complexActionWeight 0 C m.hbar * m.weight x := by
  unfold shiftImaginaryAction MeasurePathIntegralModel.weight
    MeasurePathIntegralModel.actionReScaled
    MeasurePathIntegralModel.actionImScaled complexActionWeight
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The shifted partition is the original partition times the global damping
factor. -/
lemma shiftImaginaryAction_partition
    (m : MeasurePathIntegralModel α) (C : ℝ) (hC : 0 ≤ C) :
    (shiftImaginaryAction m C hC).partition =
      complexActionWeight 0 C m.hbar * m.partition := by
  unfold MeasurePathIntegralModel.partition
  calc
    ∫ x, (shiftImaginaryAction m C hC).weight x ∂m.μ =
        ∫ x, complexActionWeight 0 C m.hbar * m.weight x ∂m.μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        shiftImaginaryAction_weight m C hC x
    _ = complexActionWeight 0 C m.hbar * ∫ x, m.weight x ∂m.μ := by
      simpa using
        integral_const_mul (complexActionWeight 0 C m.hbar) m.weight

/-- Every unnormalised Green function acquires the same global factor under a
constant imaginary-action shift. -/
lemma shiftImaginaryAction_unnormalizedExpectation
    (m : MeasurePathIntegralModel α) (C : ℝ) (hC : 0 ≤ C)
    (O : α → ℂ) :
    (shiftImaginaryAction m C hC).unnormalizedExpectation O =
      complexActionWeight 0 C m.hbar * m.unnormalizedExpectation O := by
  unfold MeasurePathIntegralModel.unnormalizedExpectation
  calc
    ∫ x, (shiftImaginaryAction m C hC).weight x * O x ∂m.μ =
        ∫ x, complexActionWeight 0 C m.hbar *
          (m.weight x * O x) ∂m.μ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun x => ?_
      simp only [shiftImaginaryAction_weight]
      ring
    _ = complexActionWeight 0 C m.hbar *
        ∫ x, m.weight x * O x ∂m.μ := by
      simpa using
        integral_const_mul (complexActionWeight 0 C m.hbar)
          (fun x => m.weight x * O x)

/-- A constant imaginary-action shift cannot alter normalized Green
functions. -/
lemma shiftImaginaryAction_normalizedExpectation
    (m : MeasurePathIntegralModel α) (C : ℝ) (hC : 0 ≤ C)
    (O : α → ℂ) :
    (shiftImaginaryAction m C hC).normalizedExpectation O =
      m.normalizedExpectation O := by
  unfold MeasurePathIntegralModel.normalizedExpectation
  rw [shiftImaginaryAction_unnormalizedExpectation,
    shiftImaginaryAction_partition]
  change globallyWeightedNormalizedExpectation m
      (complexActionWeight 0 C m.hbar) O = m.normalizedExpectation O
  exact globallyWeightedNormalizedExpectation_eq m
    (complexActionWeight 0 C m.hbar) O
    (complexActionWeight_ne_zero 0 C m.hbar)

/-- Increasing the imaginary action decreases the modulus of the complex path
weight when `hbar > 0`. -/
lemma norm_complexActionWeight_antitone_imaginary
    (S_R S_I₁ S_I₂ hbar : ℝ) (hhbar : 0 < hbar)
    (hI : S_I₁ ≤ S_I₂) :
    ‖complexActionWeight S_R S_I₂ hbar‖ ≤
      ‖complexActionWeight S_R S_I₁ hbar‖ := by
  rw [norm_complexActionWeight, norm_complexActionWeight]
  apply Real.exp_le_exp.mpr
  have hdiv : S_I₁ / hbar ≤ S_I₂ / hbar :=
    div_le_div_of_nonneg_right hI hhbar.le
  linarith

/-- Additivity of imaginary action is multiplicativity of complex path
weights. -/
lemma complexActionWeight_add_imaginary
    (S_R S_I C hbar : ℝ) :
    complexActionWeight S_R (S_I + C) hbar =
      complexActionWeight 0 C hbar *
        complexActionWeight S_R S_I hbar := by
  unfold complexActionWeight
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

section EntropicGap

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Imaginary-action offset `hbar * D(rho||sigma)`. -/
def entropicGapAction
    (m : MeasurePathIntegralModel α) (ρ σ : MState d) : ℝ :=
  m.hbar * entropicGap ρ σ

lemma entropicGapAction_nonneg
    (m : MeasurePathIntegralModel α) (ρ σ : MState d) :
    0 ≤ entropicGapAction m ρ σ :=
  mul_nonneg m.hbar_pos.le (entropicGap_nonneg ρ σ)

/-- Path-integral model shifted by a global relative-entropy action. -/
def entropicGapShiftedModel
    (m : MeasurePathIntegralModel α) (ρ σ : MState d) :
    MeasurePathIntegralModel α :=
  shiftImaginaryAction m (entropicGapAction m ρ σ)
    (entropicGapAction_nonneg m ρ σ)

/-- The global shift factor is the existing entropic complex weight. -/
lemma entropicGapShiftFactor_eq
    (m : MeasurePathIntegralModel α) (ρ σ : MState d) :
    complexActionWeight 0 (entropicGapAction m ρ σ) m.hbar =
      entropicComplexWeight 0 m.hbar ρ σ := by
  rfl

/-- The relative-entropy shift factor has modulus `exp(-D(rho||sigma))`. -/
lemma norm_entropicGapShiftFactor
    (m : MeasurePathIntegralModel α) (ρ σ : MState d) :
    ‖complexActionWeight 0 (entropicGapAction m ρ σ) m.hbar‖ =
      Real.exp (-(entropicGap ρ σ)) := by
  rw [entropicGapShiftFactor_eq]
  simpa [entropicGap] using
    norm_entropicComplexWeight 0 m.hbar m.hbar_pos.ne' ρ σ

/-- A global relative-entropy offset damps the partition and every
unnormalised Green function but cancels from normalized correlations. -/
lemma entropicGapShiftedModel_normalizedExpectation
    (m : MeasurePathIntegralModel α) (ρ σ : MState d) (O : α → ℂ) :
    (entropicGapShiftedModel m ρ σ).normalizedExpectation O =
      m.normalizedExpectation O := by
  exact shiftImaginaryAction_normalizedExpectation m
    (entropicGapAction m ρ σ) (entropicGapAction_nonneg m ρ σ) O

/-- Packaged distinction between global and path-dependent entropic action:
the global factor carries the expected damping but leaves normalized Green
functions invariant. -/
lemma globalEntropicOffset_damps_but_cancels
    (m : MeasurePathIntegralModel α) (ρ σ : MState d) (O : α → ℂ) :
    ‖complexActionWeight 0 (entropicGapAction m ρ σ) m.hbar‖ =
        Real.exp (-(entropicGap ρ σ))
      ∧ (entropicGapShiftedModel m ρ σ).normalizedExpectation O =
        m.normalizedExpectation O :=
  ⟨norm_entropicGapShiftFactor m ρ σ,
    entropicGapShiftedModel_normalizedExpectation m ρ σ O⟩

end EntropicGap

/-! ## Dyson--Wick compatibility -/

/-- Rivers' Dyson--Wick expansion remains valid after multiplication by the
complex-action or entropic weight. -/
lemma complexActionWeightedDysonWick
    {𝓕 : FieldSpecification} (S_R S_I hbar : ℝ)
    (φs : List 𝓕.FieldOp) :
    complexActionWeight S_R S_I hbar •
        WickAlgebra.timeOrder (WickAlgebra.ofFieldOpList φs) =
      ∑ φsΛ : WickContraction φs.length,
        complexActionWeight S_R S_I hbar • φsΛ.wickTerm :=
  complexActionWeight_smul_wicks_theorem S_R S_I hbar φs

/-- The ordinary Dyson--Wick expansion is recovered by dividing out the
never-zero entropic weight. -/
lemma entropicDysonWick_recovers_standard
    {d : Type*} [Fintype d] [DecidableEq d]
    {𝓕 : FieldSpecification} (S_R hbar : ℝ)
    (ρ σ : MState d) (φs : List 𝓕.FieldOp) :
    WickAlgebra.timeOrder (WickAlgebra.ofFieldOpList φs) =
      ∑ φsΛ : WickContraction φs.length, φsΛ.wickTerm :=
  entropic_weight_recovers_wicks_theorem S_R hbar ρ σ φs

end Physlib.QFT.ScalarGreenFunctions

end
