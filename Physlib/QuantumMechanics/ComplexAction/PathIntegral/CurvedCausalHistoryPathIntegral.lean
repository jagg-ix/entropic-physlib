/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.PathIntegral.CurvedMeasurePathIntegral
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction
public import Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston

/-!
# Curved-background causal sum over histories

This file connects the curved-background measure path integral
`CurvedMeasurePathIntegralModel` with the causal-diamond and
consistent-history layers.

The construction is intentionally finite on the history index.  A history label
`η` selects a path-space point `path h : α`, an event map `event h : ℂ`
localizes that history in the `t + i r` causal diamond, and the curved
background supplies the measure `dμ_g = ρ_g dμ` through
`CurvedMeasurePathIntegralModel.toMeasurePathIntegralModel`.

The main content is:

* each curved history weight has norm equal to the path-integral damping;
* the finite causal sum over histories is bounded by the number of histories;
* the associated rank-one decoherence functional has diagonal Born weight and
  off-diagonal damping product.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.CurvedCausalHistoryPathIntegral

open scoped BigOperators
open Complex
open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction
open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston

/-! ## A. Causal localization of histories -/

/-- A spacetime event lies in the canonical causal diamond with vertices `-R`
and `R` in the complex `t + i r` plane. -/
def InCanonicalCausalDiamond (R : ℝ) (z : ℂ) : Prop :=
  z ∈ causalDiamond (-(R : ℂ)) (R : ℂ)

/-- All finite history labels are localized in the same canonical causal
diamond. -/
def DiamondLocalizedHistories {η : Type*} (R : ℝ) (event : η → ℂ) : Prop :=
  ∀ h : η, InCanonicalCausalDiamond R (event h)

/-! ## B. Curved-background history weights -/

/-- The complex weight of one history in a curved-background path-integral
model. -/
def curvedHistoryWeight {α η : Type*} [MeasurableSpace α]
    (c : CurvedMeasurePathIntegralModel α) (path : η → α) (h : η) : ℂ :=
  c.toMeasurePathIntegralModel.weight (path h)

/-- The norm of a curved history weight is the damping of the underlying
measure path-integral model. -/
lemma curvedHistoryWeight_norm_eq_damping {α η : Type*} [MeasurableSpace α]
    (c : CurvedMeasurePathIntegralModel α) (path : η → α) (h : η) :
    ‖curvedHistoryWeight c path h‖ =
      c.toMeasurePathIntegralModel.damping (path h) := by
  unfold curvedHistoryWeight MeasurePathIntegralModel.damping
  rw [c.toMeasurePathIntegralModel.weight_norm_is_damping]

/-- Each curved history weight has norm at most one, because the imaginary
action is nonnegative. -/
lemma curvedHistoryWeight_norm_le_one {α η : Type*} [MeasurableSpace α]
    (c : CurvedMeasurePathIntegralModel α) (path : η → α) (h : η) :
    ‖curvedHistoryWeight c path h‖ ≤ 1 := by
  unfold curvedHistoryWeight
  exact c.toMeasurePathIntegralModel.weight_bochner_bounded (path h)

/-- Finite causal sum over histories in the curved-background path integral. -/
def curvedCausalHistoryAmplitude {α η : Type*} [MeasurableSpace α] [Fintype η]
    (c : CurvedMeasurePathIntegralModel α) (path : η → α) : ℂ :=
  ∑ h : η, curvedHistoryWeight c path h

/-- The finite curved causal-history amplitude is bounded by the number of
history labels. -/
lemma curvedCausalHistoryAmplitude_norm_le_card
    {α η : Type*} [MeasurableSpace α] [Fintype η]
    (c : CurvedMeasurePathIntegralModel α) (path : η → α) :
    ‖curvedCausalHistoryAmplitude c path‖ ≤ (Fintype.card η : ℝ) := by
  calc
    ‖curvedCausalHistoryAmplitude c path‖
        ≤ ∑ h : η, ‖curvedHistoryWeight c path h‖ := by
          unfold curvedCausalHistoryAmplitude
          exact norm_sum_le _ _
    _ ≤ ∑ _h : η, (1 : ℝ) := by
          exact Finset.sum_le_sum
            (fun h _ => curvedHistoryWeight_norm_le_one c path h)
    _ = (Fintype.card η : ℝ) := by
          simp

/-- Causal localization plus the finite curved path-integral amplitude bound. -/
lemma diamondLocalized_curvedCausalHistoryAmplitude_norm_le_card
    {α η : Type*} [MeasurableSpace α] [Fintype η]
    (c : CurvedMeasurePathIntegralModel α) (path : η → α)
    (R : ℝ) (event : η → ℂ)
    (hlocal : DiamondLocalizedHistories R event) :
    (∀ h : η, event h ∈ causalDiamond (-(R : ℂ)) (R : ℂ)) ∧
      ‖curvedCausalHistoryAmplitude c path‖ ≤ (Fintype.card η : ℝ) :=
  ⟨hlocal, curvedCausalHistoryAmplitude_norm_le_card c path⟩

/-! ## C. Decoherence functional from curved history weights -/

/-- The rank-one consistent-history decoherence functional induced by the
curved-background path-integral weights. -/
def curvedHistoryDecoherenceFunctional {α η : Type*} [MeasurableSpace α]
    (c : CurvedMeasurePathIntegralModel α) (path : η → α) : η → η → ℂ :=
  decoherenceFunctional (curvedHistoryWeight c path)

/-- Product form of the curved-history decoherence functional. -/
lemma curvedHistoryDecoherenceFunctional_apply
    {α η : Type*} [MeasurableSpace α]
    (c : CurvedMeasurePathIntegralModel α) (path : η → α) (h k : η) :
    curvedHistoryDecoherenceFunctional c path h k =
      curvedHistoryWeight c path h *
        (starRingEnd ℂ) (curvedHistoryWeight c path k) := by
  simp [curvedHistoryDecoherenceFunctional, decoherenceFunctional_apply]

/-- The diagonal of the curved-history decoherence functional is the Born
weight of that history. -/
lemma curvedHistoryDecoherenceFunctional_diag_re
    {α η : Type*} [MeasurableSpace α]
    (c : CurvedMeasurePathIntegralModel α) (path : η → α) (h : η) :
    (curvedHistoryDecoherenceFunctional c path h h).re =
      Complex.normSq (curvedHistoryWeight c path h) := by
  simp [curvedHistoryDecoherenceFunctional, decoherenceFunctional_diag_re]

/-- The norm of a curved-history decoherence matrix element is the product of
the two path-integral damping factors. -/
lemma curvedHistoryDecoherenceFunctional_norm_eq_damping_mul
    {α η : Type*} [MeasurableSpace α]
    (c : CurvedMeasurePathIntegralModel α) (path : η → α) (h k : η) :
    ‖curvedHistoryDecoherenceFunctional c path h k‖ =
      c.toMeasurePathIntegralModel.damping (path h) *
        c.toMeasurePathIntegralModel.damping (path k) := by
  rw [curvedHistoryDecoherenceFunctional_apply, norm_mul]
  have hconj :
      ‖(starRingEnd ℂ) (curvedHistoryWeight c path k)‖ =
        ‖curvedHistoryWeight c path k‖ := by
    exact RCLike.norm_conj (curvedHistoryWeight c path k)
  rw [hconj, curvedHistoryWeight_norm_eq_damping,
    curvedHistoryWeight_norm_eq_damping]

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.CurvedCausalHistoryPathIntegral

end
