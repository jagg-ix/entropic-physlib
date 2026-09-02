/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Optics.TemporalDoubleSlit
public import Physlib.QFT.PathIntegral.FeynmanKac
public import Physlib.QFT.PathIntegral.MeasureModel
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction
public import Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.CurvedCausalHistoryPathIntegral
public import Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates

/-!
# Temporal double-slit spacetime-diamond bridge

This file connects three existing layers.

* `TemporalDoubleSlit.visibility` gives the optical visibility law
  `V = V_cl * exp (-(lambda * S))`.
* `MeasurePathIntegralModel.weight_norm_is_damping` identifies the norm of a
  complex path-integral weight with `exp (-S_I / hbar)`.
* `CausalDiamond.Construction.causalDiamond` gives the closed spacetime diamond
  in the `t + i r` plane.

The link is the explicit identity
`S_I(path) = hbar * lambda * S`.  Under that hypothesis the path-integral
decoherence factor and the temporal double-slit visibility factor are the same
real exponential.  The diamond lemmas localize the two temporal slits in the
canonical diamond with vertices `-R` and `R`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Optics.TemporalDoubleSlitSpacetimeDiamond

open scoped MState
open scoped ComplexOrder
open QuantumInfo.Finite
open Complex
open Physlib.Optics.TemporalDoubleSlit
open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.CurvedCausalHistoryPathIntegral
open Physlib.QuantumMechanics.Foundations.EverettHeisenbergRelativeStates
open Physlib.QuantumMechanics.Foundations.UnitaryDecoherentMeasurement
open Physlib.QuantumMechanics.Lindblad

/-! ## A. Temporal slits inside the canonical diamond -/

/-- The two temporal-slit labels reuse the two-outcome branch labels. -/
abbrev TemporalSlit := SpinOutcome

/-- The real-time event associated to one of two temporal slits separated by `S`.

The events are placed symmetrically at `t = -S/2` and `t = S/2`, with zero radial
coordinate in the complex `t + i r` plane used by the causal-diamond module. -/
def temporalSlitEvent (S : ℝ) : TemporalSlit → ℂ
  | .minus => (-(S / 2) : ℝ)
  | .plus => (S / 2 : ℝ)

/-- A real time `t` between `-R` and `R` lies in the canonical closed diamond. -/
lemma realTime_mem_canonicalDiamond {R t : ℝ}
    (hleft : -R ≤ t) (hright : t ≤ R) :
    (t : ℂ) ∈ causalDiamond (-(R : ℂ)) (R : ℂ) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have hsq : 0 ≤ (t + R) ^ 2 := sq_nonneg (t + R)
    simpa [lorentzianForm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsq
  · simp only [Complex.sub_re, Complex.ofReal_re, neg_re]
    linarith
  · have hsq : 0 ≤ (R - t) ^ 2 := sq_nonneg (R - t)
    simpa [lorentzianForm] using hsq
  · simpa using sub_nonneg.mpr hright

/-- If the half-separation of the two temporal slits fits in radius `R`, both
slit events lie in the canonical closed diamond with vertices `-R` and `R`. -/
lemma temporalSlitEvent_mem_canonicalDiamond {R S : ℝ}
    (hS_nonneg : 0 ≤ S) (hhalf : S / 2 ≤ R) (s : TemporalSlit) :
    temporalSlitEvent S s ∈ causalDiamond (-(R : ℂ)) (R : ℂ) := by
  cases s
  · apply realTime_mem_canonicalDiamond
    · linarith
    · exact hhalf
  · apply realTime_mem_canonicalDiamond
    · linarith
    · linarith

/-! ## B. Diamond-local Heisenberg updates -/

/-- A Heisenberg descriptor update localized to the canonical diamond. -/
def diamondUpdate {Obs : Type*} (R : ℝ) (inside old : ℂ → Obs) : ℂ → Obs :=
  updateOnSupport (causalDiamond (-(R : ℂ)) (R : ℂ)) inside old

/-- A diamond-local Heisenberg update agrees with the old descriptor outside
the canonical diamond. -/
lemma diamondUpdate_agreesOutside {Obs : Type*}
    (R : ℝ) (inside old : ℂ → Obs) :
    AgreesOutside (causalDiamond (-(R : ℂ)) (R : ℂ))
      (diamondUpdate R inside old) old :=
  updateOnSupport_agreesOutside _ inside old

/-! ## C. Path-integral damping equals double-slit visibility damping -/

/-- Visibility obtained by multiplying the classical two-path visibility by the
norm damping of a path-integral model. -/
def pathIntegralDoubleSlitVisibility {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (V_cl : ℝ) (x : α) : ℝ :=
  V_cl * m.damping x

/-- The path-integral visibility factor is the classical visibility times the
norm of the complex path-integral weight. -/
lemma pathIntegralDoubleSlitVisibility_eq_weight_norm
    {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (V_cl : ℝ) (x : α) :
    pathIntegralDoubleSlitVisibility m V_cl x = V_cl * ‖m.weight x‖ := by
  unfold pathIntegralDoubleSlitVisibility MeasurePathIntegralModel.damping
  rw [m.weight_norm_is_damping]

/-- If the imaginary action of a path is `hbar * lambda * S`, the
path-integral damping gives exactly the temporal double-slit visibility law. -/
lemma pathIntegralDoubleSlitVisibility_eq_visibility_of_actionIm
    {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (V_cl lambda S : ℝ) (x : α)
    (hSI : m.actionIm x = m.hbar * (lambda * S)) :
    pathIntegralDoubleSlitVisibility m V_cl x = visibility V_cl lambda S := by
  have hscaled : m.actionImScaled x = lambda * S := by
    unfold MeasurePathIntegralModel.actionImScaled
    rw [hSI]
    field_simp [ne_of_gt m.hbar_pos]
  unfold pathIntegralDoubleSlitVisibility MeasurePathIntegralModel.damping visibility
  rw [hscaled]

/-- The same identification stated directly in terms of the norm of the complex
path-integral weight. -/
lemma visibility_eq_weight_norm_of_actionIm
    {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (V_cl lambda S : ℝ) (x : α)
    (hSI : m.actionIm x = m.hbar * (lambda * S)) :
    visibility V_cl lambda S = V_cl * ‖m.weight x‖ := by
  rw [← pathIntegralDoubleSlitVisibility_eq_weight_norm m V_cl x]
  exact (pathIntegralDoubleSlitVisibility_eq_visibility_of_actionIm
    m V_cl lambda S x hSI).symm

/-- Log-slope extraction from the path-integral imaginary action:
`log(V/V_cl) = -S_I/hbar`. -/
lemma log_pathIntegralDoubleSlitVisibility_ratio_eq_neg_actionImScaled
    {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) {V_cl : ℝ} (x : α) (hV : 0 < V_cl) :
    Real.log (pathIntegralDoubleSlitVisibility m V_cl x / V_cl) =
      -m.actionImScaled x := by
  unfold pathIntegralDoubleSlitVisibility MeasurePathIntegralModel.damping
  rw [mul_div_cancel_left₀ _ hV.ne']
  exact Real.log_exp _

/-! ## D. Two-slit decoherence functional from path weights -/

/-- The two branch weights obtained by evaluating the path-integral weight on
the two slit histories. -/
def twoSlitPathWeights {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (path : TemporalSlit → α) : TemporalSlit → ℂ :=
  fun s => m.weight (path s)

/-- The existing Sorkin-Johnston/Dowker-Halliwell decoherence functional
specialized to the two temporal-slit path weights. -/
def twoSlitDecoherenceFunctional {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (path : TemporalSlit → α) :
    TemporalSlit → TemporalSlit → ℂ :=
  decoherenceFunctional (twoSlitPathWeights m path)

/-- Product form of the two-slit decoherence functional. -/
lemma twoSlitDecoherenceFunctional_apply
    {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (path : TemporalSlit → α)
    (s t : TemporalSlit) :
    twoSlitDecoherenceFunctional m path s t =
      m.weight (path s) * (starRingEnd ℂ) (m.weight (path t)) := by
  simp [twoSlitDecoherenceFunctional, twoSlitPathWeights, decoherenceFunctional_apply]

/-- The diagonal of the two-slit decoherence functional is the Born weight of
the corresponding path-integral branch. -/
lemma twoSlitDecoherenceFunctional_diag_re
    {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (path : TemporalSlit → α)
    (s : TemporalSlit) :
    (twoSlitDecoherenceFunctional m path s s).re =
      Complex.normSq (m.weight (path s)) := by
  simp [twoSlitDecoherenceFunctional, twoSlitPathWeights, decoherenceFunctional_diag_re]

/-- The norm of a two-slit decoherence-functional matrix element is the product
of the two path-integral damping factors. -/
lemma twoSlitDecoherenceFunctional_norm_eq_damping_mul
    {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (path : TemporalSlit → α)
    (s t : TemporalSlit) :
    ‖twoSlitDecoherenceFunctional m path s t‖ =
      m.damping (path s) * m.damping (path t) := by
  rw [twoSlitDecoherenceFunctional_apply, norm_mul]
  have hconj : ‖(starRingEnd ℂ) (m.weight (path t))‖ = ‖m.weight (path t)‖ := by
    exact RCLike.norm_conj (m.weight (path t))
  unfold MeasurePathIntegralModel.damping
  rw [hconj, m.weight_norm_is_damping, m.weight_norm_is_damping]

/-- Fringe visibility read from the off-diagonal two-slit decoherence
functional. -/
def twoSlitInterferenceVisibility {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (path : TemporalSlit → α) (V_cl : ℝ) : ℝ :=
  V_cl * ‖twoSlitDecoherenceFunctional m path .minus .plus‖

/-- The off-diagonal visibility is the classical visibility times the two
branch damping factors. -/
lemma twoSlitInterferenceVisibility_eq_damping_product
    {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (path : TemporalSlit → α) (V_cl : ℝ) :
    twoSlitInterferenceVisibility m path V_cl =
      V_cl * (m.damping (path .minus) * m.damping (path .plus)) := by
  unfold twoSlitInterferenceVisibility
  rw [twoSlitDecoherenceFunctional_norm_eq_damping_mul]

/-- If each branch contributes half of the imaginary action
`hbar * lambda * S`, the off-diagonal decoherence functional gives exactly the
temporal double-slit visibility law. -/
lemma twoSlitInterferenceVisibility_eq_visibility_of_half_actionIm
    {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (path : TemporalSlit → α)
    (V_cl lambda S : ℝ)
    (hminus : m.actionIm (path .minus) = m.hbar * ((lambda * S) / 2))
    (hplus : m.actionIm (path .plus) = m.hbar * ((lambda * S) / 2)) :
    twoSlitInterferenceVisibility m path V_cl = visibility V_cl lambda S := by
  have hminus_scaled : m.actionImScaled (path .minus) = (lambda * S) / 2 := by
    unfold MeasurePathIntegralModel.actionImScaled
    rw [hminus]
    field_simp [ne_of_gt m.hbar_pos]
  have hplus_scaled : m.actionImScaled (path .plus) = (lambda * S) / 2 := by
    unfold MeasurePathIntegralModel.actionImScaled
    rw [hplus]
    field_simp [ne_of_gt m.hbar_pos]
  rw [twoSlitInterferenceVisibility_eq_damping_product]
  unfold MeasurePathIntegralModel.damping visibility
  rw [hminus_scaled, hplus_scaled]
  rw [← Real.exp_add]
  congr 1
  ring_nf

/-- Combined double-slit spacetime statement: the two temporal slits lie in the
canonical diamond, and the off-diagonal path-integral decoherence functional
reduces to the optical visibility law when each branch has half of the total
imaginary action. -/
lemma diamond_twoSlitInterferenceVisibility_eq_visibility
    {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (path : TemporalSlit → α)
    {R S V_cl lambda : ℝ}
    (hS_nonneg : 0 ≤ S) (hhalf : S / 2 ≤ R)
    (hminus : m.actionIm (path .minus) = m.hbar * ((lambda * S) / 2))
    (hplus : m.actionIm (path .plus) = m.hbar * ((lambda * S) / 2)) :
    (∀ s : TemporalSlit,
        temporalSlitEvent S s ∈ causalDiamond (-(R : ℂ)) (R : ℂ)) ∧
      twoSlitInterferenceVisibility m path V_cl = visibility V_cl lambda S := by
  exact ⟨temporalSlitEvent_mem_canonicalDiamond hS_nonneg hhalf,
    twoSlitInterferenceVisibility_eq_visibility_of_half_actionIm
      m path V_cl lambda S hminus hplus⟩

/-! ## E. Feynman-Kac form of the same visibility damping -/

/-- The temporal double-slit visibility law is the constant-potential
Feynman-Kac damping with potential `lambda` and time interval `S`. -/
lemma visibility_eq_Vcl_mul_feynmanKacWeight
    (V_cl lambda S : ℝ) :
    visibility V_cl lambda S =
      V_cl * feynman_kac_weight (fun _ : Unit => lambda) S () := by
  unfold visibility feynman_kac_weight
  ring_nf

/-- Splitting the separation into two equal branch intervals gives the same
constant-potential Feynman-Kac weight. -/
lemma feynmanKacWeight_half_mul_half_eq_full
    (lambda S : ℝ) :
    feynman_kac_weight (fun _ : Unit => lambda) (S / 2) () *
        feynman_kac_weight (fun _ : Unit => lambda) (S / 2) () =
      feynman_kac_weight (fun _ : Unit => lambda) S () := by
  unfold feynman_kac_weight
  rw [← Real.exp_add]
  congr 1
  ring_nf

/-- Under the half-action hypotheses, the off-diagonal two-slit decoherence
visibility equals the product of the two half-interval Feynman-Kac weights. -/
lemma twoSlitInterferenceVisibility_eq_feynmanKac_half_product_of_half_actionIm
    {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (path : TemporalSlit → α)
    (V_cl lambda S : ℝ)
    (hminus : m.actionIm (path .minus) = m.hbar * ((lambda * S) / 2))
    (hplus : m.actionIm (path .plus) = m.hbar * ((lambda * S) / 2)) :
    twoSlitInterferenceVisibility m path V_cl =
      V_cl *
        (feynman_kac_weight (fun _ : Unit => lambda) (S / 2) () *
          feynman_kac_weight (fun _ : Unit => lambda) (S / 2) ()) := by
  have hminus_scaled : m.actionImScaled (path .minus) = (lambda * S) / 2 := by
    unfold MeasurePathIntegralModel.actionImScaled
    rw [hminus]
    field_simp [ne_of_gt m.hbar_pos]
  have hplus_scaled : m.actionImScaled (path .plus) = (lambda * S) / 2 := by
    unfold MeasurePathIntegralModel.actionImScaled
    rw [hplus]
    field_simp [ne_of_gt m.hbar_pos]
  rw [twoSlitInterferenceVisibility_eq_damping_product]
  unfold MeasurePathIntegralModel.damping feynman_kac_weight
  rw [hminus_scaled, hplus_scaled]
  ring_nf

/-- The same two-slit object has both readings: off-diagonal decoherence
functional damping and constant-potential Feynman-Kac damping. -/
lemma twoSlitInterferenceVisibility_eq_feynmanKac_full_of_half_actionIm
    {α : Type*} [MeasurableSpace α]
    (m : MeasurePathIntegralModel α) (path : TemporalSlit → α)
    (V_cl lambda S : ℝ)
    (hminus : m.actionIm (path .minus) = m.hbar * ((lambda * S) / 2))
    (hplus : m.actionIm (path .plus) = m.hbar * ((lambda * S) / 2)) :
    twoSlitInterferenceVisibility m path V_cl =
      V_cl * feynman_kac_weight (fun _ : Unit => lambda) S () := by
  rw [twoSlitInterferenceVisibility_eq_feynmanKac_half_product_of_half_actionIm
    m path V_cl lambda S hminus hplus]
  rw [feynmanKacWeight_half_mul_half_eq_full]

/-! ## F. Link to unitary decoherent measurement -/

/-- The two-slit visibility read from the master complex-action path-integral
weight. -/
def complexActionDoubleSlitVisibility
    (V_cl S_R S_I ℏ : ℝ) : ℝ :=
  V_cl * ‖complexActionPathIntegralWeight S_R S_I ℏ‖

/-- The complex-action two-slit visibility is the existing
environmental-decoherence/Kuiken damping factor. -/
lemma complexActionDoubleSlitVisibility_eq_kuiken
    (V_cl S_R S_I ℏ : ℝ) :
    complexActionDoubleSlitVisibility V_cl S_R S_I ℏ =
      V_cl * kuikenWeight ℏ S_I := by
  unfold complexActionDoubleSlitVisibility
  rw [environmentalDecoherence_is_pathIntegralDamping]

/-- If `S_I = ℏ * lambda * S`, the complex-action environmental damping is
the same visibility law used by the temporal double-slit module. -/
lemma complexActionDoubleSlitVisibility_eq_visibility_of_actionIm
    (V_cl S_R S_I ℏ lambda S : ℝ) (hℏ : ℏ ≠ 0)
    (hSI : S_I = ℏ * (lambda * S)) :
    complexActionDoubleSlitVisibility V_cl S_R S_I ℏ =
      visibility V_cl lambda S := by
  rw [complexActionDoubleSlitVisibility_eq_kuiken]
  unfold kuikenWeight visibility
  rw [hSI]
  field_simp [hℏ]

/-- Diamond-local double-slit measurement package: the slit events are inside
the spacetime diamond, the complex-action environmental damping gives the
optical visibility law, and the operational steps are the existing unitary,
environmental, Lindblad, and Born-conditioning steps rather than a primitive
state-vector collapse postulate. -/
lemma diamond_complexActionDoubleSlitMeasurement_package
    {R S V_cl S_R S_I ℏ lambda : ℝ}
    (hS_nonneg : 0 ≤ S) (hhalf : S / 2 ≤ R) (hℏ : ℏ ≠ 0)
    (hSI : S_I = ℏ * (lambda * S)) :
    (∀ s : TemporalSlit,
        temporalSlitEvent S s ∈ causalDiamond (-(R : ℂ)) (R : ℂ)) ∧
      complexActionDoubleSlitVisibility V_cl S_R S_I ℏ =
        visibility V_cl lambda S ∧
      ¬ IsPrimitiveCollapse .unitaryInteraction ∧
      ¬ IsPrimitiveCollapse .environmentalDecoherence ∧
      ¬ IsPrimitiveCollapse .lindbladReducedDynamics ∧
      ¬ IsPrimitiveCollapse .bornWeightedConditioning := by
  exact ⟨temporalSlitEvent_mem_canonicalDiamond hS_nonneg hhalf,
    complexActionDoubleSlitVisibility_eq_visibility_of_actionIm
      V_cl S_R S_I ℏ lambda S hℏ hSI,
    everettHeisenberg_excludes_primitive_collapse.1,
    everettHeisenberg_excludes_primitive_collapse.2.1,
    everettHeisenberg_excludes_primitive_collapse.2.2.1,
    everettHeisenberg_excludes_primitive_collapse.2.2.2⟩

/-- Full double-slit measurement bridge.  It combines diamond localization and
the complex-action visibility law with the repository's unitary decoherent
measurement summary: unitary entropy invariance, environmental damping,
finite-dimensional Lindblad/GKLS structure, Born-weighted conditioning, and
exclusion of primitive collapse steps. -/
lemma diamond_complexActionDoubleSlit_unitaryDecoherentMeasurement_summary
    {d dE ι β : Type*}
    [Fintype d] [DecidableEq d] [Fintype dE] [DecidableEq dE]
    [Fintype ι] [Fintype β]
    (ρSE : MState (d × dE)) (U : 𝐔[d × dE])
    (H : Matrix d d ℂ) (L : ι → Matrix d d ℂ)
    (ρMat : Matrix d d ℂ) (ρ : MState d) (p : ProbDistribution β)
    {R S V_cl S_R S_I ℏ lambda : ℝ}
    (hS_nonneg : 0 ≤ S) (hhalf : S / 2 ≤ R) (hℏ : ℏ ≠ 0)
    (hSI : S_I = ℏ * (lambda * S)) :
    (∀ s : TemporalSlit,
        temporalSlitEvent S s ∈ causalDiamond (-(R : ℂ)) (R : ℂ)) ∧
      complexActionDoubleSlitVisibility V_cl S_R S_I ℏ =
        visibility V_cl lambda S ∧
      Sᵥₙ (U ◃ ρSE) = Sᵥₙ ρSE ∧
      ‖complexActionPathIntegralWeight S_R S_I ℏ‖ = kuikenWeight ℏ S_I ∧
      (lindbladJumpChannel L).IsCompletelyPositive ∧
      (lindbladDriftCoefficient L).PosSemidef ∧
      (gklsGenerator H L ℏ ρMat).trace = 0 ∧
      0 ≤ gklsEntropicRate L ρ ∧
      (∑ i, (p.prob i : ℝ) * (-ℏ * Real.log (p.prob i)) = ℏ * Hₛ p) ∧
      ¬ IsPrimitiveCollapse .unitaryInteraction ∧
      ¬ IsPrimitiveCollapse .environmentalDecoherence ∧
      ¬ IsPrimitiveCollapse .lindbladReducedDynamics ∧
      ¬ IsPrimitiveCollapse .bornWeightedConditioning := by
  exact ⟨temporalSlitEvent_mem_canonicalDiamond hS_nonneg hhalf,
    complexActionDoubleSlitVisibility_eq_visibility_of_actionIm
      V_cl S_R S_I ℏ lambda S hℏ hSI,
    unitaryDecoherentMeasurement_summary ρSE U S_R S_I ℏ H L ρMat ρ p⟩

/-! ## G. Curved-background causal-history double slit -/

/-- The two temporal-slit events form a finite history family localized in the
canonical causal diamond. -/
lemma temporalSlitEvent_diamondLocalizedHistories {R S : ℝ}
    (hS_nonneg : 0 ≤ S) (hhalf : S / 2 ≤ R) :
    DiamondLocalizedHistories R (temporalSlitEvent S) :=
  fun s => temporalSlitEvent_mem_canonicalDiamond hS_nonneg hhalf s

/-- The curved-background finite history amplitude of the two temporal slits. -/
def curvedTemporalDoubleSlitAmplitude {α : Type*} [MeasurableSpace α]
    (c : CurvedMeasurePathIntegralModel α) (path : TemporalSlit → α) : ℂ :=
  curvedCausalHistoryAmplitude c path

/-- The curved-background two-slit history amplitude has norm at most two. -/
lemma curvedTemporalDoubleSlitAmplitude_norm_le_two
    {α : Type*} [MeasurableSpace α]
    (c : CurvedMeasurePathIntegralModel α) (path : TemporalSlit → α) :
    ‖curvedTemporalDoubleSlitAmplitude c path‖ ≤ 2 := by
  unfold curvedTemporalDoubleSlitAmplitude
  simpa [TemporalSlit, spinOutcome_card] using
    curvedCausalHistoryAmplitude_norm_le_card c path

/-- Causal localization plus the curved-background two-history amplitude bound
for the temporal double slit. -/
lemma curvedTemporalDoubleSlit_localizedAmplitude_norm_le_two
    {α : Type*} [MeasurableSpace α]
    (c : CurvedMeasurePathIntegralModel α) (path : TemporalSlit → α)
    {R S : ℝ} (hS_nonneg : 0 ≤ S) (hhalf : S / 2 ≤ R) :
    DiamondLocalizedHistories R (temporalSlitEvent S) ∧
      ‖curvedTemporalDoubleSlitAmplitude c path‖ ≤ 2 := by
  exact ⟨temporalSlitEvent_diamondLocalizedHistories hS_nonneg hhalf,
    curvedTemporalDoubleSlitAmplitude_norm_le_two c path⟩

/-- The generic curved-history decoherence functional specializes to the
two-slit decoherence functional already used in this file. -/
lemma curvedHistoryDecoherenceFunctional_eq_twoSlitDecoherenceFunctional
    {α : Type*} [MeasurableSpace α]
    (c : CurvedMeasurePathIntegralModel α) (path : TemporalSlit → α) :
    curvedHistoryDecoherenceFunctional c path =
      twoSlitDecoherenceFunctional c.toMeasurePathIntegralModel path := by
  funext s t
  rw [curvedHistoryDecoherenceFunctional_apply,
    twoSlitDecoherenceFunctional_apply]
  rfl

/-- In a curved-background measure path integral, if each temporal-slit branch
has half of the total imaginary action, the off-diagonal history functional
gives the same visibility law. -/
lemma curvedTwoSlitInterferenceVisibility_eq_visibility_of_half_actionIm
    {α : Type*} [MeasurableSpace α]
    (c : CurvedMeasurePathIntegralModel α) (path : TemporalSlit → α)
    (V_cl lambda S : ℝ)
    (hminus : c.actionIm (path .minus) = c.hbar * ((lambda * S) / 2))
    (hplus : c.actionIm (path .plus) = c.hbar * ((lambda * S) / 2)) :
    twoSlitInterferenceVisibility c.toMeasurePathIntegralModel path V_cl =
      visibility V_cl lambda S :=
  twoSlitInterferenceVisibility_eq_visibility_of_half_actionIm
    c.toMeasurePathIntegralModel path V_cl lambda S hminus hplus

/-- Curved-background causal-history form of the double-slit spacetime bridge:
the two slit histories are localized in the causal diamond, their finite
history amplitude is bounded by two, and their off-diagonal decoherence
functional gives the optical visibility law under the half-action hypotheses. -/
lemma curvedDiamond_twoSlitInterferenceVisibility_eq_visibility
    {α : Type*} [MeasurableSpace α]
    (c : CurvedMeasurePathIntegralModel α) (path : TemporalSlit → α)
    {R S V_cl lambda : ℝ}
    (hS_nonneg : 0 ≤ S) (hhalf : S / 2 ≤ R)
    (hminus : c.actionIm (path .minus) = c.hbar * ((lambda * S) / 2))
    (hplus : c.actionIm (path .plus) = c.hbar * ((lambda * S) / 2)) :
    DiamondLocalizedHistories R (temporalSlitEvent S) ∧
      ‖curvedTemporalDoubleSlitAmplitude c path‖ ≤ 2 ∧
      twoSlitInterferenceVisibility c.toMeasurePathIntegralModel path V_cl =
        visibility V_cl lambda S := by
  exact ⟨temporalSlitEvent_diamondLocalizedHistories hS_nonneg hhalf,
    curvedTemporalDoubleSlitAmplitude_norm_le_two c path,
    curvedTwoSlitInterferenceVisibility_eq_visibility_of_half_actionIm
      c path V_cl lambda S hminus hplus⟩

end Physlib.Optics.TemporalDoubleSlitSpacetimeDiamond

end
