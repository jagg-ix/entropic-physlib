/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenJonesPolynomialChernSimons
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon
public import Physlib.QFT.PathIntegral.Coercivity

/-!
# Witten analytic Wilson integrals as cutoff-free functional integrals

This file connects the analytic path-integral carrier extracted from Witten's
Chern-Simons/Jones-polynomial construction to a direct, cutoff-free functional
integral API.

The point is deliberately narrow and intentionally **not** a cutoff argument:

* `WittenAnalyticPathIntegral` already supplies the rigorous complex
  Feynman-Kac obligations for Wilson observables: measurability, boundedness,
  Bochner integrability, and the damping norm bound.
* If those analytic obligations are supplied on the intended field space, the
  Wilson functional is already a continuum functional integral.  No auxiliary
  cutoff sequence is introduced here.

Cutoff-limit APIs remain useful elsewhere for theories whose continuum measure
has not been constructed.  Witten's analytic carrier is used here in the
opposite way: it is the direct analytic object.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral

open Filter Topology MeasureTheory
open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon

variable {Field Link : Type*} [MeasurableSpace Field]


/-- A cutoff-free analytic functional integral.

This structure represents the case where the path-integral model itself is the
continuum object.  The analytic work is not a UV cutoff limit; it is the direct
Bochner-integrability proof for the chosen admissible observables. -/
structure CutoffFreeAnalyticFunctionalIntegral (Field : Type*) [MeasurableSpace Field] where
  /-- The already-defined analytic path-integral model. -/
  model : MeasurePathIntegralModel Field
  /-- Observables for which the model has certified analytic control. -/
  admissible : (Field → ℂ) → Prop
  /-- The vacuum observable is admissible. -/
  admissible_one : admissible (fun _ => 1)
  /-- Every admissible observable is Bochner-integrable against the complex
  path-integral weight. -/
  integrable :
    ∀ {O : Field → ℂ}, admissible O →
      Integrable (fun A => model.weight A * O A) model.μ
  /-- A representative gauge transformation on field configurations. -/
  gaugeTransform : Field → Field
  /-- Pullback by the gauge transformation preserves admissibility. -/
  admissible_gauge :
    ∀ {O : Field → ℂ}, admissible O → admissible (fun A => O (gaugeTransform A))
  /-- Gauge/Ward identity directly at the analytic continuum level. -/
  gauge_invariant :
    ∀ {O : Field → ℂ}, admissible O →
      model.unnormalizedExpectation (fun A => O (gaugeTransform A))
        = model.unnormalizedExpectation O

namespace CutoffFreeAnalyticFunctionalIntegral

variable {Field : Type*} [MeasurableSpace Field]

/-- The cutoff-free amplitude is just the analytic model's unnormalised
expectation. -/
def amplitude (I : CutoffFreeAnalyticFunctionalIntegral Field)
    (O : Field → ℂ) (_hO : I.admissible O) : ℂ :=
  I.model.unnormalizedExpectation O

/-- The vacuum partition amplitude. -/
def partition (I : CutoffFreeAnalyticFunctionalIntegral Field) : ℂ :=
  I.amplitude (fun _ => 1) I.admissible_one

/-- Normalized expectation in the direct analytic model. -/
def normalizedExpectation (I : CutoffFreeAnalyticFunctionalIntegral Field)
    (O : Field → ℂ) (hO : I.admissible O) : ℂ :=
  I.amplitude O hO / I.partition

/-- The named amplitude unfolds to the shared path-integral expectation. -/
@[simp] lemma amplitude_eq_unnormalizedExpectation
    (I : CutoffFreeAnalyticFunctionalIntegral Field)
    (O : Field → ℂ) (hO : I.admissible O) :
    I.amplitude O hO = I.model.unnormalizedExpectation O :=
  rfl

/-- The stored analytic obligation is available for every admissible
observable. -/
lemma amplitude_integrable
    (I : CutoffFreeAnalyticFunctionalIntegral Field)
    (O : Field → ℂ) (hO : I.admissible O) :
    Integrable (fun A => I.model.weight A * O A) I.model.μ :=
  I.integrable hO

/-- Gauge/Ward identity at the cutoff-free analytic level. -/
lemma amplitude_gauge_invariant
    (I : CutoffFreeAnalyticFunctionalIntegral Field)
    (O : Field → ℂ) (hO : I.admissible O) :
    I.amplitude (fun A => O (I.gaugeTransform A)) (I.admissible_gauge hO)
      = I.amplitude O hO :=
  I.gauge_invariant hO

/-- If the partition is nonzero, normalized expectation times partition
recovers the unnormalised amplitude. -/
lemma normalizedExpectation_mul_partition
    (I : CutoffFreeAnalyticFunctionalIntegral Field)
    (O : Field → ℂ) (hO : I.admissible O) (hZ : I.partition ≠ 0) :
    I.normalizedExpectation O hO * I.partition = I.amplitude O hO := by
  unfold normalizedExpectation
  field_simp [hZ]

end CutoffFreeAnalyticFunctionalIntegral


/-- The Witten Wilson integral agrees with the shared path-integral
`unnormalizedExpectation` API.  The definitions differ only by the scalar
product order `observable * weight` versus `weight * observable`. -/
lemma wittenWilsonIntegral_eq_unnormalizedExpectation
    (W : WittenAnalyticPathIntegral Field Link) (L : Link) :
    W.wilsonIntegral L =
      W.model.unnormalizedExpectation (W.wilsonObservable L) := by
  unfold WittenAnalyticPathIntegral.wilsonIntegral
    MeasurePathIntegralModel.complexFKExpectation
    MeasurePathIntegralModel.unnormalizedExpectation
  congr with A
  exact mul_comm _ _

/-- The same compatibility in the opposite orientation, convenient for direct
functional-integral rewrites. -/
lemma unnormalizedExpectation_eq_wittenWilsonIntegral
    (W : WittenAnalyticPathIntegral Field Link) (L : Link) :
    W.model.unnormalizedExpectation (W.wilsonObservable L) =
      W.wilsonIntegral L :=
  (wittenWilsonIntegral_eq_unnormalizedExpectation W L).symm

/-- Witten's rigorous FK theorem supplies direct Bochner integrability for the
Wilson observable against the analytic model's complex weight. -/
lemma wittenWilson_integrable
    (W : WittenAnalyticPathIntegral Field Link) (L : Link) :
    Integrable
      (fun A => W.model.weight A * W.wilsonObservable L A) W.model.μ := by
  refine (W.wilsonIntegral_integrable L).congr ?_
  exact Filter.Eventually.of_forall fun A => by
    simp [mul_comm]

/-- The Witten FK norm bound is available in the cutoff-free bridge without
reproving any analytic estimates. -/
lemma wittenWilson_norm_le_partition
    (W : WittenAnalyticPathIntegral Field Link) (L : Link) :
    ‖W.model.unnormalizedExpectation (W.wilsonObservable L)‖
      ≤ W.wilsonBound L * W.partitionFunction := by
  rw [unnormalizedExpectation_eq_wittenWilsonIntegral W L]
  exact W.wilsonIntegral_norm_le L


/-- The Witten Wilson integral imported into the cutoff-free bridge is also
the repository's master complex-action integral. -/
lemma wittenContinuumWilson_eq_master_integral
    (W : WittenAnalyticPathIntegral Field Link) (L : Link) :
    W.model.unnormalizedExpectation (W.wilsonObservable L) =
      ∫ A, W.wilsonObservable L A *
        complexActionPathIntegralWeight
          (W.model.actionRe A) (W.model.actionIm A) W.model.hbar ∂W.model.μ := by
  rw [unnormalizedExpectation_eq_wittenWilsonIntegral W L]
  exact W.wilsonIntegral_eq_master_integral L

/-- The same cutoff-free Wilson bridge expressed through the Lorentzian kernel. -/
lemma wittenContinuumWilson_eq_lorentzianKernel_integral
    (W : WittenAnalyticPathIntegral Field Link) (L : Link) :
    W.model.unnormalizedExpectation (W.wilsonObservable L) =
      ∫ A, W.wilsonObservable L A *
        lorentzianKernel
          (W.model.actionRe A) (W.model.actionIm A) W.model.hbar ∂W.model.μ := by
  rw [unnormalizedExpectation_eq_wittenWilsonIntegral W L]
  exact W.wilsonIntegral_eq_lorentzianKernel_integral L


/-- Complex action supplies the reusable weight-level analytic obligations:
measurability of the weight and damping, the modulus identity, positivity of
the damping, and the universal bound `damping ≤ 1`.

It does not by itself prove Wilson-observable measurability/boundedness, nor
does it prove `L¹` integrability on an arbitrary infinite-volume field space. -/
lemma complexAction_supplies_weight_obligations
    (model : MeasurePathIntegralModel Field) :
    Measurable model.weight ∧
      Measurable model.damping ∧
      (∀ A, ‖model.weight A‖ = model.damping A) ∧
      (∀ A, 0 < model.damping A) ∧
      (∀ A, model.damping A ≤ 1) := by
  exact ⟨model.measurable_weight, model.measurable_damping,
    (fun A => by
      rw [model.weight_norm_is_damping]
      rfl),
    model.damping_pos, model.damping_le_one⟩

/-- On a finite reference measure, the complex-action damping obligation is
automatically `L¹` because `0 < damping ≤ 1`. -/
lemma complexAction_finiteMeasure_supplies_damping_integrable
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ] :
    Integrable (fun A => model.damping A) model.μ :=
  WittenAnalyticPathIntegral.damping_integrable_of_finiteMeasure model

/-- The Wilson-loop analytic obligations that are **not** consequences of the
complex-action weight alone.

The complex-action model knows `weight`, `damping`, and the modulus/damping
estimates.  It does not know that a chosen Wilson-loop functional is
measurable, nor that its norm is a.e. bounded by a finite real function of the
link.  Those are properties of the holonomy/representation observable and must
be supplied separately. -/
structure WilsonObservableAnalyticObligations
    (model : MeasurePathIntegralModel Field)
    (wilsonObservable : Link → Field → ℂ) where
  /-- A finite declared bound for each Wilson observable. -/
  wilsonBound : Link → ℝ
  /-- Measurability of each Wilson observable. -/
  measurable_wilsonObservable : ∀ L, Measurable (wilsonObservable L)
  /-- The declared bounds are nonnegative. -/
  wilsonBound_nonneg : ∀ L, 0 ≤ wilsonBound L
  /-- Each Wilson observable is a.e. bounded by its declared bound. -/
  wilson_bounded : ∀ L, ∀ᵐ A ∂model.μ, ‖wilsonObservable L A‖ ≤ wilsonBound L

namespace WilsonObservableAnalyticObligations

variable {model : MeasurePathIntegralModel Field}
variable {wilsonObservable : Link → Field → ℂ}

/-- Unpack the observable obligations in the shape used by the rigorous FK
theorem. -/
lemma as_obligations
    (H : WilsonObservableAnalyticObligations model wilsonObservable) :
    (∀ L, Measurable (wilsonObservable L)) ∧
      (∀ L, 0 ≤ H.wilsonBound L) ∧
      (∀ L, ∀ᵐ A ∂model.μ, ‖wilsonObservable L A‖ ≤ H.wilsonBound L) :=
  ⟨H.measurable_wilsonObservable, H.wilsonBound_nonneg, H.wilson_bounded⟩

/-- Pointwise bounded measurable Wilson observables supply the a.e. bounded
observable obligations. -/
def ofPointwiseBound
    (wilsonBound : Link → ℝ)
    (hMeas : ∀ L, Measurable (wilsonObservable L))
    (hNonneg : ∀ L, 0 ≤ wilsonBound L)
    (hBound : ∀ L A, ‖wilsonObservable L A‖ ≤ wilsonBound L) :
    WilsonObservableAnalyticObligations model wilsonObservable where
  wilsonBound := wilsonBound
  measurable_wilsonObservable := hMeas
  wilsonBound_nonneg := hNonneg
  wilson_bounded := fun L => Filter.Eventually.of_forall (hBound L)

/-- A uniform finite bound for all links and fields is a special case of the
Wilson observable obligations. -/
def ofUniformBound
    (C : ℝ)
    (hMeas : ∀ L, Measurable (wilsonObservable L))
    (hC : 0 ≤ C)
    (hBound : ∀ L A, ‖wilsonObservable L A‖ ≤ C) :
    WilsonObservableAnalyticObligations model wilsonObservable :=
  ofPointwiseBound (model := model) (wilsonObservable := wilsonObservable)
    (fun _ => C) hMeas (fun _ => hC) hBound

/-- Norm-one/unitary Wilson observables are bounded by `1`.  This is the
standard route for compact/unitary holonomy representations once measurability
has been proved. -/
def ofNormLeOne
    (hMeas : ∀ L, Measurable (wilsonObservable L))
    (hBound : ∀ L A, ‖wilsonObservable L A‖ ≤ 1) :
    WilsonObservableAnalyticObligations model wilsonObservable :=
  ofUniformBound (model := model) (wilsonObservable := wilsonObservable)
    1 hMeas zero_le_one hBound

/-- Unit-modulus Wilson observables, e.g. phase-valued abelian Wilson loops,
automatically satisfy the `≤ 1` bound. -/
def ofUnitNorm
    (hMeas : ∀ L, Measurable (wilsonObservable L))
    (hNorm : ∀ L A, ‖wilsonObservable L A‖ = 1) :
    WilsonObservableAnalyticObligations model wilsonObservable :=
  ofNormLeOne (model := model) (wilsonObservable := wilsonObservable)
    hMeas (fun L A => by simp [hNorm L A])

/-- Continuous Wilson observables with a pointwise bound give the measurable
bounded-observable obligations.  This is the topological/holonomy route:
prove the holonomy functional is continuous, then bound it by representation
unitarity/compactness. -/
def ofContinuousPointwiseBound
    [TopologicalSpace Field] [BorelSpace Field]
    (wilsonBound : Link → ℝ)
    (hContinuous : ∀ L, Continuous (wilsonObservable L))
    (hNonneg : ∀ L, 0 ≤ wilsonBound L)
    (hBound : ∀ L A, ‖wilsonObservable L A‖ ≤ wilsonBound L) :
    WilsonObservableAnalyticObligations model wilsonObservable :=
  ofPointwiseBound (model := model) (wilsonObservable := wilsonObservable)
    wilsonBound (fun L => (hContinuous L).measurable) hNonneg hBound

/-- Constant charge-sector Wilson observables are automatically measurable and
bounded.  This covers finite/topological carriers such as Verlinde-basis or
topological-spin Wilson data before they are promoted to field-dependent
holonomy functionals. -/
def ofConstant
    (model : MeasurePathIntegralModel Field)
    (value : Link → ℂ) :
    WilsonObservableAnalyticObligations model (fun L _ => value L) where
  wilsonBound := fun L => ‖value L‖
  measurable_wilsonObservable := fun _ => measurable_const
  wilsonBound_nonneg := fun L => norm_nonneg (value L)
  wilson_bounded := fun _ => Filter.Eventually.of_forall fun _ => le_rfl

end WilsonObservableAnalyticObligations

/-- A constructor that makes the remaining obligations explicit: complex
action supplies the analytic weight, while the caller supplies Wilson
measurability, Wilson boundedness, and the damping `L¹` proof. -/
noncomputable def wittenAnalyticPathIntegralOfComplexAction
    (model : MeasurePathIntegralModel Field)
    (wilsonObservable : Link → Field → ℂ)
    (measurable_wilsonObservable : ∀ L, Measurable (wilsonObservable L))
    (wilsonBound : Link → ℝ)
    (wilsonBound_nonneg : ∀ L, 0 ≤ wilsonBound L)
    (wilson_bounded : ∀ L, ∀ᵐ A ∂model.μ, ‖wilsonObservable L A‖ ≤ wilsonBound L)
    (damping_integrable : Integrable (fun A => model.damping A) model.μ) :
    WittenAnalyticPathIntegral Field Link where
  model := model
  wilsonObservable := wilsonObservable
  measurable_wilsonObservable := measurable_wilsonObservable
  wilsonBound := wilsonBound
  wilsonBound_nonneg := wilsonBound_nonneg
  wilson_bounded := wilson_bounded
  damping_integrable := damping_integrable

/-- Constructor from the explicit Wilson-observable obligation package.  This
is the preferred API when the complex-action model is already fixed and the
remaining proof work concerns the Wilson-loop functional itself. -/
noncomputable def wittenAnalyticPathIntegralOfComplexActionWithWilsonObligations
    (model : MeasurePathIntegralModel Field)
    (wilsonObservable : Link → Field → ℂ)
    (H : WilsonObservableAnalyticObligations model wilsonObservable)
    (damping_integrable : Integrable (fun A => model.damping A) model.μ) :
    WittenAnalyticPathIntegral Field Link :=
  wittenAnalyticPathIntegralOfComplexAction
    model wilsonObservable H.measurable_wilsonObservable
    H.wilsonBound H.wilsonBound_nonneg H.wilson_bounded
    damping_integrable

/-- With explicit damping `L¹`, complex action plus the explicit
Wilson-observable obligation package gives the rigorous Wilson FK conclusion.
This is the non-finite-field-space route. -/
lemma complexAction_withWilsonObligations_supplies_witten_FK
    (model : MeasurePathIntegralModel Field)
    (wilsonObservable : Link → Field → ℂ)
    (H : WilsonObservableAnalyticObligations model wilsonObservable)
    (damping_integrable : Integrable (fun A => model.damping A) model.μ)
    (L : Link) :
    let W :=
      wittenAnalyticPathIntegralOfComplexActionWithWilsonObligations
        model wilsonObservable H damping_integrable
    Integrable (fun A => W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ W.wilsonBound L * W.partitionFunction := by
  exact
    (wittenAnalyticPathIntegralOfComplexActionWithWilsonObligations
      model wilsonObservable H damping_integrable).rigorousComplexFK L

/-- Finite reference measure proves the damping `L¹` obligation.  The
remaining obligations are exactly the Wilson observable's measurability and
a.e. boundedness. -/
noncomputable def wittenAnalyticPathIntegralOfComplexActionFiniteMeasure
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ]
    (wilsonObservable : Link → Field → ℂ)
    (measurable_wilsonObservable : ∀ L, Measurable (wilsonObservable L))
    (wilsonBound : Link → ℝ)
    (wilsonBound_nonneg : ∀ L, 0 ≤ wilsonBound L)
    (wilson_bounded : ∀ L, ∀ᵐ A ∂model.μ, ‖wilsonObservable L A‖ ≤ wilsonBound L) :
    WittenAnalyticPathIntegral Field Link :=
  WittenAnalyticPathIntegral.ofFiniteMeasureModel
    model wilsonObservable measurable_wilsonObservable
    wilsonBound wilsonBound_nonneg wilson_bounded

/-- Finite-measure constructor using the explicit Wilson-observable obligation
package.  The finite measure supplies damping `L¹`; the package supplies the
Wilson-loop measurability and boundedness that complex action alone does not. -/
noncomputable def wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ]
    (wilsonObservable : Link → Field → ℂ)
    (H : WilsonObservableAnalyticObligations model wilsonObservable) :
    WittenAnalyticPathIntegral Field Link :=
  wittenAnalyticPathIntegralOfComplexActionFiniteMeasure
    model wilsonObservable H.measurable_wilsonObservable
    H.wilsonBound H.wilsonBound_nonneg H.wilson_bounded

/-- A coercive imaginary action supplies the expected Gaussian damping bound.
This is the useful complex-action analytic estimate; to obtain `L¹` on an
infinite field space it must be combined with a Gaussian-integrability theorem
for the chosen measure/model. -/
lemma complexAction_coercive_supplies_exponential_damping
    {Field : Type*} [MeasurableSpace Field] [NormedAddCommGroup Field]
    (model : MeasurePathIntegralModel Field)
    (coer : CoercivityCondition (Φ := Field))
    (hbound : ∀ A : Field, coer.C * ‖A‖ ^ 2 ≤ model.actionIm A) :
    ∀ A : Field,
      model.damping A ≤ Real.exp (-coer.C * ‖A‖ ^ 2 / model.hbar) := by
  intro A
  convert
    (coercivity_implies_exponential_damping
      model.actionIm model.hbar model.hbar_pos coer A (hbound A)) using 2
  unfold MeasurePathIntegralModel.damping MeasurePathIntegralModel.actionImScaled
    path_integral_damping
  congr 1
  ring

/-- Once the finite-measure constructor builds the Witten carrier, the repo's
rigorous complex Feynman-Kac theorem immediately gives integrability and the
Wilson norm bound. -/
lemma complexActionFiniteMeasure_supplies_witten_FK
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ]
    (wilsonObservable : Link → Field → ℂ)
    (measurable_wilsonObservable : ∀ L, Measurable (wilsonObservable L))
    (wilsonBound : Link → ℝ)
    (wilsonBound_nonneg : ∀ L, 0 ≤ wilsonBound L)
    (wilson_bounded : ∀ L, ∀ᵐ A ∂model.μ, ‖wilsonObservable L A‖ ≤ wilsonBound L)
    (L : Link) :
    let W :=
      wittenAnalyticPathIntegralOfComplexActionFiniteMeasure
        model wilsonObservable measurable_wilsonObservable
        wilsonBound wilsonBound_nonneg wilson_bounded
    Integrable (fun A => W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ W.wilsonBound L * W.partitionFunction := by
  exact
    (wittenAnalyticPathIntegralOfComplexActionFiniteMeasure
      model wilsonObservable measurable_wilsonObservable
      wilsonBound wilsonBound_nonneg wilson_bounded).rigorousComplexFK L

/-- With a finite reference measure, complex action plus the explicit
Wilson-observable obligation package gives the rigorous Wilson FK conclusion. -/
lemma complexActionFiniteMeasure_withWilsonObligations_supplies_witten_FK
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ]
    (wilsonObservable : Link → Field → ℂ)
    (H : WilsonObservableAnalyticObligations model wilsonObservable)
    (L : Link) :
    let W :=
      wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
        model wilsonObservable H
    Integrable (fun A => W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ W.wilsonBound L * W.partitionFunction := by
  exact
    (wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
      model wilsonObservable H).rigorousComplexFK L

/-- Finite-measure unitary/norm-one Wilson observables give rigorous Wilson
FK integrals with the sharp bound by the partition function. -/
lemma complexActionFiniteMeasure_normOneWilson_supplies_witten_FK
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ]
    (wilsonObservable : Link → Field → ℂ)
    (hMeas : ∀ L, Measurable (wilsonObservable L))
    (hBound : ∀ L A, ‖wilsonObservable L A‖ ≤ 1)
    (L : Link) :
    let H :=
      WilsonObservableAnalyticObligations.ofNormLeOne
        (model := model) (wilsonObservable := wilsonObservable) hMeas hBound
    let W :=
      wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
        model wilsonObservable H
    Integrable (fun A => W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ W.partitionFunction := by
  let H :=
    WilsonObservableAnalyticObligations.ofNormLeOne
      (model := model) (wilsonObservable := wilsonObservable) hMeas hBound
  let W :=
    wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
      model wilsonObservable H
  have h := W.rigorousComplexFK L
  exact ⟨h.1, by
    simpa [W, H, wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations,
      wittenAnalyticPathIntegralOfComplexActionFiniteMeasure,
      WittenAnalyticPathIntegral.ofFiniteMeasureModel,
      WilsonObservableAnalyticObligations.ofNormLeOne,
      WilsonObservableAnalyticObligations.ofUniformBound,
      WilsonObservableAnalyticObligations.ofPointwiseBound] using h.2⟩

/-- Constant topological/charge-sector Wilson data are automatically measurable
and bounded, so finite-measure complex action gives a rigorous Wilson FK
integral for them. -/
lemma complexActionFiniteMeasure_constantWilson_supplies_witten_FK
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ]
    (value : Link → ℂ)
    (L : Link) :
    let H := WilsonObservableAnalyticObligations.ofConstant (model := model) value
    let W :=
      wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
        model (fun L _ => value L) H
    Integrable (fun A => W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ ‖value L‖ * W.partitionFunction := by
  let H := WilsonObservableAnalyticObligations.ofConstant (model := model) value
  let W :=
    wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
      model (fun L _ => value L) H
  have h := W.rigorousComplexFK L
  exact ⟨h.1, by
    simpa [W, H, wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations,
      wittenAnalyticPathIntegralOfComplexActionFiniteMeasure,
      WittenAnalyticPathIntegral.ofFiniteMeasureModel,
      WilsonObservableAnalyticObligations.ofConstant] using h.2⟩

/-- Topological-spin Wilson data are constant charge-sector observables at
this analytic level, hence automatically measurable and bounded. -/
lemma complexActionFiniteMeasure_topologicalSpinWilson_supplies_witten_FK
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ]
    (k : ℕ) (a : Fin k) :
    let value : Fin k → ℂ := fun q => wilsonTopologicalSpin k q
    let H := WilsonObservableAnalyticObligations.ofConstant (model := model) value
    let W :=
      wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
        model (fun q _ => value q) H
    Integrable (fun A => W.wilsonObservable a A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral a‖ ≤ ‖wilsonTopologicalSpin k a‖ * W.partitionFunction := by
  simpa using
    (complexActionFiniteMeasure_constantWilson_supplies_witten_FK
      (model := model) (value := fun q : Fin k => wilsonTopologicalSpin k q) a)

/-- Wilson braiding phases are also constant charge-sector observables here;
their Wilson FK obligations reduce to the constant-observable route. -/
lemma complexActionFiniteMeasure_braidingPhaseWilson_supplies_witten_FK
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ]
    (k : ℕ) (ab : Fin k × Fin k) :
    let value : Fin k × Fin k → ℂ := fun p => wilsonBraidingPhase k p.1 p.2
    let H := WilsonObservableAnalyticObligations.ofConstant (model := model) value
    let W :=
      wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
        model (fun p _ => value p) H
    Integrable (fun A => W.wilsonObservable ab A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral ab‖ ≤ ‖wilsonBraidingPhase k ab.1 ab.2‖ * W.partitionFunction := by
  simpa using
    (complexActionFiniteMeasure_constantWilson_supplies_witten_FK
      (model := model) (value := fun p : Fin k × Fin k => wilsonBraidingPhase k p.1 p.2) ab)

/-- Verlinde `S`-matrix entries are constant charge-sector Wilson data for the
analytic FK lane. -/
lemma complexActionFiniteMeasure_verlindeSMatrixWilson_supplies_witten_FK
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ]
    (k : ℕ) (ab : Fin k × Fin k) :
    let value : Fin k × Fin k → ℂ := fun p => cswSMatrix k p.1 p.2
    let H := WilsonObservableAnalyticObligations.ofConstant (model := model) value
    let W :=
      wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
        model (fun p _ => value p) H
    Integrable (fun A => W.wilsonObservable ab A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral ab‖ ≤ ‖cswSMatrix k ab.1 ab.2‖ * W.partitionFunction := by
  simpa using
    (complexActionFiniteMeasure_constantWilson_supplies_witten_FK
      (model := model) (value := fun p : Fin k × Fin k => cswSMatrix k p.1 p.2) ab)

/-- The analytic Wilson braiding carrier is the same constant observable as
the conjugated Verlinde `S`-matrix entry, up to the standard `√k`
normalization. -/
lemma braidingPhaseWilson_value_eq_verlindeSMatrix
    (k : ℕ) (hk : 0 < k) (ab : Fin k × Fin k) :
    wilsonBraidingPhase k ab.1 ab.2 =
      (Real.sqrt k : ℂ) * (starRingEnd ℂ) (cswSMatrix k ab.1 ab.2) :=
  wilsonBraidingPhase_eq_S k hk ab.1 ab.2

/-- A half-integer topological-spin Wilson line is the fermion sign `-1`, so
as a selected constant Wilson observable it has the sharp unit bound. -/
lemma complexActionFiniteMeasure_fermionTopologicalSpinWilson_supplies_witten_FK
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ]
    (k : ℕ) (hk : 0 < k) (a : Fin k) (ha : (a.val : ℝ) ^ 2 = k) :
    let wilsonObservable : Unit → Field → ℂ := fun _ _ => wilsonTopologicalSpin k a
    let H :=
      WilsonObservableAnalyticObligations.ofNormLeOne
        (model := model) (wilsonObservable := wilsonObservable)
        (fun _ => measurable_const)
        (fun _ _ => by
          change ‖wilsonTopologicalSpin k a‖ ≤ 1
          rw [wilsonTopologicalSpin_fermion k hk a ha]
          simp)
    let W :=
      wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
        model wilsonObservable H
    Integrable (fun A => W.wilsonObservable () A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral ()‖ ≤ W.partitionFunction := by
  simpa using
    (complexActionFiniteMeasure_normOneWilson_supplies_witten_FK
      (model := model)
      (wilsonObservable := fun _ : Unit => fun _ : Field => wilsonTopologicalSpin k a)
      (hMeas := fun _ => measurable_const)
      (hBound := fun _ _ => by
        rw [wilsonTopologicalSpin_fermion k hk a ha]
        simp)
      ())

/-- A Witten Wilson-line orientation carrier produces constant line-observable
data in the analytic FK lane.  Field-dependent holonomy regularity is still a
separate theorem; this covers the already-formalized source-level Wilson
carrier. -/
lemma complexActionFiniteMeasure_wilsonLineCarrier_supplies_witten_FK
    {Curve Rep : Type*}
    (model : MeasurePathIntegralModel Field) [IsFiniteMeasure model.μ]
    (WLine : WilsonLineOrientationCarrier Curve Rep) (CR : Curve × Rep) :
    let value : Curve × Rep → ℂ := fun p => WLine.wilson p.1 p.2
    let H := WilsonObservableAnalyticObligations.ofConstant (model := model) value
    let W :=
      wittenAnalyticPathIntegralOfComplexActionFiniteMeasureWithWilsonObligations
        model (fun p _ => value p) H
    Integrable (fun A => W.wilsonObservable CR A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral CR‖ ≤ ‖WLine.wilson CR.1 CR.2‖ * W.partitionFunction := by
  simpa using
    (complexActionFiniteMeasure_constantWilson_supplies_witten_FK
      (model := model) (value := fun p : Curve × Rep => WLine.wilson p.1 p.2) CR)

/-- Witten's reverse-orientation/dual-representation identity is an equality
of the corresponding constant field observables in the analytic bridge. -/
lemma wilsonLineCarrier_reverseDual_same_constantObservable
    {Field' Curve Rep : Type*}
    (WLine : WilsonLineOrientationCarrier Curve Rep) (C : Curve) (R : Rep) :
    (fun _ : Field' => WLine.wilson (WLine.reverseCurve C) (WLine.dualRep R)) =
      (fun _ : Field' => WLine.wilson C R) := by
  funext _
  exact wilson_reverse_dual_invariant WLine C R


/-- The minimal observable class certified directly by one Witten analytic
Wilson integral: the vacuum observable and one selected Wilson observable. -/
def wittenWilsonAdmissible
    (W : WittenAnalyticPathIntegral Field Link) (L : Link)
    (O : Field → ℂ) : Prop :=
  O = (fun _ => 1) ∨ O = W.wilsonObservable L

/-- The vacuum observable belongs to the minimal Witten admissible class. -/
lemma wittenWilsonAdmissible_one
    (W : WittenAnalyticPathIntegral Field Link) (L : Link) :
    wittenWilsonAdmissible W L (fun _ => 1) :=
  Or.inl rfl

/-- The selected Wilson observable belongs to the minimal Witten
admissible class. -/
lemma wittenWilsonAdmissible_wilson
    (W : WittenAnalyticPathIntegral Field Link) (L : Link) :
    wittenWilsonAdmissible W L (W.wilsonObservable L) :=
  Or.inr rfl

/-- Witten's FK damping hypothesis also gives direct integrability for the
vacuum observable. -/
lemma wittenVacuum_integrable
    (W : WittenAnalyticPathIntegral Field Link) :
    Integrable (fun A => W.model.weight A * (1 : ℂ)) W.model.μ := by
  have hOneBound : ∀ᵐ A ∂W.model.μ, ‖(1 : ℂ)‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun _ => by simp
  have hFK :=
    W.model.complexFKExpectation_integrable
      W.damping_integrable
      (fun _ : Field => (1 : ℂ))
      measurable_const
      1
      zero_le_one
      hOneBound
  simpa [mul_comm] using hFK

/-- The minimal Witten admissible class has direct integrability for all
of its observables. -/
lemma wittenWilsonAdmissible_integrable
    (W : WittenAnalyticPathIntegral Field Link) (L : Link)
    {O : Field → ℂ}
    (hO : wittenWilsonAdmissible W L O) :
    Integrable (fun A => W.model.weight A * O A) W.model.μ := by
  rcases hO with hO | hO
  · rw [hO]
    exact wittenVacuum_integrable W
  · rw [hO]
    exact wittenWilson_integrable W L

/-- Identity gauge pullback preserves the minimal Witten admissible
class. -/
lemma wittenWilsonAdmissible_gauge_id
    (W : WittenAnalyticPathIntegral Field Link) (L : Link)
    {O : Field → ℂ}
    (hO : wittenWilsonAdmissible W L O) :
    wittenWilsonAdmissible W L (fun A : Field => O (id A)) := by
  simpa using hO

/-- The identity gauge transform gives the Ward identity in the direct Witten
analytic embedding. -/
lemma wittenWilson_gaugeInvariant_id
    (W : WittenAnalyticPathIntegral Field Link) (L : Link)
    {O : Field → ℂ}
    (_hO : wittenWilsonAdmissible W L O) :
    W.model.unnormalizedExpectation (fun A : Field => O (id A)) =
      W.model.unnormalizedExpectation O :=
  rfl

/-- Witten's analytic path integral as a cutoff-free functional integral for
the vacuum observable and one Wilson loop. -/
def wittenWilsonCutoffFreeFunctionalIntegral
    (W : WittenAnalyticPathIntegral Field Link) (L : Link) :
    CutoffFreeAnalyticFunctionalIntegral Field where
  model := W.model
  admissible := wittenWilsonAdmissible W L
  admissible_one := wittenWilsonAdmissible_one W L
  integrable := fun hO => wittenWilsonAdmissible_integrable W L hO
  gaugeTransform := id
  admissible_gauge := fun hO => wittenWilsonAdmissible_gauge_id W L hO
  gauge_invariant := fun hO => wittenWilson_gaugeInvariant_id W L hO

/-- The direct Witten cutoff-free amplitude is exactly Witten's Wilson
integral. -/
lemma wittenWilsonCutoffFreeFunctionalIntegral_amplitude_wilson
    (W : WittenAnalyticPathIntegral Field Link) (L : Link) :
    (wittenWilsonCutoffFreeFunctionalIntegral W L).amplitude
      (W.wilsonObservable L)
      (wittenWilsonAdmissible_wilson W L) =
        W.wilsonIntegral L := by
  exact unnormalizedExpectation_eq_wittenWilsonIntegral W L

/-- The direct Witten cutoff-free amplitude inherits the FK norm bound. -/
lemma wittenWilsonCutoffFreeFunctionalIntegral_amplitude_norm_le
    (W : WittenAnalyticPathIntegral Field Link) (L : Link) :
    ‖(wittenWilsonCutoffFreeFunctionalIntegral W L).amplitude
        (W.wilsonObservable L)
        (wittenWilsonAdmissible_wilson W L)‖
      ≤ W.wilsonBound L * W.partitionFunction := by
  rw [wittenWilsonCutoffFreeFunctionalIntegral_amplitude_wilson W L]
  exact W.wilsonIntegral_norm_le L

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral

end

end
