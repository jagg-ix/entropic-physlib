/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenChernSimonsRepo
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ConcreteSynthesis
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ThetaModular
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ThetaResummation
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QFT.PathIntegral.RigorousComplexFK
public import Physlib.QFT.PathIntegral.FeynmanKac
meta import Zil

/-!
# Witten's Chern-Simons construction of the Jones polynomial

This module formalizes the Lean-checkable algebraic core extracted from E. Witten,
*Quantum Field Theory and the Jones Polynomial*, Commun. Math. Phys. **121** (1989), 351-399.

The full undamped Chern-Simons oscillatory functional integral is still isolated as an analytic
obligation: the repository's rigorous complex path-integral lane is the entropically damped
Feynman-Kac/Bochner-integrable class (`QFT.PathIntegral.RigorousComplexFK`).  This file therefore
formalizes Witten's construction in two layers:

* Wilson-line orientation/dual-representation invariance, as a carrier;
* normalized link expectation values and the product rule for unlinked unknots;
* the skein relation as a three-term linear relation, with solved overcrossing and smoothing forms;
* framing shifts as a multiplicative phase law;
* surgery on a solid torus as a finite Verlinde-basis sum;
* Witten's genus-one formulas `Z(S³)=S₀₀`, `Z(S³;Rⱼ)=S₀,dual(j)`, and the surgery identity behind
  Verlinde diagonalization;
* the concrete CSW item-9 layer: Poisson/theta resummation, finite `S`-matrix Verlinde fusion,
  Wilson/Verlinde operators, and the torus geometric-quantization dimension count;
* a measurable analytic path-integral carrier whose partition function and Wilson expectations are
  genuine Bochner integrals, with integrability and norm bounds proved by the existing rigorous
  complex Feynman-Kac formalization;
* a concrete bridge back to the finite local CSW action, gauge invariance, flatness, and torus Hilbert
  finite-dimensionality already formalized in `ChernSimons.ConcreteSynthesis`.

## References

* E. Witten, *Quantum Field Theory and the Jones Polynomial*, Commun. Math. Phys. **121** (1989), 351-399.
  Local source: `qft-witten-polynomials.pdf`.
* Repo carriers: `ChernSimons.ConcreteSynthesis`, `ChernSimons.TorusHilbert`,
  `ChernSimons.ModularRepresentation`, `ChernSimons.ThetaResummation`,
  `ChernSimons.WittenChernSimonsRepo`.


-/

set_option autoImplicit false

open scoped BigOperators
open MeasureTheory
open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity


/-- Local bibliographic/source record for Witten's Jones-polynomial paper. -/
structure WittenJonesPaperReference where
  title : String
  author : String
  journal : String
  pages : String
  localPdf : String
  deriving Repr, DecidableEq

/-- The local Witten source inspected for this formalization. -/
def wittenJonesPaperReference : WittenJonesPaperReference :=
  { title := "Quantum Field Theory and the Jones Polynomial"
    author := "Edward Witten"
    journal := "Communications in Mathematical Physics 121 (1989)"
    pages := "351-399"
    localPdf := "qft-witten-polynomials.pdf" }

/-- Stable anchors for the Witten 1989 claims formalized below. -/
inductive WittenJonesAnchor where
  | chernSimonsAction
  | wilsonLines
  | jonesExpectation
  | framingLaw
  | skeinRelation
  | surgeryFormula
  | genusOneVerlindeBasis
  | s3Partition
  | verlindeDiagonalization
  | braidTrace
  deriving Repr, DecidableEq

/-- Paper locator for each formalized Witten 1989 anchor. -/
def WittenJonesAnchor.paperLabel : WittenJonesAnchor → String
  | .chernSimonsAction => "Section 1, equations (1.3)-(1.4)"
  | .wilsonLines => "Section 1, equations (1.5)-(1.6)"
  | .jonesExpectation => "Section 1 and Section 4.1"
  | .framingLaw => "Section 2, around equations (2.33); Section 4.1"
  | .skeinRelation => "Section 4.1, equations (4.9)-(4.22)"
  | .surgeryFormula => "Section 4.2-4.3, equations (4.25)-(4.28)"
  | .genusOneVerlindeBasis => "Section 4.3"
  | .s3Partition => "Section 4.5, equations (4.37)-(4.43)"
  | .verlindeDiagonalization => "Section 4.5, equations (4.45)-(4.54)"
  | .braidTrace => "Section 4.6"

/-- A Wilson-line carrier for Witten (1.5): reversing the oriented curve and replacing the representation
by the dual/conjugate leaves the Wilson observable unchanged. -/
structure WilsonLineOrientationCarrier (Curve Rep : Type*) where
  wilson : Curve → Rep → ℂ
  reverseCurve : Curve → Curve
  dualRep : Rep → Rep
  reverse_dual_invariant : ∀ C R, wilson (reverseCurve C) (dualRep R) = wilson C R

/-- **[Witten (1.5), orientation/dual representation]** Wilson lines are unchanged by reversing the curve
orientation while replacing the representation by the dual/conjugate representation. -/
lemma wilson_reverse_dual_invariant {Curve Rep : Type*}
    (W : WilsonLineOrientationCarrier Curve Rep) (C : Curve) (R : Rep) :
    W.wilson (W.reverseCurve C) (W.dualRep R) = W.wilson C R :=
  W.reverse_dual_invariant C R


/-- Witten's normalized expectation value `<L> = Z(S³;L)/Z(S³)`. -/
noncomputable def normalizedExpectation (vacuumZ linkZ : ℂ) : ℂ :=
  linkZ / vacuumZ

/-- The normalized expectation of a finite unlink: the product of normalized expectations of its
unknotted components, Witten (4.7). -/
def unlinkNormalizedExpectation {Rep : Type*} (unknot : Rep → ℂ) : List Rep → ℂ
  | [] => 1
  | R :: Rs => unknot R * unlinkNormalizedExpectation unknot Rs

/-- **[Witten (4.7)]** The normalized expectation for a split unlink is multiplicative. -/
lemma unlinkNormalizedExpectation_append {Rep : Type*} (unknot : Rep → ℂ)
    (Rs Ss : List Rep) :
    unlinkNormalizedExpectation unknot (Rs ++ Ss) =
      unlinkNormalizedExpectation unknot Rs * unlinkNormalizedExpectation unknot Ss := by
  induction Rs with
  | nil =>
      simp [unlinkNormalizedExpectation]
  | cons R Rs ih =>
      simp [unlinkNormalizedExpectation, ih, mul_assoc]

/-- **[Connected-sum normalization]** If Witten's connected-sum identity
`Z(L₁#L₂) Z(C) = Z(L₁) Z(L₂)` holds and the unknot amplitude is nonzero, the connected-sum partition
function is the quotient `Z(L₁)Z(L₂)/Z(C)`. -/
lemma connected_sum_partition_solve (Zsum Zunknot Z₁ Z₂ : ℂ) (hC : Zunknot ≠ 0)
    (h : Zsum * Zunknot = Z₁ * Z₂) :
    Zsum = Z₁ * Z₂ / Zunknot := by
  rw [← h]
  field_simp [hC]

/-- **[Normalized connected-sum product]** Witten (4.55) becomes multiplicativity after dividing by the
unknot amplitude. -/
lemma normalized_connected_sum_multiplicative (Zsum Zunknot Z₁ Z₂ : ℂ)
    (hC : Zunknot ≠ 0) (h : Zsum * Zunknot = Z₁ * Z₂) :
    normalizedExpectation Zunknot Zsum =
      normalizedExpectation Zunknot Z₁ * normalizedExpectation Zunknot Z₂ := by
  unfold normalizedExpectation
  rw [connected_sum_partition_solve Zsum Zunknot Z₁ Z₂ hC h]
  field_simp [hC]


/-- Witten's three local link pictures in the skein relation: overcrossing, smoothing, undercrossing. -/
structure WittenSkeinTriple where
  overCrossing : ℂ
  smoothing : ℂ
  underCrossing : ℂ

/-- A three-term skein relation `α L₊ + β L₀ + γ L₋ = 0`, Witten (4.11)/(4.22). -/
def WittenSkeinRelation (α β γ : ℂ) (T : WittenSkeinTriple) : Prop :=
  α * T.overCrossing + β * T.smoothing + γ * T.underCrossing = 0

/-- **[Skein solves the overcrossing]** If `α ≠ 0`, Witten's skein relation determines `L₊` from
`L₀` and `L₋`. -/
lemma skein_solve_overcrossing (α β γ : ℂ) (T : WittenSkeinTriple) (hα : α ≠ 0)
    (h : WittenSkeinRelation α β γ T) :
    T.overCrossing = -(β * T.smoothing + γ * T.underCrossing) / α := by
  have hsum : α * T.overCrossing + (β * T.smoothing + γ * T.underCrossing) = 0 := by
    simpa [WittenSkeinRelation, add_assoc] using h
  have hmain : α * T.overCrossing = -(β * T.smoothing + γ * T.underCrossing) := by
    calc
      α * T.overCrossing = α * T.overCrossing + (β * T.smoothing + γ * T.underCrossing)
          - (β * T.smoothing + γ * T.underCrossing) := by ring
      _ = 0 - (β * T.smoothing + γ * T.underCrossing) := by rw [hsum]
      _ = -(β * T.smoothing + γ * T.underCrossing) := by ring
  have hcancel : (α * T.overCrossing) / α = T.overCrossing := by
    field_simp [hα]
  rw [← hcancel, hmain]

/-- **[Skein solves the smoothing]** If `β ≠ 0`, Witten's skein relation determines `L₀` from `L₊`
and `L₋`; this is the algebraic step used in the crossing-reduction recursion. -/
lemma skein_solve_smoothing (α β γ : ℂ) (T : WittenSkeinTriple) (hβ : β ≠ 0)
    (h : WittenSkeinRelation α β γ T) :
    T.smoothing = -(α * T.overCrossing + γ * T.underCrossing) / β := by
  have hsum : β * T.smoothing + (α * T.overCrossing + γ * T.underCrossing) = 0 := by
    have h' : α * T.overCrossing + γ * T.underCrossing + β * T.smoothing = 0 := by
      simpa [WittenSkeinRelation, add_comm, add_left_comm, add_assoc] using h
    simpa [add_comm, add_left_comm, add_assoc] using h'
  have hmain : β * T.smoothing = -(α * T.overCrossing + γ * T.underCrossing) := by
    calc
      β * T.smoothing = β * T.smoothing + (α * T.overCrossing + γ * T.underCrossing)
          - (α * T.overCrossing + γ * T.underCrossing) := by ring
      _ = 0 - (α * T.overCrossing + γ * T.underCrossing) := by rw [hsum]
      _ = -(α * T.overCrossing + γ * T.underCrossing) := by ring
  have hcancel : (β * T.smoothing) / β = T.smoothing := by
    field_simp [hβ]
  rw [← hcancel, hmain]

/-- A forward framing shift by `t` twists contributes a multiplicative phase.  We keep the phase abstract:
in Witten's notation it is an exponential involving the conformal weight of the Wilson-line
representation. -/
def framingShiftFactor (phase : ℂ) (t : ℕ) : ℂ :=
  phase ^ t

/-- **[Framing shifts add]** Repeated framing shifts multiply their phase factors. -/
lemma framingShiftFactor_add (phase : ℂ) (m n : ℕ) :
    framingShiftFactor phase (m + n) =
      framingShiftFactor phase m * framingShiftFactor phase n := by
  simp [framingShiftFactor, pow_add]


/-- Witten's finite genus-one surgery sum in the Verlinde basis, equation (4.27)/(4.28). -/
noncomputable def wittenSurgerySum {Charge : Type*} [Fintype Charge]
    (K : Matrix Charge Charge ℂ) (initial : Charge) (ZwithWilson : Charge → ℂ) : ℂ :=
  ∑ j, K initial j * ZwithWilson j

/-- **[Surgery with only the trivial charge]** If the solid-torus complement contributes only the trivial
charge, Witten's surgery sum gives `Z(S³)=S₀₀`, equations (4.37)-(4.38). -/
lemma witten_surgery_trivial_charge {Charge : Type*} [Fintype Charge] [DecidableEq Charge]
    (S : Matrix Charge Charge ℂ) (zero : Charge) :
    wittenSurgerySum S zero (fun j => if j = zero then 1 else 0) = S zero zero := by
  classical
  simp [wittenSurgerySum]

/-- **[Unknotted Wilson line from the `S` matrix]** If the two-charge cylinder pairing is the duality
metric, surgery gives `Z(S³;Rⱼ)=S₀,dual(j)`, Witten (4.42)-(4.43). -/
lemma witten_unknot_partition_from_smatrix {Charge : Type*} [Fintype Charge] [DecidableEq Charge]
    (S : Matrix Charge Charge ℂ) (zero : Charge) (dual : Charge → Charge) (j : Charge) :
    wittenSurgerySum S zero (fun i => if i = dual j then 1 else 0) = S zero (dual j) := by
  classical
  simp [wittenSurgerySum]

/-- **[Surgery plus unlink product gives Verlinde identity]** Witten's comparison of the surgery formula
with the unlinked two-component partition function yields the identity behind the Verlinde diagonalization,
equation (4.46). -/
lemma witten_verlinde_identity_from_surgery_and_unlink
    {Charge : Type*} [Fintype Charge] [DecidableEq Charge]
    (S : Matrix Charge Charge ℂ) (N : Charge → Charge → Charge → ℂ)
    (zero j k : Charge) (Z : ℂ)
    (hsurgery : Z = ∑ i, S zero i * N i j k)
    (hunlink : Z = S zero j * S zero k / S zero zero) :
    (∑ i, S zero i * N i j k) = S zero j * S zero k / S zero zero := by
  rw [← hsurgery, hunlink]

/-- **[Linked-pair amplitude from the `S` matrix]** The Hopf-link-type linked pair produced by standard
surgery has partition function `Sᵢⱼ`, Witten (4.47), represented here as a reusable carrier. -/
def wittenLinkedPairAmplitude {Charge : Type*} (S : Matrix Charge Charge ℂ)
    (i j : Charge) : ℂ :=
  S i j

/-- **[Connected linked-pair factorization]** Witten (4.49)-(4.50): if a connected link factors through a
one-dimensional two-charge Hilbert space, then its partition function is the quotient of the two linked-pair
amplitudes by the unknot amplitude. -/
lemma witten_connected_link_factorization (Zconnected Zunknot Zij Zik : ℂ) (hZ : Zunknot ≠ 0)
    (h : Zconnected * Zunknot = Zij * Zik) :
    Zconnected = Zij * Zik / Zunknot :=
  connected_sum_partition_solve Zconnected Zunknot Zij Zik hZ h

/-- The Witten genus-one surgery kernel specialized to the formalized CSW Verlinde `S` matrix. -/
noncomputable def cswSMatrixKernel (k : ℕ) : Matrix (Fin k) (Fin k) ℂ :=
  fun a b => cswSMatrix k a b

/-- **[Witten surgery uses the CSW `S` matrix]** The abstract genus-one surgery sum becomes the finite
`S`-matrix sum over CSW charge sectors. -/
lemma wittenSurgerySum_cswSMatrix_eq (k : ℕ) (initial : Fin k) (ZwithWilson : Fin k → ℂ) :
    wittenSurgerySum (cswSMatrixKernel k) initial ZwithWilson =
      ∑ j : Fin k, cswSMatrix k initial j * ZwithWilson j :=
  rfl

/-- **[Witten unknot formula specialized to CSW]** With the delta charge vector in the solid torus,
Witten's `Z(S³;R_j)=S_{0j}` formula is exactly the CSW `S`-matrix entry. -/
lemma witten_csw_surgery_delta_charge (k : ℕ) (hk : 0 < k) (j : Fin k) :
    wittenSurgerySum (cswSMatrixKernel k) (cswZeroCharge k hk) (cswChargeBasis k j) =
      cswSMatrix k (cswZeroCharge k hk) j := by
  classical
  simp [wittenSurgerySum, cswSMatrixKernel, cswChargeBasis]

/-- **[Wilson/Verlinde operator in Witten's charge basis]** The Wilson operator associated to charge `a`
acts on the charge basis by the formalized Verlinde fusion coefficient. -/
lemma witten_csw_wilsonVerlindeOperator_basis_rule (k : ℕ) (a b c : Fin k) :
    cswWilsonVerlindeOperator k a (cswChargeBasis k b) c =
      cswFusionCoeff k a b c :=
  cswWilsonVerlindeOperator_basis k a b c


/-- **Witten analytic Chern-Simons path integral, in the repo's rigorous FK lane.**

`Path` is the measurable configuration/path space, `Link` indexes Wilson-link observables, and
`model` is the already-formalized `MeasurePathIntegralModel` with complex weight
`exp(i S_R/ℏ - S_I/ℏ)`.  The analytic obligations are exactly the ones needed by
`QFT.PathIntegral.RigorousComplexFK`:

* the entropic/FK damping is integrable;
* each Wilson observable is measurable;
* each Wilson observable has an a.e. finite bound.

Once those obligations are supplied, Lean checks that the Wilson expectation is a genuine Bochner
integral and satisfies the FK norm bound. -/
structure WittenAnalyticPathIntegral (Path Link : Type*) [MeasurableSpace Path] where
  /-- Measurable complex-action path-integral model. -/
  model : MeasurePathIntegralModel Path
  /-- Wilson-link observable `W_L(A)` on the path/configuration space. -/
  wilsonObservable : Link → Path → ℂ
  /-- Measurability of each Wilson observable. -/
  measurable_wilsonObservable : ∀ L, Measurable (wilsonObservable L)
  /-- A finite a.e. bound for each Wilson observable. -/
  wilsonBound : Link → ℝ
  /-- The observable bound is nonnegative. -/
  wilsonBound_nonneg : ∀ L, 0 ≤ wilsonBound L
  /-- Each Wilson observable is a.e. bounded by its declared bound. -/
  wilson_bounded : ∀ L, ∀ᵐ A ∂model.μ, ‖wilsonObservable L A‖ ≤ wilsonBound L
  /-- The FK/entropic damping is integrable; this is the real analytic convergence obligation. -/
  damping_integrable : Integrable (fun A => model.damping A) model.μ

namespace WittenAnalyticPathIntegral

variable {Path Link : Type*} [MeasurableSpace Path]

/-- Finite reference measure proves the FK damping integrability obligation, because the existing
`MeasurePathIntegralModel` proves `0 < damping ≤ 1`. This covers finite-dimensional/regularized
Chern-Simons path-integral models. -/
lemma damping_integrable_of_finiteMeasure
    (model : MeasurePathIntegralModel Path) [IsFiniteMeasure model.μ] :
    Integrable (fun A => model.damping A) model.μ := by
  refine Integrable.mono'
    (g := fun _ : Path => (1 : ℝ))
    (integrable_const 1)
    model.measurable_damping.aestronglyMeasurable
    ?_
  exact Filter.Eventually.of_forall fun A => by
    rw [Real.norm_of_nonneg (model.damping_pos A).le]
    exact model.damping_le_one A

/-- Constructor for the regularized finite-measure analytic Witten path integral.  The only remaining
observable obligations are Wilson measurability and an a.e. finite bound. -/
noncomputable def ofFiniteMeasureModel
    (model : MeasurePathIntegralModel Path) [IsFiniteMeasure model.μ]
    (wilsonObservable : Link → Path → ℂ)
    (measurable_wilsonObservable : ∀ L, Measurable (wilsonObservable L))
    (wilsonBound : Link → ℝ)
    (wilsonBound_nonneg : ∀ L, 0 ≤ wilsonBound L)
    (wilson_bounded : ∀ L, ∀ᵐ A ∂model.μ, ‖wilsonObservable L A‖ ≤ wilsonBound L) :
    WittenAnalyticPathIntegral Path Link where
  model := model
  wilsonObservable := wilsonObservable
  measurable_wilsonObservable := measurable_wilsonObservable
  wilsonBound := wilsonBound
  wilsonBound_nonneg := wilsonBound_nonneg
  wilson_bounded := wilson_bounded
  damping_integrable := damping_integrable_of_finiteMeasure model

/-- The analytic Witten partition function `Z = ∫ exp(-S_I/ℏ) dμ` in the rigorous FK lane. -/
noncomputable def partitionFunction (W : WittenAnalyticPathIntegral Path Link) : ℝ :=
  W.model.partitionFunction

/-- The unnormalised Wilson-link path integral `∫ W_L(A) exp(iS_R/ℏ - S_I/ℏ) dμ`. -/
noncomputable def wilsonIntegral (W : WittenAnalyticPathIntegral Path Link) (L : Link) : ℂ :=
  W.model.complexFKExpectation (W.wilsonObservable L)

/-- The normalized Wilson expectation `<L> = Z(L)/Z`. -/
noncomputable def normalizedWilsonExpectation
    (W : WittenAnalyticPathIntegral Path Link) (L : Link) : ℂ :=
  normalizedExpectation (W.partitionFunction : ℂ) (W.wilsonIntegral L)

/-- The partition function is the integral of the FK damping factor. -/
lemma partitionFunction_eq_integral_damping
    (W : WittenAnalyticPathIntegral Path Link) :
    W.partitionFunction = ∫ A, W.model.damping A ∂W.model.μ :=
  rfl

/-- The Wilson path integral is the Bochner integral of Wilson observable times complex weight. -/
lemma wilsonIntegral_eq_integral
    (W : WittenAnalyticPathIntegral Path Link) (L : Link) :
    W.wilsonIntegral L =
      ∫ A, W.wilsonObservable L A * W.model.weight A ∂W.model.μ :=
  rfl

/-- The analytic Witten weight factorizes as oscillatory phase times FK damping. -/
lemma weight_factorizes (W : WittenAnalyticPathIntegral Path Link) (A : Path) :
    W.model.weight A =
      Complex.exp ((W.model.actionReScaled A : ℂ) * Complex.I) *
        (Real.exp (-(W.model.actionImScaled A)) : ℂ) :=
  W.model.weight_factorizes A

/-- The norm of the analytic Witten weight is exactly the FK/entropic damping. -/
lemma weight_norm_is_damping (W : WittenAnalyticPathIntegral Path Link) (A : Path) :
    ‖W.model.weight A‖ = W.model.damping A := by
  rw [W.model.weight_norm_is_damping]
  rfl

/-- The analytic Witten weight has the standard Bochner bound `‖w(A)‖ ≤ 1`. -/
lemma weight_bochner_bounded (W : WittenAnalyticPathIntegral Path Link) (A : Path) :
    ‖W.model.weight A‖ ≤ 1 :=
  W.model.weight_bochner_bounded A

/-- In the pure Chern-Simons specialization `S_I = 0`, the analytic weight is a unit-modulus
oscillatory phase.  For finite-measure regularizations this combines with `ofFiniteMeasureModel` to give
the undamped regularized Witten path integral. -/
lemma weight_norm_one_of_actionIm_zero
    (W : WittenAnalyticPathIntegral Path Link) (hIm : ∀ A, W.model.actionIm A = 0) (A : Path) :
    ‖W.model.weight A‖ = 1 := by
  rw [W.model.weight_norm_is_damping]
  unfold MeasurePathIntegralModel.actionImScaled
  simp [hIm A]

/-- **Witten Wilson integral is Bochner-integrable.**

This is exactly the existing rigorous complex Feynman-Kac theorem specialized to Wilson observables. -/
lemma wilsonIntegral_integrable
    (W : WittenAnalyticPathIntegral Path Link) (L : Link) :
    Integrable (fun A => W.wilsonObservable L A * W.model.weight A) W.model.μ :=
  W.model.complexFKExpectation_integrable W.damping_integrable
    (W.wilsonObservable L) (W.measurable_wilsonObservable L)
    (W.wilsonBound L) (W.wilsonBound_nonneg L) (W.wilson_bounded L)

/-- **FK norm bound for Witten Wilson integrals.** -/
lemma wilsonIntegral_norm_le
    (W : WittenAnalyticPathIntegral Path Link) (L : Link) :
    ‖W.wilsonIntegral L‖ ≤ W.wilsonBound L * W.partitionFunction := by
  simpa [wilsonIntegral, partitionFunction] using
    W.model.complexFKExpectation_norm_le W.damping_integrable
      (W.wilsonObservable L) (W.measurable_wilsonObservable L)
      (W.wilsonBound L) (W.wilsonBound_nonneg L) (W.wilson_bounded L)

/-- **Full rigorous complex FK package for Witten Wilson observables.**

Lean checks both analytic conclusions from the stated FK obligations: the Wilson integral exists as a
Bochner integral, and its norm is controlled by the damping partition function. -/
lemma rigorousComplexFK
    (W : WittenAnalyticPathIntegral Path Link) (L : Link) :
    Integrable (fun A => W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ W.wilsonBound L * W.partitionFunction := by
  simpa [wilsonIntegral, partitionFunction] using
    W.model.complex_FK_rigorous W.damping_integrable
      (W.wilsonObservable L) (W.measurable_wilsonObservable L)
      (W.wilsonBound L) (W.wilsonBound_nonneg L) (W.wilson_bounded L)

/-- The normalized Wilson expectation is the quotient of the Wilson integral by the partition function. -/
lemma normalizedWilsonExpectation_eq_div
    (W : WittenAnalyticPathIntegral Path Link) (L : Link) :
    W.normalizedWilsonExpectation L = W.wilsonIntegral L / (W.partitionFunction : ℂ) :=
  rfl

/-! ### Links to the repo's master complex-action / Lorentzian path-integral kernels -/

/-- **Witten analytic weight = master complex-action weight.**

The per-configuration weight of the Witten/Jones analytic carrier is exactly the repository's
`complexActionPathIntegralWeight`. -/
lemma weight_eq_master_complexActionWeight
    (W : WittenAnalyticPathIntegral Path Link) (A : Path) :
    W.model.weight A =
      complexActionPathIntegralWeight
        (W.model.actionRe A) (W.model.actionIm A) W.model.hbar := by
  unfold MeasurePathIntegralModel.weight MeasurePathIntegralModel.actionReScaled
    MeasurePathIntegralModel.actionImScaled complexActionPathIntegralWeight
  congr 1
  push_cast
  ring

/-- **Witten analytic weight = Lorentzian path-integral kernel.**

This exposes the Witten/Jones Wilson integrand to all existing consumers of
`QFT.PathIntegral.lorentzianKernel`. -/
lemma weight_eq_lorentzianKernel
    (W : WittenAnalyticPathIntegral Path Link) (A : Path) :
    W.model.weight A =
      lorentzianKernel (W.model.actionRe A) (W.model.actionIm A) W.model.hbar := by
  rw [W.weight_eq_master_complexActionWeight A, complexActionPathIntegralWeight_eq_lorentzianKernel]

/-- **Witten analytic damping = Kuiken / entropy-production weight.**

The modulus of the Witten/Jones path-integral weight is the same damping weight used by the master
complex-action/entropic-time path-integral layer. -/
lemma weight_norm_eq_kuiken
    (W : WittenAnalyticPathIntegral Path Link) (A : Path) :
    ‖W.model.weight A‖ =
      kuikenWeight W.model.hbar (W.model.actionIm A) := by
  rw [W.weight_eq_master_complexActionWeight A, master_modulus_is_kuiken]

/-- **Wilson integral as a master complex-action integral.** -/
lemma wilsonIntegral_eq_master_integral
    (W : WittenAnalyticPathIntegral Path Link) (L : Link) :
    W.wilsonIntegral L =
      ∫ A, W.wilsonObservable L A *
        complexActionPathIntegralWeight
          (W.model.actionRe A) (W.model.actionIm A) W.model.hbar ∂W.model.μ := by
  rw [W.wilsonIntegral_eq_integral L]
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro A
  simpa using congrArg (fun z => W.wilsonObservable L A * z)
    (W.weight_eq_master_complexActionWeight A)

/-- **Wilson integral as a Lorentzian-kernel integral.** -/
lemma wilsonIntegral_eq_lorentzianKernel_integral
    (W : WittenAnalyticPathIntegral Path Link) (L : Link) :
    W.wilsonIntegral L =
      ∫ A, W.wilsonObservable L A *
        lorentzianKernel (W.model.actionRe A) (W.model.actionIm A) W.model.hbar ∂W.model.μ := by
  rw [W.wilsonIntegral_eq_integral L]
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro A
  simpa using congrArg (fun z => W.wilsonObservable L A * z)
    (W.weight_eq_lorentzianKernel A)

end WittenAnalyticPathIntegral

/-- **Scalar FK recognition for the Witten damping factor.**

When `S_I = ℏ · V · T`, the scalar damping in the analytic Witten weight is exactly the existing
Feynman-Kac weight at potential `V` and Euclidean time `T`. -/
lemma witten_constant_damping_is_feynman_kac
    (V T ℏ : ℝ) (hℏ : 0 < ℏ) (S_I : ℝ) (hSI : S_I = V * T * ℏ) :
    Real.exp (-(S_I / ℏ)) =
      feynman_kac_weight (fun _ : Unit => V) T () :=
  fk_euclidean_entropic_damping_correspondence V T ℏ hℏ S_I hSI

/-- **Pathwise FK damping bound for Witten-style Euclidean damping.** -/
lemma witten_pathwise_fk_weight_le_one
    (V : ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ)
    (hV : ∀ y, 0 ≤ V y) (ht : 0 ≤ t) :
    fkPathWeight V x t ≤ 1 :=
  fkPathWeight_le_one V x t hV ht

/-- **Analytic Witten path integral + finite local CSW spine.**

This packages the new analytic FK construction with the already-formalized finite local CSW facts:
Wilson expectations are rigorous Bochner integrals under the FK obligations, while the local CSW action
is gauge-invariant and vanishes on flat chiral sectors. -/
lemma witten_analytic_pathIntegral_localCSW_bridge
    {Path Link : Type*} [MeasurableSpace Path] {n : ℕ}
    (W : WittenAnalyticPathIntegral Path Link) (L : Link)
    (c : HayashiCouplings) (G H : Matrix (Fin n) (Fin n) ℂ)
    (P : LocalCSConnection n × LocalCSConnection n) (hHG : H * G = 1) :
    (Integrable (fun A => W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ W.wilsonBound L * W.partitionFunction) ∧
      localComplexCSWAction c
          (localGaugeConjugate G H P.1, localGaugeConjugate G H P.2)
        = localComplexCSWAction c P ∧
      (LocalCSFlat P.1 → LocalCSFlat P.2 → localComplexCSWAction c P = 0) :=
  ⟨W.rigorousComplexFK L,
    localComplexCSWAction_gauge_conjugate c G H P hHG,
    fun hA hAbar => localComplexCSWAction_eq_zero_of_flat c P hA hAbar⟩

/-- **Analytic Witten/Jones path integral + concrete CSW/Kálnay field bridge.**

This composes the analytic Wilson-integral construction in this file with the existing concrete CSW
synthesis layer.  Lean checks that the same imported finite CSW spine carries the WDW/torus/orthogonality
obligations and exposes the repo's Kálnay statement that fermion-field generators are represented by
Bose-bilinear words satisfying the CAR. -/
lemma witten_analytic_concreteCSW_kalnay_field_bridge
    {Path Link : Type*} [MeasurableSpace Path] {n k : ℕ}
    (W : WittenAnalyticPathIntegral Path Link) (L : Link)
    (c : HayashiCouplings) (lam ω e : ℂ) (Λ : ℝ) (hΛ : Λ < 0)
    (HR HI : ℝ) (χ : Fin k → ℂ)
    (P : LocalCSConnection n × LocalCSConnection n) (ψ : ℂ)
    (Ψ φ : Fin k × Fin k) (O : Fin k) (p : Momentum 3) (hcharge : Ψ ≠ φ) :
    (Integrable (fun A => W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ W.wilsonBound L * W.partitionFunction)
      ∧ KalnayBoseFermiFieldStatement p := by
  rcases concreteCSWBridge_satisfies_hayashi_and_field_obligations
      c lam ω e Λ hΛ HR HI χ P ψ Ψ φ O p hcharge with
    ⟨_, _, _, _, _, _, hkalnay⟩
  exact ⟨W.rigorousComplexFK L, hkalnay⟩


/-- **Witten 1989 Jones sector uses Witten's integer Chern-Simons level.**

The level entering the Jones-polynomial surgery/Verlinde sector is the same integer half-sum of the
holomorphic and antiholomorphic couplings formalized from Witten's complex Chern-Simons quantization. -/
lemma witten_jones_level_eq_half_coupling_sum (c : HayashiCouplings) :
    (holomorphicCoupling c + antiholomorphicCoupling c) / 2 = (c.level : ℂ) :=
  level_eq_half_coupling_sum c

/-- **The Witten/Jones torus character is the existing CSW theta character.** -/
lemma witten_jones_theta_eq_jacobiTheta₂ (k τ z : ℂ) :
    cswTheta k τ z = jacobiTheta₂ (k * z) (k * τ) :=
  cswTheta_eq_jacobiTheta₂ k τ z

/-- **Integer level gives the torus modular/lattice periodicities used by the Witten/Jones sector.**

This packages Witten's level quantization with the already-formalized theta-character periodicities. -/
lemma witten_jones_integer_level_theta_periodicities
    (c : HayashiCouplings) (τ z : ℂ) :
    (holomorphicCoupling c + antiholomorphicCoupling c) / 2 = (c.level : ℂ)
      ∧ cswTheta (c.level : ℂ) (τ + 2) z = cswTheta (c.level : ℂ) τ z
      ∧ cswTheta (c.level : ℂ) τ (z + 1) = cswTheta (c.level : ℂ) τ z :=
  ⟨level_eq_half_coupling_sum c,
    cswTheta_tau_add_two c.level τ z,
    cswTheta_z_add_one c.level τ z⟩

/-- **[Witten/Hayashi theta multiplet resummation]** The finite `S`-matrix sum over level-`k` charge
sectors re-sums to the single rescaled Jacobi theta. This is the honest Mathlib-backed Poisson-resummation
link used by the Witten/Jones Verlinde basis. -/
lemma witten_jones_theta_multiplet_resummation
    (k : ℕ) (hk : 0 < k) (a : Fin k) (τ z : ℂ) (hτ : 0 < τ.im) :
    (∑ b : Fin k, cswSMatrix k a b * cswThetaBasis k b τ z)
      = (1 / (Real.sqrt k : ℂ)) *
          jacobiTheta₂ (z - (a.val : ℂ) / (k : ℂ)) (τ / (k : ℂ)) :=
  cswSMatrix_thetaBasis_resummation k hk a τ z hτ

/-- **[Item 9 Poisson link plus honest resummation]** If the finite item-9 Poisson carrier supplies the
bare character-vector identity, then the same Witten/Jones charge sector is identified with the
Mathlib-backed resummed Jacobi theta. -/
lemma witten_jones_item9_poisson_to_resummed_theta
    (k : ℕ) (hk : 0 < k) (G : CSWGeometricQuantizationPackage k hk)
    (a : Fin k) (τ z : ℂ) (hτ : 0 < τ.im) :
    cswThetaBasis k a (-1 / τ) z =
      (1 / (Real.sqrt k : ℂ)) *
        jacobiTheta₂ (z - (a.val : ℂ) / (k : ℂ)) (τ / (k : ℂ)) := by
  rw [cswTheta_poisson_resummation_link k G.poisson τ z a]
  exact witten_jones_theta_multiplet_resummation k hk a τ z hτ


/-- **[Witten 1989 ↔ finite local CSW spine]** The local finite CSW action already in the repo supplies the
metric-free, gauge-covariant algebraic core of Witten's Chern-Simons action: simultaneous constant gauge
conjugation preserves the action, and flat chiral sectors make the local cubic action vanish. -/
lemma witten_local_csw_metric_free_and_gauge_invariant {n : ℕ}
    (c : HayashiCouplings) (G H : Matrix (Fin n) (Fin n) ℂ)
    (P : LocalCSConnection n × LocalCSConnection n) (hHG : H * G = 1) :
    localComplexCSWAction c
        (localGaugeConjugate G H P.1, localGaugeConjugate G H P.2)
      = localComplexCSWAction c P
      ∧ (LocalCSFlat P.1 → LocalCSFlat P.2 → localComplexCSWAction c P = 0) :=
  ⟨localComplexCSWAction_gauge_conjugate c G H P hHG,
    fun hA hAbar => localComplexCSWAction_eq_zero_of_flat c P hA hAbar⟩

/-- **[Witten genus-one Hilbert space uses the existing torus carrier]** The Verlinde-basis Hilbert space
at level `k` is finite-dimensional with rank `k` in the existing explicit torus model. -/
lemma witten_torusHilbert_finrank (k : ℕ) :
    Module.finrank ℂ (TorusHilbert k) = k :=
  torusHilbert_finrank k

/-- **[Witten diagonal torus partition is nonnegative]** The explicit diagonal genus-one invariant already
formalized for the CSW/Hayashi torus sector gives a real nonnegative partition function. -/
lemma witten_torusPartitionFunction_nonneg (k : ℕ) (χ : Fin k → ℂ) :
    0 ≤ (torusPartitionFunction k χ).re :=
  torusPartitionFunction_nonneg k χ

/-- **[Witten/Jones item-9 repo bridge]** The item-9 package is now a consumer-facing theorem in the
Witten/Jones file: it exposes the finite Poisson character-vector identity, the honest theta multiplet
resummation, Verlinde fusion, Wilson/Verlinde diagonalization, and geometric-quantization dimension count. -/
lemma witten_jones_item9_repo_bridge (k : ℕ) (hk : 0 < k)
    (G : CSWGeometricQuantizationPackage k hk) :
    (∀ τ z a,
      cswThetaBasis k a (-1 / τ) z =
        ∑ b : Fin k, cswSMatrix k a b * cswThetaBasis k b τ z) ∧
    (∀ τ z a, 0 < τ.im →
      (∑ b : Fin k, cswSMatrix k a b * cswThetaBasis k b τ z)
        = (1 / (Real.sqrt k : ℂ)) *
            jacobiTheta₂ (z - (a.val : ℂ) / (k : ℂ)) (τ / (k : ℂ))) ∧
    (∀ a b c,
      cswFusionCoeff k a b c = cswVerlindeCoefficientByS k hk a b c) ∧
    (∀ a q,
      cswWilsonVerlindeOperator k a (fun b => cswSMatrix k b q) =
        fun c => cswVerlindeEigenvalue k hk a q * cswSMatrix k c q) ∧
    Module.finrank ℂ (TorusHilbert k) = k := by
  have hItem := csw_item9_verlinde_geometric_quantization k hk G
  constructor
  · exact hItem.1
  constructor
  · intro τ z a hτ
    exact witten_jones_theta_multiplet_resummation k hk a τ z hτ
  constructor
  · exact hItem.2.1
  constructor
  · exact hItem.2.2.1
  · exact witten_torusHilbert_finrank k

/-- **[Analytic FK + local CSW + item 9 + Kálnay field bridge]** This is the broad repo-level synthesis:
the Witten Wilson observable is a rigorous complex FK integral, the local CSW spine supplies the concrete
Hayashi/Kálnay field bridge, and the same level-`k` torus sector carries item 9's Poisson/Verlinde/Wilson
operator and geometric-quantization package. -/
lemma witten_analytic_concreteCSW_item9_kalnay_field_bridge
    {Path Link : Type*} [MeasurableSpace Path] {n k : ℕ} (hk : 0 < k)
    (W : WittenAnalyticPathIntegral Path Link) (L : Link)
    (c : HayashiCouplings) (lam ω e : ℂ) (Λ : ℝ) (hΛ : Λ < 0)
    (HR HI : ℝ) (χ : Fin k → ℂ)
    (P : LocalCSConnection n × LocalCSConnection n) (ψ : ℂ)
    (Ψ φ : Fin k × Fin k) (O : Fin k) (p : Momentum 3) (hcharge : Ψ ≠ φ)
    (G : CSWGeometricQuantizationPackage k hk) :
    (Integrable (fun A => W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ W.wilsonBound L * W.partitionFunction)
      ∧ (∀ τ z a,
        cswThetaBasis k a (-1 / τ) z =
          ∑ b : Fin k, cswSMatrix k a b * cswThetaBasis k b τ z)
      ∧ (∀ a b c,
        cswFusionCoeff k a b c = cswVerlindeCoefficientByS k hk a b c)
      ∧ (∀ a q,
        cswWilsonVerlindeOperator k a (fun b => cswSMatrix k b q) =
          fun c => cswVerlindeEigenvalue k hk a q * cswSMatrix k c q)
      ∧ Module.finrank ℂ (TorusHilbert k) = k
      ∧ KalnayBoseFermiFieldStatement p := by
  have hFKField :=
    witten_analytic_concreteCSW_kalnay_field_bridge
      W L c lam ω e Λ hΛ HR HI χ P ψ Ψ φ O p hcharge
  have hItem := csw_item9_verlinde_geometric_quantization k hk G
  exact ⟨hFKField.1, hItem.1, hItem.2.1, hItem.2.2.1,
    witten_torusHilbert_finrank k, hFKField.2⟩

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.wilson_reverse_dual_invariant where
  formalizes @ "claim:the-wilson-loop-expectation-is-invariant-under-orientation-reversal-with-the-dual-representation",
  supported_by @ "paper:witten-1989-quantum-field-theory-jones-polynomial"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.skein_solve_overcrossing where
  formalizes @ "claim:the-witten-skein-relation-solves-the-overcrossing-in-terms-of-the-undercrossing-and-smoothing",
  requires @ "claim:the-wilson-loop-expectation-is-invariant-under-orientation-reversal-with-the-dual-representation",
  supported_by @ "paper:witten-1989-quantum-field-theory-jones-polynomial"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.witten_unknot_partition_from_smatrix where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-witten-unknot-partition-function-is-read-from-the-modular-s-matrix",
  requires @ "claim:the-witten-skein-relation-solves-the-overcrossing-in-terms-of-the-undercrossing-and-smoothing",
  caveat @ "claim:the-skein-and-s-matrix-inputs-are-the-chern-simons-topological-data-not-derived-from-the-path-integral"

zil_file_contract physlib.wittenJonesPolynomialChernSimons where
  promises "The Jones polynomial from Chern-Simons theory: the Wilson-loop expectation is orientation-reversal invariant with the dual representation, the Witten skein relation solves the overcrossing from the undercrossing and smoothing, and the unknot partition function is read from the modular S-matrix."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.WittenSkeinTriple",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrixKernel"]
  forbids_substitutes ["a path-integral evaluation of the knot invariant, only the skein and S-matrix bookkeeping",
    "a proof that the resulting invariant is the Jones polynomial, taken as the Witten identification"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.wilson_reverse_dual_invariant,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.skein_solve_overcrossing,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.witten_unknot_partition_from_smatrix]

/- ZIL-END -/
