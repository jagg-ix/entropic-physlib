/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederStandardVector
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaIntrinsicMaxwellGreen
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldArakiWoodsThermalParameter
public import Physlib.QuantumMechanics.DDimensions.Operators.SpectralTheory.SpectralMeasure
meta import Zil

/-!
# Continuum Hadamard states on type-III AQFT local nets

This module closes the carrier gap between three existing developments:

* `KleinGordonProgram.ContinuumHadamardTwoPoint` supplies a positive Hermitian, CCR-compatible
  two-point functional with a microlocal positive-frequency condition;
* `KleinGordonProgram.ContinuumSourceLocalNetAdapter` localizes continuum sources as bounded
  observables and already proves spacelike commutativity;
* `TypeIIILocalNet.ConcreteTypeIIINet` supplies bundled local von Neumann factors and the correct
  projection-theoretic type-III condition.

The additional datum recorded here is the genuine GNS/AQFT identification: the pulled-back Hadamard
two-point functional is the vacuum matrix coefficient of the localized observables.  Haag duality and
regionwise vacuum cyclicity then invoke the existing Reeh--Schlieder theorem to produce a standard
(cyclic and separating) vacuum vector for every local type-III algebra.

No finite trace or density matrix is introduced.  The source-level stationary spectral representation
is constructed below from a genuine projection-valued measure: its scalar matrix coefficients have a
canonical finite control measure and Radon--Nikodym density.  Type III, Haag duality, cyclicity, the
selection of the physical stationary PVM, and the quantitative dominated-analytic certificate remain
visible data; spectral boundary equalities are not assumed in the PVM bridge.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederCyclicSeparating
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederStandardVector
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator

variable {𝓕 𝓢 Ξ H region : Type*}
variable [AddCommGroup 𝓕] [Module ℂ 𝓕] [AddCommGroup 𝓢] [Module ℂ 𝓢]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Preorder region]

/-! ## A. Common Hadamard/GNS/type-III carrier -/

/-- Concrete continuum Hadamard AQFT data on a type-III local net.

The two-point realization field is the missing non-definitional link: it says that the causal
Hadamard functional obtained from the Caticha/KG Green carrier is represented by vacuum matrix
coefficients of the same localized observables that inhabit the local von Neumann algebras. -/
structure HadamardTypeIIIAQFTData
    (D : ContinuumCatichaKGData 𝓕 𝓢)
    (Q : ContinuumHadamardTwoPoint 𝓕 Ξ)
    (transport : Ξ → Ξ) (N : ConcreteTypeIIINet H region) where
  /-- Covector transport preserves the chosen positive-frequency cone. -/
  cone_preserving : Set.MapsTo transport Q.positiveFrequencyCone Q.positiveFrequencyCone
  /-- Localization of continuum sources as bounded observables of the type-III net. -/
  localization : ContinuumSourceLocalNetAdapter
    (𝒾c := 𝓢) N.toConcreteLocalNet.toLocalNet
  /-- The GNS/vacuum vector. -/
  vacuum : H
  /-- Reeh--Schlieder cyclicity on every local algebra. -/
  vacuum_cyclic : ∀ O : region,
    IsCyclic (N.toConcreteLocalNet.toLocalNet.alg O) vacuum
  /-- Haag duality on every region. -/
  haag_duality : ∀ O : region,
    HaagDuality N.toConcreteLocalNet.toLocalNet O
  /-- The pulled-back Hadamard two-point functional is realized by vacuum matrix coefficients. -/
  twoPoint_is_vacuum_matrixCoefficient : ∀ φ ψ : 𝓢,
    (D.causalHadamardCarrier Q transport cone_preserving).twoPoint φ ψ =
      inner ℂ (localization.sourceObservable φ vacuum)
        (localization.sourceObservable ψ vacuum)

/-! ## B. Standard local vacuum -/

/-- The vector state associated with `Ω`: `ωΩ(a) = ⟪Ω, a Ω⟫`.
This is defined directly on the repository's concrete bounded-operator carrier. -/
def vacuumFunctional (Ω : H) (a : BoundedOperator H) : ℂ :=
  inner ℂ Ω (a Ω)

/-- **The algebraic GNS form of a vector state is its Hilbert-space matrix coefficient.**
This is the exact operator-level identification needed to reuse the continuum KMS
spectral boundary theorem with the Hadamard/type-III vacuum carrier. -/
theorem gnsForm_vacuumFunctional
    (Ω : H) (a b : BoundedOperator H) :
    gnsForm (vacuumFunctional Ω) a b = inner ℂ (a Ω) (b Ω) := by
  unfold gnsForm vacuumFunctional
  rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

/-- The vacuum is cyclic and separating for every local type-III algebra.  Separation is derived from
cyclicity of the causal-complement algebra and Haag duality by the existing Reeh--Schlieder theorem. -/
theorem HadamardTypeIIIAQFTData.standard_vacuum
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N) (O : region) :
    ReehSchlieder (N.toConcreteLocalNet.toLocalNet.alg O) A.vacuum :=
  reehSchlieder_standard N.toConcreteLocalNet.toLocalNet O A.vacuum
    (A.haag_duality O) (A.vacuum_cyclic O)
    (A.vacuum_cyclic (N.toConcreteLocalNet.compl O))

/-- The continuum Hadamard functional has an explicit GNS realization on the local-net Hilbert space. -/
lemma HadamardTypeIIIAQFTData.twoPoint_eq_vacuum_matrixCoefficient
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N) (φ ψ : 𝓢) :
    (D.causalHadamardCarrier Q transport A.cone_preserving).twoPoint φ ψ =
      inner ℂ (A.localization.sourceObservable φ A.vacuum)
        (A.localization.sourceObservable ψ A.vacuum) :=
  A.twoPoint_is_vacuum_matrixCoefficient φ ψ

/-- **The continuum Hadamard two-point function is the concrete vacuum GNS form.**
This closes the representation-level join between the existing microlocal Hadamard
carrier and the continuum Tomita/KMS boundary infrastructure.  It does not assert that
an arbitrary Hadamard state is stationary KMS; a spectral KMS realization remains a
separate physical/geometric datum. -/
theorem HadamardTypeIIIAQFTData.twoPoint_eq_vacuum_gnsForm
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N) (φ ψ : 𝓢) :
    (D.causalHadamardCarrier Q transport A.cone_preserving).twoPoint φ ψ =
      gnsForm (vacuumFunctional A.vacuum)
        (A.localization.sourceObservable φ)
        (A.localization.sourceObservable ψ) := by
  rw [A.twoPoint_eq_vacuum_matrixCoefficient,
    gnsForm_vacuumFunctional]

/-! ## C. Localized continuum KMS realization -/

section LocalizedContinuumKMS

open MeasureTheory
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldArakiWoodsThermalParameter
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.WeylQuasifreeArakiWoods

variable {X : Type*} [MeasurableSpace X]

/-- The Tomita boundary relation restricted to the continuum sources localized
in a region and its causal complement.  Unlike an arbitrary-algebra statement,
both operands are the actual observables supplied by the Caticha/KG localization
adapter. -/
def SourceOppositeWedgeTomitaBoundary
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N) (O : region) : Prop :=
  ∀ ⦃φ : 𝓢⦄, φ ∈ A.localization.localizedSource (N.toConcreteLocalNet.compl O) →
    ∀ ⦃ψ : 𝓢⦄, ψ ∈ A.localization.localizedSource O →
      gnsForm (vacuumFunctional A.vacuum)
          (A.localization.sourceObservable φ)
          (A.localization.sourceObservable ψ) =
        gnsForm (vacuumFunctional A.vacuum)
          (star (A.localization.sourceObservable ψ))
          (star (A.localization.sourceObservable φ))

/-- Weak opposite-wedge locality evaluated by the concrete Hadamard vacuum
state on the localized source observables. -/
def SourceWeakOppositeWedgeLocalityInState
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N) (O : region) : Prop :=
  ∀ ⦃φ : 𝓢⦄, φ ∈ A.localization.localizedSource (N.toConcreteLocalNet.compl O) →
    ∀ ⦃ψ : 𝓢⦄, ψ ∈ A.localization.localizedSource O →
      vacuumFunctional A.vacuum
          (star (A.localization.sourceObservable φ) *
            A.localization.sourceObservable ψ) =
        vacuumFunctional A.vacuum
          (A.localization.sourceObservable ψ *
            star (A.localization.sourceObservable φ))

/-! ### C.1 Projection-valued spectral realization -/

open StrongSpectralMeasure

/-- **The localized source Tomita boundary follows from the concrete local
net.**  Since every von Neumann fibre is star-closed, Einstein locality makes
`star(a)` commute with `b` for `a` in the causal complement and `b` in the
region.  Expanding the GNS form gives the boundary identity for the actual
Hadamard vacuum state. -/
theorem sourceTomitaBoundary_of_locality
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N) (O : region) :
    SourceOppositeWedgeTomitaBoundary A O := by
  intro φ hφ ψ hψ
  have hweak :=
    locality_implies_weakLocalityInState
      N.toConcreteLocalNet.toLocalNet
      (vacuumFunctional A.vacuum)
      (fun _ _ ha => star_mem ha) O
  simpa [gnsForm] using
    hweak (A.localization.observable_mem hφ)
      (A.localization.observable_mem hψ)

/-- The scalar spectral measure of two localized source vectors in the
Hadamard GNS Hilbert space. -/
def sourceSpectralCoefficientMeasure
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N)
    (μS : StrongSpectralMeasure X H) (φ ψ : 𝓢) : ComplexMeasure X :=
  μS.coefficientMeasure
    (A.localization.sourceObservable φ A.vacuum)
    (A.localization.sourceObservable ψ A.vacuum)

/-- The canonical finite positive control measure of a localized source
spectral coefficient. -/
def sourceSpectralControlMeasure
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N)
    (μS : StrongSpectralMeasure X H) (φ ψ : 𝓢) : Measure X :=
  μS.coefficientControlMeasure
    (A.localization.sourceObservable φ A.vacuum)
    (A.localization.sourceObservable ψ A.vacuum)

/-- The canonical `L¹` Radon--Nikodym density of a localized source spectral
coefficient. -/
def sourceSpectralDensity
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N)
    (μS : StrongSpectralMeasure X H) (φ ψ : 𝓢) : X → ℂ :=
  μS.coefficientDensity
    (A.localization.sourceObservable φ A.vacuum)
    (A.localization.sourceObservable ψ A.vacuum)

/-- **The PVM density reconstructs the continuum Hadamard two-point
functional.**  This is the missing lower spectral boundary: it is proved from
the PVM normalization and the existing vacuum GNS realization, rather than
stored as a field. -/
theorem source_spectral_density_integral_eq_hadamard
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N)
    (μS : StrongSpectralMeasure X H) (φ ψ : 𝓢) :
    ∫ x, sourceSpectralDensity A μS φ ψ x
        ∂sourceSpectralControlMeasure A μS φ ψ =
      (D.causalHadamardCarrier Q transport A.cone_preserving).twoPoint φ ψ := by
  rw [sourceSpectralDensity, sourceSpectralControlMeasure,
    μS.coefficient_density_integral]
  exact (A.twoPoint_eq_vacuum_matrixCoefficient φ ψ).symm

/-- Normalize the canonical PVM density by the nonzero zero-time thermal mode.
Multiplying this weight by `thermalWightman ... 0` therefore recovers the
original spectral density almost everywhere. -/
def sourceThermalSpectralWeight
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N)
    (μS : StrongSpectralMeasure X H) (β : ℝ) (frequency : X → ℝ)
    (φ ψ : 𝓢) (x : X) : ℂ :=
  sourceSpectralDensity A μS φ ψ x /
    thermalWightman β (frequency x) 0

/-- **The canonical PVM thermal weight has the Hadamard lower boundary.** -/
theorem source_continuumThermalWightman_zero_eq_twoPoint
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N)
    (μS : StrongSpectralMeasure X H) (β : ℝ) (frequency : X → ℝ)
    (φ ψ : 𝓢)
    (hnormalizer :
      ∀ᵐ x ∂sourceSpectralControlMeasure A μS φ ψ,
        thermalWightman β (frequency x) 0 ≠ 0) :
    continuumThermalWightman
        (sourceSpectralControlMeasure A μS φ ψ) β frequency
        (sourceThermalSpectralWeight A μS β frequency φ ψ) 0 =
      (D.causalHadamardCarrier Q transport A.cone_preserving).twoPoint φ ψ := by
  rw [continuumThermalWightman]
  calc
    (∫ x, weightedThermalWightman β frequency
        (sourceThermalSpectralWeight A μS β frequency φ ψ) 0 x
        ∂sourceSpectralControlMeasure A μS φ ψ) =
      ∫ x, sourceSpectralDensity A μS φ ψ x
        ∂sourceSpectralControlMeasure A μS φ ψ := by
          apply integral_congr_ae
          filter_upwards [hnormalizer] with x hx
          simp [weightedThermalWightman, sourceThermalSpectralWeight, hx]
    _ = _ := source_spectral_density_integral_eq_hadamard A μS φ ψ

/-- **[PVM → continuum analytic KMS → Hadamard/Tomita boundary].**
For localized source vectors, a genuine projection-valued spectral measure
constructs the lower Hadamard boundary through its canonical finite control
measure.  The existing dominated Bochner theorem proves complex
differentiability, pointwise KMS transports the lower value to imaginary time
`-iβ`, and concrete local-net locality identifies that value with the
Tomita-reversed GNS coefficient.  No lower or upper boundary equality is an
input to this theorem. -/
theorem source_pvm_continuum_kms_tomita_chain
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N) (O : region)
    (μS : StrongSpectralMeasure X H) (β : ℝ) (frequency : X → ℝ)
    {φ ψ : 𝓢}
    (hφ : φ ∈ A.localization.localizedSource (N.toConcreteLocalNet.compl O))
    (hψ : ψ ∈ A.localization.localizedSource O)
    (hnormalizer :
      ∀ᵐ x ∂sourceSpectralControlMeasure A μS φ ψ,
        thermalWightman β (frequency x) 0 ≠ 0)
    (hregular :
      ∀ᵐ x ∂sourceSpectralControlMeasure A μS φ ψ,
        Real.exp (β * frequency x) - 1 ≠ 0)
    (Canalytic : ContinuumKMSAnalyticCertificate
      (sourceSpectralControlMeasure A μS φ ψ) β frequency
      (sourceThermalSpectralWeight A μS β frequency φ ψ)) :
    Differentiable ℂ
        (continuumThermalWightman
          (sourceSpectralControlMeasure A μS φ ψ) β frequency
          (sourceThermalSpectralWeight A μS β frequency φ ψ)) ∧
      continuumThermalWightman
          (sourceSpectralControlMeasure A μS φ ψ) β frequency
          (sourceThermalSpectralWeight A μS β frequency φ ψ) 0 =
        (D.causalHadamardCarrier Q transport A.cone_preserving).twoPoint φ ψ ∧
      continuumThermalWightman
          (sourceSpectralControlMeasure A μS φ ψ) β frequency
          (sourceThermalSpectralWeight A μS β frequency φ ψ)
          (-Complex.I * (β : ℂ)) =
        gnsForm (vacuumFunctional A.vacuum)
          (star (A.localization.sourceObservable ψ))
          (star (A.localization.sourceObservable φ)) := by
  have hlower :=
    source_continuumThermalWightman_zero_eq_twoPoint
      A μS β frequency φ ψ hnormalizer
  have hkms :=
    continuumThermalWightman_kms
      (sourceSpectralControlMeasure A μS φ ψ) β frequency
      (sourceThermalSpectralWeight A μS β frequency φ ψ) 0 hregular
  have hboundary := sourceTomitaBoundary_of_locality A O hφ hψ
  refine ⟨continuumThermalWightman_differentiable _ _ _ _ Canalytic,
    hlower, ?_⟩
  calc
    continuumThermalWightman
        (sourceSpectralControlMeasure A μS φ ψ) β frequency
        (sourceThermalSpectralWeight A μS β frequency φ ψ)
        (-Complex.I * (β : ℂ)) =
      continuumThermalWightman
        (sourceSpectralControlMeasure A μS φ ψ) β frequency
        (sourceThermalSpectralWeight A μS β frequency φ ψ) 0 := by
          simpa using hkms
    _ = (D.causalHadamardCarrier Q transport A.cone_preserving).twoPoint φ ψ :=
      hlower
    _ = gnsForm (vacuumFunctional A.vacuum)
        (A.localization.sourceObservable φ)
        (A.localization.sourceObservable ψ) :=
      A.twoPoint_eq_vacuum_gnsForm φ ψ
    _ = _ := hboundary

/-- **[Actual Caticha generator → constructed strong PVM → continuum KMS →
Hadamard/Tomita boundary].**  This specialization removes the formerly
supplied spectral-measure input for the mode-diagonal continuum Caticha
sector.  The real Caticha frequency multiplies the same `L²(Space d)` carrier
as the unbounded generator, while measurable spectral sets act by the
canonical indicator PVM proved in `SpectralMeasure`.

The quantitative Bose regularity and dominated analytic estimate remain
explicit: a constructed PVM does not by itself prove those thermal bounds. -/
theorem source_catichaGenerator_pvm_continuum_kms_tomita_chain
    {d : ℕ}
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ}
    {N : ConcreteTypeIIINet
      (QuantumMechanics.SpaceDHilbertSpace d) region}
    (A : HadamardTypeIIIAQFTData D Q transport N) (O : region)
    (lapse shift : ℝ) (hperp hi : Space d → ℂ)
    (hperpReal : starRingEnd ℂ ∘ hperp = hperp)
    (hiReal : starRingEnd ℂ ∘ hi = hi)
    (β : ℝ) {φ ψ : 𝓢}
    (hφ : φ ∈ A.localization.localizedSource
      (N.toConcreteLocalNet.compl O))
    (hψ : ψ ∈ A.localization.localizedSource O)
    (hnormalizer :
      ∀ᵐ x ∂sourceSpectralControlMeasure A
        (QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure d)
        φ ψ,
        thermalWightman β
          (catichaRealFrequency
            lapse shift hperp hi x) 0 ≠ 0)
    (hregular :
      ∀ᵐ x ∂sourceSpectralControlMeasure A
        (QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure d)
        φ ψ,
        Real.exp (β *
          catichaRealFrequency
            lapse shift hperp hi x) - 1 ≠ 0)
    (Canalytic : ContinuumKMSAnalyticCertificate
      (sourceSpectralControlMeasure A
        (QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure d)
        φ ψ)
      β
      (catichaRealFrequency
        lapse shift hperp hi)
      (sourceThermalSpectralWeight A
        (QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure d)
        β
        (catichaRealFrequency
          lapse shift hperp hi) φ ψ)) :
    continuumMultiplicationGenerator
        lapse shift hperp hi =
      QuantumMechanics.SpaceDHilbertSpace.mulOperator MeasureTheory.volume
        (fun x =>
          (catichaRealFrequency
            lapse shift hperp hi x : ℂ)) ∧
    Differentiable ℂ
        (continuumThermalWightman
          (sourceSpectralControlMeasure A
            (QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure d)
            φ ψ)
          β
          (catichaRealFrequency
            lapse shift hperp hi)
          (sourceThermalSpectralWeight A
            (QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure d)
            β
            (catichaRealFrequency
              lapse shift hperp hi) φ ψ)) ∧
      continuumThermalWightman
          (sourceSpectralControlMeasure A
            (QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure d)
            φ ψ)
          β
          (catichaRealFrequency
            lapse shift hperp hi)
          (sourceThermalSpectralWeight A
            (QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure d)
            β
            (catichaRealFrequency
              lapse shift hperp hi) φ ψ) 0 =
        (D.causalHadamardCarrier Q transport A.cone_preserving).twoPoint φ ψ ∧
      continuumThermalWightman
          (sourceSpectralControlMeasure A
            (QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure d)
            φ ψ)
          β
          (catichaRealFrequency
            lapse shift hperp hi)
          (sourceThermalSpectralWeight A
            (QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure d)
            β
            (catichaRealFrequency
              lapse shift hperp hi) φ ψ)
          (-Complex.I * (β : ℂ)) =
        gnsForm (vacuumFunctional A.vacuum)
          (star (A.localization.sourceObservable ψ))
          (star (A.localization.sourceObservable φ)) := by
  refine ⟨
    continuumMultiplicationGenerator_eq_realFrequency_mulOperator
        lapse shift hperp hi hperpReal hiReal, ?_⟩
  exact source_pvm_continuum_kms_tomita_chain A O
    (QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure d)
    β
    (catichaRealFrequency
      lapse shift hperp hi)
    hφ hψ hnormalizer hregular Canalytic

/-- **A continuum spectral KMS realization of localized Hadamard sources.**

The lower boundary is the existing microlocal Hadamard two-point function; the
upper boundary is its Tomita-reversed vacuum GNS coefficient.  The pointwise
Bose regularity and quantitative dominated-derivative certificate expose all
analytic obligations needed by the continuum KMS theorems. -/
structure HadamardSourceKMSRealization
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N) (O : region)
    (μ : Measure X) (β : ℝ) (frequency : X → ℝ) where
  spectralWeight : 𝓢 → 𝓢 → X → ℂ
  regular :
    ∀ φ ∈ A.localization.localizedSource (N.toConcreteLocalNet.compl O),
      ∀ ψ ∈ A.localization.localizedSource O,
        ∀ᵐ x ∂μ, Real.exp (β * frequency x) - 1 ≠ 0
  lowerBoundary :
    ∀ φ ∈ A.localization.localizedSource (N.toConcreteLocalNet.compl O),
      ∀ ψ ∈ A.localization.localizedSource O,
        continuumThermalWightman μ β frequency (spectralWeight φ ψ) 0 =
          (D.causalHadamardCarrier Q transport A.cone_preserving).twoPoint φ ψ
  upperBoundary :
    ∀ φ ∈ A.localization.localizedSource (N.toConcreteLocalNet.compl O),
      ∀ ψ ∈ A.localization.localizedSource O,
        continuumThermalWightman μ β frequency (spectralWeight φ ψ)
            (-Complex.I * (β : ℂ)) =
          gnsForm (vacuumFunctional A.vacuum)
            (star (A.localization.sourceObservable ψ))
            (star (A.localization.sourceObservable φ))
  analytic :
    ∀ φ ∈ A.localization.localizedSource (N.toConcreteLocalNet.compl O),
      ∀ ψ ∈ A.localization.localizedSource O,
        ContinuumKMSAnalyticCertificate μ β frequency (spectralWeight φ ψ)

/-- **Localized source correlators are genuinely complex differentiable.**
The proof applies the existing dominated Bochner differentiation theorem to
the concrete spectral weight selected for the two localized sources. -/
theorem HadamardSourceKMSRealization.correlator_differentiable
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    {A : HadamardTypeIIIAQFTData D Q transport N} {O : region}
    {μ : Measure X} {β : ℝ} {frequency : X → ℝ}
    (R : HadamardSourceKMSRealization A O μ β frequency)
    {φ ψ : 𝓢}
    (hφ : φ ∈ A.localization.localizedSource (N.toConcreteLocalNet.compl O))
    (hψ : ψ ∈ A.localization.localizedSource O) :
    Differentiable ℂ
      (continuumThermalWightman μ β frequency (R.spectralWeight φ ψ)) :=
  continuumThermalWightman_differentiable μ β frequency
    (R.spectralWeight φ ψ) (R.analytic φ hφ ψ hψ)

/-- **Continuum Hadamard KMS data gives the localized Tomita boundary.**
The lower Hadamard boundary is first converted to the actual vacuum GNS form;
the proved continuum KMS equality then transports it to the upper,
Tomita-reversed boundary. -/
theorem sourceTomitaBoundary_of_continuumKMS
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N) (O : region)
    (μ : Measure X) (β : ℝ) (frequency : X → ℝ)
    (R : HadamardSourceKMSRealization A O μ β frequency) :
    SourceOppositeWedgeTomitaBoundary A O := by
  intro φ hφ ψ hψ
  have hkms :=
    continuumThermalWightman_kms μ β frequency (R.spectralWeight φ ψ) 0
      (R.regular φ hφ ψ hψ)
  calc
    gnsForm (vacuumFunctional A.vacuum)
        (A.localization.sourceObservable φ)
        (A.localization.sourceObservable ψ) =
      (D.causalHadamardCarrier Q transport A.cone_preserving).twoPoint φ ψ :=
        (A.twoPoint_eq_vacuum_gnsForm φ ψ).symm
    _ = continuumThermalWightman μ β frequency (R.spectralWeight φ ψ) 0 :=
      (R.lowerBoundary φ hφ ψ hψ).symm
    _ = continuumThermalWightman μ β frequency (R.spectralWeight φ ψ)
          (-Complex.I * (β : ℂ)) := by
      simpa using hkms.symm
    _ = gnsForm (vacuumFunctional A.vacuum)
          (star (A.localization.sourceObservable ψ))
          (star (A.localization.sourceObservable φ)) :=
      R.upperBoundary φ hφ ψ hψ

/-- **Continuum KMS implies weak opposite-wedge locality for the actual
localized Caticha/KG observables.**  This is the GNS-form expansion of the
constructed source Tomita boundary, not an independently supplied locality
certificate. -/
theorem sourceWeakLocality_of_continuumKMS
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N) (O : region)
    (μ : Measure X) (β : ℝ) (frequency : X → ℝ)
    (R : HadamardSourceKMSRealization A O μ β frequency) :
    SourceWeakOppositeWedgeLocalityInState A O := by
  intro φ hφ ψ hψ
  simpa [gnsForm] using
    sourceTomitaBoundary_of_continuumKMS A O μ β frequency R hφ hψ

/-- **[Araki–Woods → continuum Hadamard KMS → Tomita/locality].**
For every spectral point, the existing Kay–Wald theorem identifies the
Araki–Woods modular parameter with the Hawking Boltzmann factor.  For a
localized source pair, the same spectral data gives a genuinely
complex-differentiable continuum correlator, its Tomita boundary, and weak
opposite-wedge locality on the concrete type-III vacuum carrier. -/
theorem hadamard_arakiWoods_continuum_kms_chain
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N) (O : region)
    (μ : Measure X) (β : ℝ) (frequency : X → ℝ)
    (R : HadamardSourceKMSRealization A O μ β frequency)
    {φ ψ : 𝓢}
    (hφ : φ ∈ A.localization.localizedSource (N.toConcreteLocalNet.compl O))
    (hψ : ψ ∈ A.localization.localizedSource O) :
    (∀ x : X,
        arakiWoodsGamma (thermalContraction β (frequency x)) =
          Real.exp (-(β * frequency x))) ∧
      Differentiable ℂ
        (continuumThermalWightman μ β frequency (R.spectralWeight φ ψ)) ∧
      SourceOppositeWedgeTomitaBoundary A O ∧
      SourceWeakOppositeWedgeLocalityInState A O := by
  exact ⟨fun x => arakiWoods_gamma_is_boltzmann β (frequency x),
    R.correlator_differentiable hφ hψ,
    sourceTomitaBoundary_of_continuumKMS A O μ β frequency R,
    sourceWeakLocality_of_continuumKMS A O μ β frequency R⟩

end LocalizedContinuumKMS

/-! ## D. Hadamard/type-III AQFT synthesis -/

/-- **Continuum Hadamard/type-III AQFT chain.**  For spacelike separated localized sources, the existing
Hadamard pullback and local-net theorem gives Hermiticity, positivity, CCR compatibility, microlocal
positive-frequency support, and commuting observables.  The concrete type-III carrier additionally gives
local primarity and excludes every nonzero finite local projection, while Haag duality and cyclicity give
the standard vacuum.  The same two-point function is represented by the vacuum matrix coefficient.

The theorem consumes, rather than assumes again, the repository's separate analytic and operator-algebraic
proofs; only their common-carrier data is packaged above. -/
theorem hadamard_typeIII_AQFT_chain
    {D : ContinuumCatichaKGData 𝓕 𝓢} {Q : ContinuumHadamardTwoPoint 𝓕 Ξ}
    {transport : Ξ → Ξ} {N : ConcreteTypeIIINet H region}
    (A : HadamardTypeIIIAQFTData D Q transport N)
    {O₁ O₂ : region} (hcausal : O₁ ≤ N.toConcreteLocalNet.compl O₂)
    {φ ψ : 𝓢} (hφ : φ ∈ A.localization.localizedSource O₁)
    (hψ : ψ ∈ A.localization.localizedSource O₂)
    {p : BoundedOperator H} (hp : p ∈ N.alg O₁) (hp0 : p ≠ 0) :
    IsHermitianTwoPoint
        (D.causalHadamardCarrier Q transport A.cone_preserving).twoPoint ∧
      IsPositiveTwoPoint
        (D.causalHadamardCarrier Q transport A.cone_preserving).twoPoint ∧
      IsCCRCompatibleTwoPoint
        (D.causalHadamardCarrier Q transport A.cone_preserving).twoPoint
        (D.causalHadamardCarrier Q transport A.cone_preserving).symplecticForm ∧
      MicrolocalSpectrumCondition
        (D.causalHadamardCarrier Q transport A.cone_preserving).wavefront
        (D.causalHadamardCarrier Q transport A.cone_preserving).positiveFrequencyCone ∧
      A.localization.sourceObservable φ * A.localization.sourceObservable ψ =
        A.localization.sourceObservable ψ * A.localization.sourceObservable φ ∧
      (D.causalHadamardCarrier Q transport A.cone_preserving).twoPoint φ ψ =
        inner ℂ (A.localization.sourceObservable φ A.vacuum)
          (A.localization.sourceObservable ψ A.vacuum) ∧
      ReehSchlieder (N.toConcreteLocalNet.toLocalNet.alg O₁) A.vacuum ∧
      LocalPrimarity N.toConcreteLocalNet.toLocalNet (scalarOperators H) O₁ ∧
      ¬ IsFiniteProjection (N.alg O₁) p := by
  have hlocal := ContinuumSourceLocalNetAdapter.causalHadamard_localNet_properties
    D Q transport A.cone_preserving N.toConcreteLocalNet.toLocalNet
    A.localization hcausal hφ hψ
  exact ⟨hlocal.1, hlocal.2.1, hlocal.2.2.1, hlocal.2.2.2.1,
    hlocal.2.2.2.2, A.twoPoint_is_vacuum_matrixCoefficient φ ψ,
    A.standard_vacuum O₁, N.localPrimarity O₁,
    N.no_local_nonzero_finite_projection O₁ hp hp0⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT

end


/- ZIL-BEGIN -/

open Zil

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.HadamardTypeIIIAQFTData.standard_vacuum where
  formalizes @ "claim:haag-duality-and-regionwise-reeh-schlieder-cyclicity-give-a-standard-vacuum-for-each-local-type-iii-algebra",
  supported_by @ "paper:verch-hadamard-local-algebras",
  caveat @ "claim:cyclicity-and-haag-duality-are-analytic-inputs-not-derived-from-positivity-alone"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.gnsForm_vacuumFunctional where
  formalizes @ "claim:the-gns-form-of-a-bounded-operator-vector-state-is-the-corresponding-hilbert-space-matrix-coefficient",
  supported_by @ "lean:ContinuousLinearMap.adjoint_inner_right"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.HadamardTypeIIIAQFTData.twoPoint_eq_vacuum_gnsForm where
  formalizes @ "claim:the-continuum-hadamard-two-point-function-is-the-concrete-vacuum-gns-form-on-the-local-type-iii-carrier",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.gnsForm_vacuumFunctional",
  caveat @ "claim:a-hadamard-state-is-not-asserted-to-be-kms-without-stationarity-and-a-kms-spectral-realization"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.sourceTomitaBoundary_of_locality where
  formalizes @ "claim:star-closure-and-einstein-locality-of-the-concrete-type-iii-net-give-the-localized-source-tomita-boundary",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.locality_implies_weakLocalityInState",
  caveat @ "claim:this-is-the-opposite-region-boundary-consequence-of-operator-locality-not-a-derivation-of-modular-kms-flow"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.source_spectral_density_integral_eq_hadamard where
  formalizes @ "claim:the-canonical-radon-nikodym-density-of-the-pvm-matrix-coefficient-integrates-to-the-continuum-hadamard-two-point-function",
  supported_by @ "lean:StrongSpectralMeasure.coefficient_density_integral",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.HadamardTypeIIIAQFTData.twoPoint_eq_vacuum_gnsForm",
  caveat @ "claim:the-physical-stationary-projection-valued-measure-remains-selected-data"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.source_continuumThermalWightman_zero_eq_twoPoint where
  formalizes @ "claim:normalizing-the-canonical-pvm-density-by-the-regular-zero-time-thermal-mode-constructs-the-hadamard-lower-kms-boundary",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.source_spectral_density_integral_eq_hadamard",
  caveat @ "claim:nonvanishing-of-the-zero-time-thermal-normalizer-is-required-almost-everywhere"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.source_pvm_continuum_kms_tomita_chain where
  formalizes @ "claim:a-projection-valued-spectral-measure-constructs-the-hadamard-boundary-and-continuum-analytic-kms-transports-it-to-the-tomita-reversed-gns-coefficient",
  requires @ "claim:the-selected-stationary-pvm-has-the-stated-frequency-map-and-dominated-analytic-certificate",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.source_continuumThermalWightman_zero_eq_twoPoint",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity.continuumThermalWightman_kms",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.sourceTomitaBoundary_of_locality",
  caveat @ "claim:no-lower-or-upper-spectral-boundary-equality-is-assumed-but-pvm-selection-and-quantitative-domination-remain-explicit"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.source_catichaGenerator_pvm_continuum_kms_tomita_chain where
  formalizes @ "claim:the-actual-mode-diagonal-caticha-continuum-generator-supplies-the-real-frequency-and-constructed-strong-configuration-pvm-for-the-hadamard-kms-tomita-chain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumMultiplicationGenerator_eq_realFrequency_mulOperator",
  supported_by @ "lean:QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure",
  caveat @ "claim:the-pvm-and-generator-identification-are-proved-but-bose-regularity-and-the-quantitative-dominated-analytic-certificate-remain-explicit-premises"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.HadamardSourceKMSRealization.correlator_differentiable where
  formalizes @ "claim:localized-hadamard-source-correlators-with-quantitative-spectral-domination-are-complex-differentiable",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity.continuumThermalWightman_differentiable",
  caveat @ "claim:the-realization-exposes-the-integrable-derivative-majorant-for-each-localized-source-pair"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.sourceTomitaBoundary_of_continuumKMS where
  formalizes @ "claim:the-continuum-kms-boundary-and-hadamard-vacuum-gns-realization-give-the-localized-source-tomita-boundary",
  requires @ "claim:the-selected-stationary-state-has-the-supplied-lower-and-upper-spectral-boundary-representation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.HadamardTypeIIIAQFTData.twoPoint_eq_vacuum_gnsForm",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity.continuumThermalWightman_kms"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.sourceWeakLocality_of_continuumKMS where
  formalizes @ "claim:continuum-kms-implies-weak-opposite-wedge-locality-for-the-actual-localized-caticha-kg-observables",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.sourceTomitaBoundary_of_continuumKMS",
  caveat @ "claim:weak-vacuum-expectation-locality-is-not-relabeled-as-operator-commutation"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.hadamard_arakiWoods_continuum_kms_chain where
  formalizes @ "claim:the-araki-woods-hawking-boltzmann-parameter-drives-the-analytic-continuum-hadamard-kms-tomita-and-weak-locality-chain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldArakiWoodsThermalParameter.arakiWoods_gamma_is_boltzmann",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.sourceTomitaBoundary_of_continuumKMS",
  caveat @ "claim:the-theorem-consumes-the-selected-stationary-spectral-realization-and-does-not-infer-kms-from-hadamard-regularity-alone"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.hadamard_typeIII_AQFT_chain where
  formalizes @ "claim:the-continuum-hadamard-two-point-functional-is-a-vacuum-gns-coefficient-on-a-local-type-iii-aqft-net",
  requires @ "claim:caticha-kg-green-carrier-preserves-hadamard-microlocal-data",
  requires @ "claim:localized-observables-belong-to-the-concrete-type-iii-local-net",
  supported_by @ "paper:verch-hadamard-local-algebras",
  caveat @ "claim:the-concrete-type-iii-classification-haag-duality-and-reeh-schlieder-cyclicity-remain-explicit-data"

zil_file_contract physlib.hadamardTypeIIIAQFT where
  promises "A continuum Caticha/Klein-Gordon Hadamard two-point carrier is realized as vacuum GNS matrix coefficients of localized observables in a concrete type-III local net. For the actual mode-diagonal Caticha generator, the real multiplication frequency and strong configuration PVM are constructed on the same L2 carrier; this PVM constructs each localized scalar spectral measure, its canonical finite positive control measure and Radon-Nikodym density. The density proves the Hadamard lower boundary, dominated Bochner analyticity proves the continuum correlator, KMS transports it to imaginary time, and local-net star closure identifies the Tomita-reversed boundary. The older generic supplied-PVM adapter remains available. Independently, every region is primary with no nonzero finite projections, and Haag duality plus cyclicity makes the vacuum standard."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumHadamardTwoPoint",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumSourceLocalNetAdapter.causalHadamard_localNet_properties",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederStandardVector.reehSchlieder_standard",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.TypeIIILocalNet.ConcreteTypeIIINet",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaUnboundedGenerator.continuumMultiplicationGenerator_eq_realFrequency_mulOperator",
    "lean:QuantumMechanics.SpaceDHilbertSpace.configurationStrongSpectralMeasure"]
  forbids_substitutes ["finite density matrices or traces used for type-III local algebras",
    "Hadamard microlocal regularity inferred from algebraic positivity alone",
    "a hyperfinite III1 classification inferred without net-specific analytic data",
    "a KMS label replacing the pointwise and continuum analytic boundary proof",
    "weak expectation-value locality relabeled as operator commutation"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.HadamardTypeIIIAQFTData.standard_vacuum,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.gnsForm_vacuumFunctional,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.HadamardTypeIIIAQFTData.twoPoint_eq_vacuum_gnsForm,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.sourceTomitaBoundary_of_locality,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.source_spectral_density_integral_eq_hadamard,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.source_continuumThermalWightman_zero_eq_twoPoint,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.source_pvm_continuum_kms_tomita_chain,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.source_catichaGenerator_pvm_continuum_kms_tomita_chain,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.HadamardSourceKMSRealization.correlator_differentiable,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.sourceTomitaBoundary_of_continuumKMS,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.sourceWeakLocality_of_continuumKMS,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.hadamard_arakiWoods_continuum_kms_chain,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT.hadamard_typeIII_AQFT_chain]

/- ZIL-END -/
