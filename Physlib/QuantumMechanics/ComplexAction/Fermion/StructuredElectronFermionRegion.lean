/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Particles.StandardModel.Representations
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.Fermion.BosonInformationTransfer
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ChargeConjugationDirac
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseFermiField
public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic
public import Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ModeThreeFaces
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.EntanglementEntropy
public import Physlib.QuantumMechanics.ComplexAction.Particles.ExperimentalParticleReactions
public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.StandardModelYukawaCoupling
public import Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree

/-!
# Structured electron/fermion region synthesis

This file assembles the checked pieces of the current electron/fermion model:

* Kálnay: the fermion field generator is a Bose-bilinear word, and its single-boson-sector
  representation satisfies CAR.
* Dirac/trefoil: the non-point carrier is a three-nodule, counter-rotating, one-turn phase region
  with trefoil braid, Hopf spinor sign, and Wilson/ribbon twist interfaces.
* Lorenz/Nambu: the Bloch-vector Lorenz-qubit carrier reuses the existing dissipative Nambu
  contour/strange-attractor deformation theorem.
* Information transfer: a Pauli-bounded absorption/emission cycle carries a KL payload read from
  the imaginary part of the complex action, with a Yang-Baxter convolution carrier.
* CPT/chirality: the Dirac operator is invariant under the Greaves--Thomas/Bennett `CPT`
  matrix `-iγ⁵`, and `γ⁵` supplies the left/right chirality projector and charge-grading
  structure.
* Electroweak/Yukawa support: the existing Standard Model carriers provide the commuting
  `SU(2)` fundamental and `U(1)` doublet representations, the dimensionless Yukawa coupling,
  and the post-symmetry-breaking relation `m_f = y_f v / sqrt 2`.
* Fermion quantum numbers: the `SU(5)`/Standard-Model construction computes the 15 Weyl states'
  `(Q,T₃,Y,B,L,spin,color,weak,chiral)` and proves the electric, hypercharge, and cubic
  hypercharge traces match the anomaly-free generation; named electron, neutrino, quark, antiquark,
  and `e^c` states are generated from the same `5̄ ⊕ Λ²(5)` indices.
* Zitterbewegung: the checked rest-frame frequency identity is available as the Dirac branch
  splitting marker.

The theorem below is intentionally conditional on the explicit carriers and hypotheses. It does not
claim a full interaction Hamiltonian, CAR on a spacetime region, Haag duality, or a global Lorenz
invariant set for the normalized nonlinear qubit channel.


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Fermion.StructuredElectronFermionRegion

open Complex
open FieldSpecification.FieldOpFreeAlgebra
open Matrix
open spaceTime
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ChiralityHelicityProjectors
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.DiracProjectors
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.BraidRelationTrefoilTorus
open Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.Fermion.BosonInformationTransfer
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTComplexification
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ChargeConjugation
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ChargeConjugationDirac
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.lessDiracTrefoilPhaseRegion
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.lessDiracTrefoilPhaseRegion.ThreeNodulePhaseRegion
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.TrefoilFermionChernSimonsInvariant
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseBilinearRealization
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseFermiField
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
open Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
open Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.NambuEntropicContour
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.Particles.GellMannNishijima
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronSector
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics
open Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation
open Physlib.QuantumMechanics.ComplexAction.Particles.ExperimentalParticleReactions
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ModeThreeFaces
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.EntanglementEntropy
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtNumberFromAlpha
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellOscillatorRegime
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
open Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree
open Physlib.QuantumMechanics.ComplexAction.Yukawa.StandardModelYukawaCoupling
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon
open Physlib.Particles.StandardModel.YukawaDimensionalAnalysis
open StandardModel
open Physlib.Thermodynamics.Landauer

/-! ## Capability predicates -/

/-- The concrete Kálnay witness: `f = a† b` is a CAR fermion mode on the single-boson
two-mode sector, with idempotent number operator. -/
def HasConcreteKalnayCAR : Prop :=
  IsFermionMode boseBilinear
    ∧ fermionNumber boseBilinear = !![0, 0; 0, 1]
    ∧ star boseBilinear * star boseBilinear = 0
    ∧ star (fermionNumber boseBilinear) = fermionNumber boseBilinear
    ∧ fermionNumber boseBilinear * fermionNumber boseBilinear = fermionNumber boseBilinear
    ∧ fermionNumber boseBilinear * boseBilinear
        - boseBilinear * fermionNumber boseBilinear = -boseBilinear

/-- The field-level Kálnay dictionary: fermion creation/annihilation generators are represented
by Bose-bilinear words, and the sector representation satisfies CAR. -/
def HasKalnayFermionFromBose (p : Momentum 3) : Prop :=
  kalnayBosonizationHom (ofCrAnOpF (kalnayFermionAnnihil p))
      = boseBilinearAnnihilAsymptotic p
    ∧ kalnayBosonizationHom (ofCrAnOpF (kalnayFermionCreate p))
      = boseBilinearCreateAsymptotic p
    ∧ kalnayFermionRepHom (ofCrAnOpF (kalnayFermionAnnihil p)) = boseBilinear
    ∧ kalnayFermionRepHom
      (ofCrAnOpF (kalnayFermionAnnihil p) * ofCrAnOpF (kalnayFermionCreate p)
        + ofCrAnOpF (kalnayFermionCreate p) * ofCrAnOpF (kalnayFermionAnnihil p)) = 1

/-- The non-point phase-space carrier: three nodules, two counter-rotating relative to the
reference, one full-turn magnitude, free phase-network realization, trefoil braid word, and
spinor/ribbon fermion holonomy. -/
def HasThreeNoduleTrefoilRegion {G : Type*} [Monoid G]
    (R : ThreeNodulePhaseRegion) (sigma1 sigma2 : G) : Prop :=
  Fintype.card Nodule = 3
    ∧ (phaseNetwork R).IsDecoupled
    ∧ R.turn 1 = -R.turn 0
    ∧ R.turn 2 = -R.turn 0
    ∧ (∀ i : Nodule, (R.phase i R.period - R.phase i 0) ^ 2 = (2 * Real.pi) ^ 2)
    ∧ (∀ i : Nodule,
      (phaseNetwork R).freeTrajectory i R.period = R.phase i R.period - R.phase i 0)
    ∧ (sigma1 * sigma2) ^ 2 = sigma1 * sigma1 * sigma2 * sigma1
    ∧ spinorThreeTurnHolonomy = ribbonTwist (1 / 2)

/-- A half-integer Wilson loop realizes the same fermion sign as the three-turn spinor
holonomy of the structured region. -/
def HasWilsonFermionSpin (k : ℕ) (a : Fin k) : Prop :=
  wilsonTopologicalSpin k a = spinorThreeTurnHolonomy

/-- The Lorenz-qubit algebraic core: Lor63 and GP-butterfly vector fields plus the Hopf/Bloch
Poincare-sphere identity. -/
def HasLorenzQubitCore (χ : Fin 2 → ℂ) (r : BlochVector)
    (sigma rho beta g m gp : ℝ) : Prop :=
  lor63Generator sigma rho beta g r *ᵥ r = lor63VectorField sigma rho beta g r
    ∧ gpButterflyGenerator m gp r *ᵥ r = gpButterflyVectorField m gp r
    ∧ (r 0 : ℂ) ^ 2 + (r 1 : ℂ) ^ 2 + (r 2 : ℂ) ^ 2 = hopfIntensity χ ^ 2

/-- The existing dissipative-Nambu contour/strange-attractor deformation theorem, specialized
to the Lorenz-qubit Bloch-vector carrier. -/
def HasLorenzNambuAttractorDeformation
    (S_R : ℝ) (gD : BlochVector) (t hbar : ℝ) : Prop :=
  ‖nnPathWeight S_R (nambuImaginaryAction gD t) hbar‖ < 1

/-- The checked absorption/emission skeleton: Pauli-bounded absorption, complex-action KL
readout, unit-payload Yang-Baxter convolution, and Dirac alpha/beta zitterbewegung marker. -/
def HasFermionBosonInformationCycle
    (C : AbsorptionEmissionCycle) (s : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  BosonAbsorptionAllowed C.occupationParameter C.absorbedPayload
    ∧ C.emittedPayload = complexActionNats C.hbar C.complexAction.im
    ∧ YangBaxter (klBraidConvolutionOperator 1 true) (klBraidConvolutionOperator 1 false)
    ∧ diracAlpha s * diracBeta + diracBeta * diracAlpha s = 0

/-- Rest-frame zitterbewegung is twice the Compton frequency. -/
def HasRestZitterbewegungCompton (mass lightSpeed hbar : ℝ) : Prop :=
  zitterbewegungFrequency 0 mass lightSpeed hbar = 2 * comptonFrequency mass lightSpeed hbar

/-- The Dirac-sector CPT capability: the Greaves--Thomas/Bennett `CPT` matrix `A = -iγ⁵`
preserves the Dirac operator under total momentum inversion, maps solutions at `p` to solutions
at `-p`, is the endpoint of the chiral complexification path, and has the fermionic square
`CPT² = -1`. -/
def HasDiracCPTInvariance (p4 : Fin 4 → ℝ) (m : ℝ) (ψ : Fin 4 → ℂ) : Prop :=
  ((-I) • γ5) * diracOp (-p4) m * (-((-I) • γ5)) = diracOp p4 m
    ∧ (diracOp p4 m *ᵥ ψ = 0 →
      diracOp (-p4) m *ᵥ ((-((-I) • γ5)) *ᵥ ψ) = 0)
    ∧ cpt ψ = chiralRot (-(Real.pi / 2)) *ᵥ ψ
    ∧ cpt (cpt ψ) = -ψ

/-- The Dirac chirality capability: `γ⁵` is an involution, its Bennett left/right projectors
are complete, idempotent, and orthogonal, and the same `γ⁵` acts as the concrete chirality
charge grading: `γ⁵` preserves chirality while every Dirac vector `γ^μ` flips it. -/
def HasDiracChiralityStructure : Prop :=
  γ5 * γ5 = (1 : Matrix (Fin 4) (Fin 4) ℂ)
    ∧ bennettProjU γ5 + bennettProjV γ5 = 1
    ∧ bennettProjU γ5 * bennettProjU γ5 = bennettProjU γ5
    ∧ bennettProjV γ5 * bennettProjV γ5 = bennettProjV γ5
    ∧ bennettProjV γ5 * bennettProjU γ5 = 0
    ∧ IsChargePreserving (Matrix.mulVecLin γ5) (Matrix.mulVecLin γ5)
    ∧ ∀ μ : Fin 4, IsChargeConjugating (Matrix.mulVecLin γ5) (Matrix.mulVecLin (γ μ))

lemma dirac_cpt_invariance_checked (p4 : Fin 4 → ℝ) (m : ℝ) (ψ : Fin 4 → ℂ) :
    HasDiracCPTInvariance p4 m ψ :=
  ⟨cpt_diracOp_invariant p4 m, fun h => cpt_maps_dirac_solution p4 m ψ h,
    cpt_eq_chiralRot ψ, cpt_sq ψ⟩

lemma dirac_chirality_structure_checked : HasDiracChiralityStructure := by
  rcases chirality_projectors with ⟨hcomplete, hleft, hright, horthogonal⟩
  exact ⟨γ5_sq, hcomplete, hleft, hright, horthogonal, dirac_chirality_chargePreserving,
    fun μ => dirac_vector_chiralityConjugating μ⟩

/-- The existing electroweak representation support used here: the `U(1)` doublet
representation and the fundamental `SU(2)` doublet representation commute, so they assemble
as the `SU(2)_L × U(1)_Y` electroweak doublet action. -/
def HasElectroweakDoubletRepresentation : Prop :=
  ∀ (u1 : unitary ℂ) (g2 : specialUnitaryGroup (Fin 2) ℂ),
    repU1 u1 * fundamentalSU2 g2 = fundamentalSU2 g2 * repU1 u1

/-- Standard Model electroweak/Yukawa support already available in the repo: an electroweak
doublet representation, dimensionless Yukawa coupling, generated mass dimension after the Higgs
VEV, dimensionless Higgs-fermion coupling, and the algebraic post-EWSB identities
`m_f = y_f v / sqrt 2`, recovered `y_f`, `g_hff = y_f / sqrt 2`, and the
sterile-neutrino Dirac Yukawa channel feeding the existing Type-I seesaw matrix. -/
def HasStandardModelElectroweakYukawaSupport (y v : ℝ) : Prop :=
  HasElectroweakDoubletRepresentation
    ∧ yukawaCouplingDim4 = 1
    ∧ yukawaCouplingDim4 * higgsVEVDim4 = massParameterDim4
    ∧ massParameterDim4 / higgsVEVDim4 = 1
    ∧ _root_.Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaMass y v
      = _root_.Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.yukawaMass y v
    ∧ _root_.Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaCoupling
        (_root_.Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaMass y v) v = y
    ∧ higgsFermionCouplingFromMass
        (_root_.Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaMass y v) v
      = higgsFermionCouplingFromYukawa y
    ∧ ∀ M_N : ℝ, HasDiracNeutrinoYukawaSingletBridge y v M_N

lemma standardModel_electroweak_yukawa_support_checked (y v : ℝ) (hv : v ≠ 0) :
    HasStandardModelElectroweakYukawaSupport y v := by
  rcases standardModelYukawa_dimensional_requirements with ⟨hdimless, hmassdim, hcouplingdim⟩
  rcases standardModelYukawa_algebraic_requirements y v hv with ⟨hmass, hrecover, hcoupling⟩
  exact ⟨fun u1 g2 => repU1_fundamentalSU2_commute u1 g2, hdimless, hmassdim,
    hcouplingdim, hmass, hrecover, hcoupling,
    fun M_N => diracNeutrinoYukawaSingletBridge_checked y v M_N⟩

/-- The Standard-Model fermion quantum-number capability supplied by the checked `SU(5)` generation
construction: exactly `15` Weyl states per generation, electric charge computed by
Gell-Mann--Nishijima, electric neutrality of the full generation, vanishing `Tr Y` / `Tr Y^3`,
named first-generation components, and flavor-labelled three-generation particles. -/
def HasStandardModelFermionQuantumNumberComputation : Prop :=
  Fintype.card SMWeylFermion = 15
    ∧ (∀ f : SMWeylFermion,
      (fermionQuantumNumbers f).electricCharge =
        gellMannNishijima (fermionQuantumNumbers f).weakIsospin3
          (fermionQuantumNumbers f).hypercharge)
    ∧ smGenerationElectricChargeTrace = 0
    ∧ smGenerationHyperchargeTrace = 0
    ∧ smGenerationCubicHyperchargeTrace = 0
    ∧ HasNamedFirstGenerationFermionComputations
    ∧ HasNamedThreeGenerationFermionComputations

lemma standardModel_fermion_quantum_number_computation_checked :
    HasStandardModelFermionQuantumNumberComputation :=
  ⟨smWeylFermion_state_count, fermionElectricCharge_eq_gmn, smGenerationCharge_zero,
    smGenerationHyperchargeTrace_zero, smGenerationCubicHyperchargeTrace_zero,
    namedFirstGenerationFermionComputations_checked, namedThreeGenerationFermionComputations_checked⟩

/-! ## Document-guided C3/C6/C9 coherence-topology readings -/

/-- The document's `C3` reading, interpreted through existing checked repo
objects rather than as a new finite carrier: three phase nodules, trefoil braid
closure, spinor/ribbon fermion sign, and the three-quark baryon statistics and
named hadron computations already proved in the particle sector. -/
def HasC3TrefoilHadronCoherence {G : Type*} [Monoid G]
    (R : ThreeNodulePhaseRegion) (sigma1 sigma2 : G) : Prop :=
  HasThreeNoduleTrefoilRegion R sigma1 sigma2
    ∧ spinorThreeTurnHolonomy = ribbonTwist (1 / 2)
    ∧ scalarThreeTurnHolonomy ≠ spinorThreeTurnHolonomy
    ∧ compositeTwist 3 = -1
    ∧ 3 * quarkBaryonNumber = 1
    ∧ HasNamedHadronComputations

/-- The `C3` topology/coherence reading is exactly the existing three-lobed
trefoil region plus the existing baryon/hadron sector. This proves the checked
content of the notes' "three-loop" intuition without treating `C3` as a new
standalone object. -/
lemma c3TrefoilHadronCoherence_checked
    {G : Type*} [Monoid G] (R : ThreeNodulePhaseRegion) {sigma1 sigma2 : G}
    (hBraid : RealizesTrefoilBraid sigma1 sigma2) :
    HasC3TrefoilHadronCoherence R sigma1 sigma2 :=
  ⟨three_lobed_dirac_trefoil_phase_region R hBraid,
    spinorThreeTurnHolonomy_eq_ribbonTwist,
    scalar_spinor_threeTurnHolonomy_ne,
    baryon_is_fermion,
    baryonNumber_baryon,
    namedHadronComputations_checked⟩

/-- The document's `C6` electron reading, interpreted as the existing electron
trefoil/coherence package: trefoil chirality distinguishes electron from
positron, the spinor three-turn holonomy is the fermion ribbon sign, the
rest-frame zitterbewegung frequency is twice the Compton frequency, and the
Dirac chirality plus Standard-Model quantum-number computation are available. -/
def HasC6ElectronTrefoilCoherence (mass lightSpeed hbarZitter : ℝ) : Prop :=
  spinorThreeTurnHolonomy = ribbonTwist (1 / 2)
    ∧ scalarThreeTurnHolonomy ≠ spinorThreeTurnHolonomy
    ∧ electronJones 2 ≠ positronJones 2
    ∧ HasRestZitterbewegungCompton mass lightSpeed hbarZitter
    ∧ HasDiracChiralityStructure
    ∧ HasStandardModelFermionQuantumNumberComputation

/-- The `C6` electron coherence reading is checked from the trefoil Jones
invariant, the Hopf/ribbon spinor sign, Dirac zitterbewegung, chirality, and the
computed Standard-Model fermion quantum numbers. It does not claim a derived
electron mass hierarchy; it identifies the existing formal electron package
with the stronger trefoil/coherence interpretation found in the notes. -/
lemma c6ElectronTrefoilCoherence_checked
    (mass lightSpeed hbarZitter : ℝ) (hmass : 0 ≤ mass) :
    HasC6ElectronTrefoilCoherence mass lightSpeed hbarZitter :=
  ⟨spinorThreeTurnHolonomy_eq_ribbonTwist,
    scalar_spinor_threeTurnHolonomy_ne,
    trefoil_chiral_distinguishes,
    zitterbewegung_rest_eq_two_compton mass lightSpeed hbarZitter hmass,
    dirac_chirality_structure_checked,
    standardModel_fermion_quantum_number_computation_checked⟩

/-- The document's `C9` muon reading, interpreted through the existing muon
Schmidt/rapidity formalization: the muon mode is the same hyperbolic
three-faces object as the horizon-cell oscillator at the muon's rapidity,
with positive entanglement entropy. -/
def HasC9MuonCoherenceMode (α : ℝ) : Prop :=
  0 < α
    ∧ IsHarmonicOscillator 1 (cellEnergyVector (muonRapidity α))
    ∧ timelike (cellEnergyVector (muonRapidity α))
    ∧ schmidtNumber (muonRapidity α)
        = (cellEnergyVector (muonRapidity α)).re
          / (cellEnergyVector (muonRapidity α)).im
    ∧ schmidtNumber (muonRapidity α) = schmidtNumberFromAlpha α
    ∧ 1 < schmidtNumber (muonRapidity α)
    ∧ anomaly (muonRapidity α) = schwingerAnomaly α
    ∧ 0 < muonRenyi2Entropy α

/-- The `C9` muon coherence reading is checked by the existing muon
three-faces theorem and the existing muon Rényi-2 entropy positivity theorem. -/
lemma c9MuonCoherenceMode_checked (α : ℝ) (hα : 0 < α) :
    HasC9MuonCoherenceMode α := by
  rcases muonMode_threeFaces α hα with
    ⟨hdyn, htime, hratio, hschmidt, hentangled, hanomaly⟩
  exact ⟨hα, hdyn, htime, hratio, hschmidt, hentangled, hanomaly,
    muonRenyi2Entropy_pos α hα⟩

/-- Conservative formal version of the notes' `C9 -> C6` projection idea:
the `C9` muon coherence mode and the `C6` electron trefoil package are both
available, and the observed Michel channel balances the additive quantum
numbers. The theorem deliberately does not claim that the topology derives the
decay rate or the lepton masses. -/
def HasC9ToC6LeptonicProjectionBridge
    (α mass lightSpeed hbarZitter : ℝ) : Prop :=
  HasC9MuonCoherenceMode α
    ∧ HasC6ElectronTrefoilCoherence mass lightSpeed hbarZitter
    ∧ muon = electron + antiNeutrino + muonNeutrino

/-- The checked `C9 -> C6` bridge: existing muon coherence/entropy, existing
electron trefoil/Dirac package, and existing Michel decay conservation. -/
lemma c9_to_c6_leptonicProjectionBridge_checked
    (α mass lightSpeed hbarZitter : ℝ) (hα : 0 < α) (hmass : 0 ≤ mass) :
    HasC9ToC6LeptonicProjectionBridge α mass lightSpeed hbarZitter :=
  ⟨c9MuonCoherenceMode_checked α hα,
    c6ElectronTrefoilCoherence_checked mass lightSpeed hbarZitter hmass,
    muon_decay_conserves⟩

/-- The combined C3/C6/C9 coherence-topology synthesis available from the
current repo: `C3` as the three-lobed trefoil/hadron sector, `C6` as the
electron trefoil/Dirac/SM quantum-number package, and `C9` as the muon
Schmidt/rapidity coherence mode whose projection to the electron channel is
conservation-compatible. -/
def HasC3C6C9CoherenceTopologySynthesis
    {G : Type*} [Monoid G] (R : ThreeNodulePhaseRegion) (sigma1 sigma2 : G)
    (α mass lightSpeed hbarZitter : ℝ) : Prop :=
  HasC3TrefoilHadronCoherence R sigma1 sigma2
    ∧ HasC6ElectronTrefoilCoherence mass lightSpeed hbarZitter
    ∧ HasC9ToC6LeptonicProjectionBridge α mass lightSpeed hbarZitter

/-- The repo-level C3/C6/C9 synthesis, proven only from existing checked
topology, particle, information, and conservation-law infrastructure. -/
lemma c3_c6_c9_coherenceTopologySynthesis_checked
    {G : Type*} [Monoid G] (R : ThreeNodulePhaseRegion) {sigma1 sigma2 : G}
    (hBraid : RealizesTrefoilBraid sigma1 sigma2)
    (α mass lightSpeed hbarZitter : ℝ) (hα : 0 < α) (hmass : 0 ≤ mass) :
    HasC3C6C9CoherenceTopologySynthesis R sigma1 sigma2 α mass lightSpeed hbarZitter :=
  ⟨c3TrefoilHadronCoherence_checked R hBraid,
    c6ElectronTrefoilCoherence_checked mass lightSpeed hbarZitter hmass,
    c9_to_c6_leptonicProjectionBridge_checked α mass lightSpeed hbarZitter hα hmass⟩

/-! ## Assembled theorem -/

/-- The repo-level checked electron/fermion-region synthesis.

Given the explicit phase-region, braid, Hopf/Bloch, Lorenz/Nambu, Wilson-line, and
absorption/emission hypotheses, Lean derives the full assembled capability from existing theorem
carriers. This is the formal model currently available in the repo: fermion fields from Bose
bilinears in the Kálnay sector, a non-point trefoil/Hopf/Wilson phase region, Lorenz-qubit
Bloch dynamics with dissipative-Nambu contour deformation, and complex-action information
emission, Dirac `CPT` invariance, the `γ⁵` chirality projectors/charge grading, and the
existing Standard Model electroweak/Yukawa support plus the computable three-generation
fermion quantum-number construction and the optional sterile right-handed neutrino singlet
extension. -/
lemma structuredElectronFermionRegion_checked
    {G : Type*} [Monoid G]
    (R : ThreeNodulePhaseRegion) {sigma1 sigma2 : G}
    (hBraid : RealizesTrefoilBraid sigma1 sigma2)
    (p : Momentum 3)
    (χ : Fin 2 → ℂ) (r : BlochVector) (hHopf : IsHopfBlochVector χ r)
    (lorSigma lorRho lorBeta lorG gpM gpG : ℝ)
    (S_R : ℝ) {gD : BlochVector} {t hbarAction : ℝ}
    (hgD : gD ≠ 0) (ht : 0 < t) (hhbarAction : 0 < hbarAction)
    (C : AbsorptionEmissionCycle) (s : Matrix (Fin 2) (Fin 2) ℂ)
    (smYukawa higgsVEV : ℝ) (hHiggsVEV : higgsVEV ≠ 0)
    (p4 : Fin 4 → ℝ) (diracMass : ℝ) (ψ4 : Fin 4 → ℂ)
    (mass lightSpeed hbarZitter : ℝ) (hmass : 0 ≤ mass)
    {k : ℕ} (hk : 0 < k) (a : Fin k) (ha : (a.val : ℝ) ^ 2 = k) :
    HasConcreteKalnayCAR
      ∧ HasKalnayFermionFromBose p
      ∧ HasThreeNoduleTrefoilRegion R sigma1 sigma2
      ∧ HasWilsonFermionSpin k a
      ∧ HasLorenzQubitCore χ r lorSigma lorRho lorBeta lorG gpM gpG
      ∧ HasLorenzNambuAttractorDeformation S_R gD t hbarAction
      ∧ HasFermionBosonInformationCycle C s
      ∧ HasRestZitterbewegungCompton mass lightSpeed hbarZitter
      ∧ HasDiracCPTInvariance p4 diracMass ψ4
      ∧ HasDiracChiralityStructure
      ∧ HasStandardModelElectroweakYukawaSupport smYukawa higgsVEV
      ∧ HasStandardModelFermionQuantumNumberComputation
      ∧ HasSterileRightHandedNeutrinoSingletComputations :=
  ⟨kalnay_bose_bilinear_realization,
    kalnay_fermion_field_from_bose_fields p,
    three_lobed_dirac_trefoil_phase_region R hBraid,
    wilson_fermion_spin_matches_threeTurnHolonomy k hk a ha,
    lorenz_qubit_checked_core χ r hHopf lorSigma lorRho lorBeta lorG gpM gpG,
    lorenzQubit_existing_nambu_attractor_deformation S_R hgD ht hhbarAction,
    fermion_boson_information_cycle_capability C s,
    zitterbewegung_rest_eq_two_compton mass lightSpeed hbarZitter hmass,
    dirac_cpt_invariance_checked p4 diracMass ψ4,
    dirac_chirality_structure_checked,
    standardModel_electroweak_yukawa_support_checked smYukawa higgsVEV hHiggsVEV,
    standardModel_fermion_quantum_number_computation_checked,
    sterileRightHandedNeutrinoSingletComputations_checked⟩

/-- The synthesis keeps the currently verified gaps explicit: it does not promote the carrier
results to CAR-on-region or Haag duality. -/
lemma structuredElectronFermionRegion_remaining_regional_gaps :
    currentRegionOperatorGapChecklist.carOnRegion = GapStatus.obligation
      ∧ currentRegionOperatorGapChecklist.haagDuality = GapStatus.obligation :=
  ⟨current_gap_status_carOnRegion, current_gap_status_haagDuality⟩

end Physlib.QuantumMechanics.ComplexAction.Fermion.StructuredElectronFermionRegion

end
