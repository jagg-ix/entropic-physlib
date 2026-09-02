/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule
public import Physlib.QuantumMechanics.Foundations.RelativeStateConventionality
public import Physlib.QuantumMechanics.FrozenLimit
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravityField
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSchrodingerNagaoNielsen
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein
public import Physlib.Electromagnetism.Distributional.Dynamics.Lagrangian
meta import Zil

/-!
# The entropic-dynamics program, as one explicitly conditional theorem

This module assembles five existing kernel-clean capstones into the historical public theorem
`entropicDynamics_derives_physics`.  The theorem name is retained for API compatibility, but its statement
must be read with the hypotheses displayed in its type.  It is a typed synthesis, not a parameter-free
derivation of quantum mechanics and gravity from no physical input:

* **I. Born amplitude reconstruction** — the entropic wave function `ψ = √ρ · e^{iΦ}` recovers the probability
  density as its squared modulus, `‖ψ‖² = ρ` (`EntropicDynamicsWaveFunctionReconstruction`). The Madelung /
  Born amplitude is a construction, not an axiom.
* **II. Born-weight selection** — a continuous branch-weight functional that obeys the symmetric-refinement
  values `k/n ↦ k/n` is forced to assign every normalized ket branch its squared amplitude
  (`RelativeStateConventionality.deutsch_born_unequal`).  This is the repository's conditional
  symmetry/refinement/continuity derivation; it is not a derivation from unitarity and it does not yet formalize
  Deutsch's decision-theoretic rationality and utility-representation layer.
* **III. Generic-measurement transport of the selected Born rule** — `‖⟪s, ψ⟫‖²` is invariant under any
  linear isometry (`CatichaMeasurementGenericBornRule.generic_born_rule`).  Unitarity transports the independently
  selected modulus-squared weight to another measurement basis; it does not select that weight by itself.
* **IV. Exact frozen-sector reduction** — under the explicit premise `H_I = 0`, entropic corrections vanish
  and the definitions reduce to their reversible/geometric forms
  (`FrozenLimit.frozen_limit_recovers_standard_physics`).  This is not an analytic `Γ → ∞` convergence theorem.
* **V. Conditional holographic Newton identity** — after assuming that `N` is the holographic bit count built
  from the same `G`, the theorem solves that identification as `G = 𝒜·c³/(ℏ·N)`.  The accompanying complex
  Einstein source equation is also an explicit premise, not a conclusion of the clock/contour algebra.

The conjunction introduces no new proof principle and is kernel-clean, but its epistemic status is
`ansatz-loaded`: the exact identities and reductions are useful only with their displayed physical/model data.
-/

set_option autoImplicit false

open scoped InnerProductSpace
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule
open Physlib.QuantumMechanics.Foundations.MinimalModalOnticDynamics
open Physlib.QuantumMechanics.Foundations.RelativeStateConventionality
open Physlib.QuantumMechanics.FrozenLimit
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity
open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.ComptonClock
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3

@[expose] public section

namespace Physlib.Meta.EntropicDynamicsThesis

/-- **[The conditional entropic-dynamics synthesis, in one theorem].**  This historical public theorem
collects: **(I)** the polar identity `‖√ρ e^{iΦ}‖² = ρ`; **(II)** selection of squared-amplitude branch weights
from explicit symmetric-refinement and continuity premises; **(III)** their unitary transport; **(IV)**
exact reduction at the explicit frozen-sector premise `H_I = 0`; and **(V)**
the area-per-bit expression for `G` conditional on identifying `N` with the holographic bit count that already
contains `G`, alongside a separately assumed complex Einstein source equation.  It is a composition of
audited capstones, not an unconditional or parameter-free derivation of quantum mechanics and gravity. -/
@[zil_claim physlib.entropicDynamics.thesis,
  zil_concept physics.entropicDynamicsDerivation, zil_requires assumptions.entropicDynamicsSpine,
  zil_export]
theorem entropicDynamics_derives_physics
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [FiniteDimensional ℂ H]
    {d : Type*} [Fintype d] [DecidableEq d] {sd : ℕ} :
    -- I. Born amplitude reconstruction (Madelung): `‖√ρ e^{iΦ}‖² = ρ`.
    (∀ ρ Φ : ℝ, 0 ≤ ρ → ‖edWaveFunction ρ Φ‖ ^ 2 = ρ)
    -- II. Born-weight selection from explicit refinement and continuity premises.
      ∧ (∀ (Ψ : Ket d) (f : ℝ → ℝ), Continuous f →
          (∀ (k n : ℕ), 0 < n → k ≤ n → f ((k : ℝ) / n) = (k : ℝ) / n) →
          ∀ m : d, f (Complex.normSq (Ψ m)) = Complex.normSq (Ψ m))
    -- III. unitary basis transport of modulus-squared transition probabilities.
      ∧ (∀ (U : E →ₗᵢ[ℂ] E) (s ψ : E), ‖⟪U s, U ψ⟫_ℂ‖ ^ 2 = ‖⟪s, ψ⟫_ℂ‖ ^ 2)
    -- IV. exact recovery in the supplied `H_I = 0` frozen sector.
      ∧ (∀ (C : FrozenContext (H := H) (d := d) (sd := sd))
           (q p : SpaceTime sd) (ψ : H) (x : SpaceTime sd) (Γ_inf : ℝ),
           FrozenRecovery C q p ψ x Γ_inf)
    -- V. conditional holographic-bit inversion `G = 𝒜·c³/(ℏ·N)`.
      ∧ (∀ (F : StaticPoissonField3) (ℏ c N m η θ ε : ℝ)
           (Λ S : StaticPotentialSpace3 → Matrix (Fin 4) (Fin 4) ℝ)
           (_ : 0 < ℏ) (_ : 0 < c) (_ : 0 < m) (_ : 0 < η)
           (_ : F.newtonConstant ≠ 0) (_ : 0 < ε)
           (_ : N = holographicBits
             (sphereArea (entropicProperDistance m c ℏ η)) F.newtonConstant ℏ c)
           (_ : ∀ x, Λ x = (8 * Real.pi * F.newtonConstant / c ^ 4) • S x),
           F.newtonConstant
             = sphereArea (entropicProperDistance m c ℏ η) * c ^ 3 / (ℏ * N)) :=
  ⟨fun ρ Φ hρ => edWaveFunction_modulus_sq ρ Φ hρ,
   fun Ψ f hf hrat m => deutsch_born_unequal Ψ f hf hrat m,
   fun U s ψ => generic_born_rule U s ψ,
   fun C q p ψ x Γ_inf => frozen_limit_recovers_standard_physics C q p ψ x Γ_inf,
   fun F ℏ c N m η θ ε Λ S hℏ hc hm hη hG hε hN hIm =>
     (holographicNewton_comptonNagaoLeviCivita_staticPoissonField_chain
       F ℏ c N m η θ ε Λ S hℏ hc hm hη hG hε hN hIm).1⟩

#zil_validate_embedded entropicDynamics_derives_physics where
  no_sorry, claim_linked, requirement_linked

zil attach entropicDynamics_derives_physics where
  formalizes @ "claim:conditional-entropic-dynamics-quantum-classical-gravity-synthesis",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:entropic-dynamics-spine",
  requires @ "claim:entropic-wavefunction-modulus",
  requires @ "assumption:continuous-symmetric-refinement-consistent-branch-weight",
  requires @ "assumption:unitary-measurement-device",
  requires @ "assumption:zero-irreversible-generator-frozen-sector",
  requires @ "assumption:holographic-bit-count-identification-containing-newton-G",
  requires @ "assumption:complex-einstein-source-equation",
  supported_by @ "paper:caticha-entropic-dynamics",
  caveat @ "claim:conjunction-of-existing-capstones-no-new-proof-principle",
  caveat @ "epistemic:born-weight-is-selected-conditionally-by-symmetric-refinement-and-continuity-then-transported-by-unitarity-the-decision-theoretic-rationality-and-utility-layer-remains-unformalized",
  caveat @ "epistemic:frozen-leg-is-an-exact-HI-zero-reduction-and-gravity-leg-inverts-an-ansatz-containing-G"

zil attach
    Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.deutsch_born_unequal
    where
  formalizes @ "claim:continuous-symmetric-refinement-selects-squared-amplitude-branch-weight",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:continuous-branch-weight-functional",
  requires @ "assumption:symmetric-refinement-values-k-over-n",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.branchWeight_symmetric_uniform",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.rational_born_realized",
  supported_by @ "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.continuous_rational_born_extension",
  caveat @ "epistemic:selects-the-unique-weight-functional-under-explicit-premises-but-does-not-formalize-the-decision-theoretic-rationality-or-utility-representation-that-interprets-it-as-betting-probability"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule.generic_born_rule
    where
  formalizes @ "claim:unitary-measurement-device-transports-the-position-born-rule-to-a-generic-measurement-basis",
  epistemic_status @ "consistency-identity",
  requires @ "assumption:position-born-rule",
  supported_by @ "lean:LinearIsometry.inner_map_map",
  caveat @ "epistemic:inner-product-invariance-does-not-derive-the-modulus-squared-position-probability-postulate-from-unitarity-alone"

zil_theorem_intent entropicDynamics_derives_physics where
  at_level bridge_theorem
  must_mention [edWaveFunction,
    Physlib.QuantumMechanics.FrozenLimit.FrozenRecovery,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3]

zil_file_contract physlib.entropicDynamicsThesis where
  promises "One kernel-clean conditional synthesis of five existing results: the entropic polar identity, squared-amplitude branch-weight selection from symmetric refinement plus continuity, unitary transport of that selected weight, exact reversible/geometric reduction at H_I = 0, and the area-per-bit expression for Newton's constant under the explicit holographic-bit identification and complex-Einstein-source premises."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq",
    "lean:Physlib.QuantumMechanics.Foundations.RelativeStateConventionality.deutsch_born_unequal",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CatichaMeasurementGenericBornRule.generic_born_rule",
    "lean:Physlib.QuantumMechanics.FrozenLimit.frozen_limit_recovers_standard_physics",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_staticPoissonField_chain"]
  forbids_substitutes ["calling the conjunction an unconditional or parameter-free derivation of quantum mechanics and gravity",
    "claiming unitarity selects the Born weight rather than transports the independently selected weight",
    "claiming the decision-theoretic rationality and utility-representation layer is formalized",
    "calling the exact H_I equals zero reduction a proved Gamma-tends-to-infinity convergence theorem",
    "calling the holographic bit-count inversion an independent numerical prediction of Newton's constant",
    "a derivation of the Standard Model or a specific particle spectrum",
    "an unconditional prediction of a fundamental constant's numerical value"]
  witnessed_by [entropicDynamics_derives_physics]

#zil_formalization_lint physlib.entropicDynamicsThesis

/-! ## B. Normalized Schrödinger realization of the thesis's Caticha layer -/

zil_file_contract physlib.entropicDynamicsThesis.normalizedSchrodingerRealization where
  promises "The normalized infinite-mode Perepelkin solution supplies a unit-Born-mass realization of the thesis's Caticha wave-function layer, with every spectral coefficient linked to the zero-damping non-Hermitian equation, Nagao--Nielsen complex-action phase, and Caticha linear generator."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSchrodingerNagaoNielsen.normalizedPerepelkin_nonHermitian_nagaoNielsen_caticha_chain"
  ]
  forbids_substitutes [
    "claiming the modewise time derivative proves the summed spatial functional Schrodinger PDE",
    "claiming pointwise Born-density reconstruction identifies the Caticha phase"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSchrodingerNagaoNielsen.normalizedPerepelkin_nonHermitian_nagaoNielsen_caticha_chain
  ]

#zil_formalization_lint physlib.entropicDynamicsThesis.normalizedSchrodingerRealization

/-! ## B.1. Constructed interacting continuum realization -/

zil_file_contract physlib.entropicDynamicsThesis.interactingFunctionalMeasurement where
  promises "The Caticha layer has a constructed configuration-local interacting functional Schrodinger evolution on continuum L2, an actual normalized Born probability measure obtained by density with respect to the configuration measure, and measurable continuum-detector outcome laws obtained by pushforward."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.evolution_unitaryC0",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.pointwiseEvolution_schrodinger",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.bornMeasure_evolution",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.ContinuumDetector.outcomeLaw_apply"
  ]
  forbids_substitutes [
    "claiming a configuration-local diagonal interaction is a constructed arbitrary functional differential Hamiltonian",
    "claiming the supplied reference measure has been derived from a renormalized path integral",
    "claiming a measurable detector readout includes pointer amplification, decoherence, or collapse"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.evolution_unitaryC0,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.pointwiseEvolution_schrodinger,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.bornMeasure_evolution,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.ContinuumDetector.outcomeLaw_apply
  ]

#zil_formalization_lint physlib.entropicDynamicsThesis.interactingFunctionalMeasurement

/-! ## C. Gauge, modular, and curved-electrodynamics realization -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.gaugeCovariantSmearedSchrodinger_equation_covariant
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.SatisfiesGaugeCovariantSmearedSchrodinger
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantDerivative_gauge_covariant
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantDerivative
  ]

zil_theorem_intent
    Electromagnetism.DistElectromagneticPotential.satisfiesDistributionalMaxwell_testFunction
    where
  at_level structural
  must_mention [
    Electromagnetism.DistElectromagneticPotential.SatisfiesDistributionalMaxwell,
    Electromagnetism.DistElectromagneticPotential.fieldStrength
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.diagonalModular_catichaIntertwines
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.CatichaModularIntertwines,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.matrixEntryReadout
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.curvedMaxwell_implies_waveWithConnection_of_lorenzGauge
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.MaxwellInhomogeneousCurved,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.WaveEquationPotentialWithConnection
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.maxwellWaveWithConnection_and_complexEinstein_split
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.WaveEquationPotentialWithConnection,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_of_lorenzGauge
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.christoffelFromMetric,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.RicciCoupledVectorWaveEquationAt
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_onChart
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.RicciCoupledVectorWaveEquationOnChart
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.metricFieldMaxwell_implies_ricciCoupledWave_onChart
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.metricFirstJet,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaConnectionField,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.RicciCoupledVectorWaveEquationOnChart
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_implies_ricciCoupledWave_onChart
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.frechetCoordinatePartial,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.RicciCoupledVectorWaveEquationOnChart
  ]

zil_file_contract physlib.entropicDynamicsThesis.curvedElectrodynamicsRealization where
  promises "The Caticha layer has explicit gauge-covariant smeared and minimally coupled evolution, a constructed finite diagonal-modular scalar readout, a Schwartz-testable distributional Maxwell equation, and a C2 field-realized chart Levi-Civita Maxwell equation whose native Frechet coordinate derivatives produce the Ricci-coupled vector wave operator."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.gaugeCovariantSmearedSchrodinger_equation_covariant",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantDerivative_gauge_covariant",
    "lean:Electromagnetism.DistElectromagneticPotential.satisfiesDistributionalMaxwell_testFunction",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.diagonalModular_catichaIntertwines",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.curvedMaxwell_implies_waveWithConnection_of_lorenzGauge",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.maxwellWaveWithConnection_and_complexEinstein_split",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_of_lorenzGauge",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_onChart",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.metricFieldMaxwell_implies_ricciCoupledWave_onChart",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_implies_ricciCoupledWave_onChart"
  ]
  forbids_substitutes [
    "claiming a finite matrix-entry readout constructs the continuum field functional",
    "discarding connection corrections in general coordinates",
    "claiming the pointwise Ricci-coupled identity supplies global hyperbolic estimates or a propagator construction",
    "promoting field-realized coordinate jets to a coordinate-free global manifold theorem",
    "claiming the flat tempered-distribution equation is already a curved-spacetime distributional equation",
    "claiming these conditional equations construct an interacting curved-spacetime QFT"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.gaugeCovariantSmearedSchrodinger_equation_covariant,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantDerivative_gauge_covariant,
    Electromagnetism.DistElectromagneticPotential.satisfiesDistributionalMaxwell_testFunction,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.diagonalModular_catichaIntertwines,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.curvedMaxwell_implies_waveWithConnection_of_lorenzGauge,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.maxwellWaveWithConnection_and_complexEinstein_split,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_of_lorenzGauge,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_onChart,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.metricFieldMaxwell_implies_ricciCoupledWave_onChart,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_implies_ricciCoupledWave_onChart
  ]

#zil_formalization_lint physlib.entropicDynamicsThesis.curvedElectrodynamicsRealization

end Physlib.Meta.EntropicDynamicsThesis
