/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.EntropicSpine
public import Physlib.QuantumMechanics.ComplexAction.BenderIdentity
public import Physlib.QuantumMechanics.FrozenLimit
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ADMConstraintPropagation
public import Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DoubleCopyCharacter
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.JacobiBianchiDoubleCopyFamily
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.NoetherConservationDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix
public import Physlib.QuantumMechanics.Entanglement.BellNoSignaling
public import Physlib.QuantumMechanics.Entanglement.BellMutualInformation
public import Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH
public import Physlib.QuantumMechanics.ComplexAction.Bell.AnnihilationPolarizationCorrelation
public import Physlib.QuantumMechanics.ComplexAction.Bell.LeviCivitaNagaoContour
public import Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling
public import Physlib.QuantumMechanics.ComplexAction.Bell.SorkinHadamardRegion
public import Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom
public import Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.HeatKernelBVAnomaly
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopPathIntegralVerch
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.PartitionFunction
public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Curvature
public import Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalEinsteinHilbertAction
public import Physlib.QuantumMechanics.ComplexAction.Curvature.GlobalElectrograviticAction
/- ZIL-BEGIN -/
public import Physlib.Meta.HolographicNewtonClockContourGravityZil
public import Physlib.Meta.MultiNormSection4PaperZil
public import Physlib.Meta.YukawaMadelungOpenProblemsZil
public import Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization
public import Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem
public import Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.GapPathIntegralOrigin
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaTypeIIIUnboundedDynamics
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtomicShellBonding
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleAPSIndexBridge
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesFiniteSpectralDynamics
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDGibbsVariational
public import Physlib.QuantumMechanics.ComplexAction.TensorNetworksComplexQuantumSystems
public meta import Zil
/- ZIL-END -/

/-!
# ZIL accountability for the entropic Physlib spine

This optional development/CI module adds no physical definitions, theorem
aliases, axioms, or proof terms. It imports the curated `Physlib.EntropicSpine`
and the principal recovery/gravity capstones, then records what their existing
Lean theorems actually establish.

The contracts deliberately separate algebraic, structural, toy-model, and
bridge-theorem levels. In particular, they do not promote pointwise identities
to empirical laws, the Bender lifetime to quantized time, conditional Newton
consistency to a measurement of `G`, or the Schwarzschild factor-two identity
to a dynamical horizon-rescaling mechanism.
-/

@[expose] public section

/- ZIL-BEGIN -/
open Zil
/- ZIL-END -/

namespace Physlib.Meta.EntropicSpineZil

/- ZIL-BEGIN -/
/-! ## A. Probability-metric structure -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric.wasserstein1Distance_triangle
    where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric.wasserstein1Distance
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric.wasserstein1Distance_triangle
    where
  formalizes @ "claim:entropic-spine-probability-metric-triangle",
  requires @ "assumption:integrable-cdf-differences",
  caveat @ "claim:does-not-establish-identity-of-indiscernibles-for-arbitrary-input-functions"

zil_file_contract physlib.entropicSpine.probabilityMetric where
  promises "formalization:probability-metric-triangle-layer"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric.wasserstein1Distance",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric.wasserstein1Distance_nonneg",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric.wasserstein1Distance_symm",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric.wasserstein1Distance_self",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric.wasserstein1Distance_triangle"
  ]
  forbids_substitutes [
    "calling the function-space construction a probability-measure metric without separation hypotheses"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric.wasserstein1Distance_triangle
  ]

/-! ## B. Free energy and relative entropy -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy.freeEnergy_ge_gibbs
    where
  at_level toy_model
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow.freeEnergyDensity,
    Real.exp,
    Real.log
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy.freeEnergy_ge_gibbs
    where
  formalizes @ "claim:pointwise-free-energy-gibbs-bound",
  supported_by @ "paper:jordan-kinderlehrer-otto-1998",
  caveat @ "claim:pointwise-density-result-not-integrated-h-theorem"

zil_file_contract physlib.entropicSpine.freeEnergyRelativeEntropy where
  promises "formalization:pointwise-free-energy-relative-entropy-layer"
  at_level toy_model
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow.freeEnergyDensity",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy.freeEnergyDensity_eq_relativeEntropy",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy.relativeEntropy_density_ge",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy.freeEnergy_ge_gibbs"
  ]
  forbids_substitutes [
    "presenting the pointwise scalar inequality as a proved normalized-density integral H-theorem",
    "presenting Gibbs minimization as an empirical relaxation-rate prediction"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy.freeEnergy_ge_gibbs
  ]

/-! ## C. Wave-function and Born reconstruction -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq
    where
  at_level algebraic
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq
    where
  formalizes @ "claim:entropic-wavefunction-modulus-squared",
  supported_by @ "paper:ipek-abedi-caticha-2018",
  caveat @ "claim:polar-form-algebra-not-first-principles-derivation-of-quantum-mechanics"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunctional_modulus_sq
    where
  at_level algebraic
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunctional
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunctional_modulus_sq
    where
  formalizes @ "claim:the-entropic-born-reconstruction-holds-pointwise-on-every-configuration-of-an-arbitrary-possibly-infinite-carrier",
  supported_by @ "paper:ipek-abedi-caticha-2018",
  caveat @ "claim:pointwise-polar-identity-without-a-discrete-or-finite-carrier-assumption-not-by-itself-a-choice-of-continuum-measure"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.integral_edWaveFunctional_modulus_sq_eq_one
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunctional
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.integral_edWaveFunctional_modulus_sq_eq_one
    where
  formalizes @ "claim:a-normalized-entropic-density-on-an-arbitrary-measure-space-reconstructs-a-wave-functional-with-total-integrated-born-probability-one",
  supported_by @ "lean:MeasureTheory.integral",
  caveat @ "claim:genuine-arbitrary-measure-continuum-normalization-conditional-on-the-explicit-density-normalization-premise-not-a-construction-of-a-functional-path-integral-measure"

zil_file_contract physlib.entropicSpine.waveFunctionReconstruction where
  promises "The entropic polar reconstruction is available as a scalar, pointwise on every configuration of an arbitrary possibly infinite carrier, and over arbitrary measure spaces; a normalized entropic density yields total integrated Born probability one."
  at_level algebraic
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.currentPotential",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunctional",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingComplexStructureSchrodinger.complexStructureJ_sq",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingComplexStructureSchrodinger.schrodinger_superposition"
  ]
  forbids_substitutes [
    "claiming that the modulus identity alone derives quantum mechanics from first principles",
    "claiming the arbitrary-measure normalization theorem constructs the continuum configuration-space measure rather than using the supplied measure and normalized density",
    "claiming that linear-map superposition proves a physical Hamiltonian is generated"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunctional_modulus_sq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.integral_edWaveFunctional_modulus_sq_eq_one
  ]

/-! ## D. Irreversible lifetime and decay -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.qifLifetime_decayFraction_eq_inv_e
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.benderDecayFraction,
    Physlib.QuantumMechanics.ComplexAction.qifLifetime,
    Real.exp
  ]

zil attach Physlib.QuantumMechanics.ComplexAction.qifLifetime_decayFraction_eq_inv_e where
  formalizes @ "claim:qif-lifetime-is-bender-one-over-e-time",
  supported_by @ "paper:bender-brody-hook-2008",
  caveat @ "claim:positive-real-lifetime-not-quantized-time",
  caveat @ "claim:does-not-prove-existence-of-a-gamow-state"

zil_file_contract physlib.entropicSpine.irreversibleLifetime where
  promises "formalization:bender-qif-lifetime-decay-bridge"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.lifetimeFromRate",
    "lean:Physlib.QuantumMechanics.ComplexAction.lifetime_pos",
    "lean:Physlib.QuantumMechanics.ComplexAction.lifetime_mul_width",
    "lean:Physlib.QuantumMechanics.ComplexAction.benderDecayFraction",
    "lean:Physlib.QuantumMechanics.ComplexAction.benderDecayFraction_strictAnti",
    "lean:Physlib.QuantumMechanics.ComplexAction.qifLifetime_decayFraction_eq_inv_e"
  ]
  forbids_substitutes [
    "time quantization",
    "a minimum physical time step",
    "existence of the assumed resonance or Gamow eigenstate"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.qifLifetime_decayFraction_eq_inv_e
  ]

/-! ## E. Frozen-limit recovery -/

zil_theorem_intent
    Physlib.QuantumMechanics.FrozenLimit.frozen_limit_recovers_standard_physics
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.FrozenLimit.FrozenContext,
    Physlib.QuantumMechanics.FrozenLimit.FrozenRecovery
  ]

zil attach
    Physlib.QuantumMechanics.FrozenLimit.frozen_limit_recovers_standard_physics
    where
  supported_by @ "lean:QuantumMechanics.decoherenceRate_tolman_invariant",
  formalizes @ "claim:zero-irreversible-generator-frozen-sector-recovers-reversible-and-geometric-identities",
  epistemic_status @ "consistency-identity",
  requires @ "assumption:zero-irreversible-generator",
  caveat @ "claim:recovery-theorem-not-a-proof-that-all-physical-systems-freeze",
  caveat @ "epistemic:exact-HI-zero-reduction-not-a-Gamma-tends-to-infinity-tendsto-theorem"

zil_file_contract physlib.entropicSpine.frozenRecovery where
  promises "formalization:exact-zero-irreversible-generator-reduction-to-reversible-and-geometric-identities"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.FrozenLimit.FrozenContext",
    "lean:Physlib.QuantumMechanics.FrozenLimit.FrozenRecovery",
    "lean:Physlib.QuantumMechanics.FrozenLimit.frozen_limit_recovers_standard_physics",
    "lean:Physlib.QuantumMechanics.FrozenLimit.tise_recovered_at_frozen_limit",
    "lean:Physlib.QuantumMechanics.FrozenLimit.finite_transition_metric_time_eq_scaled_rate_time"
  ]
  forbids_substitutes [
    "claiming unconditional equivalence between entropic time and geometric time",
    "claiming unitary recovery away from the zero irreversible-generator hypothesis",
    "claiming an analytic Gamma-tends-to-infinity limit without a Tendsto theorem"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.FrozenLimit.frozen_limit_recovers_standard_physics
  ]

/-! ## E.1 Analytic reversible-limit recovery -/

zil_file_contract physlib.entropicSpine.reversibleLimitConvergence where
  promises "formalization:analytic-and-explicit-exp-minus-two-rapidity-recovery-from-entropic-screen-and-complex-action-through-continuum-operators-bounded-time-propagators-and-measurement-readouts"
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entanglementScreenArea_tendsto_zero",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.comptonCellBits_tendsto_zero",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceEinsteinCoupling_eq_comptonCellBitForm",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonianConvolutionPotential_eq_convolution",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceSchrodingerPoissonGravitationalEnergy_eq_doubleIntegral",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_distributionalWeakFieldEinstein00_of_poisson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.temperedWeakFieldEinstein00Equation3_of_poisson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_weakFieldEinstein00",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_source_action",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_einstein00_and_energy_unique",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.GFreeNonlinearEinsteinCauchyProblem.exists_local_evolution",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.GFreeNonlinearEinsteinCauchyProblem.local_evolution_unique",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.schwartzLaplacian_convolution_right",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.temperedConvolutionSchwartz_laplacian",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.delta_temperedConvolutionSchwartz_apply",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.temperedFundamentalSolution_convolution",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.complexifyRealDistribution3_dirac",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.complexifyRealDistribution3_laplacian",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonKernelTempered3_laplacian",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonTemperedPotential3_laplacian",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonTemperedPotential3_poisson_and_energy_unique",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.inferenceNewtonTemperedPotential_laplacian",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_reversibleFamily",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinsteinTensor_tendsto_real",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.rapidityComplexStressEnergy_tendsto_real",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_conservationFamily",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.complexActionPathIntegralWeight_tendsto_phase",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.nnPathWeight_tendsto_phase",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.log_schmidtNumber_le_exp_rate",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicIrreversibleGenerator_tendsto_zero",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicIrreversibleGenerator_norm_le_exp_rate",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicComplexHamiltonian_tendsto_reversible",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicComplexHamiltonian_error_le_exp_rate",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicSchrodingerGenerator_tendsto_reversible",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicSchrodingerGenerator_error_le_exp_rate",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendsto_reversible",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_apply_tendsto_reversible",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendstoUniformly_compactTime",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendstoUniformlyOn_boundedInterval",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_apply_tendstoUniformlyOn_boundedInterval",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicTransitionAmplitude_tendstoUniformlyOn_boundedInterval",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicObservableExpectation_tendstoUniformlyOn_boundedInterval",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicBornWeight_tendstoUniformlyOn_boundedInterval",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicBornWeight_tendstoUniformlyOn_initial"
  ]
  forbids_substitutes [
    "claiming a limiting Newton constant by substituting the simultaneous zero limits of screen area and bit count into their quotient",
    "claiming that the reversible limit itself fixes the Einstein coupling rather than the finite-rapidity independent Compton-cell ratio",
    "claiming the measured value of Newtons constant without the explicit inference-scale and Compton-cell-tiling model inputs",
    "claiming the still-missing Raychaudhuri null-horizon derivation of the real Einstein equation from Clausius data",
    "claiming H-one regularity boundary-condition uniqueness or nonlinear Einstein evolution from the proved Schwartz-tempered Poisson equation",
    "claiming every irreversible generator has the model-specific log-K rapidity interpolation",
    "treating the model-specific four-exp-minus-two-eta operator estimate as a universal physical relaxation rate",
    "promoting bounded-interval uniform operator convergence to global all-real-time uniformity path-measure or functional-integral convergence",
    "claiming that convergence of the supplied squared-norm Born readout derives the Born postulate"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entanglementScreenArea_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.comptonCellBits_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceEinsteinCoupling_eq_comptonCellBitForm,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonianConvolutionPotential_eq_convolution,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceSchrodingerPoissonGravitationalEnergy_eq_doubleIntegral,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_distributionalWeakFieldEinstein00_of_poisson,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.temperedWeakFieldEinstein00Equation3_of_poisson,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_weakFieldEinstein00,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_source_action,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.inferenceNewtonTemperedPotential_einstein00_and_energy_unique,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.GFreeNonlinearEinsteinCauchyProblem.exists_local_evolution,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.GFreeNonlinearEinsteinCauchyProblem.local_evolution_unique,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.schwartzLaplacian_convolution_right,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.temperedConvolutionSchwartz_laplacian,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.delta_temperedConvolutionSchwartz_apply,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.temperedFundamentalSolution_convolution,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.complexifyRealDistribution3_dirac,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.complexifyRealDistribution3_laplacian,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonKernelTempered3_laplacian,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonTemperedPotential3_laplacian,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.newtonTemperedPotential3_poisson_and_energy_unique,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianConvolutionPotential.inferenceNewtonTemperedPotential_laplacian,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_reversibleFamily,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinsteinTensor_tendsto_real,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.rapidityComplexStressEnergy_tendsto_real,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.gFree_complexEinstein_conservationFamily,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.complexActionPathIntegralWeight_tendsto_phase,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.nnPathWeight_tendsto_phase,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.log_schmidtNumber_le_exp_rate,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicIrreversibleGenerator_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicIrreversibleGenerator_norm_le_exp_rate,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicComplexHamiltonian_tendsto_reversible,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicComplexHamiltonian_error_le_exp_rate,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicSchrodingerGenerator_tendsto_reversible,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicSchrodingerGenerator_error_le_exp_rate,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendsto_reversible,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_apply_tendsto_reversible,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendstoUniformly_compactTime,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_tendstoUniformlyOn_boundedInterval,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicPropagator_apply_tendstoUniformlyOn_boundedInterval,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicTransitionAmplitude_tendstoUniformlyOn_boundedInterval,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicObservableExpectation_tendstoUniformlyOn_boundedInterval,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicBornWeight_tendstoUniformlyOn_boundedInterval,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ReversibleLimitConvergence.entropicBornWeight_tendstoUniformlyOn_initial
  ]

/-! ## F. Entropic Newton constant across GR and classical mechanics -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.entropicNewtonConstant_converges
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.holographicBits,
    Physlib.Thermodynamics.sphereArea,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit.weakFieldRicci00,
    Physlib.Thermodynamics.verlindeEntropicForce,
    Physlib.Thermodynamics.verlindeGravityTemperature,
    Physlib.Thermodynamics.verlindeDisplacementEntropy
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.entropicNewtonConstant_converges
    where
  formalizes @ "claim:one-entropic-newton-constant-gr-and-classical",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:jacobson-1995",
  requires @ "assumption:holographic-screen-bit-count",
  requires @ "assumption:weak-field-ricci-relation",
  caveat @ "claim:conditional-consistency-not-measurement-derived-newton-constant"

zil_file_contract physlib.entropicSpine.newtonConvergence where
  promises "formalization:conditional-entropic-newton-gr-classical-convergence"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Thermodynamics.holographicBits",
    "lean:Physlib.Thermodynamics.sphereArea",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ScreenCouplingReductions.newtonG_is_area_per_bit_reproducing_newton",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.entropicNewtonConstant_converges",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.gr_tendsto_newton_as_c_atTop"
  ]
  forbids_substitutes [
    "claiming that Lean has empirically measured Newton's constant",
    "claiming an unconditional derivation without the screen-count and weak-field hypotheses",
    "conflating algebraic consistency with uniqueness of a physical theory"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.entropicNewtonConstant_converges
  ]

/-! ## G. Damped heat/Stokes semigroup and Euclidean resolvent -/

zil_theorem_intent
    Physlib.QFT.PathIntegral.stokesModeLaplaceResolvent_one_eq_euclideanPropagator
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QFT.PathIntegral.dampedHeatLaplaceResolvent,
    Physlib.QFT.PathIntegral.euclidean_propagator
  ]

zil attach
    Physlib.QFT.PathIntegral.stokesModeLaplaceResolvent_one_eq_euclideanPropagator
    where
  supported_by @ "lean:RealC0ContractionSemigroup.dampedHeatLaplaceResolvent_one_eq_euclideanPropagator",
  formalizes @ "claim:modewise-stokes-laplace-resolvent-is-euclidean-propagator",
  requires @ "assumption:positive-laplace-parameter",
  requires @ "assumption:nonnegative-viscosity-wave-number-square-and-entropic-damping",
  caveat @ "claim:scalar-fourier-mode-not-full-pde-semigroup",
  caveat @ "claim:does-not-establish-nonlinear-navier-stokes-existence-or-regularity"

zil_file_contract physlib.entropicSpine.dampedHeatStokesResolvent where
  promises "formalization:modewise-c0-contraction-generator-and-euclidean-resolvent"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QFT.PathIntegral.RealC0ContractionSemigroup",
    "lean:Physlib.QFT.PathIntegral.dampedHeatC0ContractionSemigroup",
    "lean:Physlib.QFT.PathIntegral.dampedHeat_hasInfinitesimalGenerator",
    "lean:Physlib.QFT.PathIntegral.dampedHeatLaplaceResolvent_eq_euclideanPropagator",
    "lean:Physlib.QFT.PathIntegral.stokesMode_hasInfinitesimalGenerator",
    "lean:Physlib.QFT.PathIntegral.stokesModeLaplaceResolvent_one_eq_euclideanPropagator"
  ]
  forbids_substitutes [
    "presenting a scalar Fourier-mode semigroup as construction of the full heat PDE semigroup",
    "presenting the linear Stokes-mode result as nonlinear Navier-Stokes existence or regularity",
    "treating the nonnegative damping parameter as an empirically derived entropy-production law"
  ]
  witnessed_by [
    Physlib.QFT.PathIntegral.stokesModeLaplaceResolvent_one_eq_euclideanPropagator
  ]

/-! ## H. Finite Fourier Stokes semigroup and energy balance -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.dampedStokesEvolution_kineticEnergy_hasDerivAt
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.kineticEnergy,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.enstrophy
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.dampedStokesEvolution_kineticEnergy_hasDerivAt
    where
  supported_by @ "lean:PressureProjectedNonlinearData.dampedStokesEvolution_amp_hasDerivAt",
  formalizes @ "claim:finite-fourier-damped-stokes-exact-energy-balance",
  requires @ "assumption:finite-diagonal-fourier-galerkin-carrier",
  caveat @ "claim:does-not-include-pressure-projection-or-nonlinear-triadic-flow",
  caveat @ "claim:does-not-establish-full-pde-semigroup-or-navier-stokes-regularity"

zil_file_contract physlib.entropicSpine.finiteFourierDampedStokes where
  promises "formalization:finite-fourier-c0-generator-resolvent-and-energy-balance"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.stokesGalerkinC0ContractionSemigroup",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.stokesGalerkin_hasInfinitesimalGenerator",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.stokesGalerkinLaplaceResolvent_apply_eq_euclideanPropagator",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.stokesGalerkin_resolvent_equation",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.dampedStokesEvolution_kineticEnergy_hasDerivAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.dampedStokesEvolution_kineticEnergy_le"
  ]
  forbids_substitutes [
    "promoting the finite diagonal Galerkin carrier to an infinite-dimensional heat or Stokes PDE semigroup",
    "claiming that the pressure projection or nonlinear Navier-Stokes triadic interaction is present",
    "claiming nonlinear Navier-Stokes existence, uniqueness, or regularity",
    "treating the damping parameter as an empirically derived entropy-production coefficient"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.dampedStokesEvolution_kineticEnergy_hasDerivAt
  ]

/-! ## I. Finite Fourier Sobolev dissipation cascade -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade.dampedStokesEvolution_sobolevDissipationCascade
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.kineticEnergy,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.enstrophy,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.palinstrophy,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.superPalinstrophy
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade.dampedStokesEvolution_sobolevDissipationCascade
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.dampedStokesEvolution_kineticEnergy_hasDerivAt",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade.dampedStokesEvolution_enstrophy_hasDerivAt",
  formalizes @ "claim:finite-fourier-h0-h3-sobolev-dissipation-cascade",
  requires @ "assumption:finite-diagonal-damped-stokes-evolution",
  caveat @ "claim:effective-minus-lambda-enstrophy-term-is-not-nonlinear-vortex-stretching",
  caveat @ "claim:bkm-surrogate-density-is-not-the-analytic-l-infinity-bkm-criterion",
  caveat @ "claim:does-not-establish-full-pde-semigroup-or-navier-stokes-regularity"

zil_file_contract physlib.entropicSpine.fourierSobolevDissipationCascade where
  promises "formalization:finite-fourier-exact-sobolev-dissipation-cascade"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade.dampedStokesEvolution_enstrophy_hasDerivAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade.dampedStokesEvolution_palinstrophy_hasDerivAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade.dampedStokesEvolution_sobolevHierarchy_le",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade.dampedStokesEvolution_enstrophy_hasDerivAt_enstrophyRate",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade.dampedStokesEvolution_effectiveDefect_nonneg",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade.dampedStokesEvolution_bkmSurrogateDensity_hasDerivAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade.dampedStokesEvolution_sobolevDissipationCascade"
  ]
  forbids_substitutes [
    "identifying the effective minus-lambda-enstrophy term with the nonlinear vortex-stretching integral",
    "promoting the finite Fourier BKM surrogate to the analytic L-infinity Beale-Kato-Majda criterion",
    "claiming a pressure-projected or nonlinear Navier-Stokes evolution",
    "claiming nonlinear Navier-Stokes existence, uniqueness, or regularity"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade.dampedStokesEvolution_sobolevDissipationCascade
  ]

/-! ## J. Time-integrated finite Fourier dissipation cascade -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_integratedSobolevDissipationCascade
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.kineticEnergy,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.enstrophy,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.palinstrophy,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.superPalinstrophy
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_integratedSobolevDissipationCascade
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_enstrophy_integralBalance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_kineticEnergy_integralBalance",
  formalizes @ "claim:finite-fourier-exact-time-integrated-sobolev-dissipation-cascade",
  requires @ "assumption:finite-diagonal-damped-stokes-evolution",
  requires @ "assumption:mathlib-interval-fundamental-theorem-of-calculus",
  caveat @ "claim:kinetic-energy-normalization-without-one-half-produces-factor-two",
  caveat @ "claim:interval-bkm-surrogate-is-not-the-analytic-l-infinity-bkm-criterion",
  caveat @ "claim:does-not-construct-a-nonlinear-leray-weak-solution"

zil_file_contract physlib.entropicSpine.fourierIntegratedDissipationCascade where
  promises "formalization:finite-fourier-exact-interval-integrated-dissipation-and-budgets"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_kineticEnergy_integralBalance",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_enstrophy_integralBalance",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_palinstrophy_integralBalance",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_integratedEnstrophy_le_initialEnergy",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_orbitTraversal_le_initialEnergy",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_bkmSurrogateIntegral_le_initialSobolevBudget",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_integratedSobolevDissipationCascade"
  ]
  forbids_substitutes [
    "presenting finite-dimensional interval identities as construction of a nonlinear Leray weak solution",
    "promoting the finite Fourier BKM surrogate integral to the analytic L-infinity Beale-Kato-Majda criterion",
    "claiming that pressure projection or nonlinear triadic vortex stretching is present",
    "silently replacing the repository kinetic-energy normalization by the conventional one-half normalization"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_integratedSobolevDissipationCascade
  ]

/-! ## K. Discrete-to-continuous finite Fourier budget bridge -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_discreteBkm_converges_to_certifiedBudget
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.bkmSurrogateIntegral,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.enstrophy,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.palinstrophy,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.kineticEnergy
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_discreteBkm_converges_to_certifiedBudget
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_bkmSurrogateIntegral_le_initialSobolevBudget",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_bkmSurrogateIntegral_tendsto",
  formalizes @ "claim:fixed-step-fourier-bkm-surrogate-converges-to-certified-interval-budget",
  requires @ "assumption:finite-diagonal-damped-stokes-evolution",
  requires @ "assumption:nonnegative-viscosity-and-damping-for-monotonicity",
  requires @ "assumption:strictly-positive-viscosity-for-the-certified-budget",
  caveat @ "claim:finite-fourier-bkm-surrogate-is-not-the-analytic-l-infinity-bkm-criterion",
  caveat @ "claim:does-not-construct-a-nonlinear-pressure-projected-flow-or-leray-weak-solution",
  caveat @ "claim:entropic-proper-time-limit-does-not-assert-time-quantization"

zil_file_contract physlib.entropicSpine.fourierRiemannSumBridge where
  promises "formalization:fixed-step-fourier-budgets-converge-to-exact-interval-budgets"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.LeftRiemannSum.abs_leftRiemannSum_sub_integral_le",
    "lean:Physlib.Mathematics.LeftRiemannSum.tendsto_leftRiemannSum_integral",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_enstrophy_antitoneOn",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_palinstrophy_antitoneOn",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_integratedEnstrophy_error",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_integratedPalinstrophy_error",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_bkmSurrogateIntegral_tendsto",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_entropicProperTime_tendsto",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_discreteBkm_converges_to_certifiedBudget"
  ]
  forbids_substitutes [
    "promoting convergence for nonnegative antitone trajectories to arbitrary discontinuous or oscillatory integrands",
    "promoting the finite Fourier BKM surrogate to the analytic L-infinity Beale-Kato-Majda criterion",
    "presenting the finite diagonal Fourier evolution as a nonlinear pressure-projected flow or Leray weak solution",
    "reading the entropic proper-time convergence theorem as time quantization"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_discreteBkm_converges_to_certifiedBudget
  ]

/-! ## L. Fixed-resolution finite Fourier budget certificate -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_discreteBkm_le_certifiedBudget
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.bkmSurrogateIntegral,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.kineticEnergy,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.enstrophy,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.palinstrophy
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_discreteBkm_le_certifiedBudget
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_bkmSurrogateIntegral_error",
  formalizes @ "claim:every-positive-fixed-resolution-has-an-explicit-fourier-bkm-budget-certificate",
  requires @ "assumption:positive-fixed-step-resolution",
  requires @ "assumption:finite-diagonal-damped-stokes-evolution",
  requires @ "assumption:strictly-positive-viscosity-and-nonnegative-damping",
  caveat @ "claim:one-over-resolution-remainder-is-a-quadrature-bound-not-a-physical-uncertainty",
  caveat @ "claim:finite-fourier-bkm-surrogate-is-not-the-analytic-l-infinity-bkm-criterion",
  caveat @ "claim:does-not-discretize-or-certify-the-full-nonlinear-navier-stokes-pde"

zil_file_contract physlib.entropicSpine.fourierFixedResolutionCertificate where
  promises "formalization:finite-resolution-fourier-bkm-budget-with-explicit-one-over-n-remainder"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_integratedEnstrophy_error",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_integratedPalinstrophy_error",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_bkmSurrogateIntegral_error",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_bkmSurrogateIntegral_le_initialSobolevBudget",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_discreteBkm_le_certifiedBudget"
  ]
  forbids_substitutes [
    "presenting the one-over-resolution quadrature remainder as a measured physical uncertainty",
    "promoting a fixed-step certificate for the finite diagonal evolution to a nonlinear Navier-Stokes discretization theorem",
    "promoting the finite Fourier BKM surrogate to the analytic L-infinity Beale-Kato-Majda criterion",
    "dropping positivity of the selected resolution or viscosity"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_discreteBkm_le_certifiedBudget
  ]

/-! ## M. Tolerance-driven Fourier resolution selection -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_exists_resolution_for_bkm_tolerance
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.bkmSurrogateIntegral,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.kineticEnergy,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.enstrophy
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_exists_resolution_for_bkm_tolerance
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.bkmToleranceResolution_pos",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_discreteBkm_le_budget_add_tolerance",
  formalizes @ "claim:every-positive-bkm-quadrature-tolerance-has-an-explicit-eventual-resolution-certificate",
  requires @ "assumption:positive-requested-quadrature-tolerance",
  requires @ "assumption:finite-diagonal-damped-stokes-evolution",
  requires @ "assumption:strictly-positive-viscosity-and-nonnegative-damping",
  caveat @ "claim:selected-resolution-controls-only-the-proved-fixed-step-quadrature-remainder",
  caveat @ "claim:tolerance-is-not-a-physical-measurement-error-or-probabilistic-confidence-bound",
  caveat @ "claim:does-not-provide-a-nonlinear-navier-stokes-numerical-convergence-rate"

zil_file_contract physlib.entropicSpine.fourierToleranceResolution where
  promises "formalization:explicit-resolution-selection-for-any-positive-fourier-bkm-quadrature-tolerance"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.bkmToleranceResolution",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.bkmToleranceResolution_pos",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.bkmToleranceResolution_remainder_lt",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_discreteBkm_le_budget_add_tolerance",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_exists_resolution_for_bkm_tolerance"
  ]
  forbids_substitutes [
    "presenting the quadrature tolerance as experimental uncertainty or statistical confidence",
    "claiming the selected threshold is minimal or asymptotically optimal",
    "promoting the finite diagonal fixed-step certificate to a nonlinear PDE discretization convergence theorem",
    "dropping positivity of the tolerance or viscosity"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_exists_resolution_for_bkm_tolerance
  ]

/-! ## N. Finite Schrödinger initial-data recovery -/

zil_theorem_intent
    Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery.finiteSchrodinger_initialRecovery_and_sampledEnergy
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Schrodinger.SpectralDynamics.finiteSpectralEvolution,
    Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery.finiteSpectralL2ErrorSq,
    Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery.finiteSampledSpacetimeEnergy
  ]

zil attach
    Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery.finiteSchrodinger_initialRecovery_and_sampledEnergy
    where
  formalizes @ "claim:finite-pure-point-schrodinger-initial-data-and-sampled-energy-recovery",
  supported_by @ "paper:hickman-2023-schrodinger-pointwise-convergence",
  requires @ "assumption:finite-pure-point-spectral-coefficient-model",
  requires @ "assumption:unitary-diagonal-spectral-phase-evolution",
  caveat @ "claim:not-the-du-zhang-euclidean-almost-everywhere-carleson-theorem",
  caveat @ "claim:no-sobolev-threshold-maximal-fractal-restriction-or-decoupling-estimate"

zil_file_contract physlib.entropicSpine.finiteSchrodingerRecovery where
  promises "formalization:finite-pure-point-pointwise-l2-and-sampled-spacetime-recovery"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.Schrodinger.SpectralDynamics.finiteSpectralEvolution",
    "lean:Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery.finiteSpectralEvolution_component_tendsto_zero",
    "lean:Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery.finiteSpectralEvolution_tendsto_zero",
    "lean:Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery.finiteSpectralL2ErrorSq_tendsto_zero",
    "lean:Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery.finiteSampledSpacetimeEnergy_eq",
    "lean:Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery.finiteSchrodinger_initialRecovery_and_sampledEnergy"
  ]
  forbids_substitutes [
    "presenting finite pure-point coefficient recovery as the Du-Zhang Euclidean almost-everywhere theorem",
    "claiming the sharp Sobolev threshold s greater than n over two times n plus one",
    "claiming an L2 maximal estimate, fractal restriction estimate, or decoupling theorem",
    "promoting a finite sampled-time sum identity to a continuous space-time Strichartz estimate"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery.finiteSchrodinger_initialRecovery_and_sampledEnergy
  ]

/-! ## O. Euclidean `L²` free Schrödinger evolution -/

zil_theorem_intent
    Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.euclideanL2_freeSchrodinger_unitaryStronglyContinuous
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerEvolution,
    Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerEvolutionₗᵢ
  ]

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.euclideanL2_freeSchrodinger_unitaryStronglyContinuous
    where
  formalizes @ "claim:euclidean-l2-free-schrodinger-unitary-group-and-strong-initial-data-recovery",
  supported_by @ "paper:hickman-2023-schrodinger-pointwise-convergence",
  requires @ "assumption:mathlib-l2-plancherel-linear-isometry",
  requires @ "assumption:paper-normalized-frequency-phase-exp-i-t-norm-xi-squared",
  caveat @ "claim:strong-l2-convergence-is-not-pointwise-or-almost-everywhere-convergence",
  caveat @ "claim:no-carleson-maximal-sobolev-threshold-fractal-restriction-or-decoupling-estimate",
  caveat @ "claim:other-fourier-normalizations-require-the-corresponding-two-pi-conversion"

zil_file_contract physlib.entropicSpine.euclideanL2FreeSchrodinger where
  promises "formalization:euclidean-l2-fourier-multiplier-unitarity-group-law-and-strong-continuity"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:MeasureTheory.Lp.fourierTransformₗᵢ",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerPhase",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerMultiplierₗᵢ",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerMultiplier_tendsto_zero",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerEvolutionₗᵢ",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerEvolution_add",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.norm_freeSchrodingerEvolution",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerEvolution_tendsto_zero",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.euclideanL2_freeSchrodinger_unitaryStronglyContinuous"
  ]
  forbids_substitutes [
    "presenting strong L2 convergence as pointwise or almost-everywhere convergence",
    "claiming the Du-Zhang Sobolev threshold or Schrödinger maximal estimate",
    "claiming a fractal restriction, Littlewood-Paley, wave-packet, or decoupling theorem",
    "silently identifying different Fourier-transform phase normalizations"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.euclideanL2_freeSchrodinger_unitaryStronglyContinuous
  ]

/-! ## O1. Affine self-similarity of the Schrödinger paraboloid -/

zil_theorem_intent
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.schrodingerParaboloid_affineSelfSimilarity
    where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.paraboloidPoint,
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.frequencyRescale,
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.parabolicAmbientRescale,
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.frequencyParaboloid
  ]

zil attach
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.schrodingerParaboloid_affineSelfSimilarity
    where
  formalizes @ "claim:schrodinger-paraboloid-explicit-affine-self-similarity-and-bijection",
  supported_by @ "paper:hickman-2023-schrodinger-pointwise-convergence",
  requires @ "assumption:nonzero-frequency-rescaling-radius",
  caveat @ "claim:full-paraboloid-bijection-does-not-by-itself-prove-cap-support-or-jacobian-estimates"

zil_file_contract physlib.entropicSpine.schrodingerParabolicGeometry where
  promises "formalization:explicit-paraboloid-affine-rescaling-and-bijective-restriction"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.paraboloidPoint",
    "lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.frequencyParaboloid",
    "lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.frequencyRescaleEquiv",
    "lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.parabolicAmbientRescale_paraboloidPoint",
    "lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.parabolicAmbientRescale_bijOn_frequencyParaboloid",
    "lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.schrodingerParaboloid_affineSelfSimilarity"
  ]
  forbids_substitutes [
    "claiming an oscillatory-integral change-of-variables theorem from affine geometry alone",
    "claiming wave-packet localization, a maximal estimate, or almost-everywhere convergence",
    "silently allowing zero radius in the bijection statement"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.schrodingerParaboloid_affineSelfSimilarity
  ]

/-! ## O2. Schrödinger phase covariance under parabolic rescaling -/

zil_theorem_intent
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.schrodingerPhase_parabolicRescaling_chain
    where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.schrodingerPhase,
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.centrePhase,
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.parabolicSpaceTimeRescale,
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.schrodingerOscillatoryPhase
  ]

zil attach
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.schrodingerPhase_parabolicRescaling_chain
    where
  formalizes @ "claim:schrodinger-real-phase-and-complex-kernel-parabolic-rescaling-covariance",
  supported_by @ "paper:hickman-2023-schrodinger-pointwise-convergence",
  requires @ "assumption:paper-normalized-phase-inner-x-xi-plus-t-norm-xi-squared",
  caveat @ "claim:phase-factorization-is-not-the-full-rescaled-propagator-integral-with-jacobian-and-support-control"

zil_file_contract physlib.entropicSpine.schrodingerParabolicPhaseRescaling where
  promises "formalization:exact-real-phase-identity-complex-kernel-factorization-and-l2-multiplier-connection"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.schrodingerPhase",
    "lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.parabolicSpaceTimeRescale",
    "lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.schrodingerPhase_frequencyRescale",
    "lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.schrodingerOscillatoryPhase_frequencyRescale",
    "lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.schrodingerOscillatoryPhase_zeroSpace_eq_freeSchrodingerPhase",
    "lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.schrodingerPhase_parabolicRescaling_chain"
  ]
  forbids_substitutes [
    "claiming the full L2 parabolic-rescaling corollary without a Fourier dilation and Jacobian proof",
    "claiming cap support transport without a set-preimage proof",
    "claiming a maximal, fractal restriction, broad-narrow, or decoupling estimate"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.schrodingerPhase_parabolicRescaling_chain
  ]

/-! ## P. Euclidean Sobolev hierarchy and rough frequency localization -/

zil_theorem_intent
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.euclideanSobolev_hierarchy_freeEvolution_annularLocalization
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.HasSobolevRegularity,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.sobolevNorm,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.annularFrequencyProjection
  ]

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.euclideanSobolev_hierarchy_freeEvolution_annularLocalization
    where
  formalizes @ "claim:euclidean-bessel-potential-sobolev-hierarchy-and-rough-annular-localization",
  supported_by @ "paper:hickman-2023-schrodinger-pointwise-convergence",
  requires @ "assumption:mathlib-l2-plancherel-linear-isometry",
  requires @ "assumption:inhomogeneous-bessel-potential-weight-one-plus-norm-squared-to-s-over-two",
  caveat @ "claim:rough-annular-projection-does-not-by-itself-prove-littlewood-paley-square-function-equivalence",
  caveat @ "claim:no-schrodinger-maximal-estimate-pointwise-convergence-or-du-zhang-threshold"

zil_theorem_intent
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_sobolevNorm_has_hOneWeaklyConvergent_subsequence
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.HOneWeaklyConverges
  ]

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_sobolevNorm_has_hOneWeaklyConvergent_subsequence
    where
  formalizes @ "claim:every-uniformly-bounded-sequence-in-the-complete-continuum-h-one-r-three-bessel-energy-carrier-has-a-subsequence-converging-weakly-against-every-h-one-test-vector",
  supported_by @ "lean:WeakDual.isSeqCompact_closedBall",
  supported_by @ "lean:InnerProductSpace.toDual",
  epistemic_status @ "risky",
  caveat @ "claim:weak-sequential-precompactness-is-not-rellich-strong-compactness-and-does-not-preserve-l-two-mass-without-a-separate-tightness-or-concentration-compactness-argument",
  caveat @ "claim:this-does-not-by-itself-prove-lower-semicontinuity-of-a-hartree-functional-ground-state-attainment-euler-lagrange-regularity-or-orbital-stability"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_has_weaklyConvergent_subsequence_with_norm_bound
    where
  formalizes @ "claim:the-banach-alaoglu-weak-limit-of-a-uniformly-bounded-continuum-h-one-sequence-retains-the-same-closed-ball-energy-bound",
  supported_by @ "lean:WeakDual.isSeqCompact_closedBall",
  supported_by @ "lean:InnerProductSpace.toDual",
  epistemic_status @ "risky",
  caveat @ "claim:retaining-the-uniform-upper-bound-is-weak-lower-semicontinuity-of-the-h-one-norm-not-convergence-of-the-norm-or-strong-compactness"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_weak_of_norm
    where
  formalizes @ "claim:weak-convergence-plus-convergence-of-the-complete-h-one-energy-norm-implies-strong-continuum-h-one-convergence",
  supported_by @ "lean:norm_sub_sq",
  epistemic_status @ "risky",
  caveat @ "claim:the-norm-convergence-premise-must-be-derived-from-mass-energy-closure-or-concentration-compactness-it-is-not-implied-by-weak-convergence-alone"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.tight_probabilitySequence_has_convergent_subsequence
    where
  formalizes @ "claim:a-tight-sequence-of-genuine-three-dimensional-continuum-probability-measures-has-a-subsequence-converging-in-distribution-to-a-probability-measure",
  supported_by @ "lean:MeasureTheory.isCompact_closure_of_isTightMeasureSet",
  epistemic_status @ "risky",
  caveat @ "claim:for-schrodinger-newton-born-densities-the-required-uniform-tightness-after-recentering-still-has-to-be-derived-from-the-binding-functional"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_and_tight_probabilitySequence_has_joint_subsequence
    where
  formalizes @ "claim:one-common-subsequence-simultaneously-realizes-weak-continuum-h-one-field-convergence-with-the-energy-bound-retained-and-prokhorov-convergence-of-the-associated-tight-three-dimensional-probability-measures",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_has_weaklyConvergent_subsequence_with_norm_bound",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.tight_probabilitySequence_has_convergent_subsequence",
  epistemic_status @ "risky",
  caveat @ "claim:this-proves-the-joint-compactness-consequence-of-h-one-boundedness-and-density-tightness-but-does-not-derive-tightness-modulo-translations-from-the-schrodinger-newton-binding-energy-or-upgrade-weak-to-strong-h-one-convergence"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.uniform_firstMoment_implies_tight
    where
  formalizes @ "claim:a-uniform-finite-first-radial-moment-derives-tightness-of-a-sequence-of-genuine-three-dimensional-continuum-probability-measures",
  supported_by @ "lean:MeasureTheory.meas_ge_le_lintegral_div",
  supported_by @ "lean:MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt",
  epistemic_status @ "risky",
  caveat @ "claim:for-a-translation-invariant-schrodinger-newton-family-the-moment-bound-must-be-proved-after-a-model-specific-recentering-it-is-not-implied-by-an-unrecentered-energy-bound"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_and_firstMoment_has_joint_subsequence
    where
  formalizes @ "claim:h-one-boundedness-and-a-finite-first-radial-moment-produce-one-common-subsequence-with-weak-field-convergence-probability-measure-convergence-and-unit-total-limit-mass",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.uniform_firstMoment_implies_tight",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_and_tight_probabilitySequence_has_joint_subsequence",
  epistemic_status @ "risky",
  caveat @ "claim:for-an-arbitrary-associated-measure-the-limit-is-only-a-unit-mass-probability-measure-the-specialized-born-law-identification-is-proved-separately-under-strong-h-one-closure"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOneBornDensity_lintegral_eq_enorm_sq
    where
  formalizes @ "claim:the-actual-continuum-born-density-of-a-complete-h-one-bessel-energy-coordinate-has-total-mass-equal-to-the-squared-physical-space-l-two-norm",
  supported_by @ "lean:MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-identifies-normalization-of-the-reconstructed-wave-field-it-does-not-by-itself-prove-that-a-variational-sequence-retains-normalization-under-weak-h-one-convergence"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOneBornProbability_tendsto_of_strong
    where
  formalizes @ "claim:strong-convergence-in-the-complete-continuum-h-one-carrier-implies-l-one-convergence-of-squared-amplitude-densities-and-weak-convergence-of-the-induced-born-probability-measures",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOneBornDensityReal_tendsto_L1",
  supported_by @ "lean:MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto",
  epistemic_status @ "risky",
  caveat @ "claim:the-conclusion-needs-strong-h-one-convergence-weak-h-one-convergence-alone-does-not-preclude-loss-of-mass"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_normalized_hOne_firstMoment_has_bornLimit
    where
  formalizes @ "claim:h-one-boundedness-physical-l-two-normalization-a-finite-first-moment-and-no-loss-of-h-one-norm-produce-a-common-strong-field-subsequence-whose-prokhorov-limit-is-exactly-the-born-law-of-the-limit-field",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_normalized_hOne_firstMoment_has_joint_subsequence",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOneBornProbability_tendsto_of_strong",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_weak_of_norm",
  epistemic_status @ "risky",
  caveat @ "claim:the-finite-first-moment-usually-requires-model-specific-recentering-the-separate-energy-split-theorem-now-derives-no-loss-when-the-hartree-interaction-converges"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_of_closed_bounded_hOneBornMoment_and_normClosure
    where
  formalizes @ "claim:a-closed-physically-l-two-normalized-h-one-family-with-a-uniform-h-one-bound-a-finite-first-moment-of-its-actual-born-density-and-no-loss-of-h-one-norm-is-strongly-compact",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_normalized_hOne_firstMoment_has_bornLimit",
  epistemic_status @ "risky",
  caveat @ "claim:this-removes-the-arbitrary-measure-adapter-but-does-not-remove-the-model-specific-recentering-moment-bound-or-no-loss-of-h-one-norm-premises"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_energy_eq_and_norm_tendsto_of_minimizing_energySplit
    where
  formalizes @ "claim:weak-h-one-convergence-minimizing-energy-convergence-a-positive-quadratic-kinetic-plus-interaction-split-and-convergence-of-the-interaction-force-attainment-of-the-variational-level-and-no-loss-of-the-complete-h-one-norm",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_norm_le_of_weak_of_norm_tendsto",
  epistemic_status @ "risky",
  caveat @ "claim:the-bilinear-hls-and-local-to-global-interpolation-bridges-now-derive-interaction-convergence-from-explicit-local-rellich-recentered-tail-and-sobolev-cubic-estimates-those-model-specific-estimates-remain-visible-obligations"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_minimizing_energySplit
    where
  formalizes @ "claim:the-derived-no-loss-of-h-one-norm-upgrades-the-localized-minimizing-subsequence-from-weak-to-strong-continuum-h-one-convergence-by-radon-riesz",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_energy_eq_and_norm_tendsto_of_minimizing_energySplit",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_weak_of_norm",
  epistemic_status @ "risky",
  caveat @ "claim:this-is-not-strong-compactness-from-boundedness-alone-the-positive-energy-split-lower-bound-and-interaction-convergence-are-essential"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_normalized_hOne_firstMoment_has_energyMinimizer
    where
  formalizes @ "claim:a-bounded-normalized-localized-h-one-minimizing-sequence-attains-its-variational-level-converges-strongly-and-retains-its-actual-born-law-when-the-constraint-is-weakly-closed-and-the-interaction-converges",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_normalized_hOne_firstMoment_has_joint_subsequence",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_minimizing_energySplit",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOneBornProbability_tendsto_of_strong",
  epistemic_status @ "risky",
  caveat @ "claim:the-model-must-prove-recentering-the-first-moment-bound-weak-constraint-closure-the-positive-kinetic-interaction-split-local-rellich-uniform-tail-and-sobolev-cubic-estimates-the-proved-interpolation-and-hls-bridges-then-deliver-hartree-convergence"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_hOneBorn_energyMinimizers_of_interactionClosure
    where
  formalizes @ "claim:the-complete-ground-energy-orbit-is-strongly-compact-from-h-one-boundedness-physical-normalization-born-localization-weak-constraint-closure-and-interaction-convergence-with-no-independent-norm-closure-certificate",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_minimizing_energySplit",
  epistemic_status @ "risky",
  caveat @ "claim:this-proves-compactness-of-the-minimizing-energy-level-not-of-an-arbitrary-low-energy-sublevel-and-still-requires-model-specific-local-rellich-recentered-tail-and-sobolev-estimates-while-the-global-l-six-fifths-and-hls-steps-are-proved"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_of_closed_bounded_firstMoment_and_normClosure
    where
  formalizes @ "claim:a-closed-h-one-family-with-a-uniform-h-one-bound-a-finite-first-radial-moment-and-no-loss-of-h-one-norm-is-strongly-compact",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_and_firstMoment_has_joint_subsequence",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_weak_of_norm",
  epistemic_status @ "risky",
  caveat @ "claim:the-no-loss-of-h-one-norm-premise-is-the-model-specific-concentration-compactness-closure-step-and-is-not-derived-merely-from-tightness"

zil_theorem_intent
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.exists_hOne_minimizer_of_bounded_minimizingSequence
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.HOneSequentiallyWeaklyLowerSemicontinuous
  ]

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.exists_hOne_minimizer_of_bounded_minimizingSequence
    where
  formalizes @ "claim:the-direct-method-attains-a-global-infimum-on-the-complete-continuum-h-one-r-three-carrier-from-a-sobolev-bounded-minimizing-sequence-and-sequential-weak-lower-semicontinuity",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_sobolevNorm_has_hOneWeaklyConvergent_subsequence",
  requires @ "assumption:the-functional-is-sequentially-weakly-lower-semicontinuous-on-the-complete-h-one-carrier",
  epistemic_status @ "risky",
  caveat @ "claim:for-constrained-translation-invariant-schrodinger-newton-attainment-the-sobolev-bounded-minimizing-sequence-tightness-mass-constraint-closure-and-hartree-lower-semicontinuity-premises-remain-to-be-instantiated"

zil_file_contract physlib.entropicSpine.euclideanSobolevFrequencyLocalization where
  promises "formalization:euclidean-sobolev-hierarchy-complete-continuum-h-one-energy-carrier-weak-sequential-compactness-actual-born-law-energy-split-derived-no-loss-direct-method-free-flow-invariance-and-rough-annular-projection"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.besselPotentialWeight",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.HasSobolevRegularity",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.EuclideanHs",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.sobolevNorm_zero_eq_l2Norm",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.HasSobolevRegularity.mono",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.sobolevNorm_mono",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.EuclideanHOneThree",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOneEnergyEquiv",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.HOneWeaklyConverges",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.HOneSequentiallyWeaklyLowerSemicontinuous",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_has_weaklyConvergent_subsequence_with_norm_bound",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_has_weaklyConvergent_subsequence",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_sobolevNorm_has_hOneWeaklyConvergent_subsequence",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_weak_of_norm",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.tight_probabilitySequence_has_convergent_subsequence",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_and_tight_probabilitySequence_has_joint_subsequence",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.uniform_firstMoment_implies_tight",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_and_firstMoment_has_joint_subsequence",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOneBornDensity",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOneBornProbability",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOneBornProbability_tendsto_of_strong",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_normalized_hOne_firstMoment_has_bornLimit",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_of_closed_bounded_hOneBornMoment_and_normClosure",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_energy_eq_and_norm_tendsto_of_minimizing_energySplit",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_minimizing_energySplit",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_normalized_hOne_firstMoment_has_energyMinimizer",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_hOneBorn_energyMinimizers_of_interactionClosure",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_of_closed_bounded_firstMoment_and_normClosure",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.exists_hOne_minimizer_of_bounded_minimizingSequence",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.sobolevNorm_freeSchrodingerEvolution",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.frequencyAnnulus",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.annularFrequencyProjection",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.annularFrequencyProjection_idempotent",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.norm_annularFrequencyProjection_le",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.annularFrequencyProjection_commutes_evolution",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.sobolevNorm_annularFrequencyProjection_le",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.euclideanSobolev_hierarchy_freeEvolution_annularLocalization"
  ]
  forbids_substitutes [
    "presenting one rough annular projection as a proved Littlewood-Paley decomposition or square-function norm equivalence",
    "claiming a Schrödinger maximal estimate, pointwise convergence, or almost-everywhere convergence",
    "claiming the Du-Zhang sharp Sobolev threshold",
    "claiming wave-packet, fractal restriction, broad-narrow, or decoupling estimates",
    "presenting weak sequential H1 compactness as strong Rellich compactness, preservation of L2 mass, or concentration compactness modulo translations",
    "claiming that a first-moment tightness estimate alone yields strong H1 compactness without no-loss of the H1 norm",
    "claiming that Hartree interaction convergence follows from weak H1 convergence without the local Rellich, recentered-tail, and Sobolev-cubic estimates required by the proved interpolation and bilinear HLS continuity bridges",
    "claiming a Schrodinger-Newton minimizer, Euler-Lagrange regularity, or orbital stability without lower semicontinuity, tightness, and constraint-closure proofs"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.euclideanSobolev_hierarchy_freeEvolution_annularLocalization,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOneEnergyCoordinate_fromEnergyCoordinate,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_has_weaklyConvergent_subsequence_with_norm_bound,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_sobolevNorm_has_hOneWeaklyConvergent_subsequence,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_weak_of_norm,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.tight_probabilitySequence_has_convergent_subsequence,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_and_tight_probabilitySequence_has_joint_subsequence,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.uniform_firstMoment_implies_tight,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_hOne_and_firstMoment_has_joint_subsequence,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOneBornDensity_lintegral_eq_enorm_sq,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOneBornProbability_tendsto_of_strong,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_normalized_hOne_firstMoment_has_bornLimit,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_of_closed_bounded_hOneBornMoment_and_normClosure,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_energy_eq_and_norm_tendsto_of_minimizing_energySplit,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.hOne_tendsto_of_minimizing_energySplit,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.bounded_normalized_hOne_firstMoment_has_energyMinimizer,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_hOneBorn_energyMinimizers_of_interactionClosure,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.isCompact_of_closed_bounded_firstMoment_and_normClosure,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.exists_hOne_minimizer_of_bounded_minimizingSequence
  ]

/-! ## Q. Finite Euclidean Littlewood--Paley orthogonality -/

zil_theorem_intent
    Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley.finiteLittlewoodPaley_orthogonality_bessel
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley.SpectrallySeparated,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.annularFrequencyProjection,
    Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerEvolution
  ]

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley.finiteLittlewoodPaley_orthogonality_bessel
    where
  formalizes @ "claim:finite-euclidean-littlewood-paley-orthogonality-pythagorean-bessel",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:mathlib-l2-plancherel-linear-isometry",
  requires @ "assumption:finite-family-of-pairwise-disjoint-rough-annular-frequency-cells",
  caveat @ "claim:exact-disjoint-rough-cell-l2-result-not-smooth-finite-overlap-multinorm-theory",
  caveat @ "claim:no-l1-square-function-equivalence-local-hardy-space-or-atomic-characterization"

zil_file_contract physlib.entropicSpine.euclideanFiniteLittlewoodPaley where
  promises "formalization:finite-separated-annular-orthogonality-pythagorean-bessel-and-free-flow-covariance"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley.frequencyAnnulus_disjoint_of_le_half",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley.inner_annularCutoff_eq_zero_of_disjoint",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley.inner_annularFrequencyProjection_eq_zero_of_disjoint",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley.SpectrallySeparated",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley.norm_sq_sum_annularFrequencyProjection",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley.norm_sum_annularFrequencyProjection_le",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley.finiteLittlewoodPaley_bessel",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley.finiteLittlewoodPaley_orthogonality_bessel"
  ]
  forbids_substitutes [
    "claiming the smooth multi-norm finite-overlap Littlewood-Paley decomposition",
    "claiming L1 equivalence of square functions",
    "claiming a Calderon reproducing formula, local multi-norm Hardy space, or atomic characterization",
    "claiming an infinite-series convergence or completeness result from the finite-family theorem",
    "claiming a Schrödinger maximal estimate or pointwise almost-everywhere convergence"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley.finiteLittlewoodPaley_orthogonality_bessel
  ]

/-! ## R. Standard-matrix multi-norm dilation geometry -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.standardMultiNorm_dilationGauge_geometry
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix,
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.physicalDilation,
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.frequencyDilation,
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.physicalGauge,
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.frequencyGauge
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.standardMultiNorm_dilationGauge_geometry
    where
  formalizes @ "claim:standard-multinorm-matrix-dilations-homogeneous-gauges-common-unit-ball",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:finite-nonempty-family-of-real-normed-coordinate-blocks",
  caveat @ "claim:foundational-multinorm-geometry-not-marked-partition-tube-or-frequency-cell-construction",
  caveat @ "claim:no-calderon-reproducing-formula-square-function-equivalence-or-hardy-space"

zil_file_contract physlib.entropicSpine.standardMultiNormGeometry where
  promises "formalization:standard-matrix-physical-frequency-dilations-degree-one-gauges-and-common-unit-ball"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.reciprocal_product_one_le",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.twoFactor",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.physicalDilation",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.frequencyDilation",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.physicalDilation_mul",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.frequencyDilation_mul",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.physicalGauge",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.frequencyGauge",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.physicalGauge_dilation",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.frequencyGauge_dilation",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.physical_frequency_common_unitBall",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.standardMultiNorm_dilationGauge_geometry"
  ]
  forbids_substitutes [
    "claiming that the gauges have been bundled as norms with every norm axiom",
    "claiming the marked-partition cone, maximal tube, or multi-norm dyadic-block decomposition",
    "claiming a smooth partition of unity or Calderon reproducing formula",
    "claiming L1 square-function equivalence, a local Hardy space, or an atomic characterization"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.standardMultiNorm_dilationGauge_geometry
  ]

/-! ## S. Multi-norm dominance and marked-block substrate -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.strictDominance_markedBlock_structure
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.logFrequencyGauge,
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictlyDominates,
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment,
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.block
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.strictDominance_markedBlock_structure
    where
  formalizes @ "claim:multinorm-dominance-transfer-unique-strict-dominants-idempotent-marked-blocks",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:nonnegative-logarithmic-coordinate-point-with-chosen-strict-dominant-for-each-gauge",
  caveat @ "claim:strict-dominance-assignment-is-input-and-excludes-the-paper-tie-locus",
  caveat @ "claim:marked-block-substrate-not-cone-tube-dyadic-cell-or-square-function-construction"

zil_file_contract physlib.entropicSpine.standardMultiNormDominance where
  promises "formalization:log-frequency-gauge-dominance-transfer-uniqueness-principal-cone-and-idempotent-marked-blocks"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.logFrequencyGauge",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.Dominates",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictlyDominates",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictlyDominates.dominates",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.logFrequencyGauge_eq_of_dominates",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.dominates_self_of_dominates",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.strictlyDominates_self_of_strictlyDominates",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.strictlyDominant_unique",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.InPrincipalCone",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.inPrincipalCone_iff_diagonal_dominance",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.owner_idempotent",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.strictDominance_markedBlock_structure"
  ]
  forbids_substitutes [
    "claiming existence or measurability of a strict-dominance assignment on the paper's full frequency space",
    "claiming that the singular tie locus has been proved measure zero",
    "claiming construction of every marked cone Gamma_S, maximal tube, or dyadic frequency cell",
    "claiming a smooth partition of unity, reproducing formula, L1 equivalence, or local Hardy-space theorem"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.strictDominance_markedBlock_structure
  ]

/-! ## T. Multi-norm marked partitions and cones -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.strictDominance_induces_unique_markedCone
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.cone,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.strictCone,
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictlyDominates,
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.toMarkedPartition
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.strictDominance_induces_unique_markedCone
    where
  formalizes @ "claim:multinorm-marked-partitions-closed-strict-cones-and-unique-strict-cone-membership",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:nonnegative-logarithmic-coordinate-point-with-chosen-strict-dominant-for-each-gauge",
  caveat @ "claim:strict-dominance-assignment-is-input-and-excludes-the-paper-tie-locus",
  caveat @ "claim:marked-cones-not-maximal-tubes-dyadic-frequency-cells-or-square-function-construction"

zil_file_contract physlib.entropicSpine.standardMultiNormMarkedCone where
  promises "formalization:marked-partitions-closed-strict-dominance-cones-principal-cone-and-unique-strict-cone-membership"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.block",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.marks",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.principal",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.cone",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.strictCone",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.mem_principal_cone_iff",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.toMarkedPartition",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.mem_strictCone_toMarkedPartition",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.eq_toMarkedPartition_of_strictDominates",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.strictDominance_induces_unique_markedCone"
  ]
  forbids_substitutes [
    "claiming existence or measurability of a strict-dominance assignment on the paper's full frequency space",
    "claiming that the singular tie locus has been classified or proved measure zero",
    "claiming construction of maximal tubes, dyadic frequency cells, or a smooth partition of unity",
    "claiming an infinite reproducing formula, L1 equivalence, or local Hardy-space theorem"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.strictDominance_induces_unique_markedCone
  ]

/-! ## U. Explicit coordinates for multi-norm marked cones -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.markedCone_explicitCoordinate_characterization
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.cone,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.explicitCone
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.markedCone_explicitCoordinate_characterization
    where
  formalizes @ "claim:multinorm-marked-cone-tau-coefficients-and-explicit-coordinate-characterization",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:finite-standard-multinorm-matrix-and-marked-partition",
  caveat @ "claim:algebraic-cone-characterization-without-nonempty-interior-or-tie-locus-classification",
  caveat @ "claim:no-maximal-tube-dyadic-frequency-cell-smooth-multiplier-or-square-function-construction"

zil_file_contract physlib.entropicSpine.standardMultiNormMarkedConeCoordinates where
  promises "formalization:tau-coefficients-positivity-normalization-and-exact-explicit-marked-cone-inequalities"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.MarkedIndex",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.blockFinset",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.tau",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.tau_le_ratio",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.exists_tau_eq_ratio",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.tau_pos",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.tau_self",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.explicitCone",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.cone_mark_le_tau_mul",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.dominates_of_explicitCone",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.mem_cone_iff_explicitCone",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.markedCone_explicitCoordinate_characterization"
  ]
  forbids_substitutes [
    "claiming that every marked cone has nonempty interior",
    "claiming classification or measure-zero analysis of the singular tie locus",
    "claiming construction of maximal tubes, admissible dyadic scales, or smooth frequency cells",
    "claiming a reproducing formula, L1 square-function equivalence, or local Hardy-space theorem"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.markedCone_explicitCoordinate_characterization
  ]

/-! ## V. Minimum-mark cones and the canonical dotted set -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.minimalMarkedPartition_dottedSet_characterization
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.AdmitsMarkedCone,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.minimalMarkedPartition,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.minimalDottedSet,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.cone
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.minimalMarkedPartition_dottedSet_characterization
    where
  formalizes @ "claim:multinorm-minimum-mark-cone-strict-separation-and-canonical-dotted-set",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:nonzero-logarithmic-point-admitting-at-least-one-containing-marked-cone",
  caveat @ "claim:containing-marked-cone-existence-is-an-explicit-premise-not-a-global-coverage-theorem",
  caveat @ "claim:minimal-dotted-set-not-yet-the-Gamma-D-partition-maximal-cubes-or-tubes"

zil_file_contract physlib.entropicSpine.standardMultiNormMinimalDottedSet where
  promises "formalization:block-merge-mark-count-minimization-strict-mark-separation-and-universal-minimal-dotted-set"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.marksFinset",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.markCount",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.mergeBlocks",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.marksFinset_mergeBlocks",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.markCount_mergeBlocks_lt",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.mem_cone_mergeBlocks",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.AdmitsMarkedCone",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.minimalMarkCount",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.minimalMarkedPartition",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.mark_pos_of_mem_cone",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.minimal_marks_strictlySeparated",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.minimal_marks_subset_of_mem_cone",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.minimum_mark_sets_unique",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.minimalDottedSet",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.minimalMarkedPartition_dottedSet_characterization"
  ]
  forbids_substitutes [
    "claiming global existence of a containing marked cone for every nonnegative point",
    "claiming that the singular tie locus has been classified or proved measure zero",
    "claiming that the regions Gamma-D or their maximal dyadic cubes and tubes have been constructed",
    "claiming a smooth multiplier family, reproducing formula, L1 equivalence, or Hardy-space theorem"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.minimalMarkedPartition_dottedSet_characterization
  ]

/-! ## W. Nonnegative marked-cone coverage and the `Γ(D)` partition -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.nonnegativePoint_markedCone_and_uniqueDottedRegion
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.AdmitsMarkedCone,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.dottedRegion
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.nonnegativePoint_markedCone_and_uniqueDottedRegion
    where
  formalizes @ "claim:every-nonnegative-multinorm-logarithmic-point-has-a-containing-marked-cone-and-unique-Gamma-D-index",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:finite-nonempty-standard-multinorm-coordinate-type-and-coordinatewise-nonnegative-point",
  caveat @ "claim:tie-walls-covered-without-classifying-their-measure-or-stratification",
  caveat @ "claim:Gamma-D-index-partition-without-maximal-dyadic-cubes-tubes-or-smooth-frequency-cells"

zil_file_contract physlib.entropicSpine.standardMultiNormConeCoverage where
  promises "formalization:global-nonnegative-marked-cone-coverage-premise-free-canonical-dotted-set-and-unique-Gamma-D-partition"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.exists_dominant",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.dominantOwner",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.dominantOwner_idempotent",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.coveringMarkedPartition",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.admitsMarkedCone_of_nonnegative",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.canonicalDottedSet",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.canonicalDottedSet_characterization",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.dottedRegion",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.existsUnique_dottedRegion",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.nonnegativePoint_markedCone_and_uniqueDottedRegion"
  ]
  forbids_substitutes [
    "claiming classification or measure-zero analysis of the singular tie locus",
    "claiming construction of maximal dyadic cubes, tubes, or smooth multiplier cells",
    "claiming a Calderon reproducing formula, L1 square-function equivalence, or local Hardy-space theorem"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.nonnegativePoint_markedCone_and_uniqueDottedRegion
  ]

/-! ## X. Exact Proposition 3.5 characterization of `Γ(D)` -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.dottedRegion_eq_markedConeUnion_inter_strictDottedLocus
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.dottedRegion,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.markedConeUnion,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.strictDottedLocus
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.dottedRegion_eq_markedConeUnion_inter_strictDottedLocus
    where
  formalizes @ "claim:multinorm-Proposition-3-5-exact-Gamma-D-marked-cone-union-strict-separation-characterization",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:nonempty-dotted-set-and-finite-nonempty-standard-multinorm-coordinate-type",
  caveat @ "claim:logarithmic-cone-characterization-not-yet-maximal-apex-existence-or-frequency-space-block-decomposition"

zil_file_contract physlib.entropicSpine.standardMultiNormDottedRegionCharacterization where
  promises "formalization:exact-Proposition-3-5-canonical-dotted-region-characterization"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.markedConeUnion",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.strictDottedLocus",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.canonicalDottedSet_eq_marks_of_strict",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.mem_dottedRegion_iff_markedConeUnion_and_strictDottedLocus",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.dottedRegion_eq_markedConeUnion_inter_strictDottedLocus"
  ]
  forbids_substitutes [
    "claiming convexity of every Gamma-D region",
    "claiming the singular tie locus is empty or measure zero",
    "claiming maximal dyadic apex existence, tube coverage, or smooth multiplier cells"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.dottedRegion_eq_markedConeUnion_inter_strictDottedLocus
  ]

/-! ## Y. Maximal dotted scales and finite dyadic tubes -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maximalDottedScale_finiteTube_geometry
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.dottedRegion,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.tubeIndexSet,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.logTube,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.logCell
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maximalDottedScale_finiteTube_geometry
    where
  formalizes @ "claim:multinorm-maximal-dotted-lattice-scale-finite-downward-tube-and-cell-union-geometry",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:supplied-lattice-scale-satisfying-the-explicit-maximal-dotted-scale-predicate",
  caveat @ "claim:maximality-is-verified-not-global-existence-or-unique-apex-selection",
  caveat @ "claim:logarithmic-cell-union-not-yet-frequency-preimage-smooth-partition-or-square-function"

zil_file_contract physlib.entropicSpine.standardMultiNormDyadicTube where
  promises "formalization:maximal-dotted-scale-predicate-finite-discrete-tube-greatest-apex-and-continuous-cell-union"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.toLogPoint",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.increment",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.logCell",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.IsMaximalDottedScale",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.isMaximalDottedScale_iff_geometric",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.tubeIndexSet",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.tubeIndexSet_finite",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.apex_isGreatest_tubeIndexSet",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.logTube",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maximalDottedScale_finiteTube_geometry"
  ]
  forbids_substitutes [
    "claiming every lattice cell has a proved unique maximal apex",
    "claiming the family of tubes already covers the orthant with disjoint interiors",
    "claiming frequency-space blocks, smooth multipliers, or an infinite Littlewood-Paley theorem"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maximalDottedScale_finiteTube_geometry
  ]

/-! ## Z. Wall-robust maximal-floor criterion -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.isMaximalDottedScale_iff_maximalFloorProfile
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.IsMaximalDottedScale,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.HasMaximalFloorProfile
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.isMaximalDottedScale_iff_maximalFloorProfile
    where
  formalizes @ "claim:multinorm-maximal-lattice-scale-iff-wall-robust-floor-profile",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:nonempty-canonical-dotted-region-and-membership-of-the-lattice-point",
  caveat @ "claim:floor-profile-quantifies-over-all-containing-marked-cones-on-tie-walls",
  caveat @ "claim:printed-strict-pairwise-tau-clause-is-not-asserted-because-it-is-stronger-than-maximality-under-the-stated-matrix-axioms"

zil_file_contract physlib.entropicSpine.standardMultiNormMaximalFloorCriterion where
  promises "formalization:correct-wall-robust-maximal-floor-characterization"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.floorCoordinate",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.SatisfiesFloorProfile",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.HasMaximalFloorProfile",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.increment_mem_cone_iff",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.isMaximalDottedScale_iff_maximalFloorProfile"
  ]
  forbids_substitutes [
    "asserting the printed strict pairwise tau condition without an additional hypothesis",
    "claiming unique maximal-apex existence from the criterion alone",
    "claiming frequency-space smooth cells or an infinite Littlewood-Paley theorem"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.isMaximalDottedScale_iff_maximalFloorProfile
  ]

/-! ## AA. Unique maximal apices, coverage, and disjoint interiors -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.uniqueMaximalApex_coverage_disjointInteriors
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.IsMaximalDottedScale,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.tubeIndexSet,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.logTube
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.uniqueMaximalApex_coverage_disjointInteriors
    where
  formalizes @ "claim:multinorm-unique-maximal-apex-regionwise-tube-coverage-and-disjoint-genuine-interiors",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:finite-nonempty-coordinate-type-and-nonempty-canonical-dotted-regions",
  caveat @ "claim:empty-dotted-origin-case-is-not-bundled-into-this-capstone",
  caveat @ "claim:continuous-tubes-are-logarithmic-boxes-not-yet-frequency-preimages-or-smooth-multiplier-cells"

zil_file_contract physlib.entropicSpine.standardMultiNormUniqueApexTubePartition where
  promises "formalization:unique-maximal-apex-lattice-partition-regionwise-coverage-and-disjoint-topological-interiors"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.markedApex",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.existsUnique_maximalApex",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.logTubeBox",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.logTube_eq_logTubeBox",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.interior_logTube",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.dottedRegion_cellUnion_eq_maximalTubeUnion",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.interiors_disjoint_of_distinct_maximal",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.uniqueMaximalApex_coverage_disjointInteriors"
  ]
  forbids_substitutes [
    "claiming the empty dotted origin case is part of the nonempty-region capstone",
    "claiming closed-tube intersections themselves are empty rather than their interiors being disjoint",
    "claiming frequency-space blocks, smooth multipliers, infinite reproducing series, or Hardy-space equivalence"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.uniqueMaximalApex_coverage_disjointInteriors
  ]

/-! ## AB. Quantitative maximal-tube proximity and overlap -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maximalScale_proximity_and_intersectingTube_bound
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.thickenedPrincipalCone,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.logTube,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.scaleSupDistance,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maxReciprocalEntry
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maximalScale_proximity_and_intersectingTube_bound
    where
  formalizes @ "claim:multinorm-maximal-apices-in-unit-thickened-principal-cone-and-intersecting-tubes-have-uniform-apex-distance",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:finite-standard-matrix-and-nonempty-canonical-dotted-regions",
  caveat @ "claim:overlap-bound-alone-does-not-produce-a-coloring-without-the-modular-separation-construction"

zil_file_contract physlib.entropicSpine.standardMultiNormTubeProximity where
  promises "formalization:maximal-apex-unit-cone-thickening-and-matrix-uniform-intersecting-tube-apex-bound"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.thickenedPrincipalCone",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maximalScale_div_lt_add_one",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maximalScale_mem_thickenedPrincipalCone_one",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maxReciprocalEntry",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.scaleSupDistance",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.scaleSupDistance_le_of_logTube_inter",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maximalScale_proximity_and_intersectingTube_bound"
  ]
  forbids_substitutes [
    "claiming a smooth multiplier partition or Hardy-space equivalence",
    "claiming the overlap inequality alone is a constructed finite coloring"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maximalScale_proximity_and_intersectingTube_bound
  ]

/-! ## AC. Principal-cone density and meet proximity -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.principalCone_density_and_maximalMeet_proximity
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.IsMaximalDottedScale,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.pointScaleSupDistance,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.scaleInf,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.scaleSupDistance
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.principalCone_density_and_maximalMeet_proximity
    where
  formalizes @ "claim:lemma-3-8-principal-cone-density-and-coordinatewise-meet-proximity",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:finite-standard-matrix-on-a-nonempty-coordinate-type",
  caveat @ "claim:matrix-uniform-additive-logarithmic-proximity-not-smooth-multiplier-regularity"

zil_file_contract physlib.entropicSpine.standardMultiNormApexDensity where
  promises "formalization:lemma-3-8-ii-iii-density-of-maximal-apices-and-meet-proximity"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.exists_maximalApex_near_thickenedLattice",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.exists_maximalApex_near_principalCone",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.exists_maximalApex_near_scaleInf",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.apex_eq_zero_of_isMaximalDottedScale_empty",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.exists_maximalApex_near_scaleInf_general",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.principalCone_density_and_maximalMeet_proximity"
  ]
  forbids_substitutes [
    "claiming Euclidean density rather than the stated logarithmic sup-distance bound",
    "claiming smooth multiplier bounds or Hardy-space equivalence"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.principalCone_density_and_maximalMeet_proximity
  ]

/-! ## AD. Constructed maximal-tube coloring and local overlap -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.constructedTubeColoring_and_finiteLocalOverlap
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.TubeColor,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.tubeColor,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.TubesAtPoint
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.constructedTubeColoring_and_finiteLocalOverlap
    where
  formalizes @ "claim:matrix-determined-finite-maximal-tube-coloring-and-uniform-local-overlap",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:lemma-3-8-intersecting-tube-apex-distance-bound",
  caveat @ "claim:coloring-applies-to-maximal-logarithmic-tubes-not-yet-to-smooth-multiplier-supports"

zil_file_contract physlib.entropicSpine.standardMultiNormTubeColoring where
  promises "formalization:constructed-finite-coloring-with-disjoint-fibers-and-pointwise-overlap-bound"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.tubeColorModulus",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.eq_of_tubeColor_eq_of_inter",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.tubeColor_fiber_pairwiseDisjoint",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.natCard_tubesAtPoint_le_colorCard",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.constructedTubeColoring_and_finiteLocalOverlap"
  ]
  forbids_substitutes [
    "claiming the color map is externally supplied",
    "identifying rough logarithmic tubes with smooth multiplier supports",
    "claiming infinite square-function or Hardy-space estimates"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.constructedTubeColoring_and_finiteLocalOverlap
  ]

/-! ## AE. Exact frequency preimages of logarithmic tubes -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock.frequencyBlock_eq_coordinateDyadicShell
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock.frequencyBlock,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock.coordinateDyadicShell
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock.frequencyBlock_eq_coordinateDyadicShell
    where
  formalizes @ "claim:multinorm-frequency-block-is-exact-positive-logarithmic-tube-preimage",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:maximal-lattice-scale-in-a-nonempty-canonical-dotted-region",
  caveat @ "claim:coordinate-shell-is-rough-and-does-not-yet-construct-smooth-multipliers"

zil_file_contract physlib.entropicSpine.standardMultiNormFrequencyBlock where
  promises "formalization:exact-frequency-preimage-as-product-of-dyadic-balls-and-dotted-annuli"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock.positiveLog2Norm",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock.frequencyBlock",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock.coordinateDyadicShell",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock.mem_frequencyBlock_iff_coordinateDyadicShell",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock.frequencyBlock_eq_coordinateDyadicShell"
  ]
  forbids_substitutes [
    "claiming smooth frequency cutoffs or derivative estimates",
    "claiming an infinite Littlewood-Paley reproducing formula",
    "claiming Hardy-space or L1 square-function equivalence"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock.frequencyBlock_eq_coordinateDyadicShell
  ]

/-! ## AF. Frequency-block gauge comparison -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison.frequencyBlock_blockGauge_comparison
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison.blockPhysicalGauge,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison.floorNormalizedBlockGauge,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison.blockGaugeConstant
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison.frequencyBlock_blockGauge_comparison
    where
  formalizes @ "claim:multinorm-frequency-block-outer-physical-gauge-and-corrected-normalized-inner-inclusion",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:containing-marked-cone-and-wall-robust-maximal-floor-profile",
  caveat @ "claim:printed-single-constant-inner-bound-is-not-asserted-on-floor-tie-walls"

zil_file_contract physlib.entropicSpine.standardMultiNormBlockGaugeComparison where
  promises "formalization:outer-anisotropic-block-gauge-estimate-and-valid-floor-normalized-reverse-inclusion"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison.blockPhysicalGauge",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison.floorNormalizedBlockGauge",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison.blockGaugeConstant",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison.blockPhysicalGauge_le_of_mem_frequencyBlock",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison.mem_frequencyBlock_of_normalizedBlockGauges",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison.frequencyBlock_blockGauge_comparison"
  ]
  forbids_substitutes [
    "asserting the paper's raw one-constant inner inclusion without an extra tie-wall hypothesis",
    "identifying a rough product shell with a smooth multiplier partition",
    "claiming bounded overlap, a Calderon formula, or Hardy-space equivalence from the gauge comparison alone"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison.frequencyBlock_blockGauge_comparison
  ]

/-! ## AG. Smooth cutoffs subordinate to exact frequency blocks -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff.smoothBlockCutoff_subordinate_frequencyBlock
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff.smoothBlockCutoff,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock.frequencyBlock,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff.paddedCoordinateShell
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff.smoothBlockCutoff_subordinate_frequencyBlock
    where
  formalizes @ "claim:smooth-cutoff-equals-one-on-exact-multinorm-frequency-block-with-explicit-padded-support",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:finite-dimensional-coordinate-spaces-admitting-contdiff-bumps",
  caveat @ "claim:individual-subordinate-cutoffs-not-yet-a-normalized-partition-of-unity"

zil_file_contract physlib.entropicSpine.standardMultiNormSmoothCutoff where
  promises "formalization:cinfinity-cutoff-range-core-equality-and-explicit-support-control"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff.smoothBlockCutoff",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff.contDiff_smoothBlockCutoff",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff.smoothBlockCutoff_eq_one_of_mem_coordinateDyadicShell",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff.support_smoothBlockCutoff_subset_paddedCoordinateShell",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff.smoothBlockCutoff_subordinate_frequencyBlock"
  ]
  forbids_substitutes [
    "claiming the individual cutoffs sum to one",
    "claiming uniform rescaled derivative or Schwartz-seminorm estimates",
    "claiming an infinite Calderon reproducing formula"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff.smoothBlockCutoff_subordinate_frequencyBlock
  ]

/-! ## AH. Coloring of actual smooth supports -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring.smoothTubeColor_fiber_pairwiseDisjoint
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring.SmoothTubeColor,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring.smoothTubeColor,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff.smoothBlockCutoff
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring.smoothTubeColor_fiber_pairwiseDisjoint
    where
  formalizes @ "claim:matrix-determined-coloring-with-disjoint-padded-smooth-multiplier-support-fibers",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:maximal-apex-geometry-and-explicit-smooth-support-padding",
  caveat @ "claim:finite-support-coloring-not-yet-an-infinite-littlewood-paley-reproducing-theorem"

zil_file_contract physlib.entropicSpine.standardMultiNormSmoothSupportColoring where
  promises "formalization:constructed-finite-coloring-of-the-actual-smooth-cutoff-supports"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring.paddedOverlapBound",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring.scaleSupDistance_le_of_paddedShell_inter",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring.smoothTubeColor",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring.eq_of_smoothTubeColor_eq_of_support_inter",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring.smoothTubeColor_fiber_pairwiseDisjoint"
  ]
  forbids_substitutes [
    "reusing the rough-tube coloring constant without accounting for smooth support padding",
    "claiming partition-of-unity normalization or derivative estimates",
    "claiming L1 or local Hardy-space equivalence"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring.smoothTubeColor_fiber_pairwiseDisjoint
  ]

/-! ## AI. Finite pointwise smooth square bound -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteSmoothSquareBound.finiteSmoothMultiplierSquareBound
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff.smoothBlockCutoff,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring.SmoothTubeColor
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteSmoothSquareBound.finiteSmoothMultiplierSquareBound
    where
  formalizes @ "claim:finite-pointwise-sum-of-squared-smooth-multinorm-cutoffs-bounded-by-constructed-color-count",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:constructed-disjoint-coloring-of-padded-smooth-supports",
  caveat @ "claim:finite-symbol-bound-not-yet-an-l1-square-function-norm-equivalence"

zil_file_contract physlib.entropicSpine.standardMultiNormFiniteSmoothSquareBound where
  promises "formalization:uniform-pointwise-active-count-and-finite-smooth-square-bound"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteSmoothSquareBound.activeSmoothTubes",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteSmoothSquareBound.smoothTubeColor_injOn_activeSmoothTubes",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteSmoothSquareBound.card_activeSmoothTubes_le_colorCount",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteSmoothSquareBound.finiteSmoothMultiplierSquareBound"
  ]
  forbids_substitutes [
    "claiming a lower square bound or normalized partition of unity",
    "claiming an infinite-series or distributional convergence theorem",
    "claiming the paper's L1 or Hardy-space conclusions"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteSmoothSquareBound.finiteSmoothMultiplierSquareBound
  ]

/-! ## AJ. Global low/high frequency coverage -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.fullFrequencyCover_and_cutoff_one
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.FullTubeIndex,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.fullFrequencyBlock,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.fullSmoothCutoff
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.fullFrequencyCover_and_cutoff_one
    where
  formalizes @ "claim:lemma-3-7-global-frequency-coverage-including-empty-region-low-block-and-unit-cutoff",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:canonical-dotted-region-partition-and-maximal-tube-coverage",
  caveat @ "claim:pointwise-global-cover-not-yet-a-locally-finite-infinite-smooth-partition"

zil_file_contract physlib.entropicSpine.standardMultiNormGlobalFrequencyCover where
  promises "formalization:completed-low-high-index-global-frequency-cover-and-unit-cutoff-selection"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.FullTubeIndex",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.exists_fullTubeIndex_mem",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.exists_fullFrequencyBlock_mem",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.fullSmoothCutoff_eq_one_of_mem_fullFrequencyBlock",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.fullFrequencyCover_and_cutoff_one"
  ]
  forbids_substitutes [
    "discarding the empty dotted region or treating the origin as a nonempty maximal tube",
    "claiming local finiteness of the full infinite smooth family",
    "claiming a distributional Calderon formula"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.fullFrequencyCover_and_cutoff_one
  ]

/-! ## AK. Finite normalized smooth partitions -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition.finiteNormalizedPartition_of_coversAt
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition.finiteSmoothEnergy,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition.normalizedSmoothSymbol,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.fullFrequencyBlock
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition.finiteNormalizedPartition_of_coversAt
    where
  formalizes @ "claim:positive-quadratic-normalization-and-exact-finite-smooth-partition-at-covered-frequencies",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:finite-completed-block-family-covering-the-evaluated-frequency",
  caveat @ "claim:finite-pointwise-normalization-not-yet-the-paper-infinite-schwartz-partition"

zil_file_contract physlib.entropicSpine.standardMultiNormFiniteNormalizedPartition where
  promises "formalization:cinfinity-finite-normalization-domain-positive-denominator-and-exact-partition"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition.finiteSmoothEnergy",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition.contDiff_finiteSmoothEnergy",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition.normalizedSmoothSymbol",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition.contDiffOn_normalizedSmoothSymbol",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition.sum_normalizedSmoothSymbol_eq_one",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition.finiteNormalizedPartition_of_coversAt"
  ]
  forbids_substitutes [
    "assuming denominator positivity without a covering block",
    "claiming a finite pointwise identity is an infinite distributional sum",
    "claiming uniform Schwartz seminorm or vanishing-moment estimates"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition.finiteNormalizedPartition_of_coversAt
  ]

/-! ## AL. Finite reproducing and square identities -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteReproducingFormula.finiteMultiNorm_reproducing_square_support
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteReproducingFormula.normalizedMultiplierPiece,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteReproducingFormula.normalizedAnalysisPiece,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition.normalizedSmoothSymbol
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteReproducingFormula.finiteMultiNorm_reproducing_square_support
    where
  formalizes @ "claim:exact-finite-normalized-multiplier-reconstruction-square-analysis-and-support-subordination",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:finite-completed-block-cover-at-the-evaluated-frequency",
  caveat @ "claim:fourier-side-finite-algebra-not-yet-a-convolution-or-distributional-calderon-formula"

zil_file_contract physlib.entropicSpine.standardMultiNormFiniteReproducingFormula where
  promises "formalization:finite-normalized-reconstruction-exact-square-identity-and-support-control"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteReproducingFormula.normalizedMultiplierPiece",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteReproducingFormula.normalizedAnalysisPiece",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteReproducingFormula.sum_normalizedMultiplierPiece_eq",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteReproducingFormula.sum_normalizedAnalysisPiece_sq_eq",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteReproducingFormula.support_normalizedSmoothSymbol_subset",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteReproducingFormula.finiteMultiNorm_reproducing_square_support"
  ]
  forbids_substitutes [
    "calling the finite pointwise multiplier identity Proposition 4.3",
    "claiming convergence in tempered distributions",
    "claiming cancellation, vanishing moments, or L1 square-function equivalence"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteReproducingFormula.finiteMultiNorm_reproducing_square_support
  ]

/-! ## AM. Global neighborhood-level local finiteness -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalLocalFiniteness.globalSmoothCover_locallyFinite
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.FullTubeIndex,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.fullSmoothCutoff
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalLocalFiniteness.globalSmoothCover_locallyFinite
    where
  formalizes @ "claim:completed-smooth-multinorm-cover-is-neighborhood-locally-finite-and-pointwise-nonvanishing",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:finite-standard-multinorm-index-and-explicit-padded-cutoff-support",
  caveat @ "claim:local-finiteness-does-not-by-itself-prove-uniform-schwartz-seminorm-estimates"

zil_file_contract physlib.entropicSpine.standardMultiNormGlobalLocalFiniteness where
  promises "formalization:bounded-apex-finiteness-and-neighborhood-locally-finite-global-smooth-cover"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalLocalFiniteness.finite_boundedMaximalTubeIndex",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalLocalFiniteness.exists_dotted_apex_control",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalLocalFiniteness.locallyFinite_maximalSmoothSupports",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalLocalFiniteness.locallyFinite_fullSmoothSupports",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalLocalFiniteness.globalSmoothCover_locallyFinite"
  ]
  forbids_substitutes [
    "replacing neighborhood-level local finiteness by pointwise finite overlap",
    "using the finite coloring alone as a proof that supports cannot accumulate",
    "claiming Schwartz decay or Fourier-inversion convergence"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalLocalFiniteness.globalSmoothCover_locallyFinite
  ]

/-! ## AN. Native global smooth partition of unity -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalNormalizedPartition.globalSmoothPartitionOfUnity_spec
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalNormalizedPartition.globalSmoothPartitionOfUnity
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalNormalizedPartition.globalSmoothPartitionOfUnity_spec
    where
  formalizes @ "claim:globally-positive-smooth-quadratic-normalization-bundled-as-native-smooth-partition-of-unity",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:neighborhood-locally-finite-completed-smooth-cover-with-a-unit-cutoff-at-every-frequency",
  caveat @ "claim:normalized-frequency-symbol-partition-not-yet-a-calderon-identity-in-tempered-distributions"

zil_file_contract physlib.entropicSpine.standardMultiNormGlobalNormalizedPartition where
  promises "formalization:global-cinfinity-positive-denominator-and-native-smooth-partition-of-unity"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalNormalizedPartition.globalSmoothEnergy",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalNormalizedPartition.contDiff_globalSmoothEnergy",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalNormalizedPartition.globalSmoothEnergy_pos",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalNormalizedPartition.globalNormalizedSmoothSymbol",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalNormalizedPartition.globalSmoothPartitionOfUnity",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalNormalizedPartition.globalSmoothPartitionOfUnity_spec"
  ]
  forbids_substitutes [
    "assuming positivity of the infinite normalization denominator",
    "using an unrestricted infinite series where Mathlib finsum local finiteness is required",
    "claiming uniform multiplier derivative bounds from smoothness alone"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalNormalizedPartition.globalSmoothPartitionOfUnity_spec
  ]

/-! ## AO. Global pointwise-finite reproducing identities -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.globalMultiNorm_reproducing_square_finiteSupport
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.globalNormalizedMultiplierPiece,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.globalNormalizedAnalysisPiece,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.globalSymbolFinsupport
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.globalMultiNorm_reproducing_square_finiteSupport
    where
  formalizes @ "claim:exact-global-finsum-multiplier-reconstruction-and-square-analysis-with-canonical-pointwise-finite-carrier",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:native-global-smooth-multinorm-partition-of-unity",
  caveat @ "claim:frequency-point-algebra-not-yet-an-inverse-fourier-convolution-or-tempered-distribution-theorem"

zil_file_contract physlib.entropicSpine.standardMultiNormGlobalReproducingFormula where
  promises "formalization:exact-infinite-pointwise-finite-reconstruction-square-identity-and-support-subordination"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.globalNormalizedMultiplierPiece",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.globalNormalizedAnalysisPiece",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.finsum_globalNormalizedMultiplierPiece_eq",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.finsum_globalNormalizedAnalysisPiece_sq_eq",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.globalSymbolFinsupport",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.globalMultiNorm_reproducing_square_finiteSupport"
  ]
  forbids_substitutes [
    "calling a pointwise frequency identity a distributional Calderon reproducing formula",
    "claiming convergence of inverse Fourier transforms without Schwartz estimates",
    "claiming the paper's Hardy-space norm equivalences"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.globalMultiNorm_reproducing_square_finiteSupport
  ]

/-! ## AP. Complex multi-norm amplitude and Born resolution -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula.globalMultiNorm_complexReproducing_bornResolution
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula.globalNormalizedComplexMultiplierPiece,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula.globalNormalizedComplexAnalysisPiece,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.globalSymbolFinsupport
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula.globalMultiNorm_complexReproducing_bornResolution
    where
  formalizes @ "claim:global-multinorm-complex-amplitude-reconstruction-and-exact-born-weight-resolution",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:native-global-smooth-multinorm-partition-with-canonical-pointwise-finite-carrier",
  caveat @ "claim:pointwise-complex-frequency-resolution-not-yet-a-distributional-calderon-or-l1-square-function-theorem"

zil_file_contract physlib.entropicSpine.standardMultiNormGlobalComplexReproducingFormula where
  promises "formalization:exact-locally-finite-complex-reconstruction-and-born-resolution"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula.globalNormalizedComplexMultiplierPiece",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula.globalNormalizedComplexAnalysisPiece",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula.finsum_globalNormalizedComplexMultiplierPiece_eq",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula.finsum_normSq_globalNormalizedComplexAnalysisPiece_eq",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula.globalMultiNorm_complexReproducing_bornResolution"
  ]
  forbids_substitutes [
    "replacing a locally finite finsum by an unproved convergent infinite series",
    "calling pointwise Born resolution an integrated Plancherel or Hardy-space norm equivalence",
    "claiming a tempered-distribution Calderon formula from complex scalar reconstruction"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula.globalMultiNorm_complexReproducing_bornResolution
  ]

/-! ## AQ. Multi-norm Schrödinger localization -/

zil_theorem_intent
    Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerLocalization.multiNorm_schrodingerLocalization_bridge
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.smearedSchrodingerGenerator,
    Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerLocalization.euclideanMultiNormAnalysisCutoff,
    Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerEvolution
  ]

zil attach
    Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerLocalization.multiNorm_schrodingerLocalization_bridge
    where
  formalizes @ "claim:multinorm-analysis-branches-commute-with-linear-functional-and-free-schrodinger-evolution",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:fixed-background-complex-linear-functional-generator-and-one-block-euclidean-l2-specialization",
  caveat @ "claim:contractive-smooth-l2-localization-does-not-imply-a-schrodinger-maximal-estimate-or-l1-square-function-equivalence"

zil_file_contract physlib.entropicSpine.multiNormSchrodingerLocalization where
  promises "formalization:functional-generator-covariance-and-contractive-euclidean-l2-free-flow-covariance"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerLocalization.globalComplexAnalysisPiece_commutes_smearedSchrodinger",
    "lean:Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerLocalization.euclideanMultiNormAnalysisCutoff",
    "lean:Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerLocalization.norm_euclideanMultiNormAnalysisCutoff_le",
    "lean:Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerLocalization.euclideanMultiNormAnalysisCutoff_commutes_multiplier",
    "lean:Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerLocalization.euclideanMultiNormFrequencyLocalization_commutes_evolution",
    "lean:Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerLocalization.multiNorm_schrodingerLocalization_bridge"
  ]
  forbids_substitutes [
    "promoting the one-block Euclidean specialization to the full anisotropic product-space Fourier theory",
    "claiming nonlinear gravity-coupled Schrödinger superposition",
    "claiming pointwise almost-everywhere convergence or a maximal estimate from free-flow covariance"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerLocalization.multiNorm_schrodingerLocalization_bridge
  ]

/-! ## AR. Multi-norm Schrödinger decoherence -/

zil_theorem_intent
    Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerDecoherence.multiNorm_schrodingerDecoherence_bridge
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerDecoherence.multiNormDecoherenceFunctional,
    Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert.quantalMeasure,
    Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerPhase
  ]

zil attach
    Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerDecoherence.multiNorm_schrodingerDecoherence_bridge
    where
  formalizes @ "claim:multinorm-schrodinger-branches-form-a-gram-decoherence-kernel-with-exact-born-resolution-and-free-phase-invariance",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:rank-one-sorkin-johnston-dowker-halliwell-decoherence-functional-on-localized-complex-branches",
  caveat @ "claim:branch-index-kernel-does-not-supply-a-coarse-graining-event-lattice-or-environmental-decoherence-dynamics"

zil_file_contract physlib.entropicSpine.multiNormSchrodingerDecoherence where
  promises "formalization:gram-decoherence-kernel-exact-born-diagonal-resolution-and-unitary-free-phase-invariance"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerDecoherence.multiNormDecoherenceFunctional",
    "lean:Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerDecoherence.multiNormDecoherenceFunctional_eq_gram",
    "lean:Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerDecoherence.finsum_multiNormDecoherenceFunctional_quantalMeasure_eq",
    "lean:Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerDecoherence.multiNormDecoherenceFunctional_offdiag_eq",
    "lean:Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerDecoherence.euclideanMultiNormDecoherence_freeSchrodingerPhase_invariant",
    "lean:Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerDecoherence.multiNorm_schrodingerDecoherence_bridge"
  ]
  forbids_substitutes [
    "calling phase invariance environmental decoherence or entropy production",
    "claiming a full IsDecoherenceFunctional event algebra without additive coarse-graining data",
    "promoting pointwise Born resolution to an integrated probability normalization without integrability"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerDecoherence.multiNorm_schrodingerDecoherence_bridge
  ]

/-! ## AS. Section 4 dyadic Schwartz kernels -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.dyadicSchwartzKernel_cancellation_telescope
    where
  at_level structural
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.dyadicApproximationKernel,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.dyadicDetailKernel
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.dyadicSchwartzKernel_cancellation_telescope
    where
  formalizes @ "claim:section4-normalized-dyadic-schwartz-kernels-positive-level-cancellation-and-finite-telescoping",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-section4",
  requires @ "assumption:finite-dimensional-real-inner-product-space-and-normalized-compactly-supported-smooth-bump",
  caveat @ "claim:one-parameter-order-one-cancellation-not-yet-the-paper-multi-parameter-higher-moment-family"

zil_file_contract physlib.entropicSpine.multiNormSection4SchwartzKernel where
  promises "formalization:genuine-schwartz-kernel-unit-mass-cancellation-and-exact-finite-telescope"
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.normalizedBumpSchwartz",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.dyadicApproximationKernel",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.integral_dyadicApproximationKernel",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.integral_dyadicDetailKernel_succ",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.sum_range_dyadicDetailKernel",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.dyadicSchwartzKernel_cancellation_telescope"
  ]
  forbids_substitutes [
    "calling order-one integral cancellation arbitrary multi-index moment cancellation",
    "claiming uniform anisotropic multi-parameter Schwartz seminorm bounds",
    "calling a finite telescope a distributional limit without a topology"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.dyadicSchwartzKernel_cancellation_telescope
  ]

/-! ## AT. Section 4 tempered-distribution Calderón identity -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.dyadicDetailDistribution_tendsto_delta
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.dyadicDetailDistribution,
    TemperedDistribution.delta
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.dyadicDetailDistribution_tendsto_delta
    where
  formalizes @ "claim:section4-dyadic-detail-partial-sums-converge-to-dirac-in-tempered-distribution-topology",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-section4",
  requires @ "assumption:mathlib-pointwise-topology-on-tempered-distributions-and-normalized-dyadic-schwartz-kernel",
  caveat @ "claim:one-parameter-dirac-reproduction-not-yet-proposition4.3-multi-parameter-dual-calderon-family"

zil_file_contract physlib.entropicSpine.multiNormSection4TemperedCalderon where
  promises "formalization:exact-finite-distribution-sums-and-convergence-to-dirac"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.dyadicApproximationDistribution",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.dyadicDetailDistribution",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.sum_range_dyadicDetailDistribution",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.tendsto_dyadicApproximationDistribution_delta",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.dyadicDetailDistribution_tendsto_delta"
  ]
  forbids_substitutes [
    "promoting pointwise convergence on Schwartz tests to a stronger unspecified distribution topology",
    "claiming the tensor-product or convolution-family identities of Propositions 4.3 and 4.4",
    "claiming L1 square-function or Hardy-space bounds from distributional reproduction"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.dyadicDetailDistribution_tendsto_delta
  ]

/-! ## AU. Section 4 physical convolution and multi-norm adapter -/

zil_theorem_intent
    Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.physicalCalderon_reconstruction_multiNormMultiplier_bridge
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.dyadicCalderonPartialReconstruction,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula.globalNormalizedComplexMultiplierPiece
  ]

zil attach
    Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.physicalCalderon_reconstruction_multiNormMultiplier_bridge
    where
  formalizes @ "claim:section4-physical-convolution-reconstruction-and-existing-multinorm-frequency-multiplier-adapter",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley-section4",
  requires @ "assumption:schwartz-amplitude-and-one-block-kernel-realization-of-an-existing-normalized-multinorm-symbol",
  caveat @ "claim:adapter-does-not-construct-the-full-anisotropic-symbol-realization-or-dual-tilded-family"

zil_file_contract physlib.entropicSpine.multiNormSection4PhysicalCalderon where
  promises "formalization:pointwise-schwartz-convolution-reconstruction-fourier-product-and-existing-multinorm-multiplier-reuse"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.dyadicCalderonConvolutionPiece",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.dyadicCalderonPartialReconstruction",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.dyadicCalderonPartialReconstruction_tendsto_apply",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.fourier_dyadicCalderonConvolutionPiece_apply",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.fourier_convolution_eq_globalNormalizedComplexMultiplierPiece",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.physicalCalderon_reconstruction_multiNormMultiplier_bridge"
  ]
  forbids_substitutes [
    "treating a conditional one-block symbol adapter as construction of every anisotropic multi-norm kernel",
    "claiming uniform multi-parameter Schwartz estimates or higher moment cancellation",
    "claiming L1 square-function equivalence or atomic Hardy-space decomposition"
  ]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.physicalCalderon_reconstruction_multiNormMultiplier_bridge
  ]

/-! ## AV. Finite-overlap Euclidean Littlewood--Paley energy -/

zil_theorem_intent
    Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley.finiteDyadicOverlapLittlewoodPaley_constructedColoring_bessel
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley.dyadicAnnulusColor,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.annularFrequencyProjection,
    Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.freeSchrodingerEvolution
  ]

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley.finiteDyadicOverlapLittlewoodPaley_constructedColoring_bessel
    where
  formalizes @ "claim:constructed-two-color-dyadic-littlewood-paley-energy-and-bessel-bound",
  supported_by @ "paper:hejna-nagel-ricci-2025-multinorm-littlewood-paley",
  requires @ "assumption:standard-binary-dyadic-annular-radius-family",
  caveat @ "claim:finite-rough-l2-bound-not-infinite-smooth-l1-square-function-equivalence"

zil_file_contract physlib.entropicSpine.euclideanFiniteOverlapLittlewoodPaley where
  promises "formalization:finite-spectral-coloring-exact-fiber-energy-overlap-bessel-and-free-flow-covariance"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley.HasSpectralColoring",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley.finiteOverlapLittlewoodPaley_coloredEnergy",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley.finiteOverlapLittlewoodPaley_bessel",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley.dyadicAnnulusColor",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley.hasSpectralColoring_dyadicAnnuli",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley.finiteDyadicOverlapLittlewoodPaley_constructedColoring_bessel"
  ]
  forbids_substitutes [
    "claiming that the dyadic parity coloring is the paper's smooth multi-norm multiplier coloring",
    "claiming an infinite-series Littlewood-Paley square-function theorem",
    "claiming L1 equivalence, a Calderon reproducing formula, local Hardy-space completeness, or atomic decomposition",
    "claiming a Schrödinger maximal estimate or pointwise almost-everywhere convergence"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley.finiteDyadicOverlapLittlewoodPaley_constructedColoring_bessel
  ]

/-! ## AW. Entropic density on a curved, gauge-coupled QFT measure -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.entropicDensity_curvedMeasure_gaugeQuantumMatter_bridge
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction,
    Physlib.QFT.PathIntegral.CurvedMeasurePathIntegralModel.partition,
    Physlib.QFT.PathIntegral.CurvedMeasurePathIntegralModel.gaugeCoupledPartition,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential.curvedQuantumPotential
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential.quantumMatter_is_classical_plus_curvedQuantum
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint.kgMatterDensity,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential.curvedQuantumPotential
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.entropicDensity_curvedMeasure_maxwellContinuity_bridge
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction,
    Physlib.QFT.PathIntegral.CurvedMeasurePathIntegralModel.gaugeCoupledPartition,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant.fourCurrent,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday.faraday
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.edWaveFunction_complexCovariantDeriv_gauge_bridge
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.complexCovariantDeriv
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.entropicDensity_curvedMeasure_gaugeQuantumMatter_bridge
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential.quantumMatter_is_classical_plus_curvedQuantum",
  formalizes @ "claim:caticha-entropic-density-is-the-curved-qft-measure-density-and-quantum-matter-density",
  requires @ "assumption:curved-model-volume-density-identified-with-entropic-probability-density",
  requires @ "assumption:gauge-operator-stack-supplies-the-source-potential",
  caveat @ "claim:interface-theorem-does-not-derive-minimal-electromagnetic-coupling",
  caveat @ "claim:path-integral-measure-identity-does-not-establish-existence-of-an-interacting-curved-qft"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential.quantumMatter_is_classical_plus_curvedQuantum
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential.curvedQuantumPotential_eq",
  formalizes @ "claim:caticha-quantum-matter-hamiltonian-is-classical-curved-klein-gordon-plus-curved-quantum-potential",
  caveat @ "claim:exact-density-level-split-not-the-functional-poisson-bracket-derivation"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.entropicDensity_curvedMeasure_maxwellContinuity_bridge
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday.faraday_bianchi",
  formalizes @ "claim:caticha-entropic-density-and-curved-gauge-source-share-the-potential-generating-a-conserved-maxwell-current",
  requires @ "assumption:curved-model-volume-density-identified-with-entropic-probability-density",
  requires @ "assumption:path-integral-gauge-potential-identified-with-the-real-maxwell-potential",
  caveat @ "claim:explicit-potential-adapter-not-a-derivation-of-minimal-coupling",
  caveat @ "claim:momentum-space-maxwell-continuity-and-bianchi-not-a-general-curved-pde-solution"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.edWaveFunction_complexCovariantDeriv_gauge_bridge
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.complexCovariantDeriv_gauge_covariant",
  formalizes @ "claim:caticha-wavefunction-phase-shift-is-covariant-under-the-entropic-complex-gauge-derivative",
  requires @ "assumption:ordinary-derivative-data-transform-by-the-abelian-product-rule",
  caveat @ "claim:algebraic-abelian-gauge-covariance-not-a-dynamical-generation-of-the-electromagnetic-potential",
  caveat @ "claim:does-not-yet-construct-the-full-functional-schrodinger-gauge-covariant-pde"

zil_file_contract physlib.entropicSpine.entropicCurvedGaugeQFT where
  promises "formalization:one-shared-density-links-caticha-born-amplitude-curved-path-integral-measure-gauge-source-shift-and-curved-quantum-matter"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq",
    "lean:Physlib.QFT.PathIntegral.CurvedMeasurePathIntegralModel.partition_eq_base_integral_density_smul",
    "lean:Physlib.QFT.PathIntegral.CurvedMeasurePathIntegralModel.gaugeCoupledPartition",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential.quantumMatter_is_classical_plus_curvedQuantum",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.entropicDensity_curvedMeasure_gaugeQuantumMatter_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.entropicDensity_curvedMeasure_maxwellContinuity_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.complexCovariantDeriv_gauge_covariant",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.edWaveFunction_complexCovariantDeriv_gauge_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant.fourCurrent_conserved",
    "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday.faraday_bianchi"
  ]
  forbids_substitutes [
    "conjoining unrelated models without a shared density identification",
    "calling the source shift a derivation of gauge covariance or minimal coupling",
    "calling a measure-level path integral model a constructed interacting curved-spacetime QFT"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential.quantumMatter_is_classical_plus_curvedQuantum,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.entropicDensity_curvedMeasure_gaugeQuantumMatter_bridge,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.entropicDensity_curvedMeasure_maxwellContinuity_bridge,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.edWaveFunction_complexCovariantDeriv_gauge_bridge
  ]

/-! ## AX. Einstein--Maxwell equations and conservation at the bit-count coupling -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_system_bitForm
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectroGravitationalFieldEquation,
    Physlib.Thermodynamics.holographicBits
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_equations_bitForm
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectroGravitationalFieldEquation,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday.faraday,
    Physlib.Thermodynamics.holographicBits
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_conservation_bitForm
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectroGravitationalFieldEquation,
    Physlib.Thermodynamics.holographicBits
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_system_bitForm
    where
  supported_by @ "lean:Physlib.Thermodynamics.GravitationalCouplingSystem.einsteinCoupling_bitForm",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:einstein-maxwell-system-at-holographic-area-per-bit-coupling",
  requires @ "assumption:holographic-screen-bit-count",
  caveat @ "claim:constructs-the-system-from-explicit-einstein-maxwell-entropic-curvature-and-double-copy-premises"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_equations_bitForm
    where
  supported_by @ "lean:Physlib.Thermodynamics.GravitationalCouplingSystem.einsteinCoupling_bitForm",
  formalizes @ "claim:einstein-maxwell-bianchi-double-copy-equations-at-bit-count-coupling",
  requires @ "assumption:electrogravitational-field-equation-carrier",
  requires @ "assumption:holographic-screen-bit-count",
  caveat @ "claim:algebraic-momentum-space-maxwell-carrier-not-a-general-curved-pde-solution"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_conservation_bitForm
    where
  supported_by @ "lean:Physlib.Thermodynamics.GravitationalCouplingSystem.einsteinCoupling_bitForm",
  formalizes @ "claim:electromagnetic-stress-energy-conservation-from-contracted-second-bianchi-at-bit-count-coupling",
  requires @ "assumption:contracted-einstein-divergence-and-second-bianchi",
  requires @ "assumption:holographic-screen-bit-count",
  caveat @ "claim:conservation-is-conditional-on-the-explicit-divergence-identification"

zil_file_contract physlib.entropicSpine.electroGravitationalBitForm where
  promises "formalization:public-kernel-clean-einstein-maxwell-system-equations-and-conservation-at-area-per-bit-newton-coupling"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_system_bitForm",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_equations_bitForm",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_conservation_bitForm"
  ]
  forbids_substitutes [
    "calling a conditional bit-count coupling identity an empirical measurement of Newton's constant",
    "promoting the momentum-space Faraday carrier to a general curved-spacetime Maxwell PDE",
    "claiming the BCJ algebraic split constructs a quantum gravity theory"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_system_bitForm,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_equations_bitForm,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_conservation_bitForm
  ]

/-! ## AY. Caticha spectral evolution and curved-spacetime algebraic QFT -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.kleinGordon_continuity_program
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorInterpolation.muInterp,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular.modularGenerator
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.schmidt_quasifree_bridge
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime.quasifreeWeight
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.spacetime_superoperator_program
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.KazamaTomitaTakesakiModular.modularGenerator,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday.faraday
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.catichaFunctional_kleinGordon_continuity_bridge
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.CatichaModularIntertwines,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.smearedSchrodingerGenerator,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorInterpolation.muInterp
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.catichaFunctional_emLiouvillian_bridge
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.CatichaModularIntertwines,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.smearedSchrodingerGenerator,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMFieldSuperoperator.emLiouvillian
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.catichaDensity_schmidt_quasifree_bridge
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction,
    Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime.quasifreeWeight
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.schmidt_quasifree_bridge
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.pure_quasifree_separable",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.pure_state_complex_structure",
  formalizes @ "claim:schmidt-bogoliubov-entanglement-carrier-is-a-verch-quasifree-hadamard-weighted-state",
  caveat @ "claim:finite-two-mode-symplectic-carrier-not-a-full-locally-covariant-weyl-algebra-construction"

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.kleinGordon_continuity_program
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.evolution_continuity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.mu1_eq_smul_mu0",
  formalizes @ "claim:verch-klein-gordon-cauchy-evolution-links-energy-hadamard-norms-symplectic-continuity-and-the-modular-liouvillian",
  caveat @ "claim:finite-cauchy-data-carrier-not-the-full-operator-analytic-continuity-theorem"

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.spacetime_superoperator_program
    where
  formalizes @ "claim:klein-gordon-polarizator-and-electromagnetic-field-use-the-same-modular-adjoint-superoperator-pattern",
  caveat @ "claim:finite-matrix-carrier-not-an-unbounded-operator-evolution-on-a-curved-spacetime-hilbert-space"

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.catichaFunctional_kleinGordon_continuity_bridge
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.kleinGordon_continuity_program",
  formalizes @ "claim:caticha-functional-schrodinger-generator-intertwines-with-verch-klein-gordon-liouvillian-through-a-scalar-readout",
  requires @ "assumption:explicit-scalar-readout-intertwines-caticha-and-modular-generators",
  caveat @ "claim:readout-intertwiner-is-an-explicit-interface-not-a-constructed-continuum-field-evaluation-functional"

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.catichaFunctional_emLiouvillian_bridge
    where
  formalizes @ "claim:caticha-functional-schrodinger-generator-is-the-scalar-readout-of-electromagnetic-modular-field-evolution",
  requires @ "assumption:explicit-scalar-readout-intertwines-caticha-and-fin4-modular-generators",
  caveat @ "claim:finite-matrix-liouvillian-readout-not-a-full-curved-maxwell-functional-schrodinger-pde"

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.catichaDensity_schmidt_quasifree_bridge
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.schmidt_quasifree_bridge",
  formalizes @ "claim:caticha-born-density-is-the-schmidt-verch-quasifree-weight-under-an-explicit-one-particle-identification",
  requires @ "assumption:caticha-density-equals-schmidt-tanh-suppression",
  caveat @ "claim:pointwise-density-identification-does-not-prove-the-hadamard-microlocal-spectrum-condition"

zil_file_contract physlib.entropicSpine.curvedAlgebraicQFT where
  promises "formalization:audited-caticha-spectral-schrodinger-verch-quasifree-and-klein-gordon-electromagnetic-modular-carriers"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSchrodingerNagaoNielsen.normalizedPerepelkin_nonHermitian_nagaoNielsen_caticha_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.schmidt_quasifree_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.kleinGordon_continuity_program",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.spacetime_superoperator_program",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.CatichaModularIntertwines",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.catichaFunctional_kleinGordon_continuity_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.catichaFunctional_emLiouvillian_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.catichaDensity_schmidt_quasifree_bridge"
  ]
  forbids_substitutes [
    "claiming that side-by-side finite carriers prove a locally covariant interacting QFT",
    "identifying a modewise ordinary derivative with the full functional Schrodinger PDE",
    "claiming Hadamard microlocal spectrum estimates from a finite quasifree weight identity",
    "hiding the intertwining premise for general readouts or presenting the constructed finite entry readout as a canonical continuum functional"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSchrodingerNagaoNielsen.normalizedPerepelkin_nonHermitian_nagaoNielsen_caticha_chain,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.kleinGordon_continuity_program,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.schmidt_quasifree_bridge,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.spacetime_superoperator_program,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.catichaFunctional_kleinGordon_continuity_bridge,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.catichaFunctional_emLiouvillian_bridge,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.catichaDensity_schmidt_quasifree_bridge
  ]

/-! ## AZ. Constructed Caticha electrodynamics and general-coordinate Maxwell evolution -/

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
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantFieldDerivative_gauge_covariant
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantFieldDerivative
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDLorentzianKineticDensity_gauge_invariant
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantFieldDerivative_gauge_covariant,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaLorentzianKineticDensity
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
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.covariantSecondDerivVectorAt_commutator_eq_riemannAction
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.riemannFromConnection,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.IsTorsionFree
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.metricCompatibleFaradayDivergenceAt_eq_wave_sub_gradDiv_sub_ricci
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.covariantVectorWaveAt,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.raisedRicciActionAt
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

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.gaugeCovariantSmearedSchrodinger_equation_covariant
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.complexCovariantDeriv_gauge_covariant",
  formalizes @ "claim:caticha-smeared-functional-schrodinger-equation-is-covariant-under-the-explicit-phase-connection-transformation",
  caveat @ "claim:single-mode-complex-linear-operator-layer-not-a-continuum-field-space-gauge-bundle"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantDerivative_gauge_covariant
    where
  formalizes @ "claim:caticha-qed-minimal-coupling-derivative-is-the-existing-entropic-complex-connection-and-transforms-homogeneously-under-the-explicit-local-gauge-shift",
  supported_by @ "paper:caticha-entropic-dynamics-qed-2511.19238-eq-58",
  caveat @ "claim:finite-index-derivative-identity-not-the-continuum-functional-gauss-constraint"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantFieldDerivative_gauge_covariant
    where
  formalizes @ "claim:catichas-minimally-coupled-derivative-transforms-homogeneously-pointwise-on-arbitrary-spacetime-and-configuration-carriers",
  supported_by @ "paper:caticha-entropic-dynamics-qed-2511.19238-eq-58",
  caveat @ "claim:continuum-pointwise-covariance-not-the-functional-gauss-constraint-or-an-interacting-qed-measure"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDLorentzianKineticDensity_gauge_invariant
    where
  formalizes @ "claim:the-full-mostly-minus-lorentzian-kinetic-contraction-of-the-caticha-covariant-field-derivative-is-invariant-under-local-unit-phases-at-every-spacetime-point",
  supported_by @ "lean:Physlib.Relativity.minkowskiBilinC",
  caveat @ "claim:flat-signature-pointwise-continuum-identity-not-yet-the-curved-pseudo-riemannian-volume-integral-or-maxwell-field-equation"

zil attach
    Electromagnetism.DistElectromagneticPotential.satisfiesDistributionalMaxwell_testFunction
    where
  formalizes @ "claim:stationarity-of-the-existing-distributional-maxwell-current-lagrangian-gives-mu0-inverse-times-the-weak-faraday-divergence-equal-to-current-on-every-schwartz-test-function",
  supported_by @ "paper:caticha-entropic-dynamics-qed-2511.19238-maxwell-sector",
  caveat @ "claim:flat-spacetime-tempered-distribution-result-not-a-curved-globally-hyperbolic-green-operator-construction"

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.diagonalModular_catichaIntertwines
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.kleinGordon_continuity_program",
  formalizes @ "claim:canonical-matrix-entry-readout-constructs-a-caticha-modular-intertwiner-with-generator-equal-to-the-diagonal-spectral-gap",
  caveat @ "claim:finite-matrix-entry-readout-not-a-continuum-field-evaluation-functional"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.curvedMaxwell_implies_waveWithConnection_of_lorenzGauge
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.covariantDivTwoContravariant_eq_partial_add_connectionCorrection",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.partialDiv_faraday_eq_wave_of_lorenzGauge",
  formalizes @ "claim:curved-coordinate-maxwell-implies-the-potential-wave-equation-with-both-christoffel-index-corrections-retained",
  requires @ "assumption:lorenz-gauge-closure-and-displayed-mixed-partial-symmetry",
  caveat @ "claim:explicit-coordinate-correction-not-yet-repackaged-as-the-metric-dalembertian-plus-ricci-coupling"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.maxwellWaveWithConnection_and_complexEinstein_split
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.curvedMaxwell_implies_waveWithConnection_of_lorenzGauge",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation_iff_einstein",
  formalizes @ "claim:general-connection-maxwell-potential-evolution-and-the-real-imaginary-complex-einstein-split-hold-together",
  caveat @ "claim:conditional-field-equation-bridge-not-a-derivation-of-the-matter-current-or-einstein-source"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.covariantSecondDerivVectorAt_commutator_eq_riemannAction
    where
  supported_by @ "lean:KroneckerDelta.sum_mul",
  formalizes @ "claim:torsion-free-vector-covariant-derivative-commutator-equals-the-existing-connection-built-riemann-curvature-action",
  requires @ "assumption:commuting-second-partials-and-torsion-free-connection",
  caveat @ "claim:pointwise-finite-coordinate-jet-identity-not-a-global-regularity-or-distributional-curvature-result"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.metricCompatibleFaradayDivergenceAt_eq_wave_sub_gradDiv_sub_ricci
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.covariantSecondDerivVectorAt_commutator_contraction_eq_ricciAction",
  formalizes @ "claim:metric-compatible-faraday-divergence-is-the-covariant-vector-wave-minus-the-raised-lorenz-gradient-minus-the-ricci-endomorphism-action",
  requires @ "assumption:metric-compatibility-is-used-to-remove-derivatives-of-the-inverse-metric",
  caveat @ "claim:algebraic-pointwise-identity-does-not-supply-calderon-zygmund-bounds-or-schwartz-kernel-extension"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_of_lorenzGauge
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.christoffelFromMetric_isMetricCompatible",
  formalizes @ "claim:metric-built-levi-civita-maxwell-in-lorenz-gauge-implies-the-ricci-coupled-curved-vector-wave-equation",
  caveat @ "claim:conditional-pointwise-field-equation-not-a-construction-of-global-maxwell-solutions"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_onChart
    where
  formalizes @ "claim:the-metric-built-levi-civita-ricci-coupled-maxwell-wave-equation-holds-at-every-indexed-coordinate-chart-point",
  supported_by @ "paper:faraday-cauchy-problem-globally-hyperbolic-manifolds-2306.06896",
  caveat @ "claim:chart-indexed-pointwise-jet-lift-does-not-prove-smooth-jet-realization-boundary-well-posedness-or-green-operator-existence"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.metricFieldMaxwell_implies_ricciCoupledWave_onChart
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_onChart",
  formalizes @ "claim:metric-first-jets-christoffel-fields-connection-first-jets-and-vector-first-and-second-jets-are-constructed-from-chart-fields-before-the-levi-civita-maxwell-ricci-wave-identity-is-applied",
  requires @ "assumption:componentwise-mixed-second-coordinate-derivatives-commute",
  caveat @ "claim:field-realized-coordinate-calculus-not-yet-a-coordinate-free-manifold-bundle-or-global-green-operator-construction"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_implies_ricciCoupledWave_onChart
    where
  formalizes @ "claim:c2-vector-components-discharge-the-mixed-partial-premise-for-the-native-frechet-coordinate-derivative-and-yield-the-field-realized-levi-civita-maxwell-ricci-wave-identity",
  supported_by @ "mathlib:contdiffat-isSymmSndFDerivAt",
  caveat @ "claim:smooth-finite-chart-coordinate-calculus-not-yet-a-coordinate-free-manifold-bundle-global-cauchy-theory-or-green-operator-construction"

zil_file_contract physlib.entropicSpine.catichaCurvedElectrodynamics where
  promises "formalization:constructed-caticha-modular-readout-gauge-covariant-functional-evolution-and-levi-civita-ricci-coupled-maxwell-einstein-bridge"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.gaugeCovariantSmearedSchrodinger_equation_covariant",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantDerivative_gauge_covariant",
    "lean:Electromagnetism.DistElectromagneticPotential.satisfiesDistributionalMaxwell_testFunction",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.diagonalModular_catichaIntertwines",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.curvedMaxwell_implies_waveWithConnection_of_lorenzGauge",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.maxwellWaveWithConnection_and_complexEinstein_split",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.covariantSecondDerivVectorAt_commutator_eq_riemannAction",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.metricCompatibleFaradayDivergenceAt_eq_wave_sub_gradDiv_sub_ricci",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_of_lorenzGauge",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_onChart",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.metricFieldMaxwell_implies_ricciCoupledWave_onChart",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_implies_ricciCoupledWave_onChart"
  ]
  forbids_substitutes [
    "presenting a finite matrix entry as a continuum field functional",
    "dropping the explicit Christoffel correction in a general coordinate chart",
    "claiming the pointwise Ricci identity supplies global hyperbolic regularity or propagator estimates",
    "claiming Calderon-Zygmund or Schwartz-kernel bounds without the separate analytic hypotheses",
    "claiming the flat tempered-distribution equation is already a curved-spacetime distributional equation",
    "claiming gauge covariance constructs the interacting curved-spacetime QFT"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.gaugeCovariantSmearedSchrodinger_equation_covariant,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantDerivative_gauge_covariant,
    Electromagnetism.DistElectromagneticPotential.satisfiesDistributionalMaxwell_testFunction,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.diagonalModular_catichaIntertwines,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.curvedMaxwell_implies_waveWithConnection_of_lorenzGauge,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.maxwellWaveWithConnection_and_complexEinstein_split,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.covariantSecondDerivVectorAt_commutator_eq_riemannAction,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.metricCompatibleFaradayDivergenceAt_eq_wave_sub_gradDiv_sub_ricci,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_of_lorenzGauge,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_onChart,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.metricFieldMaxwell_implies_ricciCoupledWave_onChart,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_implies_ricciCoupledWave_onChart
  ]

/-! ## BA. Coordinate-free pseudo-Riemannian curvature carrier -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.manifoldCovariantCurvatureAction_swap
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.manifoldCovariantCurvatureAction
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.pseudoRiemannianCurvatureEvaluation_swap
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.pseudoRiemannianCurvatureEvaluation
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.metricLeviCivitaCovariantDerivative_torsion_eq_zero
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.metricLeviCivitaCovariantDerivative
  ]

zil_theorem_intent PseudoRiemannianMetric.koszul where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.IsLeviCivitaConnection]

zil_theorem_intent PseudoRiemannianMetric.leviCivita_unique_on_smooth where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.IsLeviCivitaConnection]

zil_theorem_intent PseudoRiemannianMetric.leviCivitaAtlas_overlap where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.IsLeviCivitaAtlas]

zil_theorem_intent PseudoRiemannianMetric.leviCivitaOfOpenCover_isLeviCivita where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.IsCompatibleConnectionOn,
    PseudoRiemannianMetric.IsTorsionFreeConnectionOn
  ]

zil_theorem_intent PseudoRiemannianMetric.LocalLeviCivitaAtlasData.overlap where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.LocalLeviCivitaAtlasData]

zil_theorem_intent
    PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivative_isLeviCivita where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.IsLeviCivitaConnection]

zil_theorem_intent
    PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivativeOfOpenCover_isLeviCivita where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivativeOfOpenCover,
    PseudoRiemannianMetric.IsLeviCivitaConnection
  ]

zil_theorem_intent
    PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivative_independent where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivative]

zil_theorem_intent PseudoRiemannianMetric.leviCivitaAtlas_curvature_overlap where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.IsLeviCivitaAtlas,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.manifoldCovariantCurvatureAction
  ]

zil_theorem_intent PseudoRiemannianMetric.leviCivitaAtlas_frameRicci_overlap where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.frameRicciContractionAt]

zil_theorem_intent PseudoRiemannianMetric.leviCivitaAtlas_frameBochnerWave_overlap where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.frameBochnerWaveAt]

zil_theorem_intent PseudoRiemannianMetric.frameRicciContractionAt_independent where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.frameRicciContractionAt,
    PseudoRiemannianMetric.IsPseudoOrthonormalBasisAt
  ]

zil_theorem_intent PseudoRiemannianMetric.frameBochnerWaveAt_independent where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.frameBochnerWaveAt,
    PseudoRiemannianMetric.IsPseudoOrthonormalBasisAt
  ]

zil_theorem_intent PseudoRiemannianMetric.frameBochnerWaveAt_eq_metricTraceAt where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.frameBochnerWaveAt,
    PseudoRiemannianMetric.metricTraceAt
  ]

zil_theorem_intent
    PseudoRiemannianMetric.frameRaisedRicciActionAt_eq_raisedCurvatureRicciAt where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.frameRaisedRicciActionAt,
    PseudoRiemannianMetric.raisedCurvatureRicciAt
  ]

zil_theorem_intent PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellAt_iff_tensor where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellAt,
    PseudoRiemannianMetric.TensorRicciCoupledMaxwellAt
  ]

zil_theorem_intent PseudoRiemannianMetric.tensorRicciCoupledMaxwellOn_iff_onChart_of_cover where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.TensorRicciCoupledMaxwellOn,
    PseudoRiemannianMetric.TensorRicciCoupledMaxwellOnChart
  ]

zil_theorem_intent PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellAt_atlas_iff where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellAt]

zil_theorem_intent PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_atlas_iff where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn]

zil_theorem_intent PseudoRiemannianMetric.localLeviCivitaAtlas_intrinsicMaxwellOn_iff where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn,
    PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivative
  ]

zil_theorem_intent PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_iff_operator_eq where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOperator]

zil_theorem_intent PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData,
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn
  ]

zil_theorem_intent
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves_tensor where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData,
    PseudoRiemannianMetric.TensorRicciCoupledMaxwellOn
  ]

zil_theorem_intent PseudoRiemannianMetric.IntrinsicMaxwellGreenData.advanced_solves where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData,
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn
  ]

zil_theorem_intent PseudoRiemannianMetric.IntrinsicMaxwellGreenData.eq_retarded_of_solves where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData,
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn
  ]

zil_theorem_intent
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.waveOperator_causalPropagator_eq_zero where
  at_level bridge_theorem
  must_mention [PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator]

zil_theorem_intent
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves_for_leviCivitaAtlas where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData,
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn,
    PseudoRiemannianMetric.IsLeviCivitaAtlas
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_basis_eq_riemannFromConnection
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.manifoldCovariantCurvatureAction,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.riemannFromConnection
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_ricci_eq_ricciFromConnection
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.ricciFromConnection
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureEndomorphismAt_basis_apply
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureEndomorphismAt,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.manifoldCovariantCurvatureAction
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureRicciTrace_eq_ricciFromConnection
    where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.curvatureRicciTraceAt,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureEndomorphismAt,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.ricciFromConnection
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateBochnerEndomorphismAt_trace_eq_wave
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateBochnerEndomorphismAt,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.covariantVectorWaveAt
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.ricciCoupledVectorWaveEquationAt_iff_traceContractions
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.RicciCoupledVectorWaveEquationAt,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateBochnerEndomorphismAt,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateRaisedRicciTraceActionAt
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.ricciCoupledVectorWaveEquationOnChart_iff_traceContractions
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.RicciCoupledVectorWaveEquationOnChart,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateBochnerEndomorphismAt,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateRaisedRicciTraceActionAt
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_firstBianchi
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation.FirstBianchi
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_bundledGeometry_onChart
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.metricLeviCivitaCovariantDerivative,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.RicciCoupledVectorWaveEquationOnChart
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.manifoldCovariantCurvatureAction_swap
    where
  formalizes @ "claim:the-bundled-manifold-covariant-derivative-and-manifold-lie-bracket-define-a-coordinate-free-curvature-action-antisymmetric-in-its-two-direction-fields",
  supported_by @ "mathlib:covariant-derivative-and-manifold-lie-bracket",
  caveat @ "claim:raw-curvature-action-not-yet-a-tensorial-curvature-bundle-or-a-levi-civita-existence-and-uniqueness-theorem"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.pseudoRiemannianCurvatureEvaluation_swap
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.manifoldCovariantCurvatureAction_swap",
  formalizes @ "claim:a-pseudo-riemannian-metric-lowers-the-coordinate-free-tangent-bundle-curvature-action-to-g-of-rxy-z-w-and-preserves-antisymmetry-in-x-and-y",
  caveat @ "claim:metric-lowered-curvature-evaluation-does-not-yet-prove-the-pair-exchange-bianchi-ricci-contraction-or-einstein-equations"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.metricLeviCivitaCovariantDerivative_torsion_eq_zero
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.christoffelFromMetric_isTorsionFree",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.coordinateCovariantDerivative_torsion_eq_zero",
  formalizes @ "claim:metric-christoffel-symbols-on-a-finite-real-chart-promote-to-a-mathlib-bundled-covariant-derivative-with-zero-bundled-torsion",
  requires @ "assumption:symmetric-metric-first-jet-matrices",
  caveat @ "claim:global-finite-chart-construction-not-an-atlas-gluing-or-levi-civita-uniqueness-theorem-on-an-arbitrary-manifold"

zil attach PseudoRiemannianMetric.koszul where
  formalizes @ "claim:every-global-torsion-free-pseudo-riemannian-metric-compatible-connection-obeys-the-coordinate-free-koszul-identity",
  supported_by @ "mathlib:bundled-covariant-derivative-torsion-and-manifold-lie-bracket",
  caveat @ "claim:characterization-and-uniqueness-do-not-construct-a-global-connection-or-a-partition-of-unity-gluing"

zil attach PseudoRiemannianMetric.leviCivita_unique_on_smooth where
  formalizes @ "claim:two-global-torsion-free-metric-compatible-connections-for-the-same-nondegenerate-pseudo-riemannian-metric-agree-on-smooth-vector-fields",
  caveat @ "claim:the-mathlib-connection-interface-only-constrains-smooth-sections-so-no-equality-on-arbitrary-nonsmooth-sections-is-claimed"

zil attach PseudoRiemannianMetric.leviCivitaAtlas_overlap where
  supported_by @ "lean:PseudoRiemannianMetric.leviCivita_unique_on_smooth",
  formalizes @ "claim:atlas-indexed-global-levi-civita-representatives-for-one-pseudo-riemannian-metric-agree-on-chart-overlaps",
  requires @ "assumption:each-chart-representative-is-already-a-global-torsion-free-metric-compatible-bundled-connection",
  caveat @ "claim:overlap-uniqueness-does-not-yet-provide-the-chart-transition-construction-or-global-hyperbolic-maxwell-green-evolution"

zil attach PseudoRiemannianMetric.leviCivitaOfOpenCover_isLeviCivita where
  formalizes @ "claim:one-overlap-consistent-raw-connection-operator-verified-locally-torsion-free-and-metric-compatible-on-an-open-cover-assembles-into-a-global-bundled-levi-civita-connection",
  supported_by @ "mathlib:covariant-derivative-open-cover-constructor",
  caveat @ "claim:the-theorem-requires-a-common-raw-operator-and-does-not-derive-christoffel-transition-laws-or-global-maxwell-cauchy-evolution"

zil attach PseudoRiemannianMetric.LocalLeviCivitaAtlasData.overlap where
  formalizes @ "claim:independently-constructed-chart-local-levi-civita-operators-for-one-pseudo-riemannian-metric-agree-on-every-overlap-when-applied-to-differentiable-vector-fields",
  supported_by @ "lean:PseudoRiemannianMetric.localLeviCivita_uniqueAt",
  caveat @ "claim:the-local-atlas-carrier-requires-each-transported-chart-operator-to-satisfy-the-local-covariant-derivative-torsion-free-and-metric-compatibility-laws"

zil attach
    PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivative_isLeviCivita where
  formalizes @ "claim:a-cover-by-independently-constructed-chart-local-levi-civita-operators-determines-a-global-bundled-torsion-free-metric-compatible-covariant-derivative",
  supported_by @ "mathlib:bundled-covariant-derivative-interface",
  caveat @ "claim:the-choice-based-global-operator-is-canonical-on-differentiable-fields-by-overlap-uniqueness-but-does-not-prove-green-hyperbolicity-or-maxwell-cauchy-well-posedness"

zil attach
    PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivativeOfOpenCover_isLeviCivita where
  formalizes @ "claim:the-overlap-compatible-pointwise-selection-from-genuinely-local-levi-civita-chart-data-feeds-through-mathlibs-open-cover-constructor-and-produces-the-same-global-torsion-free-metric-compatible-connection",
  supported_by @ "mathlib:covariant-derivative-open-cover-constructor",
  caveat @ "claim:the-constructor-globalizes-proved-local-levi-civita-data-and-does-not-derive-the-local-chart-connections-or-their-regularity"

zil attach
    PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivative_independent where
  formalizes @ "claim:any-two-local-levi-civita-atlases-for-the-same-pseudo-riemannian-metric-globalize-to-the-same-covariant-derivative-on-differentiable-vector-fields",
  supported_by @ "lean:PseudoRiemannianMetric.leviCivita_unique_on_smooth",
  caveat @ "claim:canonical-independence-on-smooth-fields-does-not-construct-the-local-chart-operators-or-extend-the-connection-interface-to-arbitrary-nonsmooth-fields"

zil attach PseudoRiemannianMetric.leviCivitaAtlas_curvature_overlap where
  supported_by @ "lean:PseudoRiemannianMetric.leviCivitaAtlas_overlap",
  formalizes @ "claim:the-coordinate-free-curvature-action-of-two-levi-civita-atlas-representatives-agrees-on-smooth-vector-fields-at-every-overlap-point",
  requires @ "assumption:differentiability-of-the-vector-fields-and-the-first-covariant-derivative-sections-used-by-the-outer-curvature-derivatives",
  caveat @ "claim:atlas-curvature-independence-not-a-construction-of-chart-transition-functions-or-a-second-differential-bianchi-theorem"

zil attach PseudoRiemannianMetric.leviCivitaAtlas_frameRicci_overlap where
  supported_by @ "lean:PseudoRiemannianMetric.leviCivitaAtlas_curvature_overlap",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:contracting-the-intrinsic-curvature-in-a-signed-pseudo-orthonormal-frame-gives-an-atlas-independent-ricci-expression",
  requires @ "assumption:a-common-signed-frame-and-the-explicit-smoothness-needed-by-the-curvature-commutator",
  caveat @ "claim:frame-contraction-does-not-establish-frame-existence-completeness-or-the-contracted-second-bianchi-identity"

zil attach PseudoRiemannianMetric.leviCivitaAtlas_frameBochnerWave_overlap where
  supported_by @ "lean:PseudoRiemannianMetric.leviCivitaAtlas_overlap",
  formalizes @ "claim:the-intrinsic-frame-traced-bochner-wave-operator-with-its-connection-frame-correction-is-independent-of-the-levi-civita-atlas-representative",
  caveat @ "claim:operator-coordinate-independence-not-cauchy-well-posedness-essential-self-adjointness-or-green-hyperbolicity"

zil attach PseudoRiemannianMetric.frameRicciContractionAt_independent where
  formalizes @ "claim:any-two-pseudo-orthonormal-frame-contractions-representing-one-curvature-endomorphism-equal-its-basis-independent-linear-trace-and-therefore-agree",
  supported_by @ "mathlib:basis-independent-linear-map-trace",
  caveat @ "claim:the-representation-premises-isolate-the-separate-tensoriality-proof-connecting-the-curvature-commutator-to-the-pointwise-endomorphism"

zil attach PseudoRiemannianMetric.frameBochnerWaveAt_independent where
  formalizes @ "claim:any-two-pseudo-orthonormal-frame-bochner-sums-representing-one-vector-valued-covariant-hessian-have-the-same-basis-independent-metric-trace",
  supported_by @ "lean:PseudoRiemannianMetric.IsMetricTraceAt.unique",
  caveat @ "claim:frame-independence-of-the-pointwise-rough-wave-expression-not-a-global-evolution-or-green-operator-existence-theorem"

zil attach PseudoRiemannianMetric.frameBochnerWaveAt_eq_metricTraceAt where
  formalizes @ "claim:the-signed-pseudo-orthonormal-frame-bochner-sum-computes-the-basis-free-metric-trace-constructed-by-finite-dimensional-biduality-and-linear-map-trace",
  supported_by @ "mathlib:finite-dimensional-reflexivity-and-basis-independent-linear-map-trace",
  caveat @ "claim:the-representation-premise-identifies-the-bilinear-map-with-the-fields-covariant-hessian-on-the-selected-basis"

zil attach
    PseudoRiemannianMetric.frameRaisedRicciActionAt_eq_raisedCurvatureRicciAt where
  formalizes @ "claim:the-signed-frame-raised-ricci-sum-is-the-metric-sharp-of-the-basis-independent-linear-trace-of-the-curvature-endomorphism-family",
  supported_by @ "lean:PseudoRiemannianMetric.frameRicciContractionAt_eq_curvatureRicciTraceAt",
  caveat @ "claim:the-curvature-family-must-represent-the-manifold-covariant-curvature-action-on-the-basis"

zil attach PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellAt_iff_tensor where
  formalizes @ "claim:the-existing-signed-frame-ricci-coupled-maxwell-equation-is-exactly-the-frame-free-tensor-equation-metric-trace-of-hessian-minus-sharp-of-curvature-trace-equals-current",
  supported_by @ "lean:PseudoRiemannianMetric.frameBochnerWaveAt_eq_metricTraceAt",
  caveat @ "claim:pointwise-frame-free-equivalence-is-a-geometric-pde-identity-not-a-cauchy-existence-or-green-hyperbolicity-result"

zil attach PseudoRiemannianMetric.tensorRicciCoupledMaxwellOn_iff_onChart_of_cover where
  formalizes @ "claim:the-frame-free-intrinsic-maxwell-equation-holds-globally-if-and-only-if-it-holds-on-every-member-of-an-actual-manifold-cover",
  requires @ "assumption:the-chart-sources-cover-the-manifold",
  caveat @ "claim:local-to-global-logical-equivalence-does-not-supply-chartwise-solutions-transition-regularity-or-causal-evolution"

zil attach PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellAt_atlas_iff where
  supported_by @ "lean:PseudoRiemannianMetric.leviCivitaAtlas_frameBochnerWave_overlap",
  formalizes @ "claim:the-global-intrinsic-ricci-coupled-lorenz-gauge-maxwell-wave-equation-is-equivalent-for-any-two-representatives-of-one-levi-civita-atlas",
  requires @ "assumption:a-common-signed-frame-smooth-potential-and-the-explicit-first-derivative-and-lie-bracket-regularity",
  caveat @ "claim:global-coordinate-independent-pde-identity-not-a-global-maxwell-cauchy-evolution-semigroup-or-green-operator-construction"

zil attach PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_atlas_iff where
  supported_by @ "lean:PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellAt_atlas_iff",
  formalizes @ "claim:the-pointwise-intrinsic-ricci-coupled-maxwell-wave-equation-on-the-whole-manifold-is-independent-of-the-selected-global-levi-civita-atlas-representative",
  requires @ "assumption:global-smoothness-of-the-potential-frame-first-covariant-frame-derivatives-and-frame-lie-brackets",
  caveat @ "claim:global-equation-invariance-not-existence-uniqueness-causal-propagation-or-green-hyperbolicity"

zil attach PseudoRiemannianMetric.localLeviCivitaAtlas_intrinsicMaxwellOn_iff where
  formalizes @ "claim:independently-constructed-local-levi-civita-atlases-induce-equivalent-global-intrinsic-curved-maxwell-equations",
  supported_by @ "lean:PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivative_isLeviCivita",
  caveat @ "claim:the-result-globalizes-and-compares-the-equation-but-does-not-supply-a-maxwell-solution-or-cauchy-evolution-operator"

zil attach PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_iff_operator_eq where
  supported_by @ "lean:CPTPMap.funext",
  formalizes @ "claim:the-global-intrinsic-curved-maxwell-equation-is-exactly-equality-between-the-geometric-ricci-coupled-wave-expression-and-the-source-field",
  caveat @ "claim:operator-expression-is-not-by-itself-a-linearity-continuity-or-domain-closure-proof-on-raw-manifold-sections"

zil attach PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves where
  formalizes @ "claim:a-retarded-green-right-inverse-from-an-admissible-source-carrier-to-a-propagated-field-carrier-produces-a-global-solution-of-the-intrinsic-curved-maxwell-equation",
  requires @ "assumption:an-analytic-field-carrier-linear-wave-realization-and-retarded-green-inversion",
  caveat @ "claim:the-theorem-consumes-rather-than-derives-global-hyperbolicity-boundary-conditions-and-retarded-support"

zil attach PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves_tensor where
  supported_by @ "lean:PseudoRiemannianMetric.frameBochnerWaveAt_eq_metricTraceAt",
  supported_by @ "lean:PseudoRiemannianMetric.frameRaisedRicciActionAt_eq_raisedCurvatureRicciAt",
  formalizes @ "claim:a-retarded-green-right-inverse-produces-a-global-solution-of-the-frame-free-tensor-maxwell-equation-once-the-hessian-and-curvature-families-realize-the-propagated-field",
  requires @ "assumption:explicit-green-operator-data-retarded-sector-and-tensor-realization-of-the-propagated-field",
  caveat @ "claim:pseudo-riemannian-geometry-alone-does-not-imply-global-hyperbolicity-green-inversion-or-retarded-support"

zil attach PseudoRiemannianMetric.IntrinsicMaxwellGreenData.advanced_solves where
  supported_by @ "lean:PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_iff_operator_eq",
  formalizes @ "claim:an-advanced-green-right-inverse-between-the-separated-source-and-propagated-field-carriers-produces-a-global-intrinsic-curved-maxwell-solution",
  requires @ "assumption:an-analytic-field-carrier-linear-wave-realization-and-advanced-green-inversion",
  caveat @ "claim:advanced-support-and-existence-remain-properties-of-the-supplied-analytic-green-data"

zil attach PseudoRiemannianMetric.IntrinsicMaxwellGreenData.eq_retarded_of_solves where
  supported_by @ "lean:PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_iff_operator_eq",
  formalizes @ "claim:injectivity-of-the-wave-operator-on-an-explicit-retarded-sector-makes-the-retarded-green-field-the-unique-retarded-solution-for-its-source",
  requires @ "assumption:the-solution-lies-in-the-selected-retarded-support-or-boundary-condition-subspace",
  caveat @ "claim:uniqueness-is-relative-to-the-selected-domain-and-boundary-condition-carrier-not-all-distributional-solutions"

zil attach
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.waveOperator_causalPropagator_eq_zero where
  formalizes @ "claim:the-difference-of-retarded-and-advanced-intrinsic-maxwell-green-operators-is-a-homogeneous-causal-propagator",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalPauliJordan",
  caveat @ "claim:operator-level-homogeneous-identity-does-not-prove-microlocal-wavefront-or-causal-support-estimates"

zil attach
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves_for_leviCivitaAtlas where
  supported_by @ "lean:PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_atlas_iff",
  supported_by @ "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves",
  formalizes @ "claim:a-retarded-green-solution-built-for-one-levi-civita-atlas-representative-solves-the-global-intrinsic-maxwell-equation-for-every-representative",
  requires @ "assumption:the-explicit-global-differentiability-needed-by-the-curvature-comparison",
  caveat @ "claim:atlas-independence-transports-an-existing-retarded-solution-but-does-not-construct-the-green-data"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_basis_eq_riemannFromConnection
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantDerivative_connectionColumn_apply",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.coordinateCovariantDerivative_constantBasis_apply",
  formalizes @ "claim:the-coordinate-free-curvature-commutator-of-the-bundled-chart-connection-evaluated-on-coordinate-basis-fields-is-exactly-riemann-from-connection",
  requires @ "assumption:componentwise-differentiability-of-the-connection-field-at-the-chart-point",
  caveat @ "claim:basis-chart-equivalence-not-yet-an-atlas-transition-naturality-theorem"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_ricci_eq_ricciFromConnection
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_basis_eq_riemannFromConnection",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:contracting-the-coordinate-free-basis-curvature-over-the-upper-and-first-direction-indices-equals-the-existing-ricci-from-connection",
  caveat @ "claim:coordinate-ricci-contraction-does-not-by-itself-prove-pair-exchange-symmetry-or-the-contracted-differential-bianchi-identity"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureEndomorphismAt_basis_apply
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_basis_eq_riemannFromConnection",
  supported_by @ "lean:CPTPMap.funext",
  formalizes @ "claim:the-connection-built-riemann-matrix-bundles-as-a-linear-curvature-endomorphism-whose-coordinate-basis-action-is-the-manifold-covariant-curvature-commutator",
  requires @ "assumption:componentwise-differentiability-of-the-coordinate-connection-field",
  caveat @ "claim:the-endomorphism-is-a-chart-specialization-and-not-a-constructor-from-an-arbitrary-coordinate-metric-matrix-to-a-global-pseudo-riemannian-metric"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureRicciTrace_eq_ricciFromConnection
    where
  formalizes @ "claim:the-basis-independent-linear-trace-of-the-coordinate-curvature-endomorphism-is-exactly-the-existing-coordinate-ricci-from-connection",
  supported_by @ "mathlib:basis-independent-linear-map-trace",
  caveat @ "claim:exact-ricci-contraction-bridge-not-an-atlas-level-construction-of-a-pseudo-riemannian-metric-from-coordinate-matrix-data"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateBochnerEndomorphismAt_trace_eq_wave where
  formalizes @ "claim:raising-one-covariant-hessian-index-with-a-symmetric-inverse-metric-and-taking-linear-map-trace-is-exactly-the-existing-coordinate-bochner-vector-wave-component",
  requires @ "assumption:symmetry-of-the-inverse-metric-matrix",
  caveat @ "claim:algebraic-chart-contraction-does-not-prove-that-arbitrary-supplied-second-jet-data-comes-from-a-smooth-global-vector-field"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.ricciCoupledVectorWaveEquationAt_iff_traceContractions where
  formalizes @ "claim:the-complete-coordinate-ricci-coupled-vector-wave-equation-is-exactly-bochner-linear-trace-minus-raised-curvature-linear-trace-equals-current",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureRicciTrace_eq_ricciFromConnection",
  caveat @ "claim:exact-chart-equivalence-does-not-assert-green-operator-existence-on-an-arbitrary-pseudo-riemannian-manifold"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.ricciCoupledVectorWaveEquationOnChart_iff_traceContractions where
  formalizes @ "claim:the-coordinate-ricci-coupled-vector-wave-equation-on-the-entire-chart-domain-is-equivalent-pointwise-to-the-frame-free-bochner-trace-minus-raised-curvature-trace-equation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.ricciCoupledVectorWaveEquationAt_iff_traceContractions",
  caveat @ "claim:chart-domain-equivalence-does-not-by-itself-construct-a-global-green-operator-or-prove-global-hyperbolicity"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_firstBianchi
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_basis_eq_riemannFromConnection",
  formalizes @ "claim:the-coordinate-free-basis-curvature-of-the-torsion-free-bundled-chart-connection-obeys-the-first-algebraic-bianchi-identity",
  requires @ "assumption:pointwise-torsion-freeness-and-connection-component-differentiability",
  caveat @ "claim:first-algebraic-bianchi-not-the-uncontracted-or-contracted-second-differential-bianchi-identity"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_bundledGeometry_onChart
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_implies_ricciCoupledWave_onChart",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_firstBianchi",
  formalizes @ "claim:one-metric-field-construction-supplies-zero-bundled-torsion-coordinate-free-to-coordinate-riemann-equivalence-ricci-contraction-first-bianchi-metric-compatibility-and-the-general-ricci-coupled-curved-maxwell-wave-equation",
  requires @ "assumption:inverse-metric-symmetry-connection-component-regularity-c2-vector-field-geometric-maxwell-equation-and-covariant-lorenz-gauge",
  caveat @ "claim:finite-global-chart-theorem-not-a-global-hyperbolic-existence-green-operator-or-calderon-zygmund-estimate"

zil_file_contract physlib.entropicSpine.coordinateFreeCurvature where
  promises "formalization:intrinsic-koszul-local-atlas-levi-civita-uniqueness-and-globalization-atlas-and-frame-independent-curvature-ricci-bochner-wave-and-global-coordinate-independent-curved-maxwell-chain"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.manifoldCovariantCurvatureAction_swap",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.pseudoRiemannianCurvatureEvaluation_swap",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.metricLeviCivitaCovariantDerivative_torsion_eq_zero",
    "lean:PseudoRiemannianMetric.koszul",
    "lean:PseudoRiemannianMetric.leviCivita_unique_on_smooth",
    "lean:PseudoRiemannianMetric.leviCivitaAtlas_overlap",
    "lean:PseudoRiemannianMetric.leviCivitaOfOpenCover_isLeviCivita",
    "lean:PseudoRiemannianMetric.LocalLeviCivitaAtlasData.overlap",
    "lean:PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivative_isLeviCivita",
    "lean:PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivativeOfOpenCover_isLeviCivita",
    "lean:PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivative_independent",
    "lean:PseudoRiemannianMetric.leviCivitaAtlas_curvature_overlap",
    "lean:PseudoRiemannianMetric.leviCivitaAtlas_frameRicci_overlap",
    "lean:PseudoRiemannianMetric.leviCivitaAtlas_frameBochnerWave_overlap",
    "lean:PseudoRiemannianMetric.frameRicciContractionAt_independent",
    "lean:PseudoRiemannianMetric.frameBochnerWaveAt_independent",
    "lean:PseudoRiemannianMetric.frameBochnerWaveAt_eq_metricTraceAt",
    "lean:PseudoRiemannianMetric.frameRaisedRicciActionAt_eq_raisedCurvatureRicciAt",
    "lean:PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellAt_iff_tensor",
    "lean:PseudoRiemannianMetric.tensorRicciCoupledMaxwellOn_iff_onChart_of_cover",
    "lean:PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellAt_atlas_iff",
    "lean:PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_atlas_iff",
    "lean:PseudoRiemannianMetric.localLeviCivitaAtlas_intrinsicMaxwellOn_iff",
    "lean:PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_iff_operator_eq",
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves",
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves_tensor",
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.advanced_solves",
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.eq_retarded_of_solves",
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.waveOperator_causalPropagator_eq_zero",
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves_for_leviCivitaAtlas",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_basis_eq_riemannFromConnection",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_ricci_eq_ricciFromConnection",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureEndomorphismAt_basis_apply",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureRicciTrace_eq_ricciFromConnection",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateBochnerEndomorphismAt_trace_eq_wave",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.ricciCoupledVectorWaveEquationAt_iff_traceContractions",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.ricciCoupledVectorWaveEquationOnChart_iff_traceContractions",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_firstBianchi",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_bundledGeometry_onChart"
  ]
  forbids_substitutes [
    "claiming the local-atlas globalization derives the chart transport formulas or local Levi-Civita premises rather than consuming their proofs",
    "claiming the first algebraic Bianchi identity proves the second differential Bianchi identity",
    "claiming the coordinate-independent curved Maxwell identity supplies global Cauchy existence a semigroup Green hyperbolicity or Calderon-Zygmund estimates"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.manifoldCovariantCurvatureAction_swap,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.pseudoRiemannianCurvatureEvaluation_swap,
    Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.metricLeviCivitaCovariantDerivative_torsion_eq_zero,
    PseudoRiemannianMetric.koszul,
    PseudoRiemannianMetric.leviCivita_unique_on_smooth,
    PseudoRiemannianMetric.leviCivitaAtlas_overlap,
    PseudoRiemannianMetric.leviCivitaOfOpenCover_isLeviCivita,
    PseudoRiemannianMetric.LocalLeviCivitaAtlasData.overlap,
    PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivative_isLeviCivita,
    PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivativeOfOpenCover_isLeviCivita,
    PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivative_independent,
    PseudoRiemannianMetric.leviCivitaAtlas_curvature_overlap,
    PseudoRiemannianMetric.leviCivitaAtlas_frameRicci_overlap,
    PseudoRiemannianMetric.leviCivitaAtlas_frameBochnerWave_overlap,
    PseudoRiemannianMetric.frameRicciContractionAt_independent,
    PseudoRiemannianMetric.frameBochnerWaveAt_independent,
    PseudoRiemannianMetric.frameBochnerWaveAt_eq_metricTraceAt,
    PseudoRiemannianMetric.frameRaisedRicciActionAt_eq_raisedCurvatureRicciAt,
    PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellAt_iff_tensor,
    PseudoRiemannianMetric.tensorRicciCoupledMaxwellOn_iff_onChart_of_cover,
    PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellAt_atlas_iff,
    PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_atlas_iff,
    PseudoRiemannianMetric.localLeviCivitaAtlas_intrinsicMaxwellOn_iff,
    PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_iff_operator_eq,
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves,
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves_tensor,
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.advanced_solves,
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.eq_retarded_of_solves,
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.waveOperator_causalPropagator_eq_zero,
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves_for_leviCivitaAtlas,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_basis_eq_riemannFromConnection,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_ricci_eq_ricciFromConnection,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureEndomorphismAt_basis_apply,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureRicciTrace_eq_ricciFromConnection,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateBochnerEndomorphismAt_trace_eq_wave,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.ricciCoupledVectorWaveEquationAt_iff_traceContractions,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.ricciCoupledVectorWaveEquationOnChart_iff_traceContractions,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_firstBianchi,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_bundledGeometry_onChart
  ]

/-! ## BB. Curved Sorkin histories, causal Green functions, and Calderón localization -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalGreen_sjState
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState.IsSJState,
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalPauliJordan
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalGreen_complexSchrodinger_functional_bridge_checked
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.HasCausalGreenComplexSchrodingerFunctionalBridge
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.pathIntegralFeynmanKernel_calderon_reconstruction
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.pathIntegralFeynmanKernel,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.dyadicCalderonPartialReconstruction
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.CurvedCausalHistoryPathIntegral.curvedHistoryDecoherenceFunctional_norm_eq_damping_mul
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.CurvedCausalHistoryPathIntegral.curvedHistoryDecoherenceFunctional,
    Physlib.QFT.PathIntegral.MeasurePathIntegralModel.damping
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral.causalSet_gravity_eq_matsubara
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.complexActionPathIntegralWeight,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraBoltzmannWeight
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.CurvedCausalHistoryPathIntegral.curvedHistoryDecoherenceFunctional_norm_eq_damping_mul
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.CurvedCausalHistoryPathIntegral.curvedHistoryDecoherenceFunctional_apply",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.CurvedCausalHistoryPathIntegral.curvedHistoryWeight_norm_eq_damping",
  formalizes @ "claim:the-norm-of-a-curved-sum-over-histories-decoherence-matrix-element-is-the-product-of-the-two-path-integral-damping-factors",
  caveat @ "claim:finite-rank-one-history-carrier-not-the-full-sorkin-quantum-measure-hierarchy-or-a-continuum-history-space"

zil attach
    Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral.causalSet_gravity_eq_matsubara
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral.causalSet_gravity_is_fifth",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MatsubaraSorkinReggeEntropicWeight.matsubara_boltzmann_is_kuiken",
  formalizes @ "claim:the-bdg-causal-set-complex-action-weight-and-matsubara-thermal-weight-have-the-same-entropic-modulus-when-the-imaginary-action-is-beta-times-energy",
  caveat @ "claim:equality-of-damping-weights-not-an-equivalence-of-causal-set-gravity-and-thermal-field-theories"

zil attach
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalGreen_sjState
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalPauliJordan_isPauliJordan",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState.wightman_isSJState",
  formalizes @ "claim:a-symmetric-green-kernel-and-causal-order-construct-an-antisymmetric-pauli-jordan-kernel-and-with-a-positive-symmetric-hadamard-part-an-sj-state",
  caveat @ "claim:abstract-causal-order-and-kernel-data-not-a-construction-of-a-globally-hyperbolic-green-operator"

zil attach
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalGreen_complexSchrodinger_functional_bridge_checked
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.complexSchrodinger_greenOperator_equation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.connectedGreenFunctional_zero",
  formalizes @ "claim:causal-feynman-time-ordering-complex-schrodinger-evolution-spectral-green-kernels-and-path-integral-two-point-functionals-share-the-repository-bridge-api",
  caveat @ "claim:packaged-exact-identities-not-an-interacting-curved-spacetime-qft-existence-theorem"

zil attach
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.pathIntegralFeynmanKernel_calderon_reconstruction
    where
  supported_by @ "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.dyadicCalderonPartialReconstruction_tendsto_apply",
  formalizes @ "claim:each-explicitly-schwartz-realized-spatial-slice-of-the-path-integral-feynman-kernel-is-reconstructed-pointwise-by-the-existing-physical-calderon-convolution-partial-sums",
  requires @ "assumption:the-selected-feynman-kernel-slice-has-a-bundled-schwartz-realization",
  caveat @ "claim:time-ordering-alone-does-not-prove-schwartz-decay-calderon-zygmund-estimates-or-curved-manifold-localization"

zil_file_contract physlib.entropicSpine.curvedSorkinHistories where
  promises "formalization:curved-causal-history-decoherence-sorkin-johnston-causal-green-and-schwartz-calderon-feynman-kernel-bridges"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.CurvedCausalHistoryPathIntegral.curvedHistoryDecoherenceFunctional_norm_eq_damping_mul",
    "lean:Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral.causalSet_gravity_eq_matsubara",
    "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalGreen_sjState",
    "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalGreen_complexSchrodinger_functional_bridge_checked",
    "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.pathIntegralFeynmanKernel_calderon_reconstruction"
  ]
  forbids_substitutes [
    "calling a finite rank-one history functional a constructed continuum quantum measure",
    "identifying equality of damping moduli with equality of the underlying theories",
    "inferring Schwartz regularity or curved Calderon-Zygmund estimates from causal time ordering"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.CurvedCausalHistoryPathIntegral.curvedHistoryDecoherenceFunctional_norm_eq_damping_mul,
    Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral.causalSet_gravity_eq_matsubara,
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalGreen_sjState,
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalGreen_complexSchrodinger_functional_bridge_checked,
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.pathIntegralFeynmanKernel_calderon_reconstruction
  ]

/-! ## BC. Witten functional integrals and Verlinde sectors -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.complexActionFiniteMeasure_verlindeSMatrixWilson_supplies_witten_FK
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral_amplitude_wilson
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral_amplitude_norm_le
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswVerlinde_formula
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswFusionCoeff,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswVerlindeCoefficientByS
  ]

zil_theorem_intent Physlib.Thermodynamics.newton_law_of_gravity_from_verlinde where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.verlindeEntropicForce,
    Physlib.Thermodynamics.verlindeGravityTemperature,
    Physlib.Thermodynamics.verlindeDisplacementEntropy
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.complexActionFiniteMeasure_verlindeSMatrixWilson_supplies_witten_FK
    where
  supported_by @ "lean:WilsonObservableAnalyticObligations.complexActionFiniteMeasure_constantWilson_supplies_witten_FK",
  formalizes @ "claim:finite-measure-complex-action-path-integrals-make-constant-verlinde-s-matrix-wilson-observables-integrable-and-bound-their-wilson-integral-by-the-partition-function",
  caveat @ "claim:finite-reference-measure-and-constant-charge-sector-observable-not-a-construction-of-the-full-chern-simons-continuum-measure"

zil attach
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral_amplitude_wilson
    where
  supported_by @ "lean:WilsonObservableAnalyticObligations.unnormalizedExpectation_eq_wittenWilsonIntegral",
  formalizes @ "claim:the-direct-cutoff-free-functional-integral-amplitude-of-the-selected-wilson-observable-is-definitionally-the-existing-witten-wilson-integral",
  caveat @ "claim:analytic-embedding-of-an-assumed-witten-path-integral-model-not-a-construction-of-that-continuum-measure"

zil attach
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral_amplitude_norm_le
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral_amplitude_wilson",
  supported_by @ "lean:WittenAnalyticPathIntegral.wilsonIntegral_norm_le",
  formalizes @ "claim:the-direct-cutoff-free-wilson-amplitude-inherits-the-existing-feynman-kac-wilson-bound-times-partition-function",
  caveat @ "claim:norm-bound-is-conditional-on-the-witten-analytic-model-and-does-not-establish-nonabelian-renormalization-or-topological-invariance"

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswVerlinde_formula where
  formalizes @ "claim:the-u1k-fusion-coefficient-equals-the-verlinde-s-matrix-sum-by-discrete-fourier-orthogonality",
  supported_by @ "paper:verlinde-1988-and-witten-1989-abelian-u1k-sector",
  caveat @ "claim:abelian-u1k-formula-not-the-general-nonabelian-modular-tensor-category-theorem"

zil attach Physlib.Thermodynamics.newton_law_of_gravity_from_verlinde where
  formalizes @ "claim:the-verlinde-screen-temperature-and-displacement-entropy-in-the-entropic-force-law-reduce-algebraically-to-newton-universal-gravitation",
  supported_by @ "paper:verlinde-2011",
  caveat @ "claim:derivation-is-conditional-on-the-holographic-bit-count-and-entropic-displacement-postulates-equipartition-is-derived-classical-limit"

zil_file_contract physlib.entropicSpine.wittenVerlinde where
  promises "formalization:direct-cutoff-free-witten-wilson-amplitude-and-bound-finite-measure-integrability-abelian-verlinde-fusion-and-entropic-newton-law"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.complexActionFiniteMeasure_verlindeSMatrixWilson_supplies_witten_FK",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral_amplitude_wilson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral_amplitude_norm_le",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswVerlinde_formula",
    "lean:Physlib.Thermodynamics.newton_law_of_gravity_from_verlinde"
  ]
  forbids_substitutes [
    "calling a finite-measure constant Wilson observable the full continuum Chern-Simons path integral",
    "promoting the abelian U1k Verlinde identity to an unproved nonabelian theorem",
    "presenting Verlinde gravity without its thermodynamic and holographic premises"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.complexActionFiniteMeasure_verlindeSMatrixWilson_supplies_witten_FK,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral_amplitude_wilson,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral_amplitude_norm_le,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswVerlinde_formula,
    Physlib.Thermodynamics.newton_law_of_gravity_from_verlinde
  ]

/-! ## BC.1. Four-dimensional resonance thermal/loop/functional synthesis -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceModeWeight_norm_eq_matsubara
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceModeWeight,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraBoltzmannWeight
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceDecoherenceFunctional_norm_eq_matsubara_mul
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceDecoherenceFunctional,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraBoltzmannWeight
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceDecoherenceFunctional_diag_re_eq_matsubara_sq
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceDecoherenceFunctional,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraBoltzmannWeight
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonance_oneLoopWaveFunction_norm_eq_matsubara
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction,
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopPrefactor
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.chiral_resonance_oneLoop_and_no_second_loop
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.OneLoopExactGraphShape.loopNumber
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceBasis_continuumFunctionalSchrodinger
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.continuumSmearedSchrodingerGenerator
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceProjectiveRiccatiFlow_eq_eigenvalueGap
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ProjectiveSchrodingerRiccatiMobius.riccatiFlow
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceMode_constantWilson_supplies_witten_FK
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.WittenAnalyticPathIntegral.wilsonIntegral
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields.poincareQEDDysonCoefficient_two
    where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields.poincareQEDDysonCoefficient
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields.poincareQEDDysonTerm_two_eq_timeOrderedSquare
    where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields.poincareQEDDysonTerm,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields.poincareQEDDysonCoefficient
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields.poincareQEDDysonPartialSum_two
    where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields.poincareQEDDysonTerm
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonancePropagator_hasDerivAt
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonancePropagator,
    Physlib.QuantumMechanics.NonHermitian.Propagator.schrodingerGenerator
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonancePropagator_add
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonancePropagator
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceModeRatio_hasDerivAt_riccati
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceModeEvolution,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ProjectiveSchrodingerRiccatiMobius.riccatiFlow
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.abelianWilsonHolonomy_supplies_witten_FK
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.abelianWilsonHolonomy,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.WittenAnalyticPathIntegral.wilsonIntegral
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.finitePathOrderedWilson_supplies_witten_FK
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.finitePathOrderedWilson,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.WittenAnalyticPathIntegral.wilsonIntegral
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.finitePathOrderedWilson_localGauge_invariant
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.GaugeRelatedPath
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.secondDyson_connectedVacuum_is_two_loop
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.SecondDysonConnectedVacuum,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.secondDysonVacuumLoopNumber
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.regularInteraction_fullVacuum_loopNumber
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.connectedVacuumLoopNumber
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.exists_local_operatorRiccati_solution
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.operatorRiccatiField
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.operatorRiccati_solution_eventuallyEq
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.operatorRiccatiField
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.affineOperatorRiccatiSolution_unique
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.affineOperatorRiccatiSolution,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.operatorRiccatiField
  ]

zil_file_contract physlib.entropicSpine.hermiteResonanceLoopFunctional where
  promises "formalization:explicit-four-dimensional-hermite-resonance-matsubara-decoherence-one-loop-arbitrary-valence-wick-loop-counting-global-linear-evolution-functional-schrodinger-local-nonlinear-and-global-affine-bounded-operator-riccati-and-finite-locally-gauge-covariant-nonabelian-witten-wilson-synthesis"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceModeWeight_norm_eq_matsubara",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceDecoherenceFunctional_norm_eq_matsubara_mul",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceDecoherenceFunctional_diag_re_eq_matsubara_sq",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonance_oneLoopWaveFunction_norm_eq_matsubara",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.chiral_resonance_oneLoop_and_no_second_loop",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceBasis_continuumFunctionalSchrodinger",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceProjectiveRiccatiFlow_eq_eigenvalueGap",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceMode_constantWilson_supplies_witten_FK",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields.poincareQEDDysonCoefficient_two",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields.poincareQEDDysonTerm_two_eq_timeOrderedSquare",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields.poincareQEDDysonPartialSum_two",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonancePropagator_hasDerivAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonancePropagator_add",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceModeRatio_hasDerivAt_riccati",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.abelianWilsonHolonomy_supplies_witten_FK",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.finitePathOrderedWilson_supplies_witten_FK",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.finitePathOrderedWilson_localGauge_invariant",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.secondDyson_connectedVacuum_is_two_loop",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.regularInteraction_fullVacuum_loopNumber",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.exists_local_operatorRiccati_solution",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.operatorRiccati_solution_eventuallyEq",
    "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.affineOperatorRiccatiSolution_unique"
  ]
  forbids_substitutes [
    "calling the beta-energy reparametrization an independently predicted thermal spectrum",
    "promoting one-loop-exact chiral Chern-Simons graph counting to arbitrary interacting QED or gravity",
    "calling every second Dyson-order contribution two-loop without a full connected cubic-vacuum Wick certificate",
    "promoting a finite ordered product of segment transports to a continuum nonabelian path-ordered exponential",
    "promoting local nonlinear or global affine bounded operator-Riccati results to global quadratic no-blowup or unbounded-operator domain control"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceModeWeight_norm_eq_matsubara,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceDecoherenceFunctional_norm_eq_matsubara_mul,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceDecoherenceFunctional_diag_re_eq_matsubara_sq,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonance_oneLoopWaveFunction_norm_eq_matsubara,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.chiral_resonance_oneLoop_and_no_second_loop,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceBasis_continuumFunctionalSchrodinger,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceProjectiveRiccatiFlow_eq_eigenvalueGap,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceMode_constantWilson_supplies_witten_FK,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields.poincareQEDDysonCoefficient_two,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields.poincareQEDDysonTerm_two_eq_timeOrderedSquare,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.PoincareGroupFields.poincareQEDDysonPartialSum_two,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonancePropagator_hasDerivAt,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonancePropagator_add,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.resonanceModeRatio_hasDerivAt_riccati,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.abelianWilsonHolonomy_supplies_witten_FK,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.finitePathOrderedWilson_supplies_witten_FK,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.finitePathOrderedWilson_localGauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.secondDyson_connectedVacuum_is_two_loop,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.regularInteraction_fullVacuum_loopNumber,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.exists_local_operatorRiccati_solution,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.operatorRiccati_solution_eventuallyEq,
    Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis.affineOperatorRiccatiSolution_unique
  ]

/-! ## BD. BCJ double copy and exact two-dimensional string scattering -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.cubicDoubleCopy_eq_cubicAmplitude_colorReplacement
    where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.cubicGraphAmplitude,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.cubicDoubleCopyAmplitudeFinite
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DoubleCopyCharacter.nnPathWeight_norm_doubleCopy
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence.nnPathWeight
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.JacobiBianchiDoubleCopyFamily.jacobi_bianchi_double_copy_family
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.BCJColorKinematicsDuality,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation.FirstBianchi
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.norm_reflectionFactorI
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.reflectionFactorI
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.reflectionTransmission_prob_conservation
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.reflectionFactorII,
    Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.transmissionFactorII
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.cubicDoubleCopy_eq_cubicAmplitude_colorReplacement
    where
  formalizes @ "claim:the-finite-bcj-double-copy-amplitude-is-exactly-the-cubic-gauge-amplitude-after-color-factors-are-replaced-by-a-second-kinematic-numerator-copy",
  supported_by @ "paper:bern-carrasco-johansson-color-kinematics-double-copy",
  caveat @ "claim:finite-algebraic-color-replacement-not-a-construction-of-a-quantum-gravity-s-matrix"

zil attach
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DoubleCopyCharacter.nnPathWeight_norm_doubleCopy
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.bcj_doublecopy_fk_factorization",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence.norm_nnPathWeight",
  formalizes @ "claim:the-nagao-nielsen-complex-action-norm-of-the-combined-double-copy-action-factorizes-into-the-two-entropic-path-weight-norms",
  caveat @ "claim:group-like-exponential-character-identity-not-a-proof-that-an-arbitrary-gravity-theory-is-a-bcj-double-copy"

zil attach
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.JacobiBianchiDoubleCopyFamily.jacobi_bianchi_double_copy_family
    where
  formalizes @ "claim:bcj-color-jacobi-kinematic-jacobi-gravity-first-bianchi-and-frame-lie-jacobi-share-one-three-term-cyclic-sum-carrier",
  supported_by @ "paper:bcj-2008-and-van-den-bergh-jacobi-ricci-bianchi",
  caveat @ "claim:unification-of-cyclic-identities-not-a-dynamical-klt-or-loop-level-double-copy-theorem"

zil attach
    Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.norm_reflectionFactorI
    where
  formalizes @ "claim:the-exact-theory-i-c-equals-one-two-dimensional-string-reflection-factor-is-a-pure-phase",
  supported_by @ "paper:moore-plesser-ramgoolam-exact-two-dimensional-string-s-matrix",
  caveat @ "claim:unitarity-of-one-exact-c-equals-one-reflection-factor-not-general-critical-string-unitarity"

zil attach
    Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.reflectionTransmission_prob_conservation
    where
  supported_by @ "lean:HermitianMat.exp_pos",
  formalizes @ "claim:the-exact-theory-ii-single-particle-reflection-and-transmission-probabilities-sum-to-one",
  caveat @ "claim:single-particle-probability-conservation-does-not-establish-the-paper-s-full-multiparticle-unitarity"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy.electrogravitational_bianchi_double_copy
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectroGravitationalFieldEquation,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday.faraday
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.NoetherConservationDoubleCopy.noether_double_copy_matter_conservation
    where
  at_level bridge_theorem
  must_mention [Finset.sum]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy.newtonG_from_screen_system
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea.fineStructure,
    Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification.schmidtNumber
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy.gravitational_electromagnetic_coupling_relation
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea.gravitationalCoupling,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment.schwingerAnomaly
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy.electrogravitational_bianchi_double_copy
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSecondBianchiDoubleCopy.em_second_bianchi",
  formalizes @ "claim:an-electrogravitational-solution-carries-the-maxwell-cyclic-identity-current-conservation-and-stress-energy-conservation-derived-from-the-contracted-gravity-bianchi-equation",
  caveat @ "claim:conservation-level-double-copy-contract-not-an-amplitude-level-construction-of-einstein-maxwell-theory"

zil attach
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.NoetherConservationDoubleCopy.noether_double_copy_matter_conservation
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation.contracted_bianchi_conservation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.forall_inner_eq_zero_iff",
  formalizes @ "claim:gauge-and-diffeomorphism-noether-arbitrariness-imply-current-and-nonzero-coupling-matter-stress-energy-conservation",
  requires @ "assumption:the-linearized-einstein-divergence-is-kappa-times-the-matter-divergence-with-nonzero-kappa",
  caveat @ "claim:finite-component-noether-conservation-bridge-not-a-derivation-of-the-full-bcj-s-matrix"

zil attach
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy.newtonG_from_screen_system
    where
  formalizes @ "claim:the-screen-double-copy-product-law-and-the-fine-structure-definition-eliminate-charge-and-permittivity-to-isolate-newton-g-in-area-per-bit-form",
  requires @ "assumption:the-screen-bit-count-is-an-independent-nonzero-input-and-the-double-copy-product-law-holds",
  caveat @ "claim:conditional-algebraic-isolation-of-g-not-a-parameter-free-prediction-of-its-observed-dimensionful-value"

zil attach
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy.gravitational_electromagnetic_coupling_relation
    where
  formalizes @ "claim:under-the-shared-schmidt-rapidity-anomaly-and-holographic-saturation-relations-the-dimensionless-gravitational-coupling-is-pi-over-two-times-log-one-plus-alpha-over-two-pi",
  requires @ "assumption:the-muon-anomaly-schmidt-relation-and-the-screen-saturation-gravitational-coupling-relation",
  caveat @ "claim:exact-elimination-inside-the-supplied-closure-not-an-independent-measurement-or-derivation-of-newton-g"

zil_file_contract physlib.entropicSpine.bcjAndExactString where
  promises "formalization:finite-bcj-color-replacement-jacobi-bianchi-character-and-exact-c-equals-one-string-scattering"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.cubicDoubleCopy_eq_cubicAmplitude_colorReplacement",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DoubleCopyCharacter.nnPathWeight_norm_doubleCopy",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.JacobiBianchiDoubleCopyFamily.jacobi_bianchi_double_copy_family",
    "lean:Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.norm_reflectionFactorI",
    "lean:Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.reflectionTransmission_prob_conservation",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy.electrogravitational_bianchi_double_copy",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.NoetherConservationDoubleCopy.noether_double_copy_matter_conservation",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy.newtonG_from_screen_system",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy.gravitational_electromagnetic_coupling_relation"
  ]
  forbids_substitutes [
    "promoting finite BCJ numerator algebra to a constructed interacting quantum-gravity theory",
    "promoting a shared Jacobi carrier to a proof of loop-level color-kinematics duality",
    "promoting the exact c equals one model to a theorem about all string backgrounds",
    "presenting a conditional screen solve as an independent numerical prediction of Newton's constant"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.cubicDoubleCopy_eq_cubicAmplitude_colorReplacement,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DoubleCopyCharacter.nnPathWeight_norm_doubleCopy,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.JacobiBianchiDoubleCopyFamily.jacobi_bianchi_double_copy_family,
    Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.norm_reflectionFactorI,
    Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.reflectionTransmission_prob_conservation,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy.electrogravitational_bianchi_double_copy,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.NoetherConservationDoubleCopy.noether_double_copy_matter_conservation,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy.newtonG_from_screen_system,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy.gravitational_electromagnetic_coupling_relation
  ]

/-! ## BE. Bell, CHSH, no-signalling, and the entropic one-bit readout -/

zil_theorem_intent
    Physlib.QuantumMechanics.Entanglement.chsh_tsirelson_violation_and_no_signaling
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Entanglement.chshExpression,
    Physlib.QuantumMechanics.Entanglement.bobMarginal
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.chsh_violation_gap
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.bellOperator
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.Entanglement.chsh_quantum_eq_predictBellViolation_at_log_two
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Entanglement.predictBellViolation,
    Physlib.QuantumMechanics.Entanglement.chshExpression
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.Entanglement.chsh_quantum_at_tsirelson_angles
    where
  at_level physical_theorem
  must_mention [
    Physlib.QuantumMechanics.Entanglement.chshExpression,
    Physlib.QuantumMechanics.Entanglement.quantumCorrelation
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.Entanglement.chsh_quantum_exceeds_classical_bound
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Entanglement.chshExpression,
    Physlib.QuantumMechanics.Entanglement.quantumCorrelation
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPsiMinus_traceRight_uniform
    where
  at_level physical_theorem
  must_mention [MState.traceRight]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bell_marginals_indistinguishable
    where
  at_level physical_theorem
  must_mention [MState.traceRight]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPhiPlus_not_prod
    where
  at_level physical_theorem
  must_mention [MState.pure]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.no_cloning
    where
  at_level physical_theorem
  must_mention [False]

zil attach Physlib.QuantumMechanics.Entanglement.chsh_tsirelson_violation_and_no_signaling where
  supported_by @ "lean:Physlib.QuantumMechanics.Entanglement.chsh_quantum_at_tsirelson_angles",
  supported_by @ "lean:Physlib.QuantumMechanics.Entanglement.chsh_quantum_exceeds_classical_bound",
  formalizes @ "claim:the-explicit-singlet-correlation-at-tsirelson-angles-equals-two-sqrt-two-exceeds-the-classical-bound-and-retains-setting-independent-bob-marginals",
  requires @ "assumption:the-specified-cosine-correlation-and-explicit-marginal-model",
  caveat @ "claim:finite-explicit-correlation-calculation-not-a-device-independent-experimental-bell-test-analysis"

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.chsh_violation_gap
    where
  formalizes @ "claim:the-commutative-chsh-operator-obeys-the-local-bound-two-while-the-tsirelson-maximum-is-strictly-larger",
  supported_by @ "paper:summers-werner-and-tsirelson-chsh",
  caveat @ "claim:operator-bound-gap-does-not-by-itself-construct-a-vacuum-state-that-attains-the-maximum"

zil attach Physlib.QuantumMechanics.Entanglement.chsh_quantum_eq_predictBellViolation_at_log_two where
  supported_by @ "lean:Physlib.QuantumMechanics.Entanglement.chsh_quantum_at_tsirelson_angles",
  supported_by @ "lean:Physlib.QuantumMechanics.Entanglement.predictBellViolation_at_log_two_eq_two_sqrt_two",
  formalizes @ "claim:the-explicit-tsirelson-angle-chsh-value-equals-the-repository-s-one-bit-mutual-information-predictor-at-log-two",
  caveat @ "claim:equality-of-two-defined-scalar-readouts-not-a-first-principles-derivation-of-bell-nonlocality-from-mutual-information"

zil attach Physlib.QuantumMechanics.Entanglement.chsh_quantum_at_tsirelson_angles where
  supported_by @ "lean:Physlib.QuantumMechanics.Entanglement.cos_pi_div_two_sub_pi_div_four",
  supported_by @ "lean:Physlib.QuantumMechanics.Entanglement.cos_pi_div_two_sub_three_pi_div_four",
  formalizes @ "claim:the-explicit-cosine-correlation-at-the-standard-four-angles-has-chsh-value-two-sqrt-two",
  epistemic_status @ "conditional-model",
  requires @ "assumption:the-quantum-correlation-law-is-the-specified-cosine-function",
  caveat @ "claim:exact-evaluation-of-a-supplied-correlation-law-not-a-derivation-of-the-born-rule-or-an-experimental-loophole-analysis"

zil attach Physlib.QuantumMechanics.Entanglement.chsh_quantum_exceeds_classical_bound where
  formalizes @ "claim:the-explicit-tsirelson-angle-quantum-correlation-strictly-exceeds-the-classical-chsh-bound-two",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.Entanglement.chsh_quantum_at_tsirelson_angles",
  caveat @ "claim:finite-exact-correlation-calculation-not-a-device-independent-experimental-certification"

zil attach
    Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPsiMinus_traceRight_uniform
    where
  supported_by @ "lean:MState.ext_m",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.inv_sqrt2_sq",
  formalizes @ "claim:the-explicit-singlet-density-matrix-has-the-maximally-mixed-one-wing-reduced-state",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:finite-two-qubit-partial-trace-computation-not-a-relativistic-microcausality-theorem"

zil attach
    Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bell_marginals_indistinguishable
    where
  formalizes @ "claim:the-four-explicit-bell-density-matrices-have-identical-one-wing-reduced-states",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPsiMinus_traceRight_uniform",
  caveat @ "claim:local-indistinguishability-of-four-finite-states-not-a-continuum-local-algebra-no-signalling-proof"

zil attach Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPhiPlus_not_prod where
  formalizes @ "claim:the-explicit-bell-state-density-matrix-is-not-a-product-of-pure-one-qubit-density-matrices",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPhiPlus_traceRight_uniform",
  caveat @ "claim:non-productness-of-the-explicit-finite-state-not-a-general-entanglement-classification"

zil attach Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.no_cloning where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.no_cloning_coefficient",
  formalizes @ "claim:no-inner-product-preserving-map-can-clone-every-normalized-qubit-state",
  epistemic_status @ "risky",
  requires @ "assumption:the-cloning-map-preserves-the-bipartite-inner-product",
  caveat @ "claim:standard-finite-pure-state-no-cloning-obstruction-not-a-field-theoretic-measurement-model"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling.causallyLocal_unistochastic_chsh_contract
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling.CHSHCausalLocal,
    Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling.chshWinProbability
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Bell.LeviCivitaNagaoContour.bellLeviCivita_nagaoContour_integral_synthesis
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation,
    Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour.deltaEpsC,
    Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourShift.contourIntegrand
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Bell.AnnihilationPolarizationCorrelation.annihilation_photons_saturate_tsirelson
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Bell.AnnihilationPolarizationCorrelation.pairExpectation,
    Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds.tsirelsonWitness
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Bell.SorkinHadamardRegion.branchGram_sorkin_hierarchy
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.BellBlochHistoryLinks.branchGram,
    Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert.quantalMeasure
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling.causallyLocal_unistochastic_chsh_contract
    where
  formalizes @ "claim:finite-causal-locality-gives-both-no-signalling-marginal-identities-and-a-tsirelson-expectation-bound-gives-the-chsh-score-and-win-probability-bounds",
  requires @ "assumption:a-normalized-causal-local-chsh-probability-carrier-and-a-tsirelson-bounded-expectation",
  caveat @ "claim:conditional-finite-probability-contract-not-a-relativistic-construction-of-local-observable-algebras"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Bell.LeviCivitaNagaoContour.bellLeviCivita_nagaoContour_integral_synthesis
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bell.LeviCivitaNagaoContour.complexEinstein_bellSpacelike_isInvertedOscillator",
  formalizes @ "claim:the-spacelike-bell-sector-complex-einstein-split-no-signalling-reversible-entropic-limit-and-permitted-nagao-nielsen-contour-normalization-and-deformation-invariance-form-one-synthesis",
  requires @ "assumption:a-coordinate-complex-einstein-field-equation-positive-contour-regulators-and-permitted-gaussian-rays",
  caveat @ "claim:assembled-coordinate-and-contour-identities-not-a-general-curved-spacetime-bell-experiment-or-path-integral-construction"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Bell.AnnihilationPolarizationCorrelation.annihilation_photons_saturate_tsirelson
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bell.AnnihilationPolarizationCorrelation.photonSinglet_stokes_correlation",
  formalizes @ "claim:the-explicit-two-photon-singlet-stokes-correlations-at-the-standard-four-angles-equal-minus-two-sqrt-two",
  caveat @ "claim:ideal-polarization-matrix-calculation-not-a-model-of-detector-efficiency-backgrounds-or-experimental-loopholes"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Bell.SorkinHadamardRegion.branchGram_sorkin_hierarchy
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BellBlochHistoryLinks.branchGram_isDecoherenceFunctional",
  formalizes @ "claim:the-pure-state-branch-gram-decoherence-functional-obeys-sorkin-s-third-order-sum-rule-for-three-disjoint-event-sets",
  caveat @ "claim:finite-branch-level-two-quantum-measure-identity-not-a-continuum-causal-set-measure-or-dynamics"

zil_file_contract physlib.entropicSpine.bellCHSH where
  promises "formalization:bell-chsh-tsirelson-no-signalling-operator-gap-and-one-bit-entropic-readout"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.Entanglement.chsh_tsirelson_violation_and_no_signaling",
    "lean:Physlib.QuantumMechanics.Entanglement.chsh_quantum_at_tsirelson_angles",
    "lean:Physlib.QuantumMechanics.Entanglement.chsh_quantum_exceeds_classical_bound",
    "lean:Physlib.QuantumMechanics.Entanglement.MES_entropy_composition",
    "lean:Physlib.QuantumMechanics.Entanglement.bellSinglet_entropy_composition",
    "lean:Physlib.QuantumMechanics.Entanglement.bellSinglet_qMutualInfo",
    "lean:Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPsiMinus_traceRight_uniform",
    "lean:Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bell_marginals_indistinguishable",
    "lean:Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPhiPlus_not_prod",
    "lean:Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.no_cloning",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.chsh_violation_gap",
    "lean:Physlib.QuantumMechanics.Entanglement.chsh_quantum_eq_predictBellViolation_at_log_two",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling.causallyLocal_unistochastic_chsh_contract",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bell.LeviCivitaNagaoContour.bellLeviCivita_nagaoContour_integral_synthesis",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bell.AnnihilationPolarizationCorrelation.annihilation_photons_saturate_tsirelson",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bell.SorkinHadamardRegion.branchGram_sorkin_hierarchy"
  ]
  forbids_substitutes [
    "claiming an explicit cosine model closes experimental loopholes",
    "claiming a scalar mutual-information interpolation derives the quantum correlation law",
    "identifying the two-log-two Bell-pair mutual information with the single-party log-two reduced entropy",
    "promoting finite partial-trace identities to relativistic microcausality",
    "claiming the abstract Tsirelson bound proves a particular AQFT vacuum attains it",
    "promoting finite Bell histories or coordinate contour identities to a constructed interacting curved-spacetime QFT"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.Entanglement.chsh_tsirelson_violation_and_no_signaling,
    Physlib.QuantumMechanics.Entanglement.chsh_quantum_at_tsirelson_angles,
    Physlib.QuantumMechanics.Entanglement.chsh_quantum_exceeds_classical_bound,
    Physlib.QuantumMechanics.Entanglement.MES_entropy_composition,
    Physlib.QuantumMechanics.Entanglement.bellSinglet_entropy_composition,
    Physlib.QuantumMechanics.Entanglement.bellSinglet_qMutualInfo,
    Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPsiMinus_traceRight_uniform,
    Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bell_marginals_indistinguishable,
    Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.bellPhiPlus_not_prod,
    Physlib.QuantumMechanics.ComplexAction.BellStateNoSignalling.no_cloning,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.chsh_violation_gap,
    Physlib.QuantumMechanics.Entanglement.chsh_quantum_eq_predictBellViolation_at_log_two,
    Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling.causallyLocal_unistochastic_chsh_contract,
    Physlib.QuantumMechanics.ComplexAction.Bell.LeviCivitaNagaoContour.bellLeviCivita_nagaoContour_integral_synthesis,
    Physlib.QuantumMechanics.ComplexAction.Bell.AnnihilationPolarizationCorrelation.annihilation_photons_saturate_tsirelson,
    Physlib.QuantumMechanics.ComplexAction.Bell.SorkinHadamardRegion.branchGram_sorkin_hierarchy
  ]

/-! ## BE.1. Page--Wootters conditioning and ordered clock calibration -/

zil_theorem_intent
    Physlib.Thermodynamics.Landauer.PageWoottersBipartite.tauPW_eq_t
    where
  at_level toy_model
  must_mention [Physlib.Thermodynamics.Landauer.PageWoottersBipartite]

zil_theorem_intent
    Physlib.Thermodynamics.Landauer.PageWoottersBipartite.marginal_entropies_equal
    where
  at_level physical_theorem
  must_mention [Sᵥₙ]

zil_theorem_intent
    Physlib.QuantumMechanics.RelationalTime.DissipativeConditionalClock.conditionalEntropicRate_nonneg
    where
  at_level physical_theorem
  must_mention [
    Physlib.QuantumMechanics.RelationalTime.DissipativeConditionalClock.conditionalEntropicRate
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.RelationalTime.ThreeClockDynamics.ConditionedEvolutionCertificate.conditioned_evolves
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.RelationalTime.ThreeClockDynamics.ConditionedEvolutionCertificate
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.RelationalTime.ThreeClockDynamics.OrderedFourClockCalibration.pwToProper_strictMono
    where
  at_level bridge_theorem
  must_mention [StrictMono]

zil attach Physlib.Thermodynamics.Landauer.PageWoottersBipartite.tauPW_eq_t where
  formalizes @ "claim:the-page-wootters-bipartite-carrier-identifies-its-conditional-time-with-its-clock-reading",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:the-page-wootters-carrier-supplies-the-time-identification-field",
  caveat @ "claim:projection-of-a-declared-carrier-field-not-a-dynamical-derivation-of-physical-time"

zil attach Physlib.Thermodynamics.Landauer.PageWoottersBipartite.marginal_entropies_equal where
  formalizes @ "claim:the-two-reduced-states-of-the-pure-page-wootters-bipartite-state-have-equal-von-neumann-entropy",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Sᵥₙ_of_partial_eq",
  caveat @ "claim:pure-state-schmidt-entropy-symmetry-not-a-derivation-of-the-born-rule-or-clock-dynamics"

zil attach
    Physlib.QuantumMechanics.RelationalTime.DissipativeConditionalClock.conditionalEntropicRate_nonneg
    where
  formalizes @ "claim:the-finite-dissipative-conditional-clock-rate-is-nonnegative-for-positive-hbar",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.RelationalTime.dissipationRate_nonneg",
  caveat @ "claim:finite-sum-rate-positivity-not-a-unique-backreaction-law-or-a-continuum-gkls-existence-theorem"

zil attach
    Physlib.QuantumMechanics.RelationalTime.ThreeClockDynamics.ConditionedEvolutionCertificate.conditioned_evolves
    where
  formalizes @ "claim:a-certified-page-wootters-conditioned-state-obeys-the-same-one-step-evolution-as-its-direct-state",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:conditioning-equals-the-direct-state-and-the-direct-one-step-evolution-law",
  caveat @ "claim:transport-through-an-explicit-certificate-not-a-construction-of-the-conditioning-map-from-a-hamiltonian-constraint"

zil attach
    Physlib.QuantumMechanics.RelationalTime.ThreeClockDynamics.OrderedFourClockCalibration.pwToProper_strictMono
    where
  formalizes @ "claim:strictly-monotone-page-wootters-to-modular-modular-to-entropic-and-entropic-to-proper-calibrations-compose-to-a-strictly-monotone-relational-to-proper-clock",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:each-of-the-three-clock-calibration-maps-is-supplied-and-strictly-monotone",
  caveat @ "claim:order-preservation-of-supplied-calibrations-not-the-operational-signal-delay-law-or-curved-geodesic-proper-time-construction"

zil_file_contract physlib.entropicSpine.relationalClockOrder where
  promises "formalization:finite-page-wootters-conditioning-pure-state-clock-system-entropy-symmetry-nonnegative-dissipative-clock-rate-and-ordered-page-wootters-to-proper-time-calibration"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Thermodynamics.Landauer.PageWoottersBipartite",
    "lean:Physlib.QuantumMechanics.RelationalTime.DissipativeConditionalClock",
    "lean:Physlib.QuantumMechanics.RelationalTime.ThreeClockDynamics.ConditionedEvolutionCertificate",
    "lean:Physlib.QuantumMechanics.RelationalTime.ThreeClockDynamics.OrderedFourClockCalibration"
  ]
  forbids_substitutes [
    "claiming the Page--Wootters time field is derived rather than supplied by its carrier",
    "claiming calibration monotonicity derives a signal-propagation delay law",
    "claiming finite conditional-rate positivity constructs a continuum irreversible dynamics",
    "claiming pure-state marginal entropy symmetry derives the Born rule"
  ]
  witnessed_by [
    Physlib.Thermodynamics.Landauer.PageWoottersBipartite.tauPW_eq_t,
    Physlib.Thermodynamics.Landauer.PageWoottersBipartite.marginal_entropies_equal,
    Physlib.QuantumMechanics.RelationalTime.DissipativeConditionalClock.conditionalEntropicRate_nonneg,
    Physlib.QuantumMechanics.RelationalTime.ThreeClockDynamics.ConditionedEvolutionCertificate.conditioned_evolves,
    Physlib.QuantumMechanics.RelationalTime.ThreeClockDynamics.OrderedFourClockCalibration.pwToProper_strictMono
  ]

/-! ## BF. One-loop gravitational wave function and determinant reduction -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction_norm
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction,
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopPrefactor
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction_eq_lapse_dressed
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction,
    Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster.lapseWeight
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.boson_fermion_determinant_duality
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.gelfandYaglomDet,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction.berezin
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction_norm
    where
  formalizes @ "claim:the-one-loop-complex-gravitational-wave-function-norm-is-the-entropic-damping-factor-times-the-positive-gelfand-yaglom-prefactor",
  supported_by @ "paper:mallik-narain-one-loop-complex-r-times-s3-saddles",
  caveat @ "claim:positive-determinant-parameter-is-supplied-not-a-construction-of-the-full-gravitational-functional-determinant"

zil attach
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction_eq_lapse_dressed
    where
  formalizes @ "claim:the-one-loop-wave-function-is-the-banihashemi-jacobson-lapse-displaced-complex-saddle-weight-dressed-by-the-gelfand-yaglom-prefactor",
  caveat @ "claim:algebraic-lapse-weight-identification-not-a-proof-of-contour-deformation-or-gravitational-path-integral-existence"

zil attach
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.boson_fermion_determinant_duality
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction.berezin_gaussian_eq_det",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.gelfandYaglom_dirichlet",
  formalizes @ "claim:the-dirichlet-gelfand-yaglom-bosonic-prefactor-and-the-one-mode-berezin-fermionic-integral-reduce-to-finite-determinant-data-with-opposite-determinant-powers",
  caveat @ "claim:finite-determinant-reduction-not-a-regularized-infinite-dimensional-supersymmetric-cancellation-theorem"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopPathIntegralVerch.oneLoop_pathIntegral_verch
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopScalarIntegralsQCD.tadpoleLaurent,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction.fermionGaussian,
    Physlib.QFT.Wick.Consistency.complexActionWeight
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.oneLoopExact_satisfies_QME_of_anomaly_zero
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.SatisfiesScaleQME
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopPathIntegralVerch.oneLoop_pathIntegral_verch
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopPathIntegralVerch.berezinDet_eq_bogoliubov_diagonal",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopPathIntegralVerch.oneLoop_weight_unitary_of_reversible",
  formalizes @ "claim:the-scalar-one-loop-pole-berezin-determinant-bogoliubov-energy-verch-symplectic-complex-structure-and-reversible-unit-norm-weight-are-assembled-in-one-finite-algebraic-chain",
  caveat @ "claim:finite-mode-determinant-and-symplectic-identities-not-a-renormalized-curved-spacetime-loop-expansion"

zil attach
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.oneLoopExact_satisfies_QME_of_anomaly_zero
    where
  formalizes @ "claim:a-one-loop-effective-action-satisfies-the-scale-quantum-master-equation-when-its-residual-is-identified-with-an-anomaly-that-vanishes-at-every-scale",
  requires @ "assumption:a-supplied-one-loop-qme-bridge-with-residual-equals-anomaly-and-scale-wise-anomaly-vanishing",
  caveat @ "claim:conditional-qme-transport-not-an-independent-analytic-proof-of-finiteness-or-anomaly-cancellation-for-continuum-chern-simons-theory"

zil_file_contract physlib.entropicSpine.oneLoopWaveFunction where
  promises "formalization:one-loop-gravitational-wave-function-entropic-lapse-and-finite-determinant-bridge"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction_norm",
    "lean:Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction_eq_lapse_dressed",
    "lean:Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.boson_fermion_determinant_duality",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopPathIntegralVerch.oneLoop_pathIntegral_verch",
    "lean:Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.oneLoopExact_satisfies_QME_of_anomaly_zero"
  ]
  forbids_substitutes [
    "claiming the supplied positive determinant is a constructed zeta-regularized graviton determinant",
    "claiming an algebraic lapse identity establishes a convergent gravitational path integral",
    "claiming a one-mode Berezin determinant proves full supersymmetric determinant cancellation",
    "claiming a supplied zero-anomaly QME bridge independently proves continuum one-loop exactness"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction_norm,
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction_eq_lapse_dressed,
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.boson_fermion_determinant_duality,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopPathIntegralVerch.oneLoop_pathIntegral_verch,
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.oneLoopExact_satisfies_QME_of_anomaly_zero
  ]

/-! ## BG. Page--Wootters, AdS/CFT, thermal time, and complex evolution -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.pageWootters_adscft_entropic_correspondence
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.RelationalTime.DissipativeConditionalClock.conditionalEntropicRate,
    Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime.bogoliubovEntropicTime
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.pageWootters_connesRovelli_entropic_bridge
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.RelationalTime.DissipativeConditionalClock.conditionalEntropicRate,
    QuantumMechanics.FiniteTarget.kmsThermalRate_at_inverse_temperature
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.constructive_time_derivation
    where
  at_level bridge_theorem
  must_mention [
    QuantumMechanics.FiniteTarget.complexHamiltonian,
    Physlib.QuantumMechanics.RelationalTime.hermitianPart,
    Physlib.QuantumMechanics.RelationalTime.antiHermitianPart
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.pageWootters_adscft_entropic_correspondence
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.diamond_entanglement_eq_occupation",
  formalizes @ "claim:page-wootters-conditional-entropy-production-and-the-ads-cft-boundary-entropic-time-share-nonnegativity-frozen-and-luminal-zero-characterizations",
  requires @ "assumption:a-supplied-dissipative-conditional-clock-jump-family-and-the-causal-diamond-bogoliubov-carrier",
  caveat @ "claim:conjunction-of-compatible-clock-and-boundary-identities-not-a-derivation-of-the-ads-cft-dictionary"

zil attach
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.pageWootters_connesRovelli_entropic_bridge
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.connesRovelli_modular_tick",
  formalizes @ "claim:the-connes-rovelli-kms-unit-tick-page-wootters-conditional-rate-and-causal-diamond-entropic-time-are-assembled-with-their-reversible-frozen-and-luminal-limits",
  caveat @ "claim:assembled-finite-clock-carriers-not-a-tomita-takesaki-construction-for-an-interacting-curved-spacetime-qft"

zil attach
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.constructive_time_derivation
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.connesRovelli_modular_tick",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.diamond_entanglement_eq_occupation",
  formalizes @ "claim:the-page-wootters-effective-generator-decomposes-as-the-nagao-nielsen-complex-hamiltonian-with-tise-kernel-reduction-kms-unit-tick-and-entropic-time-readout",
  requires @ "assumption:finite-dimensional-complex-hilbert-space-eigenvector-kernel-and-positive-kms-parameters",
  caveat @ "claim:operator-decomposition-and-conditional-evolution-not-a-spectral-construction-of-a-physical-universe-state"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.three_clocks
    where
  at_level bridge_theorem
  must_mention [
    QuantumMechanics.FiniteTarget.complexHamiltonian,
    Physlib.QuantumMechanics.RelationalTime.DissipativeConditionalClock.conditionalEntropicRate
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.jacobson_three_clocks_realization
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra.lorentzBoost,
    Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime.bogoliubovEntropicTime
  ]

zil attach Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.three_clocks where
  supported_by @ "lean:QuantumMechanics.FiniteTarget.complexHamiltonian_at_H_I_zero",
  formalizes @ "claim:unitary-parameter-time-modular-entropy-preserving-time-and-dissipative-page-wootters-entropic-time-are-distinguished-with-frozen-rate-and-hilbert-schmidt-orthogonality-properties",
  requires @ "assumption:finite-dimensional-hilbert-and-matrix-carriers-a-dissipative-conditional-clock-and-a-commuting-modular-direction",
  caveat @ "claim:classification-of-three-finite-carriers-not-a-uniqueness-theorem-for-physical-time-in-quantum-gravity"

zil attach
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.jacobson_three_clocks_realization
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.diamond_entanglement_eq_occupation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.diamond_reversible_iff_luminal",
  formalizes @ "claim:on-the-causal-diamond-the-boost-preserves-the-lorentz-form-while-the-entropic-clock-is-binary-entropy-and-vanishes-exactly-at-the-two-luminal-ratios",
  caveat @ "claim:kinematic-causal-diamond-realization-not-a-dynamical-bulk-reconstruction-or-clock-measurement-protocol"

zil_file_contract physlib.entropicSpine.pageWoottersAdSCFT where
  promises "formalization:page-wootters-ads-cft-connes-rovelli-entropic-and-complex-hamiltonian-clock-bridge"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.pageWootters_adscft_entropic_correspondence",
    "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.pageWootters_connesRovelli_entropic_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.constructive_time_derivation",
    "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.three_clocks",
    "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.jacobson_three_clocks_realization"
  ]
  forbids_substitutes [
    "calling a conjunction of clock identities a proof of holographic duality",
    "calling finite-dimensional effective-clock evolution a constructed quantum gravity state",
    "identifying reversible modular time with irreversible entropy production without the stated distinction",
    "promoting the kinematic three-clock classification to a unique dynamics of time"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.pageWootters_adscft_entropic_correspondence,
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.pageWootters_connesRovelli_entropic_bridge,
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.constructive_time_derivation,
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.three_clocks,
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.jacobson_three_clocks_realization
  ]

/-! ## BH. Chern--Simons--Witten modular data and the Verlinde Wilson lane -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_unitary
    where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.braidingPhaseWilson_value_eq_verlindeSMatrix
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon.wilsonBraidingPhase
  ]

zil attach Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_unitary where
  formalizes @ "claim:the-positive-level-abelian-chern-simons-witten-verlinde-s-matrix-has-orthonormal-rows-by-discrete-fourier-gauss-sum-orthogonality",
  supported_by @ "paper:witten-chern-simons-and-verlinde-modular-s-matrix",
  caveat @ "claim:abelian-level-k-modular-data-not-a-nonabelian-modular-tensor-category-construction"

zil attach
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.braidingPhaseWilson_value_eq_verlindeSMatrix
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon.wilsonBraidingPhase_eq_S",
  formalizes @ "claim:the-charge-sector-wilson-braiding-phase-is-the-sqrt-k-normalized-conjugate-verlinde-s-matrix-entry",
  caveat @ "claim:constant-charge-sector-wilson-value-identity-not-a-construction-of-the-continuum-chern-simons-measure"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_sq_eq_chargeConjugation
    where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.torusPartitionFunction_S_invariant
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.torusPartitionFunction
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_sq_eq_chargeConjugation
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswDFT_orthogonality",
  formalizes @ "claim:at-positive-abelian-level-the-square-of-the-verlinde-modular-s-matrix-is-the-finite-charge-conjugation-matrix",
  caveat @ "claim:finite-u-one-level-k-gauss-sum-identity-not-a-general-modular-functor-or-nonabelian-charge-conjugation-theorem"

zil attach
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.torusPartitionFunction_S_invariant
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_colOrthogonal",
  supported_by @ "lean:KroneckerDelta.sum_mul",
  formalizes @ "claim:the-diagonal-level-k-torus-character-partition-function-is-invariant-under-the-unitary-verlinde-s-matrix-transform",
  requires @ "assumption:a-positive-finite-abelian-level-and-a-supplied-vector-of-torus-characters",
  caveat @ "claim:finite-character-norm-invariance-not-a-continuum-cft-partition-function-or-full-sl-two-z-modular-invariance-proof"

zil_file_contract physlib.entropicSpine.chernSimonsWittenVerlindeSMatrix where
  promises "formalization:unitary-abelian-verlinde-s-matrix-braiding-wilson-value-and-analytic-witten-functional-integral-lane"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_unitary",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.braidingPhaseWilson_value_eq_verlindeSMatrix",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.complexActionFiniteMeasure_verlindeSMatrixWilson_supplies_witten_FK",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswVerlinde_formula",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_sq_eq_chargeConjugation",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.torusPartitionFunction_S_invariant"
  ]
  forbids_substitutes [
    "promoting abelian Fourier modular data to an unproved nonabelian theory",
    "claiming a constant Wilson observable constructs a continuum Chern-Simons measure",
    "claiming the conditional analytic lane evaluates a physical knot invariant without its model premises",
    "promoting finite diagonal character-norm invariance to a full continuum modular field theory"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_unitary,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.braidingPhaseWilson_value_eq_verlindeSMatrix,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.complexActionFiniteMeasure_verlindeSMatrixWilson_supplies_witten_FK,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswVerlinde_formula,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_sq_eq_chargeConjugation,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.torusPartitionFunction_S_invariant
  ]

/-! ## BI. Aggregate entropic spine -/

zil_file_contract physlib.entropicSpine.core where
  promises "formalization:curated-entropic-dynamics-qm-to-gr-spine"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric.wasserstein1Distance_triangle",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy.freeEnergy_ge_gibbs",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq",
    "lean:Physlib.QuantumMechanics.ComplexAction.qifLifetime_decayFraction_eq_inv_e",
    "lean:Physlib.QuantumMechanics.FrozenLimit.frozen_limit_recovers_standard_physics",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.entropicNewtonConstant_converges",
    "lean:Physlib.QFT.PathIntegral.stokesModeLaplaceResolvent_one_eq_euclideanPropagator",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.dampedStokesEvolution_kineticEnergy_hasDerivAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade.dampedStokesEvolution_sobolevDissipationCascade",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_integratedSobolevDissipationCascade",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_discreteBkm_converges_to_certifiedBudget",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_discreteBkm_le_certifiedBudget",
    "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_exists_resolution_for_bkm_tolerance",
    "lean:Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery.finiteSchrodinger_initialRecovery_and_sampledEnergy",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.euclideanL2_freeSchrodinger_unitaryStronglyContinuous",
    "lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.schrodingerParaboloid_affineSelfSimilarity",
    "lean:Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.schrodingerPhase_parabolicRescaling_chain",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.euclideanSobolev_hierarchy_freeEvolution_annularLocalization",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley.finiteLittlewoodPaley_orthogonality_bessel",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.standardMultiNorm_dilationGauge_geometry",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.strictDominance_markedBlock_structure",
    "lean:Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.strictDominance_induces_unique_markedCone",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.markedCone_explicitCoordinate_characterization",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.minimalMarkedPartition_dottedSet_characterization",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.nonnegativePoint_markedCone_and_uniqueDottedRegion",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.dottedRegion_eq_markedConeUnion_inter_strictDottedLocus",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maximalDottedScale_finiteTube_geometry",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.isMaximalDottedScale_iff_maximalFloorProfile",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.uniqueMaximalApex_coverage_disjointInteriors",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maximalScale_proximity_and_intersectingTube_bound",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.principalCone_density_and_maximalMeet_proximity",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.constructedTubeColoring_and_finiteLocalOverlap",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock.frequencyBlock_eq_coordinateDyadicShell",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison.frequencyBlock_blockGauge_comparison",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff.smoothBlockCutoff_subordinate_frequencyBlock",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring.smoothTubeColor_fiber_pairwiseDisjoint",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteSmoothSquareBound.finiteSmoothMultiplierSquareBound",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.fullFrequencyCover_and_cutoff_one",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition.finiteNormalizedPartition_of_coversAt",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteReproducingFormula.finiteMultiNorm_reproducing_square_support",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalLocalFiniteness.globalSmoothCover_locallyFinite",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalNormalizedPartition.globalSmoothPartitionOfUnity_spec",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.globalMultiNorm_reproducing_square_finiteSupport",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula.globalMultiNorm_complexReproducing_bornResolution",
    "lean:Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerLocalization.multiNorm_schrodingerLocalization_bridge",
    "lean:Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerDecoherence.multiNorm_schrodingerDecoherence_bridge",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.dyadicSchwartzKernel_cancellation_telescope",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.dyadicDetailDistribution_tendsto_delta",
    "lean:Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.physicalCalderon_reconstruction_multiNormMultiplier_bridge",
    "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley.finiteDyadicOverlapLittlewoodPaley_constructedColoring_bessel",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius.schwarzschildHorizon_oneBit_entire_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius.comptonCellInference_schwarzschildHorizon_oneBit_entire_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_staticPoissonField_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.comptonCellInference_comptonNagaoLeviCivita_staticPoissonField_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPoissonField3_pointwiseGeometry",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.hodgeFluxDivergence3_and_einsteinFieldEquation_at",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousHodgeScreen_bitCount_gravity_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.comptonCellInference_homogeneousHodgeScreen_gravity_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewton_surfaceFlux_bitCount_gravity_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonAt_surfaceFlux_bitCount_gravity_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.comptonCellInference_isolatedNewtonAt_surfaceFlux_gravity_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPointSources_bitCount_gravity_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourcesEinstein00.finiteNewtonPointSources_distributionalEinstein00_bitCount_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonPointSources_sourceResolvedFlux_distributionalEinstein00_bitCount_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonExteriorField3_sphereFlux_decompose",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonZonalKernel_intervalIntegral",
    "lean:Space.integral_comp_inner_unit_toSphere_eq_intervalIntegral",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.newtonSphereFluxLaw3",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonPointSources_enclosingFlux_distributionalEinstein00_bitCount_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.comptonCellInference_finiteNewtonPointSources_enclosingFluxEinstein00_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.entropicDensity_curvedMeasure_gaugeQuantumMatter_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential.quantumMatter_is_classical_plus_curvedQuantum",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.entropicDensity_curvedMeasure_maxwellContinuity_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.edWaveFunction_complexCovariantDeriv_gauge_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSchrodingerNagaoNielsen.normalizedPerepelkin_nonHermitian_nagaoNielsen_caticha_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_system_bitForm",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_equations_bitForm",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_conservation_bitForm",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.schmidt_quasifree_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.spacetime_superoperator_program",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.catichaFunctional_kleinGordon_continuity_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.catichaFunctional_emLiouvillian_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.catichaDensity_schmidt_quasifree_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.gaugeCovariantSmearedSchrodinger_equation_covariant",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.diagonalModular_catichaIntertwines",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.curvedMaxwell_implies_waveWithConnection_of_lorenzGauge",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.maxwellWaveWithConnection_and_complexEinstein_split",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_of_lorenzGauge",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.metricFieldMaxwell_implies_ricciCoupledWave_onChart",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_implies_ricciCoupledWave_onChart",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.metricLeviCivitaCovariantDerivative_torsion_eq_zero",
    "lean:PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivative_independent",
    "lean:PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_atlas_iff",
    "lean:PseudoRiemannianMetric.localLeviCivitaAtlas_intrinsicMaxwellOn_iff",
    "lean:PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_iff_operator_eq",
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves",
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.advanced_solves",
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.eq_retarded_of_solves",
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.waveOperator_causalPropagator_eq_zero",
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves_for_leviCivitaAtlas",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_basis_eq_riemannFromConnection",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_ricci_eq_ricciFromConnection",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureEndomorphismAt_basis_apply",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureRicciTrace_eq_ricciFromConnection",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_firstBianchi",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_bundledGeometry_onChart",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.cubicDoubleCopy_eq_cubicAmplitude_colorReplacement",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DoubleCopyCharacter.nnPathWeight_norm_doubleCopy",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.JacobiBianchiDoubleCopyFamily.jacobi_bianchi_double_copy_family",
    "lean:Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.norm_reflectionFactorI",
    "lean:Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.reflectionTransmission_prob_conservation",
    "lean:Physlib.QuantumMechanics.Entanglement.chsh_tsirelson_violation_and_no_signaling",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.chsh_violation_gap",
    "lean:Physlib.QuantumMechanics.Entanglement.chsh_quantum_eq_predictBellViolation_at_log_two",
    "lean:Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction_norm",
    "lean:Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction_eq_lapse_dressed",
    "lean:Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.boson_fermion_determinant_duality",
    "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.pageWootters_adscft_entropic_correspondence",
    "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.pageWootters_connesRovelli_entropic_bridge",
    "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.constructive_time_derivation",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_unitary",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.braidingPhaseWilson_value_eq_verlindeSMatrix",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy.electrogravitational_bianchi_double_copy",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.NoetherConservationDoubleCopy.noether_double_copy_matter_conservation",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy.newtonG_from_screen_system",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy.gravitational_electromagnetic_coupling_relation",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling.causallyLocal_unistochastic_chsh_contract",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bell.LeviCivitaNagaoContour.bellLeviCivita_nagaoContour_integral_synthesis",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bell.AnnihilationPolarizationCorrelation.annihilation_photons_saturate_tsirelson",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bell.SorkinHadamardRegion.branchGram_sorkin_hierarchy",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopPathIntegralVerch.oneLoop_pathIntegral_verch",
    "lean:Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.oneLoopExact_satisfies_QME_of_anomaly_zero",
    "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.three_clocks",
    "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.jacobson_three_clocks_realization",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_sq_eq_chargeConjugation",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.torusPartitionFunction_S_invariant",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.manifoldCovariantCurvatureAction_swap",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.pseudoRiemannianCurvatureEvaluation_swap",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.CurvedCausalHistoryPathIntegral.curvedHistoryDecoherenceFunctional_norm_eq_damping_mul",
    "lean:Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral.causalSet_gravity_eq_matsubara",
    "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalGreen_sjState",
    "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalGreen_complexSchrodinger_functional_bridge_checked",
    "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.pathIntegralFeynmanKernel_calderon_reconstruction",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.complexActionFiniteMeasure_verlindeSMatrixWilson_supplies_witten_FK",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral_amplitude_wilson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral_amplitude_norm_le",
    "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswVerlinde_formula",
    "lean:Physlib.Thermodynamics.newton_law_of_gravity_from_verlinde"
  ]
  forbids_substitutes [
    "documentation or filenames used as proof",
    "promotion of algebraic identities to empirical physical laws",
    "promotion of a scalar Fourier-mode contraction semigroup to the full nonlinear Navier-Stokes flow",
    "promotion of the finite diagonal Fourier/Galerkin flow to pressure-projected or nonlinear Navier-Stokes dynamics",
    "identification of the effective minus-lambda-enstrophy term with nonlinear vortex stretching",
    "promotion of the finite Fourier BKM surrogate to the analytic L-infinity Beale-Kato-Majda criterion",
    "promotion of finite Fourier interval balances to a nonlinear Leray weak solution or nonlinear regularity theorem",
    "promotion of fixed-step convergence for nonnegative antitone trajectories to arbitrary discontinuous or oscillatory integrands",
    "interpretation of the fixed-resolution one-over-resolution quadrature remainder as a physical uncertainty",
    "interpretation of a requested quadrature tolerance as experimental uncertainty or statistical confidence",
    "promotion of finite pure-point Schrödinger recovery to the Du-Zhang Euclidean almost-everywhere Carleson theorem",
    "promotion of a finite sampled-time energy identity to a continuous space-time maximal or Strichartz estimate",
    "promotion of strong Euclidean L2 Schrödinger recovery to pointwise or almost-everywhere convergence",
    "claiming a Carleson maximal estimate or Du-Zhang Sobolev threshold from Plancherel strong continuity",
    "promotion of the one-parameter distributional Calderon identity to the paper's full anisotropic tensor or convolution dual families, L1 square-function equivalence, or local Hardy-space theory",
    "promotion of pointwise complex Born resolution to integrated probability normalization without integrability",
    "promotion of the one-block Euclidean smooth localization to the paper's full anisotropic product-space Fourier theory",
    "interpretation of free Schrödinger phase invariance as environmental decoherence or entropy production",
    "claiming a Schrödinger maximal estimate or Du-Zhang threshold from Sobolev norm conservation and frequency localization",
    "time quantization",
    "a generalized n-bit Schwarzschild mass law",
    "a dynamical entanglement-to-horizon-dilation mechanism",
    "promotion of the static linearized spatial-Laplacian carrier to an exact nonlinear Einstein solution",
    "promotion of the oriented Cartesian Euclidean Hodge carrier to a general Lorentzian or curved-manifold theorem",
    "promotion of the homogeneous spherical flux specialization to a general Stokes or divergence theorem",
    "promotion of the isolated Newton distribution to a smooth or exact nonlinear Einstein point-source solution",
    "promotion of single-source translation covariance to a multi-source or arbitrary-domain theorem",
    "promotion of finite distributional superposition to an enclosing-screen flux or nonlinear Einstein multi-body theorem",
    "promotion of the scalar distributional static linearized Einstein 00 equation to a full distribution-valued tensor or exact nonlinear solution",
    "promotion of source-resolved centered-sphere flux to total-field flux through one enclosing screen",
    "promoting the proved round-sphere NewtonSphereFluxLaw3 to an arbitrary-surface divergence theorem",
    "claiming that the shared-density interface derives electromagnetic minimal coupling",
    "promoting finite matrix quasifree and modular carriers to an interacting locally covariant QFT",
    "promoting the electrogravitic momentum-space carrier to a general curved Einstein-Maxwell PDE solution",
    "promoting field-realized coordinate jets to a coordinate-free global manifold theorem",
    "promoting finite curved histories to a continuum Sorkin quantum measure",
    "promoting finite-measure constant Wilson observables to a constructed continuum Chern-Simons measure",
    "promoting abelian U1k Verlinde fusion to an unproved nonabelian theorem"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric.wasserstein1Distance_triangle,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy.freeEnergy_ge_gibbs,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction.edWaveFunction_modulus_sq,
    Physlib.QuantumMechanics.ComplexAction.qifLifetime_decayFraction_eq_inv_e,
    Physlib.QuantumMechanics.FrozenLimit.frozen_limit_recovers_standard_physics,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.entropicNewtonConstant_converges,
    Physlib.QFT.PathIntegral.stokesModeLaplaceResolvent_one_eq_euclideanPropagator,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.dampedStokesEvolution_kineticEnergy_hasDerivAt,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade.dampedStokesEvolution_sobolevDissipationCascade,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade.dampedStokesEvolution_integratedSobolevDissipationCascade,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_discreteBkm_converges_to_certifiedBudget,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_discreteBkm_le_certifiedBudget,
    Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge.dampedStokesEvolution_exists_resolution_for_bkm_tolerance,
    Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery.finiteSchrodinger_initialRecovery_and_sampledEnergy,
    Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution.euclideanL2_freeSchrodinger_unitaryStronglyContinuous,
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry.schrodingerParaboloid_affineSelfSimilarity,
    Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling.schrodingerPhase_parabolicRescaling_chain,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.euclideanSobolev_hierarchy_freeEvolution_annularLocalization,
    Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley.finiteLittlewoodPaley_orthogonality_bessel,
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.standardMultiNorm_dilationGauge_geometry,
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.strictDominance_markedBlock_structure,
    Physlib.Mathematics.HarmonicAnalysis.StandardMultiNormMatrix.StrictDominanceAssignment.strictDominance_induces_unique_markedCone,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.markedCone_explicitCoordinate_characterization,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.minimalMarkedPartition_dottedSet_characterization,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.nonnegativePoint_markedCone_and_uniqueDottedRegion,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedPartition.dottedRegion_eq_markedConeUnion_inter_strictDottedLocus,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maximalDottedScale_finiteTube_geometry,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.isMaximalDottedScale_iff_maximalFloorProfile,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.uniqueMaximalApex_coverage_disjointInteriors,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.maximalScale_proximity_and_intersectingTube_bound,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.principalCone_density_and_maximalMeet_proximity,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadic.constructedTubeColoring_and_finiteLocalOverlap,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock.frequencyBlock_eq_coordinateDyadicShell,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison.frequencyBlock_blockGauge_comparison,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff.smoothBlockCutoff_subordinate_frequencyBlock,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring.smoothTubeColor_fiber_pairwiseDisjoint,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteSmoothSquareBound.finiteSmoothMultiplierSquareBound,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover.fullFrequencyCover_and_cutoff_one,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition.finiteNormalizedPartition_of_coversAt,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteReproducingFormula.finiteMultiNorm_reproducing_square_support,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalLocalFiniteness.globalSmoothCover_locallyFinite,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalNormalizedPartition.globalSmoothPartitionOfUnity_spec,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula.globalMultiNorm_reproducing_square_finiteSupport,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula.globalMultiNorm_complexReproducing_bornResolution,
    Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerLocalization.multiNorm_schrodingerLocalization_bridge,
    Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerDecoherence.multiNorm_schrodingerDecoherence_bridge,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel.dyadicSchwartzKernel_cancellation_telescope,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon.dyadicDetailDistribution_tendsto_delta,
    Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon.physicalCalderon_reconstruction_multiNormMultiplier_bridge,
    Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley.finiteDyadicOverlapLittlewoodPaley_constructedColoring_bessel,
    Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius.schwarzschildHorizon_oneBit_entire_chain,
    Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildHorizonScaleMobius.comptonCellInference_schwarzschildHorizon_oneBit_entire_chain,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_staticPoissonField_chain,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.comptonCellInference_comptonNagaoLeviCivita_staticPoissonField_chain,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPoissonField3_pointwiseGeometry,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.hodgeFluxDivergence3_and_einsteinFieldEquation_at,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousHodgeScreen_bitCount_gravity_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.comptonCellInference_homogeneousHodgeScreen_gravity_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewton_surfaceFlux_bitCount_gravity_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonAt_surfaceFlux_bitCount_gravity_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.comptonCellInference_isolatedNewtonAt_surfaceFlux_gravity_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPointSources_bitCount_gravity_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourcesEinstein00.finiteNewtonPointSources_distributionalEinstein00_bitCount_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonPointSources_sourceResolvedFlux_distributionalEinstein00_bitCount_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonExteriorField3_sphereFlux_decompose,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonZonalKernel_intervalIntegral,
    Space.integral_comp_inner_unit_toSphere_eq_intervalIntegral,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.newtonSphereFluxLaw3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonPointSources_enclosingFlux_distributionalEinstein00_bitCount_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.comptonCellInference_finiteNewtonPointSources_enclosingFluxEinstein00_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.entropicDensity_curvedMeasure_gaugeQuantumMatter_bridge,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential.quantumMatter_is_classical_plus_curvedQuantum,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.entropicDensity_curvedMeasure_maxwellContinuity_bridge,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.edWaveFunction_complexCovariantDeriv_gauge_bridge,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSchrodingerNagaoNielsen.normalizedPerepelkin_nonHermitian_nagaoNielsen_caticha_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_system_bitForm,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_equations_bitForm,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_conservation_bitForm,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.schmidt_quasifree_bridge,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.kleinGordon_continuity_program,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.spacetime_superoperator_program,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.catichaFunctional_kleinGordon_continuity_bridge,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.catichaFunctional_emLiouvillian_bridge,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree.catichaDensity_schmidt_quasifree_bridge,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.gaugeCovariantSmearedSchrodinger_equation_covariant,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.diagonalModular_catichaIntertwines,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.curvedMaxwell_implies_waveWithConnection_of_lorenzGauge,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.maxwellWaveWithConnection_and_complexEinstein_split,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.leviCivitaMaxwell_implies_ricciCoupledWave_of_lorenzGauge,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.metricFieldMaxwell_implies_ricciCoupledWave_onChart,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_implies_ricciCoupledWave_onChart,
    Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.metricLeviCivitaCovariantDerivative_torsion_eq_zero,
    PseudoRiemannianMetric.LocalLeviCivitaAtlasData.covariantDerivative_independent,
    PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_atlas_iff,
    PseudoRiemannianMetric.localLeviCivitaAtlas_intrinsicMaxwellOn_iff,
    PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_iff_operator_eq,
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves,
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.advanced_solves,
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.eq_retarded_of_solves,
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.waveOperator_causalPropagator_eq_zero,
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves_for_leviCivitaAtlas,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_basis_eq_riemannFromConnection,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_ricci_eq_ricciFromConnection,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureEndomorphismAt_basis_apply,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCurvatureRicciTrace_eq_ricciFromConnection,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.coordinateCovariantCurvature_firstBianchi,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.contDiffMetricFieldMaxwell_bundledGeometry_onChart,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy.cubicDoubleCopy_eq_cubicAmplitude_colorReplacement,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DoubleCopyCharacter.nnPathWeight_norm_doubleCopy,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.JacobiBianchiDoubleCopyFamily.jacobi_bianchi_double_copy_family,
    Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.norm_reflectionFactorI,
    Physlib.QuantumMechanics.ComplexAction.TwoDStringExactSMatrix.reflectionTransmission_prob_conservation,
    Physlib.QuantumMechanics.Entanglement.chsh_tsirelson_violation_and_no_signaling,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumBellCHSH.chsh_violation_gap,
    Physlib.QuantumMechanics.Entanglement.chsh_quantum_eq_predictBellViolation_at_log_two,
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction_norm,
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopWaveFunction_eq_lapse_dressed,
    Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.boson_fermion_determinant_duality,
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.pageWootters_adscft_entropic_correspondence,
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.pageWootters_connesRovelli_entropic_bridge,
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.constructive_time_derivation,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_unitary,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.braidingPhaseWilson_value_eq_verlindeSMatrix,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy.electrogravitational_bianchi_double_copy,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.NoetherConservationDoubleCopy.noether_double_copy_matter_conservation,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy.newtonG_from_screen_system,
    Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy.gravitational_electromagnetic_coupling_relation,
    Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling.causallyLocal_unistochastic_chsh_contract,
    Physlib.QuantumMechanics.ComplexAction.Bell.LeviCivitaNagaoContour.bellLeviCivita_nagaoContour_integral_synthesis,
    Physlib.QuantumMechanics.ComplexAction.Bell.AnnihilationPolarizationCorrelation.annihilation_photons_saturate_tsirelson,
    Physlib.QuantumMechanics.ComplexAction.Bell.SorkinHadamardRegion.branchGram_sorkin_hierarchy,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.OneLoopPathIntegralVerch.oneLoop_pathIntegral_verch,
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.oneLoopExact_satisfies_QME_of_anomaly_zero,
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.three_clocks,
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EntropicTime.jacobson_three_clocks_realization,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswSMatrix_sq_eq_chargeConjugation,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.torusPartitionFunction_S_invariant,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.manifoldCovariantCurvatureAction_swap,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian.pseudoRiemannianCurvatureEvaluation_swap,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.CurvedCausalHistoryPathIntegral.curvedHistoryDecoherenceFunctional_norm_eq_damping_mul,
    Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral.causalSet_gravity_eq_matsubara,
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalGreen_sjState,
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.causalGreen_complexSchrodinger_functional_bridge_checked,
    Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.pathIntegralFeynmanKernel_calderon_reconstruction,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.complexActionFiniteMeasure_verlindeSMatrixWilson_supplies_witten_FK,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral_amplitude_wilson,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral.wittenWilsonCutoffFreeFunctionalIntegral_amplitude_norm_le,
    Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity.cswVerlinde_formula,
    Physlib.Thermodynamics.newton_law_of_gravity_from_verlinde
  ]

zil attach PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves_for_localLeviCivitaAtlas where
  formalizes @ "claim:retarded-maxwell-evolution-independent-of-local-levi-civita-atlas",
  supported_by @ "lean:PseudoRiemannianMetric.localLeviCivitaAtlas_intrinsicMaxwellOn_iff",
  caveat @ "claim:causal-evolution-remains-conditional-on-explicit-green-operator-and-regularity-data"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.caticha_retarded_intertwines_source where
  formalizes @ "claim:caticha-functional-evolution-intertwines-retarded-klein-gordon-source-evolution",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.continuumSmearedSchrodingerGenerator",
  caveat @ "claim:right-inverse-and-intertwining-are-explicit-analytic-data-not-derived-green-hyperbolicity"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.microlocalSpectrumCondition_image where
  formalizes @ "claim:positive-frequency-wavefront-cone-is-preserved-by-cone-preserving-covector-transport",
  caveat @ "claim:abstract-wavefront-carrier-does-not-construct-a-hadamard-state-on-an-arbitrary-spacetime"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.retardedTwoPoint_isHermitian_and_positive where
  formalizes @ "claim:retarded-green-pullback-preserves-hermitian-positive-quasifree-two-point-data",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.caticha_retarded_intertwines_source",
  caveat @ "claim:algebraic-quasifree-carrier-requires-separate-microlocal-hadamard-input"

zil attach Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.PressureProjectedNonlinearData.energy_pair_nonlinearGalerkinRHS where
  formalizes @ "claim:pressure-projected-galerkin-convection-cancels-from-the-energy-pairing",
  supported_by @ "lean:FluidDynamics.NavierStokes.inner_velocity_convectiveTerm",
  caveat @ "claim:finite-galerkin-energy-identity-not-infinite-dimensional-weak-existence-or-three-dimensional-global-regularity"

zil attach PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator_solves_homogeneous_for_localLeviCivitaAtlas where
  formalizes @ "claim:maxwell-causal-propagator-is-homogeneous-and-independent-of-local-levi-civita-atlas",
  supported_by @ "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.waveOperator_causalPropagator_eq_zero",
  caveat @ "claim:causal-propagation-is-conditional-on-explicit-green-and-global-regularity-data"

zil attach PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator_solves_tensor_homogeneous where
  formalizes @ "claim:maxwell-causal-propagator-satisfies-the-frame-free-tensor-ricci-coupled-wave-equation",
  supported_by @ "lean:PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellAt_iff_tensor",
  caveat @ "claim:tensorial-causal-propagation-is-conditional-on-explicit-green-hessian-curvature-and-frame-trace-data"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.caticha_causalPropagator_is_homogeneous where
  formalizes @ "claim:caticha-functional-evolution-preserves-the-causal-klein-gordon-solution-space",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.kleinGordon_causalPropagator_eq_zero",
  caveat @ "claim:intertwining-and-green-hyperbolicity-remain-explicit-analytic-data"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.caticha_advanced_intertwines_source where
  formalizes @ "claim:caticha-functional-evolution-of-an-advanced-klein-gordon-field-descends-to-the-declared-source-generator",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.kleinGordon_advanced",
  requires @ "assumption:advanced-green-right-inverse-and-caticha-klein-gordon-intertwining-data",
  caveat @ "claim:advanced-source-intertwining-is-conditional-on-the-declared-analytic-carrier-not-a-green-existence-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.causalHadamardCarrier_properties where
  formalizes @ "claim:causal-green-pullback-preserves-ccr-compatible-positive-hermitian-microlocal-two-point-data",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumHadamardTwoPoint.pullback",
  caveat @ "claim:the-wavefront-carrier-and-cone-preserving-covector-transport-are-explicit-hadamard-inputs"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.retarded_common_carrier where
  formalizes @ "claim:one-retarded-green-field-solves-global-curved-maxwell-and-encoded-caticha-klein-gordon-equations",
  supported_by @ "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.kleinGordon_retarded_apply",
  requires @ "assumption:explicit-real-to-complex-source-and-field-maps-with-retarded-green-compatibility",
  caveat @ "claim:the-adapter-is-explicit-analytic-data-not-a-canonical-identification-on-arbitrary-spacetimes"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.advanced_common_carrier where
  formalizes @ "claim:one-advanced-green-field-solves-global-curved-maxwell-and-encoded-caticha-klein-gordon-equations",
  supported_by @ "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.advanced_solves",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.caticha_advanced_intertwines_source",
  requires @ "assumption:explicit-real-to-complex-source-and-field-maps-with-advanced-green-compatibility",
  caveat @ "claim:the-common-carrier-map-and-advanced-green-operator-remain-explicit-analytic-data"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.causalPropagator_compat where
  formalizes @ "claim:global-maxwell-and-caticha-klein-gordon-pauli-jordan-propagators-agree-after-the-declared-complexification",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.retarded_common_carrier",
  requires @ "assumption:retarded-and-advanced-green-compatibility-on-the-common-carrier",
  caveat @ "claim:propagator-compatibility-is-derived-from-the-two-green-compatibilities-not-from-geometry-alone"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.causal_hadamard_globalMaxwell_chain where
  formalizes @ "claim:caticha-functional-aqft-hadamard-and-global-curved-maxwell-causal-evolution-share-one-explicit-carrier",
  supported_by @ "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator_solves_homogeneous",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.caticha_causalPropagator_is_homogeneous",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.causalHadamardCarrier_properties",
  requires @ "assumption:global-green-data-common-carrier-adapter-hadamard-two-point-data-and-cone-preserving-covector-transport",
  caveat @ "claim:conditional-free-field-carrier-not-a-construction-of-interacting-curved-spacetime-qft"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.homogeneous_solution_compat where
  formalizes @ "claim:arbitrary-homogeneous-global-maxwell-fields-map-to-homogeneous-complex-klein-gordon-fields",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.waveOperator_compat",
  requires @ "assumption:operator-level-common-carrier-compatibility",
  caveat @ "claim:operator-compatibility-is-explicit-adapter-data-not-derived-from-green-output-compatibility"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.unique_retarded_common_carrier where
  formalizes @ "claim:retarded-sector-uniqueness-agrees-for-global-maxwell-and-caticha-klein-gordon-evolution",
  supported_by @ "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.eq_retarded_of_solves",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.retarded_common_carrier",
  requires @ "assumption:field-lies-in-the-declared-retarded-sector-and-solves-the-intrinsic-sourced-equation",
  caveat @ "claim:uniqueness-is-relative-to-the-explicit-retarded-sector-not-an-unconditional-global-cauchy-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.causal_hadamard_localAtlas_chain where
  formalizes @ "claim:caticha-hadamard-global-maxwell-causal-evolution-is-independent-of-compatible-local-levi-civita-atlas",
  supported_by @ "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator_solves_homogeneous_for_localLeviCivitaAtlas",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.causal_hadamard_globalMaxwell_chain",
  requires @ "assumption:two-compatible-local-levi-civita-atlases-global-green-data-regularity-common-carrier-and-hadamard-data",
  caveat @ "claim:atlas-independence-does-not-supply-green-hyperbolicity-hadamard-data-or-interacting-qft"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.retarded_advanced_localAtlas_common_carrier where
  formalizes @ "claim:retarded-and-advanced-caticha-maxwell-sourced-evolution-is-jointly-independent-of-compatible-local-levi-civita-atlas",
  supported_by @ "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves_for_localLeviCivitaAtlas",
  supported_by @ "lean:PseudoRiemannianMetric.localLeviCivitaAtlas_intrinsicMaxwellOn_iff",
  requires @ "assumption:two-compatible-local-levi-civita-atlases-two-sided-green-data-and-separate-retarded-advanced-regularity",
  caveat @ "claim:two-sided-atlas-independence-does-not-construct-green-operators-or-promote-the-free-carrier-to-interacting-qft"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.AdvancedUniqueIntrinsicMaxwellData.eq_advanced_of_solves where
  formalizes @ "claim:advanced-green-solution-is-unique-inside-an-explicit-advanced-support-sector",
  supported_by @ "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.advanced_solves",
  requires @ "assumption:advanced-sector-membership-and-wave-operator-injectivity-on-that-sector",
  caveat @ "claim:sector-relative-uniqueness-not-an-unconditional-global-cauchy-or-green-existence-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.AdvancedUniqueIntrinsicMaxwellData.unique_advanced_common_carrier where
  formalizes @ "claim:advanced-sector-uniqueness-agrees-for-global-maxwell-and-caticha-klein-gordon-evolution",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.AdvancedUniqueIntrinsicMaxwellData.eq_advanced_of_solves",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.advanced_common_carrier",
  requires @ "assumption:advanced-sector-injectivity-sourced-solution-and-common-carrier-compatibility",
  caveat @ "claim:advanced-uniqueness-remains-relative-to-explicit-support-and-adapter-data"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumSourceLocalNetAdapter.localized_source_observable_isotony where
  formalizes @ "claim:continuum-source-localization-and-associated-observable-algebra-membership-are-jointly-isotone",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.LocalNet.isotony",
  requires @ "assumption:explicit-continuum-source-localization-and-observable-map-into-a-local-net",
  caveat @ "claim:localization-adapter-is-input-data-not-derived-from-the-two-point-function"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumSourceLocalNetAdapter.causalHadamard_localNet_properties where
  formalizes @ "claim:localized-caticha-sources-have-commuting-observables-at-causal-separation-alongside-hadamard-carrier-properties",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet.LocalNet.locality",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.causalHadamardCarrier_properties",
  requires @ "assumption:supplied-local-net-source-localization-observable-map-hadamard-data-and-cone-preserving-transport",
  caveat @ "claim:conditional-free-field-locality-bridge-not-a-construction-of-the-net-or-an-interacting-curved-spacetime-qft"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_tauFourier_carries_integralEquation where
  formalizes @ "claim:eq64-67-tau-fourier-transform-carries-parameterized-integral-fixed-point-to-fixed-mass-inhomogeneous-bethe-salpeter-equation",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq64-67",
  reuses @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ParametrizedDirac",
  requires @ "assumption:linear-tau-fourier-map-and-certified-interchange-with-the-interaction-kernel",
  caveat @ "claim:exact-intertwiner-consequence-not-a-proof-of-fourier-integrability-or-integral-exchange-for-arbitrary-kernels"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettSchwartzTauFourierAt_intertwines where
  formalizes @ "claim:actual-vector-valued-schwartz-tau-fourier-transform-commutes-with-a-tau-independent-continuous-interaction-operator",
  supported_by @ "lean:SchwartzMap.fourierTransformCLM",
  supported_by @ "lean:ContinuousLinearMap.integral_comp_comm",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:tau-independent-electromagnetic-potential",
  requires @ "assumption:complete-complex-banach-state-carrier-schwartz-tau-history-and-continuous-tau-independent-interaction",
  caveat @ "claim:proved-bochner-fourier-interchange-for-the-tau-independent-schwartz-sector-not-an-arbitrary-tau-dependent-kernel"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettSchwartzTauFourier_carries_integralEquation where
  formalizes @ "claim:eq64-67-concrete-schwartz-fourier-transform-carries-the-parameterized-fixed-point-equation-to-the-fixed-real-mass-bethe-salpeter-equation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettSchwartzTauFourierAt_intertwines",
  requires @ "assumption:vector-valued-schwartz-history-complete-state-carrier-and-continuous-tau-independent-interaction",
  caveat @ "claim:real-mass-schwartz-sector-with-tau-independent-interaction-not-the-most-general-distributional-or-tau-dependent-transform"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_boundState_is_massKernel_eigenstate where
  formalizes @ "claim:eq66-vanishing-transformed-free-term-turns-the-fixed-point-equation-into-a-nonzero-homogeneous-bethe-salpeter-eigenstate",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq66",
  requires @ "assumption:certified-tau-fourier-kernel-intertwiner-zero-bound-state-free-term-and-nonzero-transformed-state",
  caveat @ "claim:eigenvalue-one-is-the-fixed-point-normalization-not-a-newly-computed-physical-coupling"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettSchwartz_boundState_is_massKernel_eigenstate where
  formalizes @ "claim:eq66-concrete-schwartz-bound-state-is-a-nonzero-homogeneous-mass-kernel-eigenstate",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettSchwartzTauFourier_carries_integralEquation",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq66",
  requires @ "assumption:zero-transformed-free-term-and-nonzero-transformed-full-schwartz-state",
  caveat @ "claim:eigenvalue-one-is-fixed-point-normalization-and-does-not-by-itself-compute-the-physical-coupling-spectrum"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettConcatenatedCurrent_map where
  formalizes @ "claim:continuous-linear-spacetime-operations-commute-with-finite-tau-current-concatenation",
  supported_by @ "lean:ContinuousLinearMap.intervalIntegral_comp_comm",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq6",
  requires @ "assumption:interval-integrable-current-and-continuous-linear-spacetime-operation",
  caveat @ "claim:finite-interval-bochner-interchange-full-real-line-concatenation-needs-an-improper-integral-limit"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_integrated_continuity_eq_boundaryFlux where
  formalizes @ "claim:eq2-integrated-in-tau-gives-spacetime-divergence-equal-to-endpoint-density-flux",
  supported_by @ "lean:intervalIntegral.integral_eq_sub_of_hasDerivAt",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq2:eq6",
  requires @ "assumption:strong-tau-derivative-interval-integrability-and-local-five-current-continuity",
  caveat @ "claim:exact-finite-interval-balance-not-automatic-decay-at-infinite-tau"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_concatenatedCurrent_conserved where
  formalizes @ "claim:eq6-matching-endpoint-density-and-local-five-current-continuity-imply-conserved-concatenated-four-current",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_integrated_continuity_eq_boundaryFlux",
  requires @ "assumption:local-continuity-integrable-tau-derivative-and-vanishing-or-periodic-boundary-flux",
  caveat @ "claim:boundary-condition-is-explicit-and-is-not-inferred-for-arbitrary-parameterized-states"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_concatenatedMaxwellCurrent_conserved where
  formalizes @ "claim:tau-concatenation-preserves-conservation-of-the-maxwell-current-derived-from-an-antisymmetric-faraday-tensor",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant.fourCurrent_conserved",
  reuses @ "lean:intervalIntegral.integral_finsetSum",
  requires @ "assumption:componentwise-interval-integrability-of-the-tau-indexed-maxwell-current",
  caveat @ "claim:momentum-space-finite-interval-maxwell-current-not-a-construction-of-bennett-semiclassical-two-particle-potentials"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_wholeLine_continuity_eq_boundaryFlux where
  formalizes @ "claim:eq2-whole-real-line-tau-integration-gives-eq6-divergence-as-incoming-minus-outgoing-density-boundary-flux",
  supported_by @ "lean:MeasureTheory.integral_of_hasDerivAt_of_tendsto",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq2:eq6",
  requires @ "assumption:global-tau-derivative-integrability-and-two-parameter-endpoint-limits",
  caveat @ "claim:whole-line-result-with-explicit-decay-data-not-automatic-for-arbitrary-parameterized-dirac-states"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_wholeLine_concatenatedCurrent_conserved where
  formalizes @ "claim:eq6-the-actual-whole-line-concatenated-current-is-divergence-free-when-the-density-vanishes-at-both-tau-ends",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_wholeLine_continuity_eq_boundaryFlux",
  requires @ "assumption:local-five-current-continuity-integrable-tau-derivative-and-zero-density-limits-at-plus-and-minus-infinity",
  caveat @ "claim:conservation-is-derived-under-the-paper-boundary-condition-not-asserted-without-asymptotic-control"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_factorized_marginalCurrent_eq_oneParticle where
  formalizes @ "claim:eq50-53-a-factorized-two-particle-current-marginalizes-to-the-one-particle-concatenated-current-for-a-normalized-spectator",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq50-53",
  supported_by @ "lean:MeasureTheory.integral_const_mul",
  requires @ "assumption:distinguishable-factorized-state-and-normalized-complex-spectator-density",
  caveat @ "claim:factorized-marginal-reduction-not-the-entangled-two-particle-dirac-current-construction"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_quadraticCurrent_neg_invariant where
  formalizes @ "claim:eq48-51-fermionic-swap-sign-cancels-in-every-quadratic-current-so-the-current-is-bosonic-under-state-permutation",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq48:eq50-51",
  reuses @ "lean:ContinuousLinearMap.map_neg",
  requires @ "assumption:complex-inner-product-state-carrier-and-continuous-linear-current-operator",
  caveat @ "claim:algebraic-sign-invariance-not-a-full-spin-statistics-theorem-or-construction-of-the-two-body-wavefunction"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_factorized_operatorCurrent_marginal_eq_oneParticle where
  formalizes @ "claim:eq50-53-normalized-spectator-marginal-of-a-factorized-operator-quadratic-current-is-the-one-particle-current",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_factorized_marginalCurrent_eq_oneParticle",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq50-53",
  requires @ "assumption:factorized-state-continuous-linear-current-operator-and-normalized-spectator-amplitude",
  caveat @ "claim:operator-current-specialization-for-factorized-states-not-a-reduction-of-entangled-exchange-terms"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_antisymmetrized_quadraticCurrent_expansion where
  formalizes @ "claim:eq48-antisymmetrized-two-fermion-quadratic-current-splits-into-two-diagonal-and-two-exchange-interference-terms",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq48:eq50-51",
  reuses @ "lean:InnerProductSpace.inner_sub_left",
  requires @ "assumption:complex-inner-product-carrier-and-continuous-linear-current-operator",
  caveat @ "claim:exact-operator-current-expansion-but-not-a-construction-of-interacting-two-dirac-particle-solutions"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_antisymmetrized_quadraticCurrent_swap_invariant where
  formalizes @ "claim:eq48-51-full-antisymmetrized-current-including-interference-is-invariant-under-particle-factor-swap",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_quadraticCurrent_neg_invariant",
  requires @ "assumption:antisymmetrized-direct-minus-exchange-state-and-quadratic-current-operator",
  caveat @ "claim:fermionic-sign-cancellation-in-a-quadratic-observable-not-a-general-spin-statistics-proof"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_dirac_antisymmetrized_marginalCurrent_expansion where
  formalizes @ "claim:eq48:eq50-51-concrete-dirac-marginal-current-retains-both-exchange-interference-terms",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_antisymmetrized_quadraticCurrent_expansion",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq48:eq50-51",
  requires @ "assumption:measurable-spectator-carrier-and-direct-minus-exchange-four-spinor-amplitudes",
  caveat @ "claim:exact-pointwise-under-bochner-integral-expansion-not-a-proof-of-integrability-or-an-interacting-wave-equation"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_sharpMass_axialTauTerm where
  formalizes @ "claim:eq85-sharp-mass-tau-phase-and-adjoint-phase-produce-the-exact-two-i-m-pseudoscalar-term",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq85:eq87",
  caveat @ "claim:exact-sharp-mass-phase-algebra-not-a-derivation-of-the-local-five-current-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_sharpMass_axialDivergence where
  formalizes @ "claim:eq85-to-eq87-local-five-current-continuity-implies-the-sharp-mass-axial-divergence-minus-two-i-m-pseudoscalar-law",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_sharpMass_axialTauTerm",
  requires @ "assumption:bennett-local-axial-five-current-continuity-for-the-sharp-mass-mode",
  caveat @ "claim:classical-mass-divergence-consequence-not-the-one-loop-adler-bell-jackiw-anomaly"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_sharpMass_axialDivergence_concatenated where
  formalizes @ "claim:eq87-whole-line-tau-concatenation-of-the-sharp-mass-axial-divergence-pulls-out-minus-two-i-m",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_sharpMass_axialDivergence",
  supported_by @ "lean:MeasureTheory.integral_const_mul",
  requires @ "assumption:pointwise-sharp-mass-axial-continuity-on-the-tau-line",
  caveat @ "claim:exact-bochner-integration-consequence-and-not-a-proof-of-integrability-or-loop-renormalization"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettABJNormalization_eq_chargeSq_mul_pontryaginNormalization where
  formalizes @ "claim:eq88-adler-bell-jackiw-coefficient-minus-e-squared-over-four-pi-squared-equals-charge-squared-times-the-repo-pontryagin-normalization",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ChernSimons.PontryaginAnomaly.chernSimonsPontryaginNormalization",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq88",
  reuses @ "lean:Real.pi_ne_zero",
  caveat @ "claim:normalization-match-only-the-one-loop-triangle-anomaly-equation-is-not-derived-by-this-arithmetic-identity"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettABJAnomaly_eq_chargeSq_pontryaginDensity where
  formalizes @ "claim:eq88-one-loop-axial-divergence-in-the-shared-electromagnetic-hodge-pontryagin-convention",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettABJNormalization_eq_chargeSq_mul_pontryaginNormalization",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.hodgeStar2",
  requires @ "assumption:bennett-one-loop-abj-triangle-relation-for-the-supplied-field-and-axial-divergence",
  caveat @ "claim:concrete-hodge-carrier-and-normalization-rewrite-not-a-formal-loop-integral-or-renormalization-derivation"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettElectromagneticPontryaginDensity_faraday_gauge_invariant where
  formalizes @ "claim:eq88-electromagnetic-faraday-pontryagin-source-is-invariant-under-momentum-space-gradient-gauge-shifts",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday.faraday_gauge_invariant",
  reuses @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.hodgeStar2",
  caveat @ "claim:exact-field-strength-gauge-invariance-not-the-quantum-anomaly-calculation"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettABJ_from_renormalizedOddOneLoopAction where
  formalizes @ "claim:dimensionless-chiral-derivative-of-the-renormalized-parity-odd-one-loop-action-produces-the-abj-hodge-pontryagin-density",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction.qedYukawaOdd_hasDerivAt_pseudoscalar",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettABJNormalization_eq_chargeSq_mul_pontryaginNormalization",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq88",
  requires @ "assumption:nonzero-scalar-mass-chart-and-the-paper-level-renormalized-odd-one-loop-effective-lagrangian",
  caveat @ "claim:analytic-derivative-of-an-existing-renormalized-one-loop-action-not-a-construction-of-the-regularized-fermion-determinant-or-interacting-continuum-qed"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettABJ_oneLoopResponse_faraday_gauge_invariant where
  formalizes @ "claim:the-one-loop-derived-hodge-pontryagin-response-is-invariant-under-momentum-space-gradient-gauge-shifts",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettABJ_from_renormalizedOddOneLoopAction",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettElectromagneticPontryaginDensity_faraday_gauge_invariant",
  caveat @ "claim:exact-gauge-invariance-of-the-derived-regulated-response-within-the-existing-one-loop-effective-action-model"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bassetto_fredholmSolvability_iff where
  formalizes @ "claim:eq6-finite-dimensional-coefficient-equation-is-solvable-exactly-when-the-source-is-orthogonal-to-the-adjoint-kernel-obstructions",
  supported_by @ "lean:LinearMap.orthogonal_range",
  supported_by @ "paper:bassetto-ciccariello-tonin-1965:eq6",
  requires @ "assumption:finite-dimensional-complex-inner-product-coefficient-carrier",
  caveat @ "claim:exact-fredholm-orthogonality-criterion-but-the-paper-kernel-and-recurrence-source-must-still-be-instantiated"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bassetto_uniqueCoefficient_of_compact_of_not_eigenvalue where
  formalizes @ "claim:compact-kernel-fredholm-alternative-gives-a-unique-recurrence-coefficient-for-every-source-away-from-a-nonzero-eigenvalue",
  supported_by @ "lean:IsCompactOperator.hasEigenvalue_or_mem_resolventSet",
  supported_by @ "lean:ContinuousLinearMap.isUnit_iff_bijective",
  supported_by @ "paper:bassetto-ciccariello-tonin-1965:eq3-9",
  requires @ "assumption:compact-continuous-bethe-salpeter-kernel-nonzero-spectral-parameter-and-absence-of-that-eigenvalue",
  caveat @ "claim:unique-off-spectrum-coefficient-solver-not-a-proof-that-the-physical-ladder-kernel-is-compact"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyFiniteModeKernelOperator_isCompact where
  formalizes @ "claim:every-finite-mode-cutkosky-kernel-operator-is-compact",
  supported_by @ "lean:isCompactOperator_of_locallyCompactSpace_dom",
  requires @ "assumption:finite-number-of-collocation-nodes",
  caveat @ "claim:finite-dimensional-compactness-not-a-proof-of-compactness-for-the-continuum-cutkosky-kernel"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyFiniteMode_uniqueCoefficient_of_not_eigenvalue where
  formalizes @ "claim:concrete-finite-mode-cutkosky-recurrence-has-a-unique-coefficient-for-every-source-off-the-nonzero-spectrum",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyFiniteModeKernelOperator_isCompact",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bassetto_uniqueCoefficient_of_compact_of_not_eigenvalue",
  requires @ "assumption:nonzero-spectral-parameter-which-is-not-an-eigenvalue-of-the-finite-mode-operator",
  caveat @ "claim:discretized-fredholm-solver-not-existence-or-convergence-of-the-paper-continuum-solution"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyContinuumKernelOperator_isCompact where
  formalizes @ "claim:the-separable-continuum-kernel-is-a-compact-rank-one-operator-on-the-l2-carrier",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyKernel_eq_separable",
  supported_by @ "lean:InnerProductSpace.rankOne_def'",
  supported_by @ "lean:isCompactOperator_of_locallyCompactSpace_dom",
  requires @ "assumption:square-integrable-numerator-and-reciprocal-denominator-factors-on-the-selected-measure-space",
  caveat @ "claim:genuine-continuum-compactness-for-the-separable-kernel-but-l2-membership-and-pole-avoidance-remain-analytic-domain-requirements"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyContinuumKernelOperator_apply where
  formalizes @ "claim:the-continuum-rank-one-operator-acts-by-the-l2-inner-product-bochner-integral-coefficient",
  supported_by @ "lean:MeasureTheory.L2.inner_def",
  supported_by @ "lean:InnerProductSpace.rankOne_apply",
  requires @ "assumption:square-integrable-cutkosky-factor-representatives",
  caveat @ "claim:exact-continuum-integral-action-on-the-l2-carrier-not-a-completeness-theorem-for-bound-states"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyContinuumKernelOperator_tendsto where
  formalizes @ "claim:l2-convergence-of-both-separable-kernel-factors-implies-operator-norm-convergence-of-the-continuum-kernel-operators",
  supported_by @ "lean:InnerProductSpace.rankOne",
  requires @ "assumption:l2-convergence-of-numerator-and-reciprocal-denominator-approximants",
  caveat @ "claim:operator-norm-convergence-criterion-not-a-proof-that-a-particular-quadrature-or-cutoff-satisfies-the-l2-premises"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyNumeratorFactorFn_memLp where
  formalizes @ "claim:the-actual-one-plus-z-numerator-factor-is-square-integrable-on-every-finite-symmetric-relative-energy-interval",
  supported_by @ "lean:MeasureTheory.MemLp.of_bound",
  requires @ "assumption:nonnegative-interval-radius",
  caveat @ "claim:exact-measure-theoretic-l2-membership-with-uniform-bound-one-plus-r"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyDenominatorInvFactorFn_memLp where
  formalizes @ "claim:the-actual-reciprocal-one-plus-z-denominator-factor-is-square-integrable-on-the-pole-free-interval-minus-r-to-r",
  supported_by @ "lean:MeasureTheory.MemLp.of_bound",
  requires @ "assumption:zero-less-than-or-equal-to-r-and-r-strictly-less-than-one",
  caveat @ "claim:exact-measure-theoretic-l2-membership-with-the-pole-excluded-and-uniform-bound-one-over-one-minus-r"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyPoleFreeContinuumOperator_isCompact where
  formalizes @ "claim:the-fully-instantiated-continuum-operator-built-from-the-proved-pole-free-l2-factors-is-compact",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyNumeratorFactorFn_memLp",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyDenominatorInvFactorFn_memLp",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyContinuumKernelOperator_isCompact",
  requires @ "assumption:pole-free-radius-zero-less-than-or-equal-to-r-less-than-one",
  caveat @ "claim:genuine-compact-continuum-operator-for-cutkosky-eq16-on-the-restricted-relative-energy-carrier"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyPoleFree_inner_eq_denominatorIntegral where
  formalizes @ "claim:the-l2-inner-product-coefficient-equals-the-integral-of-the-actual-reciprocal-denominator-factor-times-the-wavefunction",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyDenominatorInvFactorL2_coeFn",
  requires @ "assumption:pole-free-radius-zero-less-than-or-equal-to-r-less-than-one",
  caveat @ "claim:representative-level-bochner-integral-identity-on-the-restricted-lebesgue-measure"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyPoleFreeContinuumOperator_ae_eq_kernelIntegral where
  formalizes @ "claim:the-fully-instantiated-l2-operator-acts-almost-everywhere-by-the-original-eq16-kernel-integral",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyKernel_eq_separable",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.cutkoskyPoleFree_inner_eq_denominatorIntegral",
  requires @ "assumption:pole-free-radius-zero-less-than-or-equal-to-r-less-than-one-and-an-l2-wavefunction",
  caveat @ "claim:exact-continuum-kernel-action-and-compactness-not-a-proof-of-the-full-four-dimensional-bethe-salpeter-spectrum-or-bound-state-completeness"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettTwoDiracCentralSolution_schrodinger where
  formalizes @ "claim:exact-sixteen-component-two-dirac-central-interaction-evolution-solves-i-times-dpsi-dtau-equals-e1-plus-e2-plus-v-times-psi",
  supported_by @ "lean:NormedSpace.hasDerivAt_exp_smul_const",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:parametrized-two-particle-sector",
  requires @ "assumption:scalar-central-interaction-channel-with-constant-mode-energies",
  caveat @ "claim:exact-interacting-central-channel-solution-not-an-arbitrary-spacetime-dependent-photon-exchange-or-full-bethe-salpeter-solution"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettTwoDiracCentralSolution_preserves_antisymmetry where
  formalizes @ "claim:the-exact-interacting-central-two-dirac-evolution-preserves-the-fermionic-exchange-odd-sector",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettTwoDiracCentralSolution_schrodinger",
  requires @ "assumption:antisymmetric-initial-state-and-scalar-central-interaction",
  caveat @ "claim:exchange-sector-preservation-for-the-exact-solvable-channel-not-a-scattering-or-bound-state-completeness-result"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.rasheedNLEDExcitation_antisymmetric where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.rasheedNLEDExcitation
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.rasheedNLEDSource_conserved where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.rasheedNLEDSource
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_wholeLine_vectorCurrent_conserved where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettWholeLineVectorCurrent
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_rasheed_commonSource_conserved where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.BennettRasheedNLEDSourceCompatible,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettWholeLineVectorCurrent
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettRasheedElectricCharge_swap_invariant where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettRasheedElectricCharge
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettRasheedElectricChargeVariation_swap_invariant where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettRasheedElectricChargeVariation
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.rasheed_nledFirstLaw_from_surfaceVariations where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.SatisfiesRasheedNLEDFirstLaw
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettRasheed_nledFirstLaw_exchange_iff where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.SatisfiesRasheedNLEDFirstLaw,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettRasheedElectricChargeVariation
  ]

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.rasheedNLEDExcitation_antisymmetric where
  formalizes @ "claim:rasheed-eq2-11-a-times-f-plus-b-times-hodge-star-f-remains-an-antisymmetric-two-form",
  supported_by @ "paper:rasheed-nonlinear-electrodynamics-black-hole-mechanics-hep-th-9702087v2:eq2-11",
  reuses @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.hodgeStar2",
  reuses @ "lean:Physlib.QFT.Lattice.LatticeTopologicalCharge.leviCivita4_swap_12",
  requires @ "assumption:four-dimensional-real-antisymmetric-field-strength-and-pointwise-nled-coefficients",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:pointwise-four-component-hodge-carrier-not-a-global-lorentzian-black-hole-field-solution"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.rasheedNLEDSource_conserved where
  formalizes @ "claim:the-fourier-symbol-divergence-current-built-from-rasheed-nonlinear-excitation-is-conserved",
  supported_by @ "paper:rasheed-nonlinear-electrodynamics-black-hole-mechanics-hep-th-9702087v2:eq2-7:eq2-11",
  reuses @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CovariantMaxwellLambShift.maxwell_current_conserved",
  requires @ "assumption:antisymmetric-field-strength-and-pointwise-rasheed-constitutive-coefficients",
  epistemic_status @ "conditional-model",
  caveat @ "claim:proves-k-dot-j-equals-zero-not-rasheed-source-free-exterior-equation-j-equals-zero-and-not-existence-of-a-stationary-black-hole-background"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_wholeLine_vectorCurrent_conserved where
  formalizes @ "claim:bennett-eq2-and-eq6-the-actual-whole-line-concatenated-four-vector-current-is-conserved",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq2:eq6",
  reuses @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_wholeLine_concatenatedCurrent_conserved",
  requires @ "assumption:local-five-current-continuity-componentwise-integrability-and-vanishing-density-at-both-tau-ends",
  epistemic_status @ "conditional-model",
  caveat @ "claim:derived-vector-conservation-under-explicit-boundary-data-not-automatic-for-arbitrary-parametrized-dirac-states"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_rasheed_commonSource_conserved where
  formalizes @ "claim:bennett-concatenated-current-and-the-sourced-matter-region-extension-of-rasheed-nled-excitation-form-one-conserved-source",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.rasheedNLEDSource_conserved",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq6",
  supported_by @ "paper:rasheed-nonlinear-electrodynamics-black-hole-mechanics-hep-th-9702087v2:eq2-7",
  requires @ "assumption:explicit-bennett-rasheed-source-compatibility-and-antisymmetric-field-strength",
  epistemic_status @ "conditional-model",
  caveat @ "claim:the-source-compatibility-is-a-visible-physical-premise-and-matching-to-rasheed-source-free-electrovac-exterior-is-not-derived"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettRasheedElectricCharge_swap_invariant where
  formalizes @ "claim:bennett-fermionic-exchange-sign-cancels-before-an-arbitrary-nonlinear-nled-response-and-rasheed-horizon-flux-are-applied",
  supported_by @ "paper:bennett-spin-statistics-relativistic-quantum-mechanics-2015:antisymmetric-two-particle-state",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq48-53",
  supported_by @ "paper:rasheed-nonlinear-electrodynamics-black-hole-mechanics-hep-th-9702087v2:eq5-4",
  reuses @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_quadraticCurrent_neg_invariant",
  requires @ "assumption:supplied-current-operator-nonlinear-field-response-and-horizon-flux-map",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:exchange-order-independence-for-every-supplied-response-not-a-construction-of-that-response-a-horizon-or-a-black-hole-charge"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.rasheed_nledFirstLaw_from_surfaceVariations where
  formalizes @ "claim:rasheed-eq5-1-eq5-5-and-eq5-15-cancel-the-potential-and-angular-velocity-variation-terms-and-yield-the-nled-black-hole-first-law-eq5-16",
  supported_by @ "paper:rasheed-nonlinear-electrodynamics-black-hole-mechanics-hep-th-9702087v2:eq5-1:eq5-5:eq5-15:eq5-16",
  requires @ "assumption:rasheed-stationary-horizon-surface-variation-identities",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:exact-algebraic-cancellation-from-the-paper-identities-without-a-smarr-homogeneity-assumption-not-a-construction-of-the-geometric-variation-identities"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettRasheed_nledFirstLaw_exchange_iff where
  formalizes @ "claim:the-rasheed-nled-first-law-is-independent-of-the-exchange-order-used-to-represent-bennett-antisymmetrized-two-fermion-endpoint-states",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettRasheedElectricChargeVariation_swap_invariant",
  supported_by @ "paper:bennett-spin-statistics-relativistic-quantum-mechanics-2015:exchange-antisymmetry",
  supported_by @ "paper:rasheed-nonlinear-electrodynamics-black-hole-mechanics-hep-th-9702087v2:eq5-16",
  requires @ "assumption:supplied-current-to-field-response-horizon-flux-and-stationary-horizon-first-law-data",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:exchange-order-equivalence-only-the-first-law-remains-conditional-on-rasheed-horizon-data-and-no-black-hole-is-derived-from-the-bennett-state"

zil_file_contract physlib.entropicSpine.bennettRasheedNLED where
  promises "Bennett's relativistic spin-statistics carrier supplies an exchange-odd two-fermion state whose quadratic current is exchange-even. Bennett's first-quantized local five-current continuity and explicit tau-endpoint decay derive conservation of the whole-line concatenated four-current. Rasheed's pointwise nonlinear excitation aF+b-star-F is an antisymmetric two-form and therefore has a conserved Fourier-symbol divergence current; the stronger source-free exterior equation is separately represented by setting that current to zero. Under a visible sourced matter-region compatibility premise the Bennett and excitation currents coincide. Because the fermionic sign cancels before the supplied nonlinear response and horizon-flux maps are applied, the resulting electric-charge variation and Rasheed first-law proposition are independent of exchange ordering. Rasheed's surface-variation identities algebraically cancel the electric-potential and angular-velocity variation terms to Eq. 5.16 without a Smarr homogeneity premise."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettQuadraticCurrent",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettWholeLineVectorCurrent",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.SatisfiesRasheedSourceFreeNLED",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.BennettRasheedNLEDSourceCompatible",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.SatisfiesRasheedNLEDFirstLaw",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.hodgeStar2",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CovariantMaxwellLambShift.maxwellCurrent"
  ]
  forbids_substitutes [
    "claiming that a Bennett two-fermion state constructs a stationary nonlinear-electrodynamic black-hole solution or horizon",
    "hiding the Bennett-current-to-Rasheed-excitation compatibility or the nonlinear response and horizon-flux carrier maps",
    "identifying conservation k-dot-J equals zero with Rasheed's source-free exterior equation J equals zero",
    "promoting the pointwise Fin-4 Fourier-symbol conservation theorem to a global Lorentzian horizon theorem"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.rasheedNLEDExcitation_antisymmetric,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.rasheedNLEDSource_conserved,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_wholeLine_vectorCurrent_conserved,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_rasheed_commonSource_conserved,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettRasheedElectricCharge_swap_invariant,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettRasheedElectricChargeVariation_swap_invariant,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.rasheed_nledFirstLaw_from_surfaceVariations,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettRasheed_nledFirstLaw_exchange_iff
  ]

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bassettoAnalyticLightlikeSeries_zero where
  formalizes @ "claim:the-convergent-epsilon-power-series-is-normalized-to-the-vacuum-like-state-at-epsilon-zero",
  supported_by @ "paper:bassetto-ciccariello-tonin-1965:eq3-4",
  requires @ "assumption:coefficient-zero-is-the-identity-map",
  caveat @ "claim:normalization-identity-not-existence-of-the-fredholm-coefficients"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bassettoAnalyticLightlikeSeries_intertwines where
  formalizes @ "claim:the-full-convergent-analytic-series-intertwines-vacuum-like-and-lightlike-bethe-salpeter-kernels",
  supported_by @ "lean:ContinuousLinearMap.map_tsum",
  supported_by @ "paper:bassetto-ciccariello-tonin-1965:eq3-9",
  requires @ "assumption:summable-coefficient-series-and-coefficientwise-fredholm-kernel-recurrence",
  caveat @ "claim:the-recurrence-and-summability-remain-paper-specific-inputs-not-properties-of-arbitrary-kernels"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bassettoAnalyticSeries_preserves_eigenvalue where
  formalizes @ "claim:a-nonzero-value-of-the-convergent-fredholm-series-preserves-the-vacuum-like-kernel-eigenvalue",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bassettoAnalyticLightlikeSeries_intertwines",
  requires @ "assumption:vacuum-like-eigenstate-and-nonzero-analytic-series-value",
  caveat @ "claim:nonvanishing-away-from-epsilon-zero-is-explicit-because-an-analytic-vector-family-may-have-isolated-zeros"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bassettoAnalytic_vacuumLike_implies_lightLike_sameEigenvalue where
  formalizes @ "claim:coefficientwise-analytic-fredholm-series-at-nonzero-null-total-momentum-preserves-the-vacuum-like-eigenvalue",
  supported_by @ "paper:bassetto-ciccariello-tonin-1965:eq3-9",
  supported_by @ "lean:Lorentz.Vector.lightLike_iff_norm_sq_zero",
  requires @ "assumption:nonzero-null-momentum-convergent-recurrent-coefficient-family-and-nonzero-series-value",
  caveat @ "claim:conditional-equal-mass-scalar-ladder-result-not-a-general-bethe-salpeter-continuation-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bassetto_lightlike_momentum_sq_zero where
  formalizes @ "claim:the-selected-nonzero-lightlike-total-momentum-has-zero-minkowski-square",
  supported_by @ "lean:Lorentz.Vector.lightLike_iff_norm_sq_zero",
  requires @ "assumption:nonzero-lightlike-total-momentum-from-the-bassetto-ladder-lift-certificate",
  caveat @ "claim:causal-character-identity-not-existence-of-a-lightlike-continuation"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bassetto_vacuumLike_implies_lightLike_sameEigenvalue where
  formalizes @ "claim:eq3-9-certified-analytic-fredholm-lift-preserves-the-bethe-salpeter-kernel-eigenvalue-from-vacuum-like-to-nonzero-lightlike-total-momentum",
  supported_by @ "paper:bassetto-ciccariello-tonin-1965:eq3-9",
  requires @ "assumption:equal-mass-scalar-ladder-analytic-expansion-fredholm-solvability-injective-lift-and-kernel-intertwining",
  caveat @ "claim:conditional-paper-specific-continuation-not-a-theorem-for-arbitrary-bethe-salpeter-kernels"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bassetto_preserves_cutkoskyEigenvalue where
  formalizes @ "claim:bassetto-lightlike-continuation-preserves-the-existing-wick-cutkosky-eigenvalue-N-times-N-plus-one",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution.cutkoskyEigenvalue_eq_casimir",
  requires @ "assumption:bassetto-ladder-lift-certificate-and-a-vacuum-like-cutkosky-eigenstate",
  caveat @ "claim:spectral-value-preservation-not-construction-or-completeness-of-the-bound-state-spectrum"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.lightlike_eigenstate_to_caticha where
  formalizes @ "claim:lightlike-bethe-salpeter-eigenstate-transports-to-a-nonzero-continuum-functional-schrodinger-generator-eigenmode",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.continuumSmearedSchrodingerGenerator",
  requires @ "assumption:injective-state-carrier-map-intertwining-the-lightlike-kernel-with-the-caticha-functional-generator",
  caveat @ "claim:conditional-carrier-transport-not-a-canonical-identification-of-first-quantized-and-field-functional-state-spaces"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettSchwartz_bassettoAnalytic_to_caticha where
  formalizes @ "claim:actual-schwartz-tau-fourier-bound-state-and-full-analytic-fredholm-series-produce-a-caticha-functional-generator-eigenmode",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq64-67",
  supported_by @ "paper:bassetto-ciccariello-tonin-1965:eq3-9",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettSchwartz_boundState_is_massKernel_eigenstate",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bassettoAnalytic_vacuumLike_implies_lightLike_sameEigenvalue",
  requires @ "assumption:zero-free-fourier-term-nonzero-mass-state-convergent-fredholm-recurrence-nonzero-series-and-injective-caticha-carrier-intertwiner",
  caveat @ "claim:concrete-fourier-and-infinite-series-chain-but-the-cross-formalism-caticha-state-map-remains-explicit-input-data"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_bassetto_catichaQED_gauge_covariant where
  formalizes @ "claim:any-linear-readout-of-the-transported-bethe-salpeter-state-obeys-the-existing-minimal-coupling-gauge-covariance-law",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.catichaQEDCovariantDerivative_gauge_covariant",
  supported_by @ "paper:caticha-entropic-dynamics-qed-2511.19238v1:eq58",
  requires @ "assumption:explicit-complex-linear-readout-of-the-continuum-functional-carrier",
  caveat @ "claim:exact-gauge-covariance-specialization-not-a-construction-of-an-interacting-qed-field"

zil attach Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennett_bassetto_caticha_curvedQED_chain where
  formalizes @ "claim:bennett-mass-sector-through-bassetto-lightlike-continuation-to-caticha-functional-evolution-global-intrinsic-maxwell-causal-evolution-and-hadamard-aqft-data",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq64-67",
  supported_by @ "paper:bassetto-ciccariello-tonin-1965:eq3-9",
  supported_by @ "paper:caticha-entropic-dynamics-qed-2511.19238v1:eq58",
  supported_by @ "paper:ipek-entropic-dynamics-relativistic-quantum-fields-curved-spacetime:local-functional-schrodinger-equation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.causal_hadamard_globalMaxwell_chain",
  requires @ "assumption:bennett-tau-fourier-kernel-intertwiner-vanishing-bound-state-free-term-nonzero-mass-state-bassetto-analytic-lift-caticha-generator-intertwiner-state-to-maxwell-source-identification-global-green-pair-and-hadamard-cone-data",
  caveat @ "claim:conditional-free-field-common-carrier-chain-not-an-interacting-curved-spacetime-qed-construction-or-new-numerical-prediction"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.localContinuity_of_solves where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.operator,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.vectorCurrent
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.localContinuity_of_solves where
  formalizes @ "claim:a-section-valued-curved-parameterized-dirac-solution-obeys-bennett-local-five-current-continuity",
  epistemic_status @ "risky",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq1:eq2",
  reuses @ "lean:PseudoRiemannianMetric.CovariantDerivative",
  requires @ "assumption:a-curved-spinor-fiber-clifford-action-spin-covariant-derivative-and-the-associated-local-noether-identity",
  caveat @ "claim:continuity-is-derived-from-the-dirac-equation-and-noether-compatibility-but-the-spin-structure-and-analytic-domain-remain-explicit-geometric-data"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.operator_gauge_covariant where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.operator,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.GaugeTransformation
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.operator_gauge_covariant where
  formalizes @ "claim:the-curved-bennett-minimally-coupled-parameterized-dirac-operator-is-gauge-covariant-under-the-spin-connection-product-rules",
  epistemic_status @ "risky",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq1",
  supported_by @ "paper:caticha-entropic-dynamics-qed-2511.19238v1:eq58",
  requires @ "assumption:unit-norm-local-phase-and-parameter-plus-spin-covariant-derivative-product-rules-for-the-transformed-potential",
  caveat @ "claim:exact-operator-covariance-on-the-selected-curved-spinor-carrier-not-a-construction-of-a-spin-structure-on-every-lorentzian-manifold"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.GaugeTransformation.transported_solution_continuity_and_current where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.operator,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.vectorCurrent
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.GaugeTransformation.transported_solution_continuity_and_current where
  formalizes @ "claim:a-unit-norm-local-gauge-phase-transports-curved-bennett-dirac-solutions-while-preserving-the-vector-current-and-deriving-the-transformed-local-continuity-law",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.operator_gauge_covariant",
  supported_by @ "paper:caticha-entropic-dynamics-qed-2511.19238v1:eq58",
  requires @ "assumption:the-selected-spin-covariant-and-parameter-derivatives-obey-the-explicit-gauge-product-rules",
  caveat @ "claim:solution-transport-current-invariance-and-continuity-are-derived-on-the-selected-carrier-not-a-universal-construction-of-a-spin-bundle-or-gauge-connection"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeCliffordAction_frame where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedFourCoframe,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeCliffordAction,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettGammaOperator
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeCliffordAction_frame where
  formalizes @ "claim:a-dual-spacetime-four-coframe-constructs-the-curved-bennett-clifford-action-from-the-canonical-four-by-four-gamma-representation-and-reduces-to-gamma-mu-on-frame-mu",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.Relativity.CliffordAlgebra.ofCliffordAlgebra",
  supported_by @ "lean:Matrix.mulVecLin",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq1",
  reuses @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.BennettDiracSpinor",
  requires @ "assumption:a-selected-global-four-frame-with-a-dual-real-coframe",
  caveat @ "claim:concrete-gamma-action-on-a-selected-trivialized-spinor-carrier-not-a-proof-that-every-lorentzian-manifold-is-parallelizable-or-admits-the-required-spin-structure"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeCliffordAction_frame_anticomm where
  at_level bridge_theorem
  must_mention [
    spaceTime.γ.diracMetricDiagonal,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeCliffordAction
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeCliffordAction_frame_anticomm where
  formalizes @ "claim:the-coframe-constructed-curved-bennett-action-satisfies-the-full-indexed-minkowski-clifford-anticommutation-law-on-every-selected-frame-pair",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:spaceTime.γ.anticommutation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettGammaOperator_anticomm",
  requires @ "assumption:a-selected-global-four-frame-with-an-exact-dual-coframe",
  caveat @ "claim:exact-clifford-law-on-the-selected-trivialized-four-spinor-carrier-not-existence-of-a-global-spin-structure-on-an-arbitrary-lorentzian-manifold"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeCliffordAction_anticomm where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeMinkowskiPair,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeCliffordAction
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeCliffordAction_anticomm where
  formalizes @ "claim:the-selected-curved-bennett-coframe-action-satisfies-the-minkowski-clifford-law-for-arbitrary-tangent-vectors-not-only-the-four-frame-generators",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:spaceTime.γ.anticommutation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettGammaContractMatrix_anticommutation",
  requires @ "assumption:a-selected-global-four-frame-with-an-exact-dual-real-coframe",
  caveat @ "claim:arbitrary-vector-clifford-closure-on-the-selected-trivialized-carrier-not-existence-of-a-spin-structure-or-a-global-parallelization"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettTetradSpinConnectionOperator_comm_gamma where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettTetradSpinConnectionOperator,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettTetradVectorConnectionOperator
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettTetradSpinConnectionOperator_comm_gamma where
  formalizes @ "claim:the-one-quarter-gamma-a-gamma-b-rigid-tetrad-spin-connection-is-compatible-with-clifford-multiplication-and-induces-the-vector-connection-action-on-gamma-d",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettGamma_bivector_commutator",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad.TetradConnection.rigid",
  requires @ "assumption:the-selected-tetrad-connection-is-rigid-and-metric-compatible-in-the-repositorys-all-lowered-sign-convention",
  caveat @ "claim:exact-spin-clifford-compatibility-on-the-concrete-four-spinor-representation-not-atlas-gluing-spin-lift-existence-or-essential-self-adjointness"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeSpinCovariantDerivative_frame where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettTetradSpinConnectionOperator,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeSpinCovariantDerivative
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeSpinCovariantDerivative_frame where
  formalizes @ "claim:the-curved-bennett-spin-derivative-is-constructed-as-the-ordinary-directional-derivative-plus-one-quarter-omega-ab-mu-gamma-a-gamma-b-with-omega-fixed-by-the-tetrad-koszul-identity",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettTetradSpinConnectionOperator_eq_koszul",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad.TetradConnection.koszul",
  requires @ "assumption:a-selected-dual-four-coframe-a-rigid-metric-compatible-tetrad-connection-and-an-ordinary-directional-spinor-derivative",
  caveat @ "claim:explicit-levi-civita-tetrad-spin-connection-constructor-on-a-trivialized-carrier-not-a-proof-of-spin-lift-existence-atlas-gluing-or-essential-self-adjointness"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causal_hadamard_chain where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causalPropagator,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.IsRegularOutsideCone,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.IsSingularOnCone
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causal_hadamard_chain where
  formalizes @ "claim:causal-cauchy-well-posedness-constructs-linear-curved-bennett-green-operators-whose-causal-difference-is-homogeneous-and-shares-an-exact-distributional-hadamard-wavefront-theorem",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.WellPosedCurvedParametrizedDiracCauchyData.toGreenData",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ContinuumSesquilinearHadamardTwoPoint.ofDistributionalTheorems_wavefront_eq",
  requires @ "assumption:curved-dirac-cauchy-existence-causal-support-sector-uniqueness-and-model-specific-localized-fourier-regularity-off-and-singularity-on-the-hadamard-cone",
  caveat @ "claim:green-linearity-and-the-homogeneous-causal-equation-are-derived-but-global-hyperbolic-dirac-existence-and-propagation-of-singularities-remain-visible-analytic-inputs"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causal_dirac_hadamard_propagation where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causalPropagator,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causalSesquilinearHadamardCarrier
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causal_dirac_hadamard_propagation where
  formalizes @ "claim:the-constructed-retarded-minus-advanced-curved-dirac-propagator-both-solves-the-homogeneous-bennett-equation-and-pulls-a-sesquilinear-hadamard-field-carrier-back-to-sources-preserving-hermiticity-positivity-ccr-and-positive-frequency-microlocal-support",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causalPropagator_solves_homogeneous",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ContinuumSesquilinearHadamardTwoPoint.pullback_properties",
  requires @ "assumption:a-field-hadamard-carrier-the-exact-pulled-back-real-symplectic-form-and-a-positive-cone-preserving-covector-transport",
  caveat @ "claim:the-two-point-carrier-is-now-constructed-through-the-dirac-causal-propagator-rather-than-merely-conjoined-but-global-hyperbolicity-and-model-specific-propagation-of-singularities-remain-explicit-inputs"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causal_dirac_distributional_hadamard_propagation where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causalPropagator,
    Physlib.Distribution.distributionalWavefrontSet
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causal_dirac_distributional_hadamard_propagation where
  formalizes @ "claim:the-curved-dirac-causal-green-difference-is-homogeneous-and-its-source-two-point-distribution-has-the-exact-field-hadamard-wavefront-cone-derived-through-bidirectionally-covering-localized-fourier-probe-families",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalProbeTransport.wavefront_eq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causalPropagator_solves_homogeneous",
  requires @ "assumption:curved-dirac-green-data-field-regularity-off-and-singularity-on-the-hadamard-cone-a-source-distribution-representing-the-causal-pullback-and-bidirectional-distributional-probe-transport-matching-base-regions-cones-and-pairings",
  caveat @ "claim:exact-wavefront-transport-between-proved-probe-families-not-an-unconditional-propagation-of-singularities-theorem-probe-completeness-theorem-or-construction-of-global-hyperbolic-dirac-green-data"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causalPropagator_localContinuity where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causalPropagator,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.vectorCurrent
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causalPropagator_localContinuity where
  formalizes @ "claim:the-retarded-minus-advanced-curved-bennett-dirac-field-obeys-the-local-five-current-continuity-law",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causalPropagator_solves_homogeneous",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq2",
  requires @ "assumption:causal-dirac-green-data-derived-from-sectorwise-cauchy-existence-and-uniqueness-plus-the-local-noether-identity",
  caveat @ "claim:the-green-noether-conservation-link-is-derived-but-existence-of-the-globally-hyperbolic-dirac-green-data-remains-an-explicit-pde-input"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.existsUnique_selfConsistentSolution where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.update,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.IsSelfConsistentSolution
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.existsUnique_selfConsistentSolution where
  formalizes @ "claim:a-contracting-curved-dirac-maxwell-green-update-has-a-unique-self-consistent-solution-satisfying-both-geometric-field-equations-with-bennett-whole-line-current",
  epistemic_status @ "risky",
  supported_by @ "lean:ContractingWith.fixedPoint_isFixedPt",
  supported_by @ "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq5:eq6",
  requires @ "assumption:complete-field-carriers-causal-dirac-and-maxwell-green-data-and-a-strict-contraction-bound-for-the-coupled-picard-update",
  caveat @ "claim:constructive-semilinear-semiclassical-fixed-point-theorem-on-selected-continuum-domains-not-a-nonperturbative-operator-valued-qed-measure-or-unconditional-large-data-global-existence-result"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.existsUnique_selfConsistentSolution_of_responseBounds where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.ResponseBounds,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.IsSelfConsistentSolution
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.existsUnique_selfConsistentSolution_of_responseBounds where
  formalizes @ "claim:componentwise-dirac-response-current-and-bounded-maxwell-green-estimates-with-max-of-kd-and-green-norm-times-kj-below-one-derive-the-unique-self-consistent-curved-maxwell-dirac-solution",
  epistemic_status @ "risky",
  supported_by @ "lean:LipschitzWith.prodMk",
  supported_by @ "lean:ContinuousLinearMap.lipschitz",
  supported_by @ "lean:ContractingWith.fixedPoint_isFixedPt",
  supported_by @ "paper:bennett-first-quantized-electrodynamics-1406.0750v3:eq5:eq6",
  requires @ "assumption:a-lipschitz-dirac-response-a-lipschitz-exact-concatenated-current-source-a-bounded-maxwell-retarded-green-operator-and-the-explicit-small-response-inequality",
  caveat @ "claim:the-full-map-contraction-is-now-derived-from-component-estimates-but-those-model-specific-pde-estimates-and-large-data-global-control-are-not-claimed-unconditionally"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.existsUnique_selfConsistentSolution_of_differentialBounds where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.DifferentialResponseBounds,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.IsSelfConsistentSolution
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.existsUnique_selfConsistentSolution_of_differentialBounds where
  formalizes @ "claim:uniform-frechet-derivative-bounds-on-the-dirac-response-and-exact-concatenated-current-source-derive-the-component-lipschitz-estimates-and-hence-the-unique-curved-maxwell-dirac-fixed-point",
  epistemic_status @ "risky",
  supported_by @ "lean:lipschitzWith_of_nnnorm_fderiv_le",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.DifferentialResponseBounds.toResponseBounds",
  requires @ "assumption:global-real-frechet-differentiability-uniform-derivative-bounds-a-bounded-retarded-maxwell-operator-and-the-explicit-small-response-inequality",
  caveat @ "claim:the-lipschitz-and-contraction-layers-are-derived-from-standard-mean-value-analysis-but-the-model-specific-uniform-pde-derivative-estimates-remain-visible-inputs"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.picard_converges_to_selfConsistentSolution where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.ResponseBounds,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.update,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.IsSelfConsistentSolution
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.picard_converges_to_selfConsistentSolution where
  formalizes @ "claim:every-seed-of-the-small-response-curved-maxwell-dirac-picard-map-converges-to-a-self-consistent-solution-with-explicit-apriori-geometric-and-aposteriori-computable-error-bounds",
  epistemic_status @ "risky",
  supported_by @ "lean:ContractingWith.tendsto_iterate_fixedPoint",
  supported_by @ "lean:ContractingWith.apriori_dist_iterate_fixedPoint_le",
  supported_by @ "lean:ContractingWith.aposteriori_dist_iterate_fixedPoint_le",
  requires @ "assumption:complete-field-carriers-component-response-bounds-and-max-of-kd-and-green-norm-times-kj-strictly-below-one",
  caveat @ "claim:constructive-small-response-iteration-with-certified-errors-not-arbitrary-large-data-global-existence-renormalized-operator-qed-or-a-numerical-discretization-error-theorem"

zil_file_contract physlib.entropicSpine.bennettCurvedContinuumQED where
  promises "Bennett's first-quantized electrodynamics is represented on a genuine section-valued M times R_tau carrier. A selected dual four-coframe constructs its Clifford action from the canonical four-by-four gamma representation and satisfies the Minkowski anticommutation law for arbitrary tangent vectors. The repository's rigid tetrad Koszul identity constructs the one-quarter omega-ab-mu gamma-a gamma-b spin connection, whose commutator with gamma-d is proved to equal the induced vector-connection action, and hence the spin covariant derivative from an ordinary directional derivative. The curved minimally coupled Dirac operator is gauge covariant; gauge transport preserves its current and derives the transformed continuity law. Its equation derives local five-current conservation, including for the retarded-minus-advanced causal field. Causal Cauchy existence and uniqueness derive complex-linear retarded and advanced Green operators; the causal difference pulls a corrected sesquilinear Hadamard field carrier back to sources, and a bidirectional transport between independently indexed field/source probes derives equality of their computed distributional wavefront sets. Uniform Frechet derivative estimates derive component response bounds; max(K_D, norm(G_ret) K_J) below one constructs the unique self-consistent Dirac-Maxwell solution, and every Picard seed converges to it with explicit a priori and a posteriori errors."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedFourCoframe",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad.TetradConnection",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettTetradSpinConnectionOperator",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettTetradSpinConnectionOperator_comm_gamma",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.WellPosedCurvedParametrizedDiracCauchyData",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.ResponseBounds",
    "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.DifferentialResponseBounds",
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.wavefront_eq_iff",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalProbeTransport.wavefront_eq",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ContinuumSesquilinearHadamardTwoPoint.pullback"
  ]
  forbids_substitutes [
    "replacing the spacetime-and-parameter continuum by a Fin-4 sampled action",
    "calling supplied spinor-bundle or Cauchy-existence data an unconditional construction from pseudo-Riemannian geometry",
    "calling a declared cone a computed Hadamard wavefront set without proving localized-Fourier regularity off the cone and singularity on it",
    "claiming a nonperturbative interacting QED measure or arbitrary-large-data global existence from the contraction theorem"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.localContinuity_of_solves,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeCliffordAction_frame,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeCliffordAction_frame_anticomm,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeCliffordAction_anticomm,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.bennettTetradSpinConnectionOperator_comm_gamma,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.coframeSpinCovariantDerivative_frame,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.operator_gauge_covariant,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracData.GaugeTransformation.transported_solution_continuity_and_current,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causalPropagator_localContinuity,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causal_hadamard_chain,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causal_dirac_hadamard_propagation,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedParametrizedDiracGreenData.causal_dirac_distributional_hadamard_propagation,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.existsUnique_selfConsistentSolution_of_differentialBounds,
    Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge.CurvedMaxwellDiracCoupling.picard_converges_to_selfConsistentSolution
  ]

zil attach Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.PressureProjectedNonlinearData.exists_local_nonlinearGalerkin_solution where
  formalizes @ "claim:picard-lindelof-local-solution-for-pressure-projected-galerkin-navier-stokes",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.PressureProjectedNonlinearData.nonlinearGalerkin_energy_hasDerivAt",
  caveat @ "claim:finite-dimensional-local-existence-not-leray-hopf-weak-existence-or-global-three-dimensional-regularity"

zil attach Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.PressureProjectedNonlinearData.exists_local_nonlinearGalerkin_energy_dissipating_solution where
  formalizes @ "claim:local-pressure-projected-galerkin-navier-stokes-solution-with-antitone-kinetic-energy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup.PressureProjectedNonlinearData.nonlinearGalerkin_energy_antitoneOn",
  caveat @ "claim:finite-dimensional-local-dissipation-not-infinite-dimensional-global-existence-or-regularity"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleDirac_isSelfAdjoint where
  formalizes @ "claim:the-maximal-fourier-domain-circle-dirac-is-a-genuinely-self-adjoint-unbounded-partial-linear-operator-on-l2-of-the-circle",
  supported_by @ "lean:AddCircle.fourierBasis",
  supported_by @ "lean:LinearPMap.IsSymmetric.isSelfAdjoint_iff",
  caveat @ "claim:continuum-infinite-dimensional-fourier-model-not-yet-the-full-circle-spectral-triple-because-compact-resolvent-and-noncentral-smooth-coordinate-algebra-commutators-remain-to-be-packaged"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleDirac_closedFredholm where
  formalizes @ "claim:the-continuum-circle-dirac-has-closed-range-and-finite-dimensional-kernel-and-cokernel",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleDirac_range_eq_circleZeroMode_ker",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleDirac_ker_eq_span_zeroMode",
  caveat @ "claim:actual-closed-unbounded-fredholm-circle-operator-not-the-general-elliptic-fredholm-theorem-on-compact-manifolds-with-boundary"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleDirac_index_eq_zero where
  formalizes @ "claim:the-continuum-circle-dirac-index-is-zero-because-both-kernel-and-cokernel-are-the-one-dimensional-zero-mode",
  supported_by @ "lean:LinearMap.index_eq_finrank_sub",
  caveat @ "epistemic:exact-operator-index-computation-not-the-atiyah-singer-or-aps-characteristic-form-formula"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderSobolevTrace_comp_extension where
  formalizes @ "claim:the-infinite-fourier-cylinder-h1-to-boundary-l2-trace-has-an-explicit-bounded-constant-normal-right-inverse",
  supported_by @ "lean:lp.inner_single_right",
  supported_by @ "lean:Real.summable_one_div_nat_pow",
  caveat @ "claim:genuine-anisotropic-cylinder-sobolev-trace-splitting-not-yet-the-chartwise-hs-to-hs-minus-half-global-manifold-trace-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderSobolevTraceAt_comp_extension where
  formalizes @ "claim:for-every-s-greater-than-one-half-the-fractional-normal-fourier-trace-has-a-bounded-right-inverse",
  supported_by @ "lean:Real.summable_one_div_nat_add_rpow",
  supported_by @ "lean:lp.inner_single_right",
  caveat @ "claim:sharp-normal-sobolev-threshold-on-the-infinite-cylinder-the-tangential-hs-minus-half-weight-and-manifold-chart-globalization-remain-separate"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderSobolevTraceAt_surjective where
  formalizes @ "claim:the-fractional-cylinder-trace-is-surjective-at-every-exponent-s-greater-than-one-half",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderSobolevTraceAt_comp_extension",
  caveat @ "claim:sharp-local-cylinder-surjectivity-not-yet-the-global-manifold-boundary-trace-and-extension-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderSobolevTrace_surjective where
  formalizes @ "claim:every-l2-circle-boundary-datum-is-the-trace-of-an-infinite-dimensional-cylinder-h1-field",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderSobolevTrace_comp_extension",
  caveat @ "claim:onto-local-cylinder-trace-not-a-collar-atlas-globalization-over-an-arbitrary-manifold-with-boundary"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleAPSBoundarySpace_isClosed where
  formalizes @ "claim:the-nonnegative-circle-dirac-spectral-subspace-is-the-closed-range-of-a-bounded-idempotent-fourier-projection",
  supported_by @ "lean:ContinuousLinearMap.IsIdempotentElem.isClosed_range",
  caveat @ "claim:genuine-continuum-boundary-spectral-space-for-the-circle-not-an-arbitrary-boundary-manifold-calculus"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleAPSBoundaryCondition_isClosed where
  formalizes @ "claim:any-continuous-sobolev-trace-into-the-circle-boundary-space-induces-a-closed-aps-boundary-realization",
  supported_by @ "lean:ContinuousLinearMap.isClosed_ker",
  requires @ "assumption:a-continuous-sobolev-trace-map-from-the-selected-bulk-space",
  caveat @ "claim:generic-closed-boundary-interface-the-circle-cylinder-instance-is-now-constructed-but-arbitrary-manifold-globalization-remains"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderAPSBoundaryCondition_isClosed where
  formalizes @ "claim:the-nonnegative-circle-dirac-condition-on-the-proved-infinite-cylinder-sobolev-trace-defines-a-closed-bulk-domain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderSobolevTrace_surjective",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleAPSBoundarySpace_isClosed",
  caveat @ "claim:concrete-continuum-cylinder-aps-domain-not-yet-the-general-elliptic-regularity-or-characteristic-form-index-formula"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderAPSBoundaryConditionAt_isClosed where
  formalizes @ "claim:at-every-sobolev-exponent-s-greater-than-one-half-the-circle-spectral-projection-defines-a-closed-fractional-cylinder-domain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleCylinderSobolevTraceAt_surjective",
  supported_by @ "lean:ContinuousLinearMap.isClosed_ker",
  caveat @ "claim:sharp-local-fractional-aps-domain-not-yet-a-global-elliptic-boundary-value-index-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleHeatTrace_poisson where
  formalizes @ "claim:exact-poisson-transformation-of-the-continuum-circle-heat-trace",
  supported_by @ "lean:Real.tsum_exp_neg_mul_int_sq",
  caveat @ "claim:exact-flat-circle-identity-not-the-general-curved-seeley-dewitt-coefficient-recursion"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleHeatTrace_tendsto_one_atTop where
  formalizes @ "claim:jacobi-theta-remainder-decays-and-fixes-the-flat-circle-leading-heat-kernel-coefficient",
  supported_by @ "lean:isBigO_at_im_infty_jacobiTheta_sub_one",
  caveat @ "claim:flat-one-dimensional-continuum-asymptotic-not-an-arbitrary-dimensional-curved-manifold-expansion"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesCircleSpectralGeometry.circleDimensionZeta_residue_one where
  formalizes @ "claim:the-circle-dirac-dimension-spectrum-has-a-pole-at-one-with-residue-two",
  supported_by @ "lean:riemannZeta_residue_one",
  caveat @ "claim:actual-meromorphic-circle-spectrum-not-a-proof-of-the-general-dimension-spectrum-theorem-or-aps-boundary-index-formula"

/-! ## BJ. Open-system entropy arrow: unconditional discrete and conditional differential layers -/

zil_theorem_intent
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.dissipative_orbit_antitone where
  at_level bridge_theorem
  must_mention [QuantumInfo.Finite.entropicProperTime,
    CPTPMap]

zil_theorem_intent
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.discreteSpohnProduction_add_processed_eq where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.discreteSpohnProduction,
    QuantumInfo.Finite.entropicProperTime,
    CPTPMap
  ]

zil attach
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.discreteSpohnProduction_add_processed_eq where
  formalizes @ "claim:one-cptp-step-relative-entropy-loss-plus-residual-equals-the-initial-relative-entropy-for-a-fixed-reference",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.entropicProperTime_DPI",
  caveat @ "claim:genuine-finite-discrete-spohn-balance-not-the-continuous-time-generator-derivative-or-a-type-iii-semigroup-theorem"

zil attach
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.discreteSpohnProduction_equilibrium_zero where
  formalizes @ "claim:discrete-relative-entropy-production-vanishes-when-the-equilibrium-reference-is-a-channel-fixed-point",
  epistemic_status @ "risky",
  supported_by @ "lean:QuantumInfo.Finite.entropicProperTime_self",
  caveat @ "claim:fixed-point-normalization-for-the-relative-entropy-contraction-not-a-claim-that-the-repository-jump-intensity-vanishes"

zil_theorem_intent
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.discreteSpohnProduction_equilibrium_zero where
  at_level structural
  must_mention [
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.discreteSpohnProduction,
    CPTPMap
  ]

zil_theorem_intent
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.accumulatedDiscreteSpohnProduction_add_residual_eq where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.accumulatedDiscreteSpohnProduction,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.channelOrbit,
    QuantumInfo.Finite.entropicProperTime
  ]

zil attach
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.accumulatedDiscreteSpohnProduction_add_residual_eq where
  formalizes @ "claim:accumulated-discrete-production-plus-residual-relative-entropy-telescopes-to-the-initial-relative-entropy",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.discreteSpohnProduction_add_processed_eq",
  caveat @ "claim:exact-finite-step-cptp-budget-without-strict-convergence-a-log-sobolev-rate-or-a-continuous-time-limit"

zil attach
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.replacement_discreteSpohnProduction_eq_relativeEntropy where
  formalizes @ "claim:the-replacement-channel-produces-the-entire-initial-relative-entropy-in-one-step",
  epistemic_status @ "risky",
  supported_by @ "lean:CPTPMap.replacement_apply",
  caveat @ "claim:nontrivial-finite-channel-witness-not-a-generic-strict-positivity-or-unique-equilibrium-theorem"

zil_theorem_intent
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.replacement_discreteSpohnProduction_eq_relativeEntropy where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.discreteSpohnProduction,
    QuantumInfo.Finite.entropicProperTime,
    CPTPMap.replacement
  ]

zil_theorem_intent
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.relativeEntropy_antitone where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.IsFixedPoint,
    QuantumInfo.Finite.entropicProperTime
  ]

zil attach
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.relativeEntropy_antitone where
  formalizes @ "claim:relative-entropy-to-a-fixed-reference-is-antitone-along-a-positive-time-cptp-semigroup",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.entropicProperTime_DPI",
  caveat @ "claim:algebraic-positive-time-semigroup-h-theorem-without-strong-continuity-a-gkls-generator-or-a-relative-entropy-derivative"

zil_theorem_intent
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction_add_residual_eq where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.stateAt,
    QuantumInfo.Finite.entropicProperTime
  ]

zil attach
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction_add_residual_eq where
  formalizes @ "claim:positive-time-interval-production-plus-residual-relative-entropy-equals-the-earlier-relative-entropy",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.relativeEntropy_antitone",
  caveat @ "claim:exact-ordered-interval-balance-in-extended-nonnegative-reals-not-an-infinitesimal-rate-formula"

zil_theorem_intent
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction_cocycle where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.IsFixedPoint
  ]

zil attach
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction_cocycle where
  formalizes @ "claim:entropy-production-is-additive-over-adjacent-ordered-positive-time-intervals",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction_add_residual_eq",
  caveat @ "claim:algebraic-cocycle-for-relative-entropy-decrements-not-a-proof-of-absolute-continuity-or-existence-of-a-production-density"

zil_theorem_intent
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction_zero_of_fixed_state where
  at_level structural
  must_mention [
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.IsFixedPoint
  ]

zil attach
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction_zero_of_fixed_state where
  formalizes @ "claim:positive-time-interval-production-vanishes-on-a-semigroup-fixed-trajectory",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.IsFixedPoint",
  caveat @ "claim:fixed-trajectory-normalization-not-a-detailed-balance-uniqueness-or-strict-relaxation-result"

zil_theorem_intent
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.initial_recovery where
  at_level structural
  must_mention [
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.stateAt
  ]

zil attach
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.initial_recovery where
  formalizes @ "claim:c0-cptp-semigroup-orbits-recover-the-initial-state-at-zero-time",
  epistemic_status @ "risky",
  supported_by @ "lean:Continuous.continuousAt",
  caveat @ "claim:strong-continuity-consequence-on-a-packaged-carrier-not-existence-of-an-interacting-gkls-flow"

zil_theorem_intent
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.identity_hasInfinitesimalGenerator_zero where
  at_level structural
  must_mention [
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.identity,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.HasInfinitesimalGenerator
  ]

zil attach
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.identity_hasInfinitesimalGenerator_zero where
  formalizes @ "claim:the-identity-c0-cptp-semigroup-has-zero-right-infinitesimal-generator",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Filter.tendsto_const_nhds",
  caveat @ "claim:concrete-zero-generator-boundary-case-not-construction-of-a-nontrivial-gkls-semigroup"

zil_theorem_intent
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.generator_eq_zero_of_fixedPoint where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.HasInfinitesimalGenerator,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.IsFixedPoint
  ]

zil attach
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.generator_eq_zero_of_fixedPoint where
  formalizes @ "claim:a-state-fixed-by-a-c0-cptp-semigroup-lies-in-the-kernel-of-every-identified-right-generator",
  epistemic_status @ "risky",
  supported_by @ "lean:Filter.tendsto_nhds_unique",
  caveat @ "claim:fixed-point-to-generator-kernel-implication-not-the-converse-or-a-uniqueness-and-relaxation-theorem"

zil_theorem_intent
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.fixedPoint_isGKLSSteady where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.HasGKLSGenerator,
    Physlib.QuantumMechanics.Lindblad.IsGKLSSteady,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.IsFixedPoint
  ]

zil attach
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.fixedPoint_isGKLSSteady where
  formalizes @ "claim:a-semigroup-fixed-state-is-gkls-steady-when-the-right-generator-is-explicitly-identified-with-the-gkls-operator",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.generator_eq_zero_of_fixedPoint",
  caveat @ "claim:conditional-fixed-point-to-steady-direction-not-existence-of-the-flow-or-the-converse"

zil_theorem_intent
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finiteSpohnIntervalProduction_rate_tendsto where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finiteSpohnIntervalProduction,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.IsFiniteSpohnTrajectory,
    Physlib.QuantumMechanics.Lindblad.gklsEntropicRate
  ]

zil attach
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finiteSpohnIntervalProduction_rate_tendsto where
  formalizes @ "claim:finite-interval-free-energy-production-per-unit-time-converges-from-the-right-to-the-postulated-spohn-rate",
  epistemic_status @ "risky",
  supported_by @ "lean:HasDerivAt.tendsto_slope_zero_right",
  caveat @ "claim:conditional-on-is-finite-spohn-trajectory-and-does-not-identify-the-nonzero-steady-state-jump-intensity-with-spohn-production"

zil_theorem_intent
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finite_spohn_H_theorem where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.IsFiniteSpohnTrajectory,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finiteGibbsFreeEnergyGap
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finite_differential_spohn_freeEnergyGap_antitoneOn where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.IsFiniteDifferentialSpohnTrajectoryOn,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finiteGibbsFreeEnergyGap
  ]

zil attach
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finite_differential_spohn_freeEnergyGap_antitoneOn where
  formalizes @ "claim:a-nonnegative-model-supplied-spohn-production-density-implies-antitone-finite-gibbs-free-energy-on-a-convex-time-domain",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:antitoneOn_of_hasDerivWithinAt_nonpos",
  caveat @ "claim:the-model-must-prove-the-exact-derivative-identity-and-nonnegativity-of-its-own-production-density"

zil_theorem_intent
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.operator_differential_spohn_gap_antitoneOn where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.IsOperatorDifferentialSpohnTrajectoryOn
  ]

zil attach
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.operator_differential_spohn_gap_antitoneOn where
  formalizes @ "claim:an-operator-relative-entropy-gap-with-actual-finite-umegaki-state-witnesses-an-exact-derivative-law-and-nonnegative-production-is-antitone-on-a-convex-time-domain",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.differential_spohn_gap_antitoneOn",
  caveat @ "claim:the-interface-requires-a-concrete-channel-to-prove-the-operator-witness-derivative-and-production-sign"

zil_theorem_intent
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_hasInfinitesimalGenerator where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.HasInfinitesimalGenerator,
    QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLMatrix
  ]

zil attach
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_hasInfinitesimalGenerator where
  formalizes @ "claim:the-explicit-one-level-channels-form-a-c0-cptp-semigroup-with-right-generator-exactly-equal-to-the-concrete-loss-gain-gksl-operator",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.oneLevelGKSLOrbit_eq_oneLevelChannelAt",
  caveat @ "claim:finite-dimensional-one-level-realization-not-an-unbounded-continuum-semigroup-result"

zil_theorem_intent
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropyTrajectory_eq where
  at_level bridge_theorem
  must_mention [
    QuantumInfo.Finite.entropicProperTime,
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup,
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropyTrajectory
  ]

zil attach
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropyTrajectory_eq where
  formalizes @ "claim:the-full-coherence-one-level-scalar-gap-is-pointwise-identical-to-the-real-umegaki-relative-entropy-of-the-actual-c0-cptp-channel-state",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.entropicProperTime_qubit_stationary_toReal",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_coherenceNormSq"

zil_theorem_intent
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropy_hasDerivAt where
  at_level bridge_theorem
  must_mention [
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropyTrajectory,
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorSpohnProduction
  ]

zil attach
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropy_hasDerivAt where
  formalizes @ "claim:the-full-coherence-finite-qubit-umegaki-relative-entropy-derivative-along-the-exact-one-level-channel-is-minus-the-explicit-operator-spohn-production-at-positive-time",
  epistemic_status @ "conditional-model",
  requires @ "assumption:nonzero-initial-coherence-and-faithful-stationary-reference",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropyTrajectory_eq",
  caveat @ "claim:not-an-arbitrary-dimensional-frechet-matrix-log-or-type-iii-derivative-theorem"

zil_theorem_intent
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorSpohnHTheorem where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.IsOperatorDifferentialSpohnTrajectoryOn,
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropyTrajectory,
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorSpohnProduction
  ]

zil attach
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorSpohnHTheorem where
  formalizes @ "claim:the-exact-coherent-one-level-c0-channel-has-an-actual-operator-umegaki-witness-exact-relative-entropy-derivative-nonnegative-coherence-sensitive-spohn-production-and-antitone-gap",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.operator_differential_spohn_gap_antitoneOn",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorSpohnProduction_nonneg",
  caveat @ "claim:finite-qubit-model-with-supplied-rates-not-a-microscopic-calibration-or-continuum-type-iii-result"

zil_theorem_intent
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelExactDiagonal_isFiniteDifferentialSpohnTrajectoryOn where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.IsFiniteDifferentialSpohnTrajectoryOn,
    QuantumMechanics.LindbladDrivenLeads.oneLevelBinaryGibbsSystem,
    QuantumMechanics.LindbladDrivenLeads.entropyProductionRate
  ]

zil attach
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelExactDiagonal_isFiniteDifferentialSpohnTrajectoryOn where
  formalizes @ "claim:the-exact-diagonal-orbit-of-the-one-level-c0-channel-satisfies-the-differential-spohn-identity-with-the-binary-kl-production-density",
  epistemic_status @ "conditional-model",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.binaryKL_predictedOccupation_hasDerivAt",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_occState",
  caveat @ "claim:finite-diagonal-instance-not-the-full-coherence-carrying-operator-relative-entropy-derivative"

zil_theorem_intent
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelExactDiagonal_freeEnergyGap_antitoneOn where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finiteGibbsFreeEnergyGap,
    QuantumMechanics.LindbladDrivenLeads.oneLevelBinaryGibbsSystem,
    QuantumMechanics.LindbladDrivenLeads.RateData.predictedOccupation
  ]

zil attach
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelExactDiagonal_freeEnergyGap_antitoneOn where
  formalizes @ "claim:the-exact-one-level-diagonal-free-energy-deficit-is-antitone-on-nonnegative-physical-time",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finite_differential_spohn_freeEnergyGap_antitoneOn",
  supported_by @ "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelExactDiagonal_entropyProductionRate_nonneg"

zil_file_contract physlib.entropicSpine.openSystemEntropyArrow where
  promises "The public spine exposes the rigorous open-system layers without conflating them: quantum relative-entropy data processing gives an unconditional discrete H-theorem and its exact production telescope; an algebraic positive-time CPTP semigroup gives time-ordered contraction, fixed-trajectory vanishing, and an exact interval-production cocycle; and a strongly continuous carrier gives initial recovery, an explicit right-generator predicate, fixed-point-to-GKLS-steadiness under generator identification, and a conditional interval-to-rate limit. The explicit one-level loss/gain channels form a nontrivial C0 CPTP semigroup whose right generator is exactly the concrete GKSL matrix operator. Its diagonal orbit instantiates the binary-KL differential Spohn interface, while its genuinely coherent orbit now instantiates the operator interface: the scalar formula is pointwise the actual finite Umegaki entropy, its positive-time derivative is minus an explicit coherence-sensitive production, that production is nonnegative by data processing, and the gap is antitone. This does not claim an arbitrary-dimensional Frechet matrix-log derivative or a type-III theorem. Grad's classical control case supplies an exact collision H-kernel and an explicit homogeneous BGK C0 semigroup with generator, quadratic Hermite entropy decay, and an unconditional interval-production rate. A symmetric-qubit NESS proves that the current positive jump-intensity functional cannot be the Spohn derivative because it is nonzero at a genuine steady state."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.entropicProperTime_DPI",
    "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.dissipative_orbit_antitone",
    "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.discreteSpohnProduction_add_processed_eq",
    "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.discreteSpohnProduction_equilibrium_zero",
    "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.accumulatedDiscreteSpohnProduction_add_residual_eq",
    "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.relativeEntropy_antitone",
    "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction_add_residual_eq",
    "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction_cocycle",
    "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.initial_recovery",
    "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.HasInfinitesimalGenerator",
    "lean:Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.generator_eq_zero_of_fixedPoint",
    "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.HasGKLSGenerator",
    "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.fixedPoint_isGKLSSteady",
    "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.IsFiniteDifferentialSpohnTrajectoryOn",
    "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finite_differential_spohn_freeEnergyGap_antitoneOn",
    "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.IsOperatorDifferentialSpohnTrajectoryOn",
    "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.operator_differential_spohn_gap_antitoneOn",
    "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finiteSpohnIntervalProduction_rate_tendsto",
    "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.gradCollisionProduction_nonneg",
    "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.gradBGKRelaxation_hasDerivAt",
    "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.gradBGKIntervalProduction_hasDerivAt_zero",
    "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.IsFiniteSpohnTrajectory",
    "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finite_spohn_H_theorem",
    "lean:Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.symmetricNess_isSteady_but_not_currentSpohnTrajectory",
    "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_hasInfinitesimalGenerator",
    "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropyTrajectory_eq",
    "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropy_hasDerivAt",
    "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorSpohnProduction_nonneg",
    "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorSpohnHTheorem",
    "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelExactDiagonal_isFiniteDifferentialSpohnTrajectoryOn",
    "lean:QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelExactDiagonal_freeEnergyGap_antitoneOn"
  ]
  forbids_substitutes [
    "claiming the finite jump-intensity functional automatically equals minus the derivative of operator relative entropy",
    "calling the nonzero steady-state jump intensity Spohn entropy production",
    "calling the exact finite-step telescope a continuous-time derivative theorem or a type-III semigroup result",
    "calling the algebraic positive-time carrier strongly continuous without supplying the c0 carrier",
    "claiming existence of a nontrivial gkls cptp semigroup merely from the c0 carrier",
    "identifying a right generator with the gkls operator without HasGKLSGenerator",
    "claiming that the interval cocycle supplies an absolutely continuous entropy-production density",
    "calling the conditional interval-to-rate theorem unconditional spohn production for the jump intensity",
    "claiming the scalar homogeneous grad bgk control model proves propagation of molecular chaos or the nonlinear boltzmann-grad limit",
    "calling the one-mode quadratic hermite defect the full nonlinear f-log-f kinetic entropy",
    "claiming continuous-time type-III Spohn monotonicity from the discrete finite-dimensional data-processing theorem",
    "promoting the full finite-qubit coherence theorem to an arbitrary-dimensional Frechet matrix-log or type-III derivative theorem",
    "claiming convergence to a unique equilibrium or a logarithmic-Sobolev rate"
  ]
  witnessed_by [
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.dissipative_orbit_antitone,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.discreteSpohnProduction_add_processed_eq,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.discreteSpohnProduction_equilibrium_zero,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.accumulatedDiscreteSpohnProduction_add_residual_eq,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.replacement_discreteSpohnProduction_eq_relativeEntropy,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.relativeEntropy_antitone,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction_add_residual_eq,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction_cocycle,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPPositiveTimeSemigroup.intervalSpohnProduction_zero_of_fixed_state,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.initial_recovery,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.identity_hasInfinitesimalGenerator_zero,
    Physlib.Thermodynamics.QuantumRelativeEntropyArrow.CPTPC0Semigroup.generator_eq_zero_of_fixedPoint,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.fixedPoint_isGKLSSteady,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finiteSpohnIntervalProduction_rate_tendsto,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.gradCollisionProduction_nonneg,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.gradCollisionProduction_eq_zero_iff,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.gradBGKRelaxation_add,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.gradBGKRelaxation_hasDerivAt,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.gradLinearizedEntropy_along_bgk,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.gradBGKIntervalProduction_nonneg,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.gradBGKIntervalProduction_hasDerivAt_zero,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finite_differential_spohn_freeEnergyGap_antitoneOn,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.operator_differential_spohn_gap_antitoneOn,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.finite_spohn_H_theorem,
    Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem.symmetricNess_isSteady_but_not_currentSpohnTrajectory,
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelCPTPC0Semigroup_hasInfinitesimalGenerator,
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropyTrajectory_eq,
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorRelativeEntropy_hasDerivAt,
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelOperatorSpohnHTheorem,
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelExactDiagonal_isFiniteDifferentialSpohnTrajectoryOn,
    QuantumMechanics.LindbladDrivenLeads.RateData.oneLevelExactDiagonal_freeEnergyGap_antitoneOn
  ]

/-! ## BK. Caticha--Hadamard--AQFT--global-Maxwell causal carrier -/

zil_theorem_intent
    PseudoRiemannianMetric.WellPosedIntrinsicMaxwellCauchyData.retardedSolution_add where
  at_level structural
  must_mention [
    PseudoRiemannianMetric.WellPosedIntrinsicMaxwellCauchyData.retardedSolution
  ]

zil attach
    PseudoRiemannianMetric.WellPosedIntrinsicMaxwellCauchyData.retardedSolution_add where
  formalizes @ "claim:retarded-solution-existence-causal-sector-closure-and-uniqueness-force-additivity-of-the-solution-selector",
  epistemic_status @ "risky",
  supported_by @ "lean:PseudoRiemannianMetric.WellPosedIntrinsicMaxwellCauchyData.wave_retarded",
  requires @ "assumption:a-well-posed-causal-cauchy-theorem-supplying-retarded-existence-support-sector-membership-and-uniqueness",
  caveat @ "claim:linearity-is-derived-from-well-posedness-but-this-theorem-does-not-prove-that-global-hyperbolicity-alone-supplies-the-pde-existence-and-support-estimates"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.wellPosedCauchy_catichaKG_intrinsicMaxwell_chain where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.WellPosedIntrinsicMaxwellCauchyData.toIntrinsicMaxwellGreenData,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ComplexLinearIntrinsicMaxwellCarrier.toContinuumCatichaKGData,
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.wellPosedCauchy_catichaKG_intrinsicMaxwell_chain where
  formalizes @ "claim:causal-cauchy-existence-and-uniqueness-construct-retarded-and-advanced-green-maps-whose-common-complex-carrier-solves-both-caticha-kg-and-intrinsic-ricci-coupled-maxwell-equations",
  epistemic_status @ "risky",
  supported_by @ "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.retarded_solves",
  requires @ "assumption:well-posed-causal-cauchy-data-and-complex-linearity-on-the-selected-analytic-domain",
  caveat @ "claim:the-kg-maxwell-operator-equality-is-exact-on-the-constructed-common-carrier-not-an-identification-of-scalar-kg-and-vector-maxwell-fields-on-every-domain"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.wavefront_eq_iff where
  at_level bridge_theorem
  must_mention [
    Physlib.Distribution.distributionalWavefrontSet,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.IsRegularOutsideCone,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.IsSingularOnCone
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.wavefront_eq_iff where
  formalizes @ "claim:exact-distributional-hadamard-wavefront-equality-is-equivalent-to-localized-fourier-regularity-at-every-nonzero-covector-off-the-cone-and-singularity-at-every-covector-on-the-cone",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Distribution.distributionalWavefrontSet",
  requires @ "assumption:a-spacetime-distribution-a-localized-schwartz-probe-family-and-a-proposed-positive-frequency-cone",
  caveat @ "claim:exact-logical-characterization-of-the-computed-probe-relative-wavefront-set-not-a-proof-that-a-specific-curved-state-satisfies-either-analytic-side-or-that-the-probes-form-the-complete-hormander-system"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.Transport.isRegularOutsideCone where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.IsRegularOutsideCone,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.Transport.toData
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.Transport.isRegularOutsideCone where
  formalizes @ "claim:bidirectional-localized-fourier-probe-transport-preserves-microlocal-regularity-off-the-hadamard-cone",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalProbeTransport.regularAt_iff",
  requires @ "assumption:complete-bidirectional-probe-coverage-and-pairing-equality-plus-source-regularity-off-the-cone",
  caveat @ "claim:transport-of-an-established-localized-fourier-estimate-not-independent-construction-of-a-hadamard-state"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.Transport.isSingularOnCone where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.IsSingularOnCone,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.Transport.toData
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.Transport.isSingularOnCone where
  formalizes @ "claim:bidirectional-localized-fourier-probe-transport-preserves-microlocal-singularity-on-the-hadamard-cone",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalProbeTransport.regularAt_iff",
  requires @ "assumption:complete-bidirectional-probe-coverage-and-pairing-equality-plus-source-singularity-on-the-cone",
  caveat @ "claim:transport-of-an-established-failure-of-rapid-decay-not-independent-propagation-of-singularities-for-a-curved-field-equation"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ContinuumSesquilinearHadamardTwoPoint.ofDistributionalTheorems_wavefront_eq where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.IsRegularOutsideCone,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.IsSingularOnCone
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ContinuumSesquilinearHadamardTwoPoint.ofDistributionalTheorems_wavefront_eq where
  formalizes @ "claim:the-two-point-carrier-wavefront-is-computed-from-localized-fourier-decay-of-a-spacetime-distribution-and-equals-the-positive-frequency-hadamard-cone-exactly-from-regular-off-cone-and-singular-on-cone-theorems",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.Distribution.HasRapidFourierDecayOn",
  requires @ "assumption:the-localized-schwartz-probe-family-represents-the-required-chart-cutoff-conic-tests-with-regularity-proved-off-the-cone-and-singularity-proved-on-it",
  caveat @ "claim:the-constructor-no-longer-copies-an-arbitrary-cone-or-accepts-an-equality-certificate-but-propagation-of-singularities-for-a-specific-curved-spacetime-state-remains-a-model-specific-analytic-theorem"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ComplexLinearIntrinsicMaxwellCarrier.catichaKG_eq_intrinsicMaxwell where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ComplexLinearIntrinsicMaxwellCarrier.toContinuumCatichaKGData,
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.waveOperator
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ComplexLinearIntrinsicMaxwellCarrier.catichaKG_eq_intrinsicMaxwell where
  formalizes @ "claim:the-caticha-klein-gordon-operator-constructed-on-the-complex-linear-maxwell-domain-is-exactly-the-intrinsic-ricci-coupled-maxwell-wave-operator",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.realizes_wave",
  requires @ "assumption:complex-linearity-of-the-wave-retarded-and-advanced-maps-on-the-selected-common-domain",
  caveat @ "claim:operator-equality-is-by-the-shared-carrier-construction-and-does-not-prove-green-existence-on-an-arbitrary-pseudo-riemannian-manifold"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ContinuumSesquilinearHadamardTwoPoint.ofInnerProduct_self_ne_zero where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ContinuumSesquilinearHadamardTwoPoint.ofInnerProduct
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ContinuumSesquilinearHadamardTwoPoint.ofInnerProduct_self_ne_zero where
  formalizes @ "claim:a-nonzero-hilbert-field-has-a-nonzero-positive-sesquilinear-two-point-self-pairing",
  epistemic_status @ "risky",
  supported_by @ "lean:inner_self_ne_zero",
  caveat @ "claim:the-hilbert-constructor-fixes-the-sesquilinear-algebraic-carrier-but-a-real-distributional-wavefront-identification-remains-an-analytic-obligation"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.causalPropagator_eq_of_sameCarrier where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.causalPropagator
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.causalPropagator_eq_of_sameCarrier where
  formalizes @ "claim:shared-source-and-field-types-reduce-caticha-maxwell-pauli-jordan-compatibility-to-equality-of-the-wave-and-two-green-operators",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ofSameCarrier",
  caveat @ "claim:identity-adapter-removes-an-encoding-choice-but-does-not-prove-the-operator-equalities-or-green-existence"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.causal_hadamard_globalMaxwell_sameCarrier_chain where
  at_level bridge_theorem
  must_mention [
    PseudoRiemannianMetric.IntrinsicRicciCoupledMaxwellOn,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData.causalHadamardCarrier
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.causal_hadamard_globalMaxwell_sameCarrier_chain where
  formalizes @ "claim:shared-carrier-operator-compatibility-yields-one-caticha-hadamard-global-maxwell-causal-chain-without-a-separate-adapter-premise",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.causal_hadamard_globalMaxwell_chain",
  requires @ "assumption:global-green-data-hadamard-two-point-data-cone-preserving-transport-and-pointwise-equality-of-the-wave-retarded-and-advanced-operators",
  caveat @ "claim:same-carrier-capstone-does-not-construct-green-operators-hadamard-regularity-or-interacting-curved-qed"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalProbeTransport.wavefront_eq where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalProbeTransport,
    Physlib.Distribution.distributionalWavefrontSet
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalProbeTransport.wavefront_eq where
  formalizes @ "claim:bidirectional-coverage-of-base-and-conic-regions-together-with-two-way-equality-of-localized-fourier-pairings-preserves-the-computed-distributional-wavefront-set-across-different-test-spaces-and-probe-index-types",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Distribution.hasRapidFourierDecayOn_congr",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalProbeTransport.regularAt_iff",
  requires @ "assumption:bidirectional-probe-coverage-with-identical-base-regions-conic-regions-and-evaluated-distributional-pairings",
  caveat @ "claim:transport-relative-to-the-supplied-probe-families-not-proof-that-either-family-is-the-complete-hormander-chart-cutoff-system"

zil_file_contract physlib.entropicSpine.catichaHadamardGlobalMaxwell where
  promises "The public spine exposes the continuum Caticha--Klein--Gordon--Hadamard--AQFT--Maxwell chain on one causal carrier. Closed causal Sobolev sectors, coercive weak forms and Riesz source coordinates construct retarded and advanced Green operators by Lax--Milgram rather than storing them. Complex covariance and causal uniqueness promote those inverses and their Pauli--Jordan difference to genuine complex continuous maps with explicit graph-energy bounds on the concrete infinite-dimensional H1 C4 carrier. Both left- and right-inverse laws prove the exact Green complex: the causal kernel is the wave image of the common causal core, and the resulting source quotient embeds faithfully into homogeneous intrinsic Maxwell solutions. The Caticha KG operator is the same intrinsic Ricci-coupled Maxwell operator on that carrier. A corrected conjugate-linear-first-slot two-point distribution is pulled back through the exact constructed causal propagator; Hermiticity, positivity and the CCR law are derived, while bidirectional localized-Fourier probe transport carries proved regularity off and singularity on the source cone to an exact target Hadamard wavefront equality. The same energy-bounded causal field is transported across compatible Levi--Civita representatives by the atlas equivalence, not by conjoining unrelated local equations or an unrelated bilinear kernel."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaKGData",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ofSameCarrier",
    "lean:PseudoRiemannianMetric.WellPosedIntrinsicMaxwellCauchyData.toIntrinsicMaxwellGreenData",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ComplexLinearIntrinsicMaxwellCarrier.toContinuumCatichaKGData",
    "lean:Physlib.Distribution.distributionalWavefrontSet",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.wavefront_eq_iff",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.Transport.isRegularOutsideCone",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.Transport.isSingularOnCone",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalProbeTransport",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ContinuumSesquilinearHadamardTwoPoint.ofInnerProduct",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.toCoerciveSectorData",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.causalGreenComplex",
    "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.causalDistributionalHadamardTransport",
    "lean:Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition.pauliJordanPart",
    "lean:PseudoRiemannianMetric.IntrinsicMaxwellGreenData.causalPropagator",
    "lean:PseudoRiemannianMetric.intrinsicRicciCoupledMaxwellOn_atlas_iff"
  ]
  forbids_substitutes [
    "claiming existence of advanced or retarded Green operators from data that merely packages them",
    "claiming that pseudo-Riemannian geometry without a global hyperbolic PDE theorem supplies causal Cauchy existence or support estimates",
    "claiming that equal carrier types automatically make independently defined wave and Green operators equal",
    "calling a declared cone the computed distributional wavefront set of a curved-spacetime two-point distribution",
    "calling an arbitrary Fourier probe family the full Hormander chart-cutoff system without proving probe completeness",
    "using a complex-bilinear positive form where a conjugate-linear first slot is required",
    "conjoining-an-unrelated-hadamard-certificate-instead-of-pulling-the-two-point-distribution-through-the-constructed-causal-propagator",
    "claiming-atlas-independence-by-conjoining-two-local-equations-without-applying-the-levi-civita-atlas-equivalence",
    "supplying-an-independent-gauge-quotient-instead-of-deriving-the-kernel-as-the-wave-image-of-the-common-causal-core",
    "claiming spacelike support or a microlocal spectrum theorem from kernel antisymmetry alone",
    "claiming interacting curved-spacetime QED from a structural common-carrier bridge"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaHadamardMaxwellMicrocausality.caticha_hadamard_maxwell_microcausality,
    PseudoRiemannianMetric.WellPosedIntrinsicMaxwellCauchyData.retardedSolution_add,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.wellPosedCauchy_catichaKG_intrinsicMaxwell_chain,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalProbeTransport.wavefront_eq,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.wavefront_eq_iff,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.Transport.isRegularOutsideCone,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.DistributionalHadamardData.Transport.isSingularOnCone,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ContinuumSesquilinearHadamardTwoPoint.ofDistributionalTheorems_wavefront_eq,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ComplexLinearIntrinsicMaxwellCarrier.catichaKG_eq_intrinsicMaxwell,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.ContinuumSesquilinearHadamardTwoPoint.ofInnerProduct_self_ne_zero,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.causalPropagator_eq_of_sameCarrier,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram.ContinuumCatichaIntrinsicMaxwellAdapter.causal_hadamard_globalMaxwell_sameCarrier_chain,
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.toCoerciveSectorData,
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.causalGreenComplex,
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.ker_causalGreen_eq_causalWaveImage,
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.curvedHOneFour_causalSourceQuotient_phaseSpace,
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.curvedHOneFour_caticha_maxwell_causal_distributional_hadamard_propagation,
    Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GloballyHyperbolicGreenHadamard.MaxwellLaxMilgramGraphData.caticha_maxwell_causal_distributional_hadamard_atlas_chain
  ]

/-! ## BL. Continuum constrained antisymmetric-tensor gauge sector -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranContinuumTensorDualVector_gauge_invariant where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranContinuumTensorDualVector,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranContinuumTensorGaugeShift
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranContinuumTensorDualVector_conserved where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranContinuumDivergence
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranMaxwellTensorLagrangian_threePlusOne where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranMaxwellTensorLagrangian,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranCauchyLagrangian
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.VytheeswaranL2CauchyDatum.onConstraintSurface_iff_primaryPreserved where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.VytheeswaranL2CauchyDatum.IsOnConstraintSurface
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranFourierLegendreAction_eq_Eq325 where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranFourierLegendreAction,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranEq325HamiltonianDensity
  ]

zil_file_contract physlib.entropicSpine.continuumAntisymmetricTensorGauge where
  promises "The public spine exposes the continuum distributional antisymmetric-tensor sector: its Hodge-dual vector is gauge invariant and identically conserved, the exact Lorentzian three-plus-one split yields the canonical density, and the L2 Fourier Cauchy domain carries almost-everywhere secondary constraints and the spatially integrated Legendre identity."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:SpaceTime.distDeriv_commute",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranMaxwellTensorLagrangian_threePlusOne",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.VytheeswaranL2CauchyDatum",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranLegendreDensity_eq_Eq325"
  ]
  forbids_substitutes [
    "claiming a curved-manifold two-form gauge theory from a Minkowski distributional carrier",
    "claiming a global Dirac--Bergmann flow, BRST cohomology, or quantum functional measure",
    "claiming self-adjoint Hamiltonian evolution from integrability of the classical Fourier density"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranContinuumTensorDualVector_gauge_invariant,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranContinuumTensorDualVector_conserved,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranMaxwellTensorLagrangian_threePlusOne,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.VytheeswaranL2CauchyDatum.onConstraintSurface_iff_primaryPreserved,
    Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector.vytheeswaranFourierLegendreAction_eq_Eq325
  ]

/-! ## BM. Coulomb mean-field / classical limit with explicit cross-sector scope -/

zil_file_contract physlib.entropicSpine.coulombMeanFieldClassicalLimit where
  promises "The public spine exposes three rigorous Coulomb mean-field/classical-limit targets: the exact one-over-N pair normalization, propagation and joint-parameter vanishing of an explicitly assumed modulated energy through Mathlib's right-derivative Gronwall theorem, and disappearance of Caticha's pointwise Fisher/Bohm quantum term as hbar tends to zero. A fourth conditional bridge identifies the monokinetic current with the existing Caticha current and places the homogeneous Poisson source beside the holographic-bit rewriting of the Einstein coupling."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.golsePaulMeanFieldPairEnergy",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.CoulombModulatedEnergyControl",
    "lean:Physlib.QuantumMechanics.ComplexAction.ParametrizedTetradGravity.EMParticleDynamics.coulombPotential",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian.fokkerPlanckCurrent",
    "lean:Physlib.Thermodynamics.GravitationalCouplingSystem.einsteinCoupling_bitForm"
  ]
  forbids_substitutes [
    "claiming the full Golse--Paul theorem without constructing its N-body density matrices, Wigner measures, Coulomb singular estimate, and compactness argument",
    "calling collisionless pressureless Euler--Poisson a Navier--Stokes equation or a Boltzmann collision H-theorem",
    "identifying repulsive Coulomb interaction with attractive Newtonian gravity without an explicit sign and coupling premise",
    "claiming that the conditional bit rewrite derives gravity from the Coulomb mean-field limit",
    "substituting hbar equal to zero into the finite nonzero-hbar holographic bit identity"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.golsePaulMeanFieldPairEnergy_eq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.CoulombModulatedEnergyControl.energy_norm_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.CoulombModulatedEnergyControl.tendsto_energy_zero,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.physicalQuantumPotential_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.golsePaul_monokineticCurrent_holographicPoisson_bridge
  ]

/-! ## BN. Klein-Gordon-Maxwell to Schrodinger-Poisson nonrelativistic limit -/

zil_theorem_intent
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.eLpNorm_six_le_gradient_two where
  at_level bridge_theorem
  must_mention [
    MeasureTheory.SNormLESNormFDerivOfEqConst
  ]

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.HasHomogeneousSobolevRegularityOne.hasSobolevOne where
  formalizes @ "claim:on-the-full-euclidean-continuum-an-L2-function-with-one-homogeneous-L2-derivative-belongs-to-inhomogeneous-H-one-so-L2-intersection-dot-H-one-equals-H-one-in-the-forward-direction",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.besselPotentialWeight",
  caveat @ "the-L2-representative-is-explicit-and-is-not-automatically-available-for-a-general-tempered-newton-potential"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.existsUnique_fourierDotHOneWeakSolution where
  formalizes @ "claim:every-continuum-dot-H-minus-one-source-on-R-three-has-a-unique-zero-boundary-dot-H-one-weak-poisson-solution-in-fourier-energy-coordinates",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:InnerProductSpace.toDual",
  caveat @ "zero-boundary-means-the-homogeneous-energy-completion-which-excludes-nondecaying-harmonic-additions-the-theorem-does-not-assert-that-every-tempered-source-lies-in-dot-H-minus-one"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.norm_fourierDotHOnePoissonSolution where
  formalizes @ "claim:the-continuum-dot-H-one-energy-norm-of-the-unique-weak-poisson-solution-equals-the-operator-norm-of-its-dot-H-minus-one-source",
  epistemic_status @ "consistency-identity",
  requires @ "claim:every-continuum-dot-H-minus-one-source-on-R-three-has-a-unique-zero-boundary-dot-H-one-weak-poisson-solution-in-fourier-energy-coordinates"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.inverseNormSchwartzThree_memLp_two where
  formalizes @ "claim:in-three-continuum-dimensions-dividing-any-schwartz-fourier-profile-by-the-radial-frequency-produces-an-L2-energy-profile-and-therefore-every-schwartz-density-is-an-actual-homogeneous-H-minus-one-source",
  epistemic_status @ "risky",
  supported_by @ "lean:MeasureTheory.integrableOn_ball_of_norm_le_rpow",
  supported_by @ "lean:SchwartzMap.memLp",
  caveat @ "the-proof-uses-local-integrability-of-norm-xi-to-the-minus-two-in-dimension-three-and-schwartz-decay-outside-the-unit-ball-it-does-not-assert-that-the-newton-potential-itself-is-L2"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.fourierDotHOnePoissonSolution_schwartzSource where
  formalizes @ "claim:the-unique-zero-boundary-homogeneous-H-one-weak-solution-of-a-schwartz-density-has-fourier-energy-coordinate-rho-hat-divided-by-absolute-xi",
  epistemic_status @ "consistency-identity",
  requires @ "claim:in-three-continuum-dimensions-dividing-any-schwartz-fourier-profile-by-the-radial-frequency-produces-an-L2-energy-profile-and-therefore-every-schwartz-density-is-an-actual-homogeneous-H-minus-one-source"

zil attach
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.schwartzNewtonFourierPotential_besselOne_memLp_iff where
  formalizes @ "claim:for-a-schwartz-newton-source-the-full-inhomogeneous-H-one-fourier-condition-is-equivalent-exactly-to-the-additional-infrared-L2-integrability-of-rho-hat-divided-by-absolute-xi-squared",
  epistemic_status @ "risky",
  supported_by @ "lean:Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.inverseNormSchwartzThree_memLp_two",
  caveat @ "this-is-a-regularity-characterization-not-an-unconditional-H-one-claim-generic-nonzero-total-mass-newton-tails-need-not-be-L2-at-spatial-infinity"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMRestSubtractedGeneratorDomain.of_multiplierSlope_tendsto where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMRestSubtractedGeneratorDomain
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_tendsto_maximalGenerator where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMRestSubtractedGeneratorDomain,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedPhysicalGenerator
  ]

zil_file_contract physlib.entropicSpine.kgmSchrodingerPoissonNonrelativisticLimit where
  promises "The public spine exposes the Klein-Gordon-Maxwell nonrelativistic-limit mechanism: the exact minimally coupled positive/negative-frequency split and its inverse; all four continuum Ec multiplier-symbol estimates from Lemma 3; genuine Plancherel-conjugated Ec-inverse L2-to-H1 and L2-to-homogeneous-H1 bounds; the concrete rest-energy-subtracted KGM Fourier propagator as a complex-linear unitary C0 group with exact time composition, L2 unitarity, native Hs conservation and strong continuity at every time; the exact maximal symbol-weighted L2 domain is packaged as a partial complex-linear frequency operator, proved dense by bounded-symbol truncation, and proved closable using its formal skew-adjoint pairing; Plancherel conjugation supplies the genuine physical partial operator and both bundled operators are identified with the strong C0 generator on their exact domains; the H1 generator theorem remains a quantitative corollary; the complete homogeneous-H1 gradient carrier and its dense-core Sobolev-to-L6 estimate; L2 plus homogeneous-H1 implies H1; every homogeneous-H-minus-one source has a unique zero-boundary homogeneous-H-one weak Poisson solution with the sharp Riesz energy norm; and every Schwartz density is proved to supply such an H-minus-one source by the genuine dimension-three inverse-frequency integrability argument, with full H-one characterized by the separate infrared L2 condition. The equation-57 spatial null-form bounds, exact equation-56 four-dimensional Schwartz convolution, the actual inverse-gradient null integral with its unconditional half-derivative lintegral majorant, and the integrated Plancherel-Holder equation-58 closure hold under their explicit premises; the remaining nonrelativistic-limit conclusions retain their existing analytic control data."
  at_level structural
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.einsteinKinetic_tendsto_schrodinger",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmPositiveFrequencyMode",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmNegativeFrequencyMode",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmInverseEnergyOperator",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmKineticOperator",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedPhysicalGeneratorOperator",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.KGMNonrelativisticLimitControl"
  ]
  forbids_substitutes [
    "claiming the explicit Fourier-majorization or sharp-wave L4 fields of the Duhamel carrier follow from the constructed unitary C0 propagator merely because its group law, norm conservation and strong continuity are proved",
    "upgrading the bundled operator's proved formal skew-adjoint pairing to equality with its Hilbert-space adjoint without the maximal adjoint-domain argument",
    "claiming the supplied Gronwall carrier proves the paper's uniform KGM well-posedness, bilinear estimates, compactness, or explicit remainder rates",
    "claiming global-in-time convergence beyond the finite lifespan encoded by the control interval",
    "dropping the oscillatory source-remainder premise when passing to the Schrodinger-Poisson charge density"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.einsteinKinetic_tendsto_schrodinger,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.energy_mul_kgmFrequencyMode_sub,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.HasHomogeneousSobolevRegularityOne.hasSobolevOne,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.existsUnique_fourierDotHOneWeakSolution,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.norm_fourierDotHOnePoissonSolution,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.inverseNormSchwartzThree_memLp_two,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.fourierDotHOnePoissonSolution_schwartzSource,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.schwartzNewtonFourierPotential_besselOne_memLp_iff,
    Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization.eLpNorm_six_le_gradient_two,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmSpatialNullFormSymbol_le_add_mul_sqrt,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmSpacetimeNullFormFourierConvolution_apply,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmInverseSpatialNormNullComponent_mul_le,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmInverseSpatialNullFourierIntegral_eq_multiplier_mul,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.enorm_kgmInverseSpatialNullFourierIntegral_le,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmEquation58Output_le_l4_mul_l4,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMDuhamelL4Control.norm_halfDerivative_le_totalControl,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmProposition3Output_le_data_forcing,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_sum_kgmProposition3Outputs_le,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution_add,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmRestSubtractedEvolution,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.sobolevNorm_kgmRestSubtractedEvolution,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution_tendsto_zero,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolution_tendsto,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtracted_unitaryC0Group,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.hasDerivAt_kgmRestSubtractedPhase,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedPhaseSlope_tendsto,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmRestSubtractedPhaseSlope_le,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_tendsto_maximalGenerator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedGeneratorDomain_iff_mem_frequencyOperator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator_isFormalAdjoint_neg,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator_hasDenseDomain,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedFrequencyGeneratorOperator_isUnbounded,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_tendsto_frequencyOperator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.KGMRestSubtractedGeneratorDomain.of_multiplierSlope_tendsto,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_exists_tendsto_iff,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_tendsto_maximalGenerator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_tendsto_physicalGeneratorOperator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_exists_tendsto_iff,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedMultiplierSlope_tendsto_generator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtractedEvolutionSlope_tendsto_generator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmRestSubtracted_unitaryC0Group_with_H1Generator,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.sobolevNorm_kgmInverseEnergyOperator_le,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.homogeneousSobolevOneNorm_kgmInverseEnergyOperator_le,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmKineticOperator_le_c_mul_sobolevNorm_one,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.norm_kgmKineticOperator_le_half_sobolevNorm_two,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.schrodingerPoissonChargeDensity_dephase,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit.kgmChargeSource_tendsto_schrodingerPoisson,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest.KGMNonrelativisticLimitControl.tendsto_schrodingerPoisson
  ]

/-! ## BO. Constructed interacting functional measurement on the public spine -/

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.ContinuumDetector.outcomeLawAt_eq where
  formalizes @ "claim:configuration-local-interacting-caticha-evolution-preserves-continuum-detector-outcome-law",
  epistemic_status @ "consistency-identity",
  requires @ "assumption:real-configuration-local-energy-and-normalized-born-density",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.bornMeasure_evolution",
  caveat @ "claim:phase-only-diagonal-interaction-preserves-position-readout-statistics-but-does-not-construct-decoherence-collapse-or-an-arbitrary-functional-differential-hamiltonian"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLaw_cascade_remainingClock_chain where
  formalizes @ "claim:the-public-entropic-spine-supports-stochastic-continuum-caticha-detectors-whose-cascaded-markov-response-laws-form-a-monotone-relative-entropy-clock-chain",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_comp_le",
  caveat @ "claim:classical-markov-response-data-processing-not-a-quantum-instrument-decoherence-collapse-or-type-III-relative-entropy-construction"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLawUnder_remainingClock_antitone where
  formalizes @ "claim:the-public-entropic-spine-carries-positive-time-stochastic-caticha-detector-dynamics-with-an-antitone-stationary-reference-relative-entropy-clock",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:a-supplied-positive-time-continuum-markov-semigroup-stationary-reference-and-finite-initial-relative-entropy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.remainingClockAt_antitone",
  caveat @ "claim:classical-outcome-semigroup-H-theorem-not-a-constructed-GKLS-generator-quantum-instrument-decoherence-or-collapse-law"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLawUnderC0_initial_observable_recovery where
  formalizes @ "claim:the-public-entropic-spine-carries-weakly-continuous-caticha-detector-time-with-initial-bounded-observable-recovery",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:a-supplied-weakly-continuous-continuum-markov-response-semigroup",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.initial_observable_recovery",
  caveat @ "claim:weak-C0-classical-outcome-dynamics-not-a-constructed-quantum-instrument-pointer-Hamiltonian-or-collapse-law"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.detectorObservableGenerator_eq_zero_of_fixedOutcome where
  formalizes @ "claim:the-public-entropic-spine-places-every-stationary-caticha-outcome-law-in-the-kernel-of-its-identified-weak-observable-generator",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:a-supplied-weak-generator-limit-and-stationary-caticha-outcome-law",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.observableGenerator_eq_zero_of_fixedReference",
  caveat @ "claim:fixed-point-balance-not-existence-uniqueness-or-GKLS-identification-of-the-generator"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.detectorRightClockProductionRate_nonneg where
  formalizes @ "claim:the-public-entropic-spine-makes-every-existing-right-clock-production-rate-of-weak-C0-caticha-detector-time-nonnegative",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:a-supplied-weak-C0-detector-semigroup-stationary-reference-finite-initial-kl-and-existing-right-rate-limit",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.rightClockProductionRate_nonneg",
  caveat @ "claim:differential-classical-H-theorem-not-a-GKLS-Spohn-rate-identification-without-a-quantum-carrier-adapter"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLawUnder_identity where
  formalizes @ "claim:the-public-spine-includes-a-concrete-identity-C0-detector-control-that-preserves-every-constructed-caticha-outcome-law",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:zero-dynamics-control-not-a-nontrivial-detector-relaxation-decoherence-or-collapse-model"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.fixedOutcome_hasDetectorRightClockProductionRate_zero where
  formalizes @ "claim:stationarity-constructs-the-zero-right-clock-production-rate-for-a-caticha-outcome-law",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:stationarity-of-the-constructed-caticha-outcome-law",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.fixedReference_hasRightClockProductionRate_zero",
  caveat @ "claim:equilibrium-rate-existence-not-a-nonequilibrium-Spohn-production-formula"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.detectorRightClockProductionRate_eq_zero_of_fixedOutcome where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.rightClockProductionRate_eq_zero_of_fixedReference",
  formalizes @ "claim:every-right-clock-production-rate-of-a-stationary-caticha-outcome-law-is-uniquely-zero",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:stationarity-constructs-the-zero-right-clock-production-rate-for-a-caticha-outcome-law",
  caveat @ "claim:stationary-equality-case-not-a-proof-of-rate-existence-away-from-equilibrium"

zil_file_contract physlib.entropicSpine.interactingFunctionalMeasurement where
  promises "The scientific entropic spine exports the constructed continuum L2 Caticha model and its Born measure. Measurable readouts and arbitrary stochastic Markov-response detectors construct conserved outcome laws; detector cascades contract the relative-entropy clock. With an explicit positive-time Markov detector semigroup and stationary reference, the outcome clock is antitone, interval production is nonnegative and additive, and the calibrated complex-action modulus is a Lyapunov monotone. A weak-C0 extension recovers initial bounded-observable expectations, puts stationary Caticha outcome laws in the kernel of any identified weak generator, and gives nonnegative existing right clock-production rates. A concrete identity control preserves every outcome law; stationarity constructs the zero right rate and forces every stationary rate to equal zero."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.evolution",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.bornMeasure",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.ContinuumDetector.outcomeLawAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLaw",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_map_le",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_comp_le",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelPositiveTimeSemigroup.remainingClockAt_antitone",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.HasObservableGenerator",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.MeasureKernelC0Semigroup.HasRightClockProductionRate"
  ]
  forbids_substitutes [
    "claiming the supplied configuration reference measure is derived from a renormalized path integral",
    "claiming a diagonal multiplication generator is an arbitrary interacting functional differential Hamiltonian",
    "calling conservation of a position-dependent detector pushforward a derivation of decoherence or wave-function collapse"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.evolution_unitaryC0,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.bornMeasure_evolution,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.ContinuumDetector.outcomeLawAt_eq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.bornMeasure_remainingClock_evolution,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.ContinuumDetector.outcomeLaw_remainingClock_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.ContinuumDetector.outcomeLaw_complexWeight_norm_mono,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLawAt_eq,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLaw_remainingClock_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLaw_complexWeight_norm_mono,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLaw_cascade,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLaw_cascade_remainingClock_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLawUnder_add,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLawUnder_remainingClock_antitone,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLawUnder_complexWeight_norm_monotone,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.detectorIntervalClockGain_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.detectorIntervalClockGain_cocycle,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLawUnderC0_initial_observable_recovery,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.detectorObservableGenerator_eq_zero_of_fixedOutcome,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.detectorRightClockProductionRate_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.outcomeLawUnder_identity,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.fixedOutcome_hasDetectorRightClockProductionRate_zero,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement.InteractingFunctionalModel.StochasticContinuumDetector.detectorRightClockProductionRate_eq_zero_of_fixedOutcome
  ]

/-! ## BP. Periodic Schrodinger continuum and entropic spectral selection -/

zil_theorem_intent
    Physlib.QuantumMechanics.PeriodicSchrodinger.periodicPotentialOperator_isSelfAdjoint where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.PeriodicSchrodinger.periodicPotentialOperator]

zil_theorem_intent
    Physlib.QuantumMechanics.PeriodicSchrodinger.infiniteTailMass_le_of_localized where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.PeriodicSchrodinger.IsInfiniteBlochLocalized,
    Physlib.QuantumMechanics.PeriodicSchrodinger.infiniteTailMass
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.PeriodicSchrodinger.resonanceMatrix_isHermitian where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.PeriodicSchrodinger.resonanceMatrix,
    Physlib.QuantumMechanics.PeriodicSchrodinger.IsHermitianCoupling
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.PeriodicSchrodinger.finiteHighEnergyGapRegion_of_crossings where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.PeriodicSchrodinger.HasFiniteHighEnergyGapRegion,
    Physlib.QuantumMechanics.PeriodicSchrodinger.SimpleBandBranch
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.PeriodicSchrodinger.norm_spectralSelectionWeight_le_one where
  at_level bridge_theorem
  must_mention [Physlib.QuantumMechanics.PeriodicSchrodinger.spectralSelectionWeight]

zil attach
    Physlib.QuantumMechanics.PeriodicSchrodinger.norm_spectralSelectionWeight_le_one where
  formalizes @ "claim:periodic-schrodinger-spectral-mismatch-gives-contractive-complex-action-selection",
  epistemic_status @ "consistency-identity",
  requires @ "assumption:positive-hbar-and-squared-spectral-mismatch-penalty",
  supported_by @ "lean:Physlib.QFT.Wick.Consistency.norm_complexActionWeight",
  caveat @ "claim:contractivity-follows-from-the-defined-mismatch-penalty-and-does-not-prove-veliev-asymptotic-error-rates-or-full-measure-simple-sets"

zil_file_contract physlib.entropicSpine.periodicSchrodingerSelection where
  promises "The public spine exposes a continuum maximal-domain self-adjoint periodic multiplication operator, summable infinite-mode Bloch-tail control, Hermitian finite resonance matrices, the conditional Bethe--Sommerfeld no-high-energy-gap conclusion from crossing branches, and the exact contractive complex-action weight attached to spectral mismatch."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.PeriodicSchrodinger.periodicPotentialOperator",
    "lean:Physlib.QuantumMechanics.PeriodicSchrodinger.IsInfiniteBlochLocalized",
    "lean:Physlib.QuantumMechanics.PeriodicSchrodinger.resonanceMatrix",
    "lean:Physlib.QuantumMechanics.PeriodicSchrodinger.HasFiniteHighEnergyGapRegion",
    "lean:Physlib.QuantumMechanics.PeriodicSchrodinger.spectralSelectionWeight"
  ]
  forbids_substitutes [
    "claiming a multiplication potential alone constructs the full unbounded periodic Schrodinger Hamiltonian",
    "claiming the abstract crossing premise proves asymptotically full measure of the simple spectral set",
    "calling a definition-driven imaginary-action penalty a new empirical decay law"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.PeriodicSchrodinger.periodicPotentialOperator_isSelfAdjoint,
    Physlib.QuantumMechanics.PeriodicSchrodinger.infiniteTailMass_le_of_localized,
    Physlib.QuantumMechanics.PeriodicSchrodinger.resonanceMatrix_isHermitian,
    Physlib.QuantumMechanics.PeriodicSchrodinger.finiteHighEnergyGapRegion_of_crossings,
    Physlib.QuantumMechanics.PeriodicSchrodinger.norm_spectralSelectionWeight_le_one
  ]

/-! ## BQ. Lovelock--Rund continuum variational and curvature geometry -/

zil_theorem_intent Physlib.Mathematics.LovelockRund.isWeakExtremal_iff_eq_zero where
  at_level bridge_theorem
  must_mention [Physlib.Mathematics.LovelockRund.IsWeakExtremal]

zil_theorem_intent
    Physlib.Mathematics.LovelockRund.NoetherCurrentData.integral_divergence_eq_zero where
  at_level bridge_theorem
  must_mention [Physlib.Mathematics.LovelockRund.NoetherCurrentData]

zil_theorem_intent
    Physlib.Mathematics.LovelockRund.normal_coordinates_connection_zero_curvature_derivative where
  at_level bridge_theorem
  must_mention [
    Physlib.Mathematics.LovelockRund.IsNormalConnectionAt,
    Physlib.Mathematics.LovelockRund.normalCoordinateCurvature
  ]

zil_theorem_intent Physlib.Mathematics.LovelockRund.infiniteRicci_eq_finite where
  at_level bridge_theorem
  must_mention [
    Physlib.Mathematics.LovelockRund.infiniteRicci,
    Physlib.Mathematics.LovelockRund.finiteRicci
  ]

zil_theorem_intent Physlib.Mathematics.LovelockRund.einsteinSpaceResidual_eq_zero_iff where
  at_level bridge_theorem
  must_mention [Physlib.Mathematics.LovelockRund.einsteinSpaceResidual]

zil attach Physlib.Mathematics.LovelockRund.isWeakExtremal_iff_eq_zero where
  formalizes @ "claim:continuum-weak-stationarity-is-pointwise-euler-lagrange-vanishing",
  epistemic_status @ "risky",
  requires @ "assumption:continuous-variational-gradient-and-compactly-supported-test-variations",
  supported_by @ "lean:Physlib.Mathematics.VariationalCalculus.fundamental_theorem_of_variational_calculus'",
  caveat @ "claim:genuine-continuum-fundamental-lemma-not-by-itself-existence-regularity-or-global-minimality-of-an-extremal"

zil_file_contract physlib.entropicSpine.lovelockRundContinuumGeometry where
  promises "The public spine exposes the genuine continuum weak Euler--Lagrange fundamental lemma, on-shell integrated Noether conservation, the normal-coordinate separation between vanishing connection coefficients and surviving curvature derivatives, agreement of infinite contractions with finite Ricci sums on finite index types, and the exact Einstein-space residual criterion."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Mathematics.LovelockRund.IsWeakExtremal",
    "lean:Physlib.Mathematics.LovelockRund.NoetherCurrentData",
    "lean:Physlib.Mathematics.LovelockRund.normalCoordinateCurvature",
    "lean:Physlib.Mathematics.LovelockRund.infiniteRicci",
    "lean:Physlib.Mathematics.LovelockRund.einsteinSpaceResidual"
  ]
  forbids_substitutes [
    "claiming weak stationarity proves existence regularity uniqueness or global minimality",
    "claiming normal coordinates eliminate curvature rather than only the connection coefficients at one point",
    "calling finite-index tsum reduction a construction of a global pseudo-Riemannian atlas or Levi--Civita connection"
  ]
  witnessed_by [
    Physlib.Mathematics.LovelockRund.isWeakExtremal_iff_eq_zero,
    Physlib.Mathematics.LovelockRund.NoetherCurrentData.integral_divergence_eq_zero,
    Physlib.Mathematics.LovelockRund.normal_coordinates_connection_zero_curvature_derivative,
    Physlib.Mathematics.LovelockRund.infiniteRicci_eq_finite,
    Physlib.Mathematics.LovelockRund.einsteinSpaceResidual_eq_zero_iff
  ]

/-! ## BR. Continuum scalar Green functions and distributional Dyson--Schwinger hierarchy -/

zil_theorem_intent
    Physlib.QFT.ScalarGreenFunctions.continuumScalarMulOperator_hasDenseDomain where
  at_level bridge_theorem
  must_mention [Physlib.QFT.ScalarGreenFunctions.continuumScalarMulOperator]

zil_theorem_intent
    Physlib.QFT.ScalarGreenFunctions.left_right_continuumScalarKernelAction_commute where
  at_level bridge_theorem
  must_mention [
    Physlib.QFT.ScalarGreenFunctions.leftContinuumScalarKernelAction,
    Physlib.QFT.ScalarGreenFunctions.rightContinuumScalarKernelAction
  ]

zil_theorem_intent Physlib.QFT.ScalarGreenFunctions.continuumContactTerm_pair_apply where
  at_level bridge_theorem
  must_mention [Physlib.QFT.ScalarGreenFunctions.continuumContactTerm]

zil_theorem_intent
    Physlib.QFT.ScalarGreenFunctions.ContinuumQuarticDysonSchwingerData.twoLegEquation_apply where
  at_level bridge_theorem
  must_mention [Physlib.QFT.ScalarGreenFunctions.ContinuumQuarticDysonSchwingerData]

zil_theorem_intent
    Physlib.QFT.ScalarGreenFunctions.ContinuumResolventFlowData.differenceQuotient where
  at_level bridge_theorem
  must_mention [
    Physlib.QFT.ScalarGreenFunctions.ContinuumResolventFlowData,
    Physlib.QFT.ScalarGreenFunctions.pointwiseKernelComposition
  ]

zil attach
    Physlib.QFT.ScalarGreenFunctions.ContinuumQuarticDysonSchwingerData.twoLegEquation_apply where
  formalizes @ "claim:rivers-continuum-two-leg-dyson-schwinger-equation-has-the-exact-dirac-contact",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:continuum-quartic-dyson-schwinger-data-including-the-distributional-hierarchy",
  supported_by @ "paper:rivers-1987-equations-1-28-through-1-36",
  caveat @ "claim:evaluates-supplied-distributional-dyson-schwinger-data-and-does-not-construct-an-interacting-continuum-qft-measure-or-renormalize-coincident-products"

zil attach
    Physlib.QFT.ScalarGreenFunctions.ContinuumResolventFlowData.differenceQuotient where
  formalizes @ "claim:continuum-external-field-propagator-resolvent-difference-quotient",
  epistemic_status @ "consistency-identity",
  requires @ "assumption:exact-two-coupling-continuum-resolvent-identity-and-distinct-couplings",
  supported_by @ "paper:rivers-1987-equations-1-60-through-1-79",
  caveat @ "claim:finite-difference-resolvent-consequence-not-a-proof-of-differentiability-or-existence-of-the-propagator-family"

zil_file_contract physlib.entropicSpine.continuumScalarGreenDyson where
  promises "The global entropic spine exports the genuine continuum L2 multiplier carrier, commuting left/right kernel actions, Schwartz-distribution Dirac contacts, the evaluated two-leg quartic Dyson--Schwinger equation, and the exact external-field resolvent difference quotient."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QFT.ScalarGreenFunctions.continuumScalarMulOperator",
    "lean:Physlib.QFT.ScalarGreenFunctions.scalarContactDistribution",
    "lean:Physlib.QFT.ScalarGreenFunctions.ContinuumQuarticDysonSchwingerData",
    "lean:Physlib.QFT.ScalarGreenFunctions.ContinuumResolventFlowData"
  ]
  forbids_substitutes [
    "calling supplied Dyson--Schwinger data a construction of an interacting continuum path-integral measure",
    "replacing distributional coincident-field contacts by pointwise products",
    "claiming an exact finite-difference identity establishes analytic dependence on the coupling"
  ]
  witnessed_by [
    Physlib.QFT.ScalarGreenFunctions.continuumScalarMulOperator_hasDenseDomain,
    Physlib.QFT.ScalarGreenFunctions.left_right_continuumScalarKernelAction_commute,
    Physlib.QFT.ScalarGreenFunctions.continuumContactTerm_pair_apply,
    Physlib.QFT.ScalarGreenFunctions.ContinuumQuarticDysonSchwingerData.twoLegEquation_apply,
    Physlib.QFT.ScalarGreenFunctions.ContinuumResolventFlowData.differenceQuotient
  ]

/-! ## BR. Glenn vacuum-photon exchange nonlinear response -/

zil_theorem_intent
    Physlib.QFT.ScalarGreenFunctions.linearQMEResponse_thirdDifference_eq_zero where
  at_level bridge_theorem
  must_mention [Physlib.QFT.ScalarGreenFunctions.opticalThirdDifference]

zil_theorem_intent
    Physlib.QFT.ScalarGreenFunctions.fourthVacuumOrder_dysonWickExpansion where
  at_level bridge_theorem
  must_mention [FieldSpecification.WickAlgebra.timeOrder]

zil_theorem_intent
    Physlib.QFT.ScalarGreenFunctions.glennTwoProcessConvolution_eq_sum where
  at_level bridge_theorem
  must_mention [
    Physlib.QFT.ScalarGreenFunctions.glennTwoProcessConvolution,
    Physlib.QFT.ScalarGreenFunctions.doubleFrequencyConvolution
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.DunklKernelSemigroup.sequentialKernel_eq_total where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.dunklWeightedKernelComposition,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.DunklKernelSemigroup.kernel
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.wienerDensity_convolution where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.wienerDensity
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.integral_wienerDensity_eq_one where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.wienerDensity
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.freeWiener_positiveTimeSlicing_eq_total where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.DunklKernelSemigroup.positiveTimeSlicing,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.wienerDensity
  ]

zil_theorem_intent
    Physlib.QFT.ScalarGreenFunctions.dunklEuclideanFK_doubleConvolution_eq_four_channels where
  at_level bridge_theorem
  must_mention [
    Physlib.QFT.ScalarGreenFunctions.doubleFrequencyConvolution,
    Physlib.QFT.ScalarGreenFunctions.dunklReflectingFrequencyAmplitude,
    Physlib.QFT.ScalarGreenFunctions.dunklAbsorbingFrequencyAmplitude
  ]

zil_theorem_intent
    Physlib.QFT.ScalarGreenFunctions.dunklScalarInsertionConvolution_eq_sequential where
  at_level bridge_theorem
  must_mention [
    Physlib.QFT.ScalarGreenFunctions.dunklInterruptedGlennKernel,
    Physlib.QFT.ScalarGreenFunctions.dunklSequentialGlennKernel
  ]

zil_theorem_intent
    Physlib.QFT.ScalarGreenFunctions.freeWienerScalarInsertionConvolution_eq_sequential where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.freeWienerDunklSemigroup,
    Physlib.QFT.ScalarGreenFunctions.dunklInterruptedGlennKernel,
    Physlib.QFT.ScalarGreenFunctions.dunklSequentialGlennKernel
  ]

zil_theorem_intent
    Physlib.QFT.ScalarGreenFunctions.GlennPhotonExchangeData.firstFiniteResponse_is_interruptedFourthOrder where
  at_level bridge_theorem
  must_mention [
    Physlib.QFT.ScalarGreenFunctions.GlennPhotonExchangeData.secondOrderResponse,
    Physlib.QFT.ScalarGreenFunctions.GlennPhotonExchangeData.fourthOrderResponse,
    Physlib.QFT.ScalarGreenFunctions.doubleFrequencyConvolution
  ]

zil_theorem_intent
    Physlib.QFT.ScalarGreenFunctions.GlennPhotonExchangeData.interruptedFourthOrder_hasNonzeroCubicDifference where
  at_level bridge_theorem
  must_mention [
    Physlib.QFT.ScalarGreenFunctions.opticalThirdDifference,
    Physlib.QFT.ScalarGreenFunctions.cubicOpticalResponse
  ]

zil attach
    Physlib.QFT.ScalarGreenFunctions.linearQMEResponse_thirdDifference_eq_zero where
  formalizes @ "claim:a-complex-linear-harmonic-qme-response-has-zero-third-forward-finite-difference-and-therefore-carries-no-cubic-optical-signal",
  epistemic_status @ "consistency-identity",
  supported_by @ "source:glenn-bennett-dorfman-mukamel-2015-equations-26-through-34",
  caveat @ "claim:this-proves-the-cubic-diagnostic-vanishes-for-the-linear-response-map-it-does-not-derive-that-every-open-system-master-equation-is-linear"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.DunklKernelSemigroup.sequentialKernel_eq_total where
  formalizes @ "claim:the-wigner-dunkl-propagator-composes-by-the-explicit-absolute-z-to-two-nu-weighted-kolmogorov-chapman-kernel-integral",
  epistemic_status @ "conditional-model",
  requires @ "assumption:a-concrete-wigner-dunkl-kernel-satisfies-junker-equation-46-with-respect-to-the-weighted-spatial-measure",
  supported_by @ "source:junker-wigner-dunkl-2024-equation-46",
  caveat @ "claim:the-lean-structure-exposes-the-weighted-kernel-composition-law-for-strictly-positive-euclidean-slices-it-does-not-prove-that-an-arbitrary-abstract-feynman-kac-model-has-a-pointwise-integral-kernel-or-represent-zero-time-by-a-function"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.wienerDensity_convolution where
  formalizes @ "claim:at-nu-zero-the-explicit-positive-time-wiener-dunkl-kernel-satisfies-the-pointwise-kolmogorov-chapman-convolution-law",
  epistemic_status @ "analytic-theorem",
  requires @ "assumption:both-euclidean-time-slices-are-strictly-positive",
  supported_by @ "source:junker-wigner-dunkl-2024-equations-46-and-79",
  supported_by @ "lean:ProbabilityTheory.integral_gaussianPDFReal_eq_one",
  caveat @ "claim:this-is-a-proved-function-valued-positive-time-kernel-law-at-nu-zero-the-zero-time-dirac-kernel-and-general-nu-bessel-integral-remain-separate-distributional-and-analytic-targets"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.integral_wienerDensity_eq_one where
  formalizes @ "claim:the-explicit-positive-time-wiener-dunkl-kernel-is-integrable-and-has-unit-total-mass",
  epistemic_status @ "analytic-theorem",
  requires @ "assumption:the-euclidean-time-is-strictly-positive",
  supported_by @ "source:junker-wigner-dunkl-2024-equation-79",
  supported_by @ "lean:ProbabilityTheory.integral_gaussianPDFReal_eq_one",
  caveat @ "claim:unit-mass-and-strict-positivity-prove-the-free-nu-zero-markov-normalization-they-do-not-prove-conservativity-for-a-killing-potential-or-a-general-nu-bessel-kernel"

zil attach
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.freeWiener_positiveTimeSlicing_eq_total where
  formalizes @ "claim:every-finite-chain-of-equal-positive-time-free-wiener-dunkl-slices-collapses-exactly-to-the-kernel-at-total-time",
  epistemic_status @ "analytic-theorem",
  requires @ "claim:at-nu-zero-the-explicit-positive-time-wiener-dunkl-kernel-satisfies-the-pointwise-kolmogorov-chapman-convolution-law",
  supported_by @ "source:junker-wigner-dunkl-2024-equations-46-and-56",
  caveat @ "claim:this-is-the-exact-finite-time-slicing-identity-it-does-not-assert-convergence-of-a-mesh-refinement-to-a-continuum-path-measure"

zil attach
    Physlib.QFT.ScalarGreenFunctions.dunklEuclideanFK_doubleConvolution_eq_four_channels where
  formalizes @ "claim:a-factorized-glenn-two-frequency-kernel-built-from-the-euclidean-wigner-dunkl-propagator-splits-into-reflecting-reflecting-reflecting-absorbing-absorbing-reflecting-and-absorbing-absorbing-bessel-channels",
  epistemic_status @ "conditional-model",
  requires @ "assumption:the-reflecting-and-absorbing-frequency-amplitudes-are-bochner-integrable",
  supported_by @ "source:junker-wigner-dunkl-2024-equations-77-through-78",
  supported_by @ "source:glenn-bennett-dorfman-mukamel-2015-equation-18",
  caveat @ "claim:the-four-channel-result-is-for-the-factorized-two-frequency-realization-and-does-not-assert-that-every-material-response-kernel-factorizes"

zil attach
    Physlib.QFT.ScalarGreenFunctions.dunklScalarInsertionConvolution_eq_sequential where
  formalizes @ "claim:a-scalar-intermediate-insertion-in-the-weighted-wigner-dunkl-kernel-collapses-to-the-consecutive-glenn-convolution-so-a-genuine-interrupted-process-requires-a-non-scalar-intermediate-operator",
  epistemic_status @ "consistency-identity",
  requires @ "claim:the-wigner-dunkl-propagator-composes-by-the-explicit-absolute-z-to-two-nu-weighted-kolmogorov-chapman-kernel-integral",
  requires @ "assumption:both-euclidean-time-slices-are-strictly-positive",
  supported_by @ "source:junker-wigner-dunkl-2024-equation-46",
  supported_by @ "source:glenn-bennett-dorfman-mukamel-2015-consecutive-versus-interrupted-processes",
  caveat @ "claim:collapse-of-scalar-insertions-separates-the-two-processes-structurally-it-does-not-evaluate-the-electromagnetic-dipole-insertion"

zil attach
    Physlib.QFT.ScalarGreenFunctions.freeWienerScalarInsertionConvolution_eq_sequential where
  formalizes @ "claim:the-explicit-free-wiener-dunkl-kernel-makes-a-scalar-glenn-intermediate-insertion-collapse-to-consecutive-positive-time-propagation",
  epistemic_status @ "analytic-theorem",
  requires @ "claim:at-nu-zero-the-explicit-positive-time-wiener-dunkl-kernel-satisfies-the-pointwise-kolmogorov-chapman-convolution-law",
  supported_by @ "source:junker-wigner-dunkl-2024-equations-46-and-79",
  supported_by @ "source:glenn-bennett-dorfman-mukamel-2015-consecutive-versus-interrupted-processes",
  caveat @ "claim:the-concrete-collapse-shows-that-time-slicing-and-scalar-spectral-weighting-alone-cannot-create-glenns-interrupted-channel-it-does-not-compute-a-position-dependent-dipole-insertion"

zil attach
    Physlib.QFT.ScalarGreenFunctions.GlennPhotonExchangeData.firstFiniteResponse_is_interruptedFourthOrder where
  formalizes @ "claim:under-the-paper-vacuum-selection-rules-the-second-order-and-balanced-two-plus-two-kernels-vanish-and-the-first-finite-response-among-the-analyzed-orders-is-the-interrupted-three-plus-one-fourth-vacuum-order-convolution",
  epistemic_status @ "conditional-model",
  requires @ "assumption:the-second-order-and-balanced-fourth-order-electromagnetic-vacuum-kernels-vanish-almost-everywhere",
  requires @ "assumption:the-interrupted-fourth-order-double-frequency-kernel-is-integrable-with-nonzero-integral",
  supported_by @ "source:glenn-bennett-dorfman-mukamel-2015-equations-12-through-18-and-appendix-c",
  supported_by @ "lean:Physlib.QFT.ScalarGreenFunctions.fourthVacuumOrder_dysonWickExpansion",
  caveat @ "claim:the-lean-carrier-does-not-construct-the-dipole-hamiltonian-or-evaluate-a-material-susceptibility-the-paper-specific-vacuum-selection-and-nonzero-kernel-are-explicit-data"

zil attach
    Physlib.QFT.ScalarGreenFunctions.GlennPhotonExchangeData.interruptedFourthOrder_hasNonzeroCubicDifference where
  formalizes @ "claim:the-surviving-interrupted-fourth-vacuum-order-response-has-a-nonzero-cubic-finite-difference-for-every-nonzero-external-field-and-is-therefore-absent-from-the-linear-qme-sector",
  epistemic_status @ "conditional-model",
  requires @ "claim:under-the-paper-vacuum-selection-rules-the-second-order-and-balanced-two-plus-two-kernels-vanish-and-the-first-finite-response-among-the-analyzed-orders-is-the-interrupted-three-plus-one-fourth-vacuum-order-convolution",
  supported_by @ "lean:Physlib.QFT.ScalarGreenFunctions.linearQMEResponse_thirdDifference_eq_zero",
  supported_by @ "source:glenn-bennett-dorfman-mukamel-2015-equation-18",
  caveat @ "claim:nonzero-third-finite-difference-certifies-cubic-nonlinearity-but-is-not-a-numerical-prediction-for-a-specific-experiment"

zil_file_contract physlib.entropicSpine.glennPhotonExchangeNonlinearity where
  promises "The scalar Green-function spine distinguishes the consecutive linear-QME photon-exchange response from the interrupted time-ordered process. The fourth vacuum-field coefficient uses the existing complete Wick theorem; the two exchanged frequencies use one product-measure Bochner convolution. Junker's exact weighted Wigner--Dunkl kernel law proves that scalar insertions collapse to consecutive propagation, and at nu zero this law is instantiated analytically by the explicit positive-time Wiener kernel through a normalized Gaussian bridge density. The concrete kernel is integrable, positive and mass one, and every finite equal-time slicing collapses exactly to total time without claiming the continuum mesh limit. The Euclidean reflecting/absorbing split resolves a factorized double-frequency exchange into four Bessel channels. Explicit vacuum-selection data then makes the second and balanced fourth orders vanish while a nonzero interrupted fourth order produces a rigorously detected cubic optical response."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QFT.ScalarGreenFunctions.dysonOrder_smul_wicks_theorem",
    "lean:MeasureTheory.integral",
    "lean:Physlib.QFT.ScalarGreenFunctions.GlennPhotonExchangeData",
    "lean:Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.DunklKernelSemigroup",
    "lean:Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.freeWienerDunklSemigroup",
    "lean:Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.dunklWeightedKernelComposition"
  ]
  forbids_substitutes [
    "calling fourth order in vacuum interactions a four-loop diagram",
    "claiming abstract linearity proves every reduced master equation has no nonlinear terms",
    "hiding the electromagnetic vacuum-selection or nonzero-integral assumptions",
    "claiming the abstract convolution computes a measured susceptibility without a concrete kernel",
    "claiming an arbitrary Feynman-Kac model has a pointwise weighted kernel without a kernel-realization premise",
    "claiming every two-frequency response factorizes into one-frequency Wigner--Dunkl amplitudes"
  ]
  witnessed_by [
    Physlib.QFT.ScalarGreenFunctions.linearQMEResponse_thirdDifference_eq_zero,
    Physlib.QFT.ScalarGreenFunctions.fourthVacuumOrder_dysonWickExpansion,
    Physlib.QFT.ScalarGreenFunctions.glennTwoProcessConvolution_eq_sum,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.DunklKernelSemigroup.sequentialKernel_eq_total,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.wienerDensity_convolution,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.integral_wienerDensity_eq_one,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.EuclideanProcess.freeWiener_positiveTimeSlicing_eq_total,
    Physlib.QFT.ScalarGreenFunctions.dunklEuclideanFK_doubleConvolution_eq_four_channels,
    Physlib.QFT.ScalarGreenFunctions.dunklScalarInsertionConvolution_eq_sequential,
    Physlib.QFT.ScalarGreenFunctions.freeWienerScalarInsertionConvolution_eq_sequential,
    Physlib.QFT.ScalarGreenFunctions.GlennPhotonExchangeData.firstFiniteResponse_is_interruptedFourthOrder,
    Physlib.QFT.ScalarGreenFunctions.GlennPhotonExchangeData.interruptedFourthOrder_hasNonzeroCubicDifference
  ]

/-! ## BS. Scalar Green functions under complex action and entropic time -/

zil_theorem_intent Physlib.QFT.ScalarGreenFunctions.shiftImaginaryAction_partition where
  at_level bridge_theorem
  must_mention [Physlib.QFT.ScalarGreenFunctions.shiftImaginaryAction]

zil_theorem_intent
    Physlib.QFT.ScalarGreenFunctions.shiftImaginaryAction_normalizedExpectation where
  at_level bridge_theorem
  must_mention [Physlib.QFT.ScalarGreenFunctions.shiftImaginaryAction]

zil_theorem_intent
    Physlib.QFT.ScalarGreenFunctions.norm_complexActionWeight_antitone_imaginary where
  at_level bridge_theorem
  must_mention [Physlib.QFT.Wick.Consistency.complexActionWeight]

zil_theorem_intent Physlib.QFT.ScalarGreenFunctions.globalEntropicOffset_damps_but_cancels where
  at_level bridge_theorem
  must_mention [
    Physlib.QFT.ScalarGreenFunctions.entropicGapAction,
    Physlib.QFT.ScalarGreenFunctions.entropicGapShiftedModel
  ]

zil_theorem_intent Physlib.QFT.ScalarGreenFunctions.complexActionWeightedDysonWick where
  at_level bridge_theorem
  must_mention [Physlib.QFT.Wick.Consistency.complexActionWeight]

zil attach Physlib.QFT.ScalarGreenFunctions.globalEntropicOffset_damps_but_cancels where
  formalizes @ "claim:global-relative-entropy-action-damps-unnormalized-amplitudes-but-cancels-from-normalized-green-functions",
  epistemic_status @ "consistency-identity",
  requires @ "assumption:finite-state-relative-entropy-used-as-a-configuration-independent-imaginary-action-offset",
  supported_by @ "lean:Physlib.QFT.ScalarGreenFunctions.shiftImaginaryAction_normalizedExpectation",
  caveat @ "claim:only-a-global-offset-cancels-configuration-dependent-imaginary-action-can-change-normalized-correlations-and-remains-the-dynamical-content"

zil_file_contract physlib.entropicSpine.scalarGreenComplexEntropicTime where
  promises "The global spine distinguishes unnormalised damping from physical normalized correlations: constant imaginary-action shifts factor from the partition and cancel exactly after normalization; increasing imaginary action contracts the complex weight; a relative-entropy offset has modulus exp(-D); and Dyson--Wick combinatorics survives complex-action weighting."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QFT.PathIntegral.MeasurePathIntegralModel",
    "lean:Physlib.QFT.ScalarGreenFunctions.shiftImaginaryAction",
    "lean:Physlib.QFT.ScalarGreenFunctions.entropicGapShiftedModel",
    "lean:Physlib.QFT.Wick.Consistency.complexActionWeight"
  ]
  forbids_substitutes [
    "interpreting a removable global normalization factor as observable entropic selection",
    "claiming the finite density-matrix entropic gap constructs a continuum relative entropy",
    "claiming weighted Wick combinatorics proves convergence or renormalizability of the perturbation series"
  ]
  witnessed_by [
    Physlib.QFT.ScalarGreenFunctions.shiftImaginaryAction_partition,
    Physlib.QFT.ScalarGreenFunctions.shiftImaginaryAction_normalizedExpectation,
    Physlib.QFT.ScalarGreenFunctions.norm_complexActionWeight_antitone_imaginary,
    Physlib.QFT.ScalarGreenFunctions.globalEntropicOffset_damps_but_cancels,
    Physlib.QFT.ScalarGreenFunctions.complexActionWeightedDysonWick
  ]

/-! ## BT. Coulomb-gauge Yang--Mills variational vacuum -/

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector_mul_self where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector_trace where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.gluonPropagator_kernel_mul where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.gluonPropagator,
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.ghost_dyson_inverse where
  at_level bridge_theorem
  must_mention [HSub.hSub, HMul.hMul]

zil_file_contract physlib.entropicSpine.yangMillsCoulombGaugeVacuum where
  promises "The global spine exports the exact Coulomb-gauge transverse projector, its d-minus-one polarization trace, the Gaussian gluon propagator inverse identity on the transverse subspace, and the ghost Dyson inverse formula."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector",
    "lean:Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.gluonPropagator"
  ]
  forbids_substitutes [
    "claiming the variational gluon energy is solved rather than supplied nonzero",
    "claiming projector algebra derives confinement or infrared ghost dominance",
    "promoting the abstract ring Dyson identity to existence of a renormalized Yang--Mills vacuum"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector_mul_self,
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector_trace,
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.gluonPropagator_kernel_mul,
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.ghost_dyson_inverse
  ]

/-! ## BU. Total-correlation entropic clock and complex-action damping -/

zil_file_contract physlib.entropicSpine.totalCorrelationComplexWeight where
  promises "The public entropic spine exports a finite bipartite total-correlation clock whose calibrated imaginary action produces the existing master complex-action weight. Its modulus decreases under explicit Liouville-plus-Boltzmann premises. The remaining-relative-entropy clock has finite coordinate-marginalization, continuum measurable-map, and arbitrary common Markov-kernel data-processing theorems. Their discarded-information gains are nonnegative, their master amplitudes recover monotonically, and a packaged Markov-kernel CoarseGrainingStep has modulus exp minus its derived conditional-KL entropy production."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.totalCorrelation",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDataProcessingHTheorem.relativeEntropy_marginal_le",
    "lean:Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_map_le",
    "lean:Physlib.Thermodynamics.BoltzmannHTheorem.klDiv_comp_le",
    "lean:Physlib.Thermodynamics.BoltzmannHTheorem.CoarseGrainingStep.tauEnt_eq_entropyProduced",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight.complexActionPathIntegralWeight"
  ]
  forbids_substitutes [
    "claiming unconditional arrow monotonicity without the explicit Liouville and reduced Boltzmann entropy premises",
    "promoting the finite total-correlation theorem or the continuum classical-measure theorem to arbitrary multipartite quantum or type-III systems"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm_le_one,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm_eq_one_iff_independent,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.correlationComplexWeight_norm_antitone,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.klDivergence_marginalFst_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClock_marginalFst_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.marginalizationClockGain_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.remainingClockComplexWeight_norm_marginalFst_mono,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_map_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureMapClockGain_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight_norm_map_mono,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClock_comp_le,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureKernelClockGain_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.measureRemainingClockComplexWeight_norm_comp_mono,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.coarseGrainingComplexWeight_norm_le_one,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.TotalCorrelationEntropicClock.coarseGrainingComplexWeight_norm_eq_entropyProduced
  ]

#zil_formalization_lint_all
/- ZIL-END -/

end Physlib.Meta.EntropicSpineZil
