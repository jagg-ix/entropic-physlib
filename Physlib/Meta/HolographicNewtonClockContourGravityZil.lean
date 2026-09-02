/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravityField
public import
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits
public import
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux
public import
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux
public import
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux
/- ZIL-BEGIN -/
public meta import Zil
/- ZIL-END -/

/-!
# ZIL accountability for the holographic-G clock/contour/gravity bridge

This optional development/CI module classifies and contracts the existing Lean
capstone without adding theorem aliases or scientific definitions.  The
contract treats the result as a conditional bridge theorem: it records the
screen-count, weak-field, and complex-Einstein assumptions.  The metric, Ricci
matrix, and scalar curvature are no longer independent inputs: they are all
constructed from the metric-derived Levi-Civita geometry.  A separate ZIL
contract records that its exact `1+1` Einstein tensor vanishes.  A second
bridge contract records the sourced plane-symmetric linearized `Fin 4`
carrier.  A third records the general static spatial-Hessian upgrade, whose
complete Ricci matrix is contracted from the connection and whose source law
uses the full three-dimensional Laplacian.  The contracts forbid promoting
these results into an unconditional prediction of Newton's constant or an
exact nonlinear `3+1` derivation.
-/

@[expose] public section

/- ZIL-BEGIN -/
open Zil
/- ZIL-END -/

namespace Physlib.Meta.HolographicNewtonClockContourGravityZil

/- ZIL-BEGIN -/
zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_einstein_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.holographicBits,
    Physlib.Thermodynamics.sphereArea,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.nnLorentzForm,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.energyMomentumComplex,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.nnConverges,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.massShellContourAngle,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.massShellContourRadius,
    Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour.deltaEpsC,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldLeviCivita2,
    Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric.christoffelFromMetric,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.ricciFromConnection,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldMetric2,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldRicciMatrix2,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldScalarCurvature2,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinFieldEquation,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation,
    Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor.gravitationalTensor
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_einstein_chain
    where
  formalizes @ "claim:holographic-g-compton-nagao-levi-civita-einstein-conditional-chain",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:jacobson-1995",
  supported_by @ "paper:nagao-nielsen-2013",
  supported_by @ "paper:levi-civita-1917",
  requires @ "assumption:holographic-screen-bit-count",
  requires @ "assumption:weak-field-ricci-relation",
  requires @ "assumption:complex-einstein-field-equation-at-kappa-8piG-over-c4",
  caveat @ "claim:conditional-algebraic-consistency-not-empirical-measurement-of-G",
  caveat @ "claim:clock-and-contour-identities-do-not-derive-the-einstein-field-equation",
  caveat @ "claim:positive-mass-shell-ray-representation-not-a-general-contour-uniqueness-theorem",
  caveat @ "claim:exact-connection-ricci-retains-the-c-minus-four-correction",
  caveat @ "claim:connection-derived-ricci-matrix-is-an-explicit-one-plus-one-dimensional-demonstrator",
  caveat @ "claim:exact-one-plus-one-einstein-tensor-forces-the-real-source-carrier-to-zero",
  caveat @ "claim:newtonian-density-relation-is-separate-from-the-exact-one-plus-one-source-carrier",
  caveat @ "claim:levi-civita-connection-and-levi-civita-gravitational-tensor-are-distinct-objects"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_linearizedEinstein4_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.holographicBits,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.energyMomentumComplex,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.massShellContourAngle,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.massShellContourRadius,
    Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour.deltaEpsC,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedLeviCivita4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.ricciFromConnection,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedRicci4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedScalar4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.minkowskiMetric4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.restDustStressEnergy4,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinFieldEquation,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_linearizedEinstein4_chain
    where
  formalizes @ "claim:holographic-g-compton-nagao-levi-civita-sourced-linearized-3plus1-chain",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:jacobson-1995",
  supported_by @ "paper:nagao-nielsen-2013",
  supported_by @ "paper:levi-civita-1917",
  requires @ "assumption:holographic-screen-bit-count",
  requires @ "assumption:weak-field-ricci-relation",
  requires @ "assumption:plane-symmetric-static-newtonian-gauge-linearization",
  requires @ "assumption:complex-einstein-imaginary-sector-lambda-equals-kappa-S",
  caveat @ "claim:conditional-algebraic-consistency-not-empirical-measurement-of-G",
  caveat @ "claim:linearized-fin4-carrier-not-an-exact-nonlinear-einstein-solution",
  caveat @ "claim:one-axis-potential-dependence-not-a-general-three-coordinate-laplacian",
  caveat @ "claim:clock-and-contour-identities-do-not-derive-the-field-equation",
  caveat @ "claim:complex-field-equation-requires-the-explicit-imaginary-sector-relation"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_linearizedEinstein4Spatial_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.holographicBits,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.energyMomentumComplex,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.massShellContourAngle,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.massShellContourRadius,
    Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour.deltaEpsC,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.spatialLaplacian3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedLeviCivita4Spatial,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedConnection4Spatial,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.ricciMatrixFromConnection,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedLeviCivitaDeriv4Spatial,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedRicci4Spatial,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedScalar4Spatial,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedEinstein4Spatial,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.restDustStressEnergy4,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinFieldEquation,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_linearizedEinstein4Spatial_chain
    where
  formalizes @ "claim:holographic-g-compton-nagao-levi-civita-full-static-laplacian-chain",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:jacobson-1995",
  supported_by @ "paper:nagao-nielsen-2013",
  supported_by @ "paper:levi-civita-1917",
  requires @ "assumption:holographic-screen-bit-count",
  requires @ "assumption:general-static-newtonian-gauge-linearization",
  requires @ "assumption:symmetric-local-spatial-hessian",
  requires @ "assumption:complex-einstein-imaginary-sector-lambda-equals-kappa-S",
  caveat @ "claim:conditional-algebraic-consistency-not-empirical-measurement-of-G",
  caveat @ "claim:linearized-static-fin4-carrier-not-an-exact-nonlinear-einstein-solution",
  caveat @ "claim:full-spatial-laplacian-does-not-imply-spherical-symmetry",
  caveat @ "claim:clock-and-contour-identities-do-not-derive-the-field-equation",
  caveat @ "claim:complex-field-equation-requires-the-explicit-imaginary-sector-relation"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_staticPotentialJet3_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.holographicBits,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.energyMomentumComplex,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.massShellContourAngle,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.laplacian,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.SatisfiesPoisson,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.leviCivita4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.leviCivitaDeriv4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.ricci4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.scalar4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.einstein4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.ricciMatrixFromConnection,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinFieldEquation,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_staticPotentialJet3_chain
    where
  formalizes @ "claim:holographic-g-clock-contour-gravity-typed-static-potential-jet-chain",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:jacobson-1995",
  supported_by @ "paper:nagao-nielsen-2013",
  supported_by @ "paper:levi-civita-1917",
  requires @ "assumption:holographic-screen-bit-count",
  requires @ "assumption:typed-local-static-potential-gradient-and-symmetric-hessian",
  requires @ "assumption:complex-einstein-imaginary-sector-lambda-equals-kappa-S",
  caveat @ "claim:local-jet-data-not-a-global-potential-existence-theorem",
  caveat @ "claim:typed-jet-carrier-not-an-exact-nonlinear-einstein-solution",
  caveat @ "claim:clock-and-contour-identities-do-not-derive-the-field-equation",
  caveat @ "claim:complex-field-equation-requires-the-explicit-imaginary-sector-relation"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_C2Potential_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.holographicBits,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.energyMomentumComplex,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.massShellContourAngle,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialSpace3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.firstSpatialDerivativeAt3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.laplacianAt3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.ofFunctionAt,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.SatisfiesPoisson,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.leviCivita4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.leviCivitaDeriv4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.ricci4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.scalar4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.einstein4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.ricciMatrixFromConnection,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinFieldEquation,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_C2Potential_chain
    where
  formalizes @ "claim:holographic-g-clock-contour-gravity-C2-static-potential-chain",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:jacobson-1995",
  supported_by @ "paper:nagao-nielsen-2013",
  supported_by @ "paper:levi-civita-1917",
  requires @ "assumption:holographic-screen-bit-count",
  requires @ "assumption:C2-local-static-potential-on-real-cartesian-three-space",
  requires @ "assumption:pointwise-newtonian-poisson-source-law",
  requires @ "assumption:complex-einstein-imaginary-sector-lambda-equals-kappa-S",
  caveat @ "claim:C2-potential-supplies-a-local-symmetric-jet-not-a-global-boundary-value-solution",
  caveat @ "claim:analytic-static-jet-carrier-not-an-exact-nonlinear-einstein-solution",
  caveat @ "claim:clock-and-contour-identities-do-not-derive-the-field-equation",
  caveat @ "claim:complex-field-equation-requires-the-explicit-imaginary-sector-relation"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_staticPoissonField_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.holographicBits,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.energyMomentumComplex,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.massShellContourAngle,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.jetAt,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.firstSpatialDerivativeAt3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.laplacianAt3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.hodgeFluxDivergence3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.SatisfiesPoisson,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.leviCivita4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.leviCivitaDeriv4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.ricci4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.scalar4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.einstein4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.ricciMatrixFromConnection,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinFieldEquation,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_staticPoissonField_chain
    where
  formalizes @ "claim:holographic-g-clock-contour-gravity-global-static-poisson-field-chain",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:jacobson-1995",
  supported_by @ "paper:nagao-nielsen-2013",
  supported_by @ "paper:levi-civita-1917",
  requires @ "assumption:holographic-screen-bit-count",
  requires @ "assumption:global-C2-static-potential-and-density",
  requires @ "assumption:pointwise-poisson-equation-with-shared-newton-coupling",
  requires @ "assumption:pointwise-complex-einstein-imaginary-sector",
  caveat @ "claim:stored-poisson-field-does-not-prove-existence-uniqueness-or-boundary-conditions",
  caveat @ "claim:global-static-linearized-family-not-an-exact-nonlinear-einstein-spacetime",
  caveat @ "claim:clock-and-contour-identities-do-not-derive-the-field-equation",
  caveat @ "claim:complex-field-equation-requires-the-explicit-imaginary-sector-relation"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.comptonCellInference_comptonNagaoLeviCivita_staticPoissonField_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCellBits,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.inferenceMass,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglieFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.energyMomentumComplex,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.hodgeFluxDivergence3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.leviCivita4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.ricciMatrixFromConnection,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinFieldEquation,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.comptonCellInference_comptonNagaoLeviCivita_staticPoissonField_chain
    where
  formalizes @ "claim:independent-compton-cell-inference-variance-coupling-drives-the-static-poisson-clock-contour-hodge-levi-civita-and-einstein-chain",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_staticPoissonField_chain",
  requires @ "assumption:caticha-cafaro-inference-mass-is-inverse-position-variance",
  requires @ "assumption:compton-cell-screen-tiling-is-the-independent-bit-count",
  requires @ "assumption:the-static-poisson-field-stores-that-same-area-per-compton-cell-coupling",
  requires @ "assumption:global-C2-static-potential-and-pointwise-poisson-law",
  requires @ "assumption:pointwise-complex-einstein-imaginary-sector",
  caveat @ "epistemic:g-equals-hbar-c-sigma0-to-the-fourth-is-conditional-on-the-cell-tiling-and-inference-mass-identifications-not-a-fit-free-numerical-prediction",
  caveat @ "claim:the-theorem-does-not-construct-the-static-poisson-field-or-prove-boundary-value-existence-or-uniqueness",
  caveat @ "claim:the-clock-and-contour-identities-do-not-derive-the-poisson-or-einstein-field-equations",
  caveat @ "claim:the-pointwise-static-carrier-is-linearized-not-an-exact-nonlinear-spacetime"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPoissonField3_pointwiseGeometry
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPoissonField3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPotential3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.firstSpatialDerivativeAt3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.jetAt,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.hodgeFluxDivergence3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.SatisfiesPoisson,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.leviCivita4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.leviCivitaDeriv4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.ricci4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.scalar4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.einstein4,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.ricciMatrixFromConnection,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinFieldEquation,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPoissonField3_pointwiseGeometry
    where
  formalizes @ "claim:explicit-homogeneous-density-quadratic-poisson-field-linearized-geometry",
  supported_by @ "paper:levi-civita-1917",
  requires @ "assumption:constant-whole-space-density-model",
  requires @ "assumption:nonzero-light-speed-for-EFE-equivalence",
  requires @ "assumption:pointwise-complex-einstein-imaginary-sector",
  caveat @ "claim:quadratic-whole-space-potential-not-an-isolated-finite-mass-source",
  caveat @ "claim:quadratic-whole-space-potential-not-asymptotically-flat",
  caveat @ "claim:explicit-linearized-model-not-an-interior-Schwarzschild-or-nonlinear-Einstein-solution",
  caveat @ "claim:complex-field-equation-requires-the-explicit-imaginary-sector-relation"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.hodgeFluxDivergence3_and_einsteinFieldEquation_at
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.hodgeFluxDivergence3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.jetAt,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinFieldEquation
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.hodgeFluxDivergence3_and_einsteinFieldEquation_at
    where
  formalizes @ "claim:static-cartesian-poisson-as-sourced-d-hodge-d-potential-and-linearized-EFE",
  supported_by @ "formalization:three-dimensional-levi-civita-tensor-and-contraction-identities",
  requires @ "assumption:oriented-cartesian-euclidean-three-space",
  requires @ "assumption:global-C2-static-potential-and-pointwise-poisson-law",
  requires @ "assumption:nonzero-light-speed-for-linearized-EFE",
  caveat @ "claim:d-hodge-d-identity-is-an-exact-reexpression-of-the-cartesian-laplacian",
  caveat @ "claim:not-a-curved-manifold-or-lorentzian-hodge-star-construction",
  caveat @ "claim:hodge-reexpression-does-not-independently-derive-gravity-or-newtons-constant",
  caveat @ "claim:result-is-static-linearized-not-an-exact-nonlinear-einstein-spacetime"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousHodgeScreen_bitCount_gravity_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.holographicBits,
    Physlib.Thermodynamics.sphereArea,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPoissonField3,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.jetAt,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.hodgeFluxDivergence3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousBallMass3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousSphereRadialPotentialDerivative3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousSphereHodgeFlux3,
    Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence.nnPathWeight,
    Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa.horizonImaginaryAction,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinFieldEquation
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousHodgeScreen_bitCount_gravity_chain
    where
  formalizes @ "claim:homogeneous-static-hodge-source-to-holographic-spherical-screen-gravity-chain",
  supported_by @ "paper:gauss-1813",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:nagao-nielsen-2013",
  supported_by @ "paper:einstein-1915",
  requires @ "assumption:constant-density-isotropic-quadratic-potential",
  requires @ "assumption:oriented-cartesian-euclidean-three-space",
  requires @ "assumption:nonzero-screen-radius",
  requires @ "assumption:holographic-screen-bit-count",
  requires @ "assumption:static-linearized-newtonian-gauge",
  caveat @ "claim:spherical-flux-is-constant-normal-component-times-area-not-a-general-stokes-theorem",
  caveat @ "claim:whole-space-quadratic-potential-not-an-isolated-finite-mass-source",
  caveat @ "claim:boundary-bit-identity-does-not-derive-the-local-poisson-law",
  caveat @ "claim:nagao-nielsen-factor-and-clock-identities-do-not-derive-the-einstein-equation",
  caveat @ "claim:result-is-static-linearized-not-an-exact-nonlinear-einstein-spacetime"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.comptonCellInference_homogeneousHodgeScreen_gravity_chain
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousHodgeScreen_bitCount_gravity_chain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  formalizes @ "claim:independent-compton-cell-inference-coupling-drives-homogeneous-hodge-flux-horizon-damping-and-linearized-einstein-chain",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:compton-cell-screen-tiling-is-the-independent-bit-count",
  requires @ "assumption:caticha-cafaro-inference-mass-is-inverse-position-variance",
  requires @ "assumption:constant-density-isotropic-quadratic-potential",
  caveat @ "claim:homogeneous-quadratic-carrier-is-not-an-isolated-source-or-nonlinear-spacetime",
  caveat @ "epistemic:the-screen-tiling-and-inference-variance-remain-explicit-model-inputs"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewton_surfaceFlux_bitCount_gravity_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.holographicBits,
    Physlib.Thermodynamics.sphereArea,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonPotentialDistribution3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonExteriorField3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.sphereFluxIntegral3,
    Physlib.Distribution.diracDelta,
    Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence.nnPathWeight,
    Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa.horizonImaginaryAction
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewton_surfaceFlux_bitCount_gravity_chain
    where
  formalizes @ "claim:isolated-newton-kernel-spherical-surface-flux-distributional-source-and-entropic-screen-chain",
  supported_by @ "paper:gauss-1813",
  supported_by @ "paper:poisson-1813",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:nagao-nielsen-2013",
  requires @ "assumption:origin-centered-positive-radius-spherical-screen",
  requires @ "assumption:isolated-inverse-radius-newton-kernel",
  requires @ "assumption:holographic-screen-bit-count",
  caveat @ "claim:unit-sphere-parameterized-integral-not-a-general-arbitrary-surface-stokes-theorem",
  caveat @ "claim:distributional-dirac-source-not-a-smooth-rest-dust-stress-energy-field",
  caveat @ "claim:point-source-law-is-newtonian-and-does-not-produce-an-exact-nonlinear-einstein-spacetime",
  caveat @ "claim:bit-count-and-nagao-nielsen-factor-do-not-derive-the-distributional-laplacian-law"

zil_theorem_intent Space.distTranslate_diracDelta where
  at_level structural
  must_mention [
    Space.distTranslate,
    Physlib.Distribution.diracDelta
  ]

zil_theorem_intent Space.distTranslate_add where
  at_level structural
  must_mention [
    Space.distTranslate
  ]

zil_theorem_intent Space.distLaplacian_distTranslate where
  at_level structural
  must_mention [
    Space.distLaplacian,
    Space.distTranslate
  ]

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonAt_surfaceFlux_bitCount_gravity_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.Thermodynamics.holographicBits,
    Physlib.Thermodynamics.sphereArea,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonPotentialDistribution3At,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonExteriorField3At,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.sphereFluxIntegral3At,
    Physlib.Distribution.diracDelta,
    Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence.nnPathWeight,
    Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa.horizonImaginaryAction
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonAt_surfaceFlux_bitCount_gravity_chain
    where
  formalizes @ "claim:translation-covariant-isolated-newton-sphere-flux-dirac-source-and-entropic-screen-chain",
  supported_by @ "paper:gauss-1813",
  supported_by @ "paper:poisson-1813",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:nagao-nielsen-2013",
  requires @ "assumption:positive-radius-round-spherical-screen-centered-at-source",
  requires @ "assumption:spatial-translation-covariance",
  requires @ "assumption:isolated-inverse-radius-newton-kernel",
  requires @ "assumption:holographic-screen-bit-count",
  caveat @ "claim:translated-centered-sphere-is-not-an-arbitrary-surface-stokes-theorem",
  caveat @ "claim:single-translated-source-does-not-establish-finite-or-continuous-source-superposition",
  caveat @ "claim:distributional-dirac-source-is-not-a-smooth-rest-dust-stress-energy-field",
  caveat @ "claim:translation-covariance-does-not-produce-an-exact-nonlinear-einstein-point-mass-solution"

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.comptonCellInference_isolatedNewtonAt_surfaceFlux_gravity_chain
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonAt_surfaceFlux_bitCount_gravity_chain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  formalizes @ "claim:independent-compton-cell-inference-coupling-drives-translated-isolated-dirac-source-actual-sphere-flux-horizon-damping-and-einstein-coupling",
  epistemic_status @ "ansatz-loaded",
  requires @ "assumption:compton-cell-screen-tiling-is-the-independent-bit-count",
  requires @ "assumption:caticha-cafaro-inference-mass-is-inverse-position-variance",
  requires @ "assumption:positive-round-screen-centered-at-the-singular-source",
  caveat @ "claim:centered-round-sphere-result-is-not-an-arbitrary-surface-stokes-theorem",
  caveat @ "claim:singular-distributional-source-is-not-an-exact-nonlinear-point-mass-spacetime",
  caveat @ "epistemic:the-screen-tiling-and-inference-variance-remain-explicit-model-inputs"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPointSources_bitCount_gravity_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPotentialDistribution3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finitePointMassDistribution3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteTotalMass,
    Physlib.Thermodynamics.holographicBits,
    Physlib.Distribution.diracDelta,
    Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence.nnPathWeight,
    Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa.horizonImaginaryAction
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPointSources_bitCount_gravity_chain
    where
  formalizes @ "claim:finite-point-source-distributional-poisson-superposition-translation-covariance-and-total-mass-entropic-screen-chain",
  supported_by @ "paper:poisson-1813",
  supported_by @ "paper:gauss-1813",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:nagao-nielsen-2013",
  requires @ "assumption:finite-family-of-newtonian-point-sources",
  requires @ "assumption:linear-superposition-of-distributions",
  requires @ "assumption:common-spatial-translation-covariance",
  requires @ "assumption:holographic-screen-bit-count-evaluated-at-total-mass",
  caveat @ "claim:no-geometric-enclosure-condition-is-proved-for-the-chosen-screen",
  caveat @ "claim:finite-source-poisson-law-does-not-prove-an-arbitrary-enclosing-surface-flux-law",
  caveat @ "claim:finite-dirac-source-is-not-a-smooth-rest-dust-stress-energy-field",
  caveat @ "claim:linear-newtonian-superposition-is-not-an-exact-nonlinear-einstein-multi-body-solution"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourcesEinstein00.finiteNewtonPointSources_distributionalEinstein00_bitCount_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00.DistributionalWeakFieldEinstein00Equation3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPotentialDistribution3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finitePointMassDistribution3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteTotalMass,
    Physlib.Thermodynamics.holographicBits,
    Physlib.Distribution.diracDelta,
    Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence.nnPathWeight,
    Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa.horizonImaginaryAction
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourcesEinstein00.finiteNewtonPointSources_distributionalEinstein00_bitCount_chain
    where
  formalizes @ "claim:finite-point-source-distributional-linearized-einstein-00-poisson-and-total-mass-entropic-screen-chain",
  supported_by @ "paper:einstein-1916",
  supported_by @ "paper:poisson-1813",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:nagao-nielsen-2013",
  requires @ "assumption:static-linearized-newtonian-gauge-00-coefficient-derived-in-smooth-3-plus-1-carrier",
  requires @ "assumption:nonzero-speed-of-light-parameter",
  requires @ "assumption:finite-family-of-newtonian-point-sources",
  requires @ "assumption:distributional-poisson-law-and-linear-superposition",
  requires @ "assumption:holographic-screen-bit-count-evaluated-at-total-mass",
  caveat @ "claim:only-the-static-scalar-linearized-00-equation-is-distribution-valued",
  caveat @ "claim:no-full-distribution-valued-curvature-or-einstein-tensor-is-constructed",
  caveat @ "claim:finite-dirac-source-is-not-a-smooth-rest-dust-field",
  caveat @ "claim:no-arbitrary-enclosing-surface-flux-law-is-proved",
  caveat @ "claim:no-exact-nonlinear-einstein-multi-body-solution-is-claimed"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonPointSources_sourceResolvedFlux_distributionalEinstein00_bitCount_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00.DistributionalWeakFieldEinstein00Equation3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPotentialDistribution3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finitePointMassDistribution3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteTotalMass,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonSourceResolvedFluxDistribution3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonSourceResolvedSphereFlux3,
    Physlib.Thermodynamics.holographicBits,
    Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence.nnPathWeight,
    Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa.horizonImaginaryAction
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonPointSources_sourceResolvedFlux_distributionalEinstein00_bitCount_chain
    where
  formalizes @ "claim:finite-point-source-resolved-centered-sphere-flux-distributional-einstein-00-and-entropic-screen-chain",
  supported_by @ "paper:gauss-1813",
  supported_by @ "paper:poisson-1813",
  supported_by @ "paper:einstein-1916",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:nagao-nielsen-2013",
  requires @ "assumption:finite-family-of-newtonian-point-sources",
  requires @ "assumption:positive-radius-round-sphere-centered-at-each-source",
  requires @ "assumption:source-resolved-flux-uses-only-each-sources-own-exterior-field",
  requires @ "assumption:static-scalar-distributional-linearized-einstein-00-carrier",
  requires @ "assumption:holographic-screen-bit-count-evaluated-at-total-mass",
  caveat @ "claim:source-resolved-flux-is-not-total-field-flux-through-one-enclosing-screen",
  caveat @ "claim:cross-source-flux-terms-are-not-evaluated",
  caveat @ "claim:no-off-center-solid-angle-or-general-divergence-theorem-is-proved",
  caveat @ "claim:the-holographic-screen-is-not-identified-with-the-source-centered-sphere-family",
  caveat @ "claim:no-exact-nonlinear-einstein-multi-body-solution-is-claimed"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonExteriorField3_sphereFlux_decompose
    where
  at_level structural
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonExteriorField3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.sphereFluxIntegral3At,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonExteriorField3At
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonExteriorField3_sphereFlux_decompose
    where
  formalizes @ "claim:finite-superposed-newton-field-one-round-screen-flux-decomposes-into-actual-off-center-single-source-fluxes",
  supported_by @ "paper:gauss-1813",
  requires @ "assumption:finite-family-of-newtonian-point-sources",
  requires @ "assumption:positive-radius-round-spherical-screen",
  requires @ "assumption:no-source-lies-on-the-screen-boundary",
  caveat @ "claim:linearity-does-not-evaluate-the-off-center-single-source-integrals",
  caveat @ "claim:no-arbitrary-surface-divergence-theorem-is-proved"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonZonalKernel_intervalIntegral
    where
  at_level physical_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonZonalKernel
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonZonalKernel_intervalIntegral
    where
  formalizes @ "claim:off-center-newton-zonal-kernel-interval-integral-is-two-inside-and-zero-outside",
  supported_by @ "paper:gauss-1813",
  supported_by @ "paper:poisson-1813",
  requires @ "assumption:positive-spherical-screen-radius",
  requires @ "assumption:nonnegative-source-offset-radius",
  requires @ "assumption:source-does-not-lie-on-screen-boundary",
  caveat @ "claim:this-is-the-one-variable-calculus-core-used-by-the-separately-proved-sphere-measure-pushforward"

zil_theorem_intent Space.integral_comp_inner_unit_toSphere_eq_intervalIntegral where
  at_level structural
  must_mention []

zil attach Space.integral_comp_inner_unit_toSphere_eq_intervalIntegral where
  formalizes @ "claim:S2-zonal-integration-about-any-unit-axis-is-two-pi-times-the-height-interval-integral",
  supported_by @ "paper:gauss-1813",
  requires @ "assumption:unit-axis-in-three-dimensional-euclidean-space",
  requires @ "assumption:interval-integrable-zonal-kernel",
  caveat @ "claim:this-is-a-round-unit-sphere-measure-transport-theorem-not-an-arbitrary-surface-formula"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.newtonSphereFluxLaw3
    where
  at_level physical_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.NewtonSphereFluxLaw3
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.newtonSphereFluxLaw3
    where
  formalizes @ "claim:off-center-newton-point-source-flux-through-a-round-sphere-is-four-pi-GM-inside-and-zero-outside",
  supported_by @ "paper:gauss-1813",
  supported_by @ "paper:poisson-1813",
  requires @ "assumption:positive-radius-round-spherical-screen",
  requires @ "assumption:source-does-not-lie-on-screen-boundary",
  caveat @ "claim:no-arbitrary-surface-divergence-theorem-is-inferred",
  caveat @ "claim:the-on-boundary-singular-case-remains-excluded"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonPointSources_enclosingFlux_distributionalEinstein00_bitCount_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonExteriorField3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.sphereFluxIntegral3At,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00.DistributionalWeakFieldEinstein00Equation3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPotentialDistribution3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finitePointMassDistribution3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteTotalMass,
    Physlib.Thermodynamics.holographicBits,
    Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence.nnPathWeight,
    Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa.horizonImaginaryAction
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonPointSources_enclosingFlux_distributionalEinstein00_bitCount_chain
    where
  formalizes @ "claim:finite-point-source-total-field-flux-through-one-enclosing-sphere-with-distributional-einstein-00-and-entropic-screen-chain",
  supported_by @ "paper:gauss-1813",
  supported_by @ "paper:poisson-1813",
  supported_by @ "paper:einstein-1916",
  supported_by @ "paper:verlinde-2011",
  supported_by @ "paper:nagao-nielsen-2013",
  requires @ "assumption:finite-family-of-newtonian-point-sources",
  requires @ "assumption:positive-radius-round-spherical-screen",
  requires @ "assumption:every-source-lies-strictly-inside-the-screen",
  requires @ "assumption:static-scalar-distributional-linearized-einstein-00-carrier",
  requires @ "assumption:holographic-screen-bit-count-evaluated-at-total-mass",
  caveat @ "claim:the-off-center-solid-angle-law-is-proved-only-for-round-spherical-screens",
  caveat @ "claim:the-unconditional-flux-evaluation-is-specific-to-round-spherical-screens",
  caveat @ "claim:no-arbitrary-surface-divergence-theorem-is-proved",
  caveat @ "claim:no-source-may-lie-on-the-singular-screen-boundary",
  caveat @ "claim:no-exact-nonlinear-einstein-multi-body-solution-is-claimed"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.comptonCellInference_finiteNewtonPointSources_enclosingFluxEinstein00_chain
    where
  at_level bridge_theorem
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCellBits,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.inferenceMass,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance.entropicProperDistance,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonExteriorField3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.sphereFluxIntegral3At,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00.DistributionalWeakFieldEinstein00Equation3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPotentialDistribution3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finitePointMassDistribution3,
    Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence.nnPathWeight
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.comptonCellInference_finiteNewtonPointSources_enclosingFluxEinstein00_chain
    where
  formalizes @ "claim:independent-compton-cell-inference-variance-coupling-drives-finite-source-enclosing-flux-distributional-einstein-00-and-entropic-damping",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonPointSources_enclosingFlux_distributionalEinstein00_bitCount_chain",
  requires @ "assumption:caticha-cafaro-inference-mass-is-inverse-position-variance",
  requires @ "assumption:compton-cell-screen-tiling-is-the-independent-bit-count",
  requires @ "assumption:finite-family-of-point-sources-strictly-inside-the-resulting-round-screen",
  caveat @ "epistemic:the-screen-tiling-and-inference-variance-are-model-inputs-not-an-independent-numerical-measurement-of-G",
  caveat @ "claim:the-flux-result-is-for-one-round-sphere-not-an-arbitrary-surface-divergence-theorem",
  caveat @ "claim:the-einstein-00-carrier-is-distributional-and-weak-field-not-a-nonlinear-many-body-spacetime"

zil_theorem_intent
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldEinsteinTensor2_eq_zero
    where
  at_level algebraic
  must_mention [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldMetric2,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldRicciMatrix2,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldScalarCurvature2,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinTensor
  ]

zil attach
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldEinsteinTensor2_eq_zero
    where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldRicciMatrix2_eq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldScalarCurvature2_eq",
  formalizes @ "claim:exact-one-plus-one-weak-field-einstein-tensor-vanishes",
  requires @ "assumption:nondegenerate-weak-field-metric-component-A",
  requires @ "assumption:nonzero-light-speed",
  caveat @ "claim:two-dimensional-einstein-identity-not-a-sourced-four-dimensional-field-equation",
  caveat @ "claim:nonzero-newtonian-density-requires-a-higher-dimensional-carrier"

zil_file_contract physlib.holographicNewtonClockContourGravity.geometry2 where
  promises "formalization:metric-to-connection-to-ricci-to-scalar-to-zero-1plus1-Einstein-tensor"
  at_level algebraic
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldMetric2",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldMetric2Inv",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldLeviCivita2_eq_christoffelFromMetric",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.ricciMatrixFromConnection",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldRicciMatrix2_eq",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.RicciWeylDecompositionTetrad.ricciScalarContraction",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldScalarCurvature2",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldScalarCurvature2_eq",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldEinsteinTensor2_eq_zero"
  ]
  forbids_substitutes [
    "treating the exact 1+1 Einstein tensor as a nonzero matter-sourced 3+1 Einstein tensor",
    "supplying an unrelated scalar curvature or metric to the connection-derived Ricci matrix",
    "dropping the exact O(c^-4) curvature correction"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldEinsteinTensor2_eq_zero
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.geometry4Linearized where
  promises "formalization:metric-Christoffel-R00-and-sourced-linearized-3plus1-Einstein-equation"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.minkowskiMetric4",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldMetric4",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldMetricDeriv4",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedLeviCivita4",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedLeviCivita4_100",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedLeviCivita4_isTorsionFree",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearized_ricci00_from_connection",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedRicci4",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedScalar4",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedEinstein4_eq",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.restDustStressEnergy4",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedEFE4_iff_poisson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedComplexEFE4_of_poisson"
  ]
  forbids_substitutes [
    "treating the linearized Fin 4 carrier as an exact nonlinear Einstein solution",
    "claiming spherical symmetry or a general three-coordinate Laplacian from one-axis dependence",
    "restoring the discarded Gamma-Gamma terms without a nonlinear metric inverse and curvature computation",
    "deriving the imaginary complex-Einstein sector from the Poisson equation"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_linearizedEinstein4_chain
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.geometry4StaticSpatial where
  promises "formalization:general-static-metric-gradient-to-complete-connection-derived-Ricci-and-full-Laplacian-EFE"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.minkowskiMetric4",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldMetricDeriv4Spatial",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedLeviCivita4Spatial",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedLeviCivita4Spatial_eq_connection",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedLeviCivita4Spatial_acceleration",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedLeviCivita4Spatial_isTorsionFree",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedConnection4Spatial",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedLeviCivitaDeriv4Spatial",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedConnDeriv4Spatial",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedLeviCivitaDeriv4Spatial_eq_connectionDeriv",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.ricciMatrixFromConnection_zero_eq_linearized",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedRicci4Spatial",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedRicci4Spatial_eq",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedRicci4Spatial_plane",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedScalar4Spatial_eq",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedEinstein4Spatial_eq",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedEFE4Spatial_iff_poisson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1.weakFieldLinearizedComplexEFE4Spatial_of_poisson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_linearizedEinstein4Spatial_chain"
  ]
  forbids_substitutes [
    "treating the full static spatial Laplacian carrier as an exact nonlinear Einstein solution",
    "claiming spherical symmetry from arbitrary Cartesian Hessian data",
    "retaining Gamma-Gamma terms after declaring a first-order linearized curvature truncation",
    "using a compact Christoffel array without proving equality to the metric-derived Levi-Civita connection",
    "packaging unverified Ricci components independently of the connection contraction",
    "deriving the imaginary complex-Einstein sector from the real Poisson equation"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_linearizedEinstein4Spatial_chain
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.geometry4StaticJet where
  promises "formalization:typed-static-potential-jet-to-metric-connection-Ricci-Poisson-and-complex-EFE"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.ofComponents",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.laplacian",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.metricDeriv4",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.leviCivita4",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.leviCivitaDeriv4",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.ricci4",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.scalar4",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.einstein4",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.SatisfiesPoisson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.leviCivita4_eq_connection",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.leviCivitaDeriv4_eq_connectionDeriv",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.ricci4_eq",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.scalar4_eq",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.einstein4_eq",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.efe4_iff_poisson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.complexEFE4_of_poisson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_staticPotentialJet3_chain"
  ]
  forbids_substitutes [
    "passing unrelated gradient and Hessian entries after a typed jet has been selected",
    "dropping the Hessian symmetry proof required by the typed local jet",
    "claiming that arbitrary local jet data proves existence of a global smooth potential",
    "treating the jet-level static linearized carrier as an exact nonlinear Einstein solution",
    "deriving the independent imaginary complex-Einstein sector from the real Poisson predicate"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_staticPotentialJet3_chain
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.geometry4StaticC2Potential where
  promises "formalization:C2-static-potential-to-symmetric-jet-metric-connection-Ricci-Poisson-and-complex-EFE"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialSpace3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.coordinateDirection3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.firstSpatialDerivativeAt3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.secondSpatialDerivativeAt3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.laplacianAt3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.secondSpatialDerivativeAt3_comm",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.ofFunctionAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.value_ofFunctionAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.gradient_ofFunctionAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.hessian_ofFunctionAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.laplacian_ofFunctionAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.satisfiesPoisson_ofFunctionAt_iff",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.efe4_ofFunctionAt_iff_poisson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.complexEFE4_ofFunctionAt_poisson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_C2Potential_chain"
  ]
  forbids_substitutes [
    "asserting mixed-partial symmetry independently when it follows from the supplied C2 potential",
    "replacing the Frechet derivatives with unrelated gradient or Hessian component data",
    "claiming that pointwise C2 jet construction solves a global Poisson boundary-value problem",
    "treating the analytic static linearized carrier as an exact nonlinear Einstein solution",
    "deriving the independent imaginary complex-Einstein sector from the real Poisson equation"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_C2Potential_chain
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.geometry4StaticPoissonField where
  promises "formalization:global-C2-static-Poisson-field-to-pointwise-Hodge-flux-metric-connection-Ricci-and-complex-EFE-family"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.newtonConstant",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.potential",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.density",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.potential_contDiff",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.poisson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.jetAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.jetAt_satisfiesPoisson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.hodgeFluxDivergence3_at",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.weakFieldRicci00_at",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.leviCivita4_at_eq_connection",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.ricciFromConnection_at_eq",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.einsteinFieldEquation_at",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.complexEinsteinFieldEquation_at",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.pointwise_staticLinearizedGeometry",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_staticPoissonField_chain"
  ]
  forbids_substitutes [
    "using a Newton coupling in the holographic screen different from the coupling stored in the Poisson field",
    "replacing the single global potential by unrelated pointwise gradient or Hessian data",
    "claiming that a bundled Poisson law proves existence uniqueness boundary conditions or asymptotic decay",
    "treating the pointwise static linearized family as an exact nonlinear Einstein spacetime",
    "deriving the independent imaginary complex-Einstein field from the real Poisson equation"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_staticPoissonField_chain
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.comptonCellInferenceStaticPoissonField where
  promises "formalization:independent-Compton-cell-inference-variance-G-to-static-Poisson-clock-contour-Hodge-Levi-Civita-and-Einstein-chain"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.comptonCellBits",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.newtonG_from_positionVariance",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant.holographicBits_eq_comptonCellBits_of_inferenceVariance",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics.inferenceMass",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.newtonConstant",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_staticPoissonField_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.comptonCellInference_comptonNagaoLeviCivita_staticPoissonField_chain"
  ]
  forbids_substitutes [
    "using the G-dependent Planck-cell count as the independent input that is supposed to determine G",
    "silently replacing the Newton coupling stored in the bundled Poisson field",
    "fitting sigma0 to measured G and then presenting G equals hbar c sigma0 to the fourth as an independent numerical prediction",
    "claiming construction or uniqueness of the global Poisson field from the coupling identity",
    "promoting the static linearized pointwise carrier to an exact nonlinear Einstein spacetime"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.comptonCellInference_comptonNagaoLeviCivita_staticPoissonField_chain
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.homogeneousDensityExample where
  promises "formalization:explicit-constant-density-quadratic-potential-Poisson-field-and-pointwise-linearized-EFE"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPotentialCoefficient",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPotential3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPotential3_contDiff",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.firstSpatialDerivativeAt3_homogeneousDensityPotential",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.secondSpatialDerivativeAt3_homogeneousDensityPotential",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.laplacianAt3_homogeneousDensityPotential",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPoissonField3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.hodgeFluxDivergence3_at",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPoissonField3_pointwiseGeometry"
  ]
  forbids_substitutes [
    "claiming non-vacuity using only the zero-potential zero-density vacuum",
    "claiming the whole-space quadratic potential is generated by an isolated finite total mass",
    "claiming asymptotic flatness for a potential growing quadratically at spatial infinity",
    "identifying the linearized constant-density model with the nonlinear interior Schwarzschild solution",
    "deriving the independent imaginary complex-Einstein field from the real Poisson equation"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.homogeneousDensityPoissonField3_pointwiseGeometry
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.geometry4StaticHodge where
  promises "formalization:oriented-cartesian-three-dimensional-hodge-star-d-star-d-potential-equals-laplacian-and-shared-Poisson-EFE-source"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionLieAlgebra.leviCivita3",
    "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.Tensor.leviCivita3_swap₁₂",
    "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.Tensor.leviCivita3_double_contraction",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.hodgeStarOneForm3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.hodgeStarTwoForm3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.hodgeStarOneForm3_antisymm",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.hodgeStarTwoForm3_hodgeStarOneForm3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.gradientHodgeFlux2",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.gradientHodgeFlux2_components",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.gradientHodgeFlux2_recovers_gradient",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.hodgeFluxDivergence3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.hodgeFluxDivergence3_eq_laplacian",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3.satisfiesPoisson_iff_hodgeFluxDivergence3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.hodgeFluxDivergence3_at",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.hodgeFluxDivergence3_and_einsteinFieldEquation_at"
  ]
  forbids_substitutes [
    "calling the oriented Cartesian three-dimensional star a general curved-manifold Hodge star",
    "silently replacing the Euclidean spatial convention by a Lorentzian spacetime convention",
    "claiming d-star-d derives Poisson dynamics independently when it is proved equal to the existing Laplacian",
    "claiming the Hodge reformulation derives Newton's constant or the clock and contour identities",
    "treating the shared static source carrier as an exact nonlinear Einstein solution"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3.hodgeFluxDivergence3_and_einsteinFieldEquation_at
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.homogeneousHodgeScreen where
  promises "formalization:homogeneous-local-d-star-d-source-to-spherical-screen-flux-bit-count-contour-and-linearized-EFE"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousBallMass3",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousSphereRadialPotentialDerivative3",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousSphereRadialPotentialDerivative3_eq_newtonAcceleration",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousSphereHodgeFlux3",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousSphereHodgeFlux3_eq_fourPiG_mass",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousSphereRadialPotentialDerivative3_bitForm",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousHodgeScreen_bitCount_gravity_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.comptonCellInference_homogeneousHodgeScreen_gravity_chain"
  ]
  forbids_substitutes [
    "promoting the homogeneous constant-normal-component calculation to a general divergence or Stokes theorem",
    "claiming that the whole-space quadratic potential is the exterior field of an isolated compact source",
    "using different Newton couplings for the local Poisson field and the holographic screen",
    "claiming that the bit count or Nagao-Nielsen contour derives the local differential field equation",
    "treating the static linearized Einstein carrier as an exact nonlinear spacetime"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousHodgeScreen_bitCount_gravity_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.comptonCellInference_homogeneousHodgeScreen_gravity_chain
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.isolatedNewtonSphereFlux where
  promises "formalization:isolated-inverse-radius-potential-actual-sphere-flux-distributional-dirac-source-and-entropic-bit-screen"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.UnitSphere3",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.sphereSurfaceIntegral3",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.sphereFluxIntegral3",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.unitSphere3_measureReal_univ",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonPotentialRadial_hasDerivAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonExteriorField3_sphereFlux",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonPotentialDistribution3_laplacian",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewton_laplacian_eq_sphereFlux_smul_dirac",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewton_surfaceFlux_bitCount_gravity_chain"
  ]
  forbids_substitutes [
    "replacing the actual Bochner angular integral with only an area-times-component definition",
    "promoting the origin-centered sphere computation to a general divergence theorem for arbitrary domains",
    "treating the Dirac source as a smooth density accepted by the static rest-dust Einstein carrier",
    "claiming an exact nonlinear Einstein point-mass solution from the Newtonian distributional kernel",
    "claiming that holographic bits derive the inverse-radius fundamental solution"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewton_surfaceFlux_bitCount_gravity_chain
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.isolatedNewtonTranslatedSphereFlux where
  promises "formalization:arbitrary-center-isolated-newton-sphere-flux-translated-dirac-source-and-entropic-bit-screen"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Space.distTranslate_diracDelta",
    "lean:Space.distLaplacian_distTranslate",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.sphereFluxIntegral3At",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonExteriorField3At",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonExteriorField3At_sphereFlux",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonPotentialDistribution3At",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonPotentialDistribution3At_laplacian",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonAt_laplacian_eq_sphereFlux_smul_dirac",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonAt_surfaceFlux_bitCount_gravity_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.comptonCellInference_isolatedNewtonAt_surfaceFlux_gravity_chain"
  ]
  forbids_substitutes [
    "promoting a round sphere centered at the translated source to a general arbitrary-surface divergence theorem",
    "claiming that one translated source proves finite, countable, or continuous source superposition",
    "treating the translated Dirac source as a smooth density accepted by the rest-dust field carrier",
    "claiming an exact nonlinear Einstein point-mass spacetime from translation covariance",
    "claiming that holographic bits derive spatial translation covariance or the inverse-radius kernel"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonAt_surfaceFlux_bitCount_gravity_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.comptonCellInference_isolatedNewtonAt_surfaceFlux_gravity_chain
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.finiteNewtonPointSources where
  promises "formalization:finite-newton-point-sources-expanded-and-factored-distributional-poisson-law-translation-covariance-and-total-mass-screen"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Space.distTranslate_add",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finitePointMassDistribution3",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPotentialDistribution3",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteTotalMass",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPotentialDistribution3_laplacian_expanded",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPotentialDistribution3_laplacian",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finitePointMassDistribution3_translate",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPotentialDistribution3_translate",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPointSources_bitCount_gravity_chain"
  ]
  forbids_substitutes [
    "claiming an enclosing-screen flux identity without a proved enclosure condition and divergence theorem",
    "promoting finite linear superposition to countable or continuous source integration",
    "treating a finite Dirac sum as a smooth density accepted by the rest-dust field carrier",
    "claiming a nonlinear Einstein multi-body solution from a linear Newtonian distributional sum",
    "claiming that holographic bits derive finite-source superposition or spatial translation covariance"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources.finiteNewtonPointSources_bitCount_gravity_chain
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.finiteNewtonPointSourcesEinstein00 where
  promises "formalization:finite-point-source-distributional-static-linearized-einstein-00-poisson-equivalence-and-entropic-screen-chain"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00.weakFieldLinearizedEinstein4Spatial_apply_00",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00.weakFieldLinearizedEinstein00Distribution3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00.restDustStressEnergy00Distribution3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00.DistributionalWeakFieldEinstein00Equation3",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00.distributionalWeakFieldEinstein00Equation3_iff_poisson",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00.weakFieldLinearizedEinstein00Distribution3_translate",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourcesEinstein00.finiteNewtonPointSources_distributionalEinstein00",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourcesEinstein00.finiteNewtonPointSources_distributionalEinstein00_translate",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourcesEinstein00.finiteNewtonPointSources_distributionalEinstein00_bitCount_chain"
  ]
  forbids_substitutes [
    "constructing or claiming a full distribution-valued Ricci or Einstein tensor",
    "multiplying singular distributions or treating a finite Dirac sum as a smooth rest-dust field",
    "promoting the static scalar linearized 00 continuation to an exact nonlinear Einstein equation",
    "claiming a nonlinear Einstein multi-body spacetime from finite Newtonian superposition",
    "claiming an enclosing-screen flux identity without a proved enclosure condition and divergence theorem",
    "claiming that holographic bits derive the distributional Einstein-Poisson equivalence"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourcesEinstein00.finiteNewtonPointSources_distributionalEinstein00_bitCount_chain
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.finiteNewtonPointSourceResolvedFlux where
  promises "formalization:finite-point-source-resolved-centered-sphere-flux-dirac-coefficients-distributional-einstein-00-and-entropic-screen-chain"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.sphereFluxIntegral3At",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonExteriorField3At",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonExteriorField3At_sphereFlux",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonSourceResolvedSphereFlux3",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonSourceResolvedSphereFlux3_expanded",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonSourceResolvedSphereFlux3_eq_totalMass",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonSourceResolvedFluxDistribution3",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonPotentialDistribution3_laplacian_eq_sourceResolvedFlux",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonSourceResolvedSphereFlux3_translate",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonSourceResolvedFluxDistribution3_translate",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonPointSources_sourceResolvedFlux_distributionalEinstein00_bitCount_chain"
  ]
  forbids_substitutes [
    "calling the source-resolved sum the flux of the total superposed field through one enclosing screen",
    "discarding or claiming cancellation of cross-source flux terms without an off-center Gauss-law proof",
    "identifying the family of source-centered Gaussian spheres with the separate holographic screen",
    "claiming an arbitrary-surface divergence theorem or off-center solid-angle theorem",
    "promoting the scalar distributional linearized Einstein 00 carrier to a full tensor or nonlinear solution",
    "claiming that holographic bits derive the source-resolved sphere-flux calculation"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux.finiteNewtonPointSources_sourceResolvedFlux_distributionalEinstein00_bitCount_chain
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.finiteNewtonEnclosingSphereFlux where
  promises "formalization:unconditional-finite-field-one-screen-flux-and-enclosing-sphere-einstein-00-entropic-chain"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonExteriorField3",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.spherePoint_sub_source_ne_zero",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.isolatedNewtonExteriorField3At_sphereFlux_integrable",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.sphereFluxIntegral3At_finset_sum",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonExteriorField3_sphereFlux_decompose",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonRadicand",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonZonalPrimitive",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonZonalKernel",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonRadicand_pos",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonZonalPrimitive_hasDerivAt",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonZonalKernel_intervalIntegrable",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonZonalKernel_intervalIntegral",
    "lean:Space.map_lastCoordinate3_toSphere",
    "lean:Space.integral_comp_inner_unit_toSphere_eq_intervalIntegral",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.NewtonSphereFluxLaw3",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.newtonSphereFluxLaw3",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.NewtonSphereFluxLaw3.inside",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.NewtonSphereFluxLaw3.outside",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonExteriorField3_enclosingSphereFlux",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonPointSources_enclosingFlux_distributionalEinstein00_bitCount_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.comptonCellInference_finiteNewtonPointSources_enclosingFluxEinstein00_chain"
  ]
  forbids_substitutes [
    "claiming that NewtonSphereFluxLaw3 has been proved merely because it is defined as a proposition",
    "allowing a source on the screen where the inverse-square field is singular",
    "promoting round-sphere finite-sum flux linearity to an arbitrary-surface divergence theorem",
    "promoting the scalar distributional linearized Einstein 00 carrier to a full tensor or nonlinear solution",
    "claiming that holographic bits derive the off-center solid-angle law"
  ]
  witnessed_by [
    Space.integral_comp_inner_unit_toSphere_eq_intervalIntegral,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonExteriorField3_sphereFlux_decompose,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.offCenterNewtonZonalKernel_intervalIntegral,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.newtonSphereFluxLaw3,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.finiteNewtonPointSources_enclosingFlux_distributionalEinstein00_bitCount_chain,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux.comptonCellInference_finiteNewtonPointSources_enclosingFluxEinstein00_chain
  ]

zil_file_contract physlib.holographicNewtonClockContourGravity.chain where
  promises "formalization:conditional-holographic-G-to-clock-contour-connection-and-EFE-chain"
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence.entropicNewtonConstant_converges",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization.einsteinEnergy_eq_rest_cosh_rapidity",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglie_eq_gamma_compton",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.nnLorentzForm_energyMomentum",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone.nnConverges_energyMomentum_iff",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.massShellContourAngle_permitted",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.energyMomentumComplex_slope_eq_tan_massShellContourAngle",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.massShellContourRadius_pos",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.energyMomentumComplex_eq_massShellContourRay",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.massShellContour_normalization",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour.contour_normalization",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldLeviCivita2_eq_christoffelFromMetric",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.ricciMatrixFromConnection",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldRicciMatrix2",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldRicciMatrix2_apply_00",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldScalarCurvature2",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldScalarCurvature2_eq",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakFieldEinsteinTensor2_eq_zero",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.weakField_ricci00_from_connection_newtonian",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations.complexEinsteinFieldEquation_iff_einstein",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI.einsteinFieldEquation_apply_00",
    "lean:Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor.complexEinstein_real_is_dAlembert",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_einstein_chain"
  ]
  forbids_substitutes [
    "claiming an empirical or numerical prediction of Newton's constant",
    "claiming that the holographic screen, Compton clock, or contour normalization derives the Einstein field equation",
    "dropping the exact O(c^-4) connection-curvature correction without an explicit limit or hypothesis",
    "claiming that the positive rapidity-derived representation makes its ray the unique admissible Nagao-Nielsen contour",
    "conflating the metric Levi-Civita connection with Levi-Civita's gravitational/inertial tensor",
    "claiming a general-dimensional metric-to-EFE derivation from the explicit 1+1 connection-derived Ricci matrix",
    "identifying the Newtonian density relation with a nonzero exact 1+1 Einstein-equation source"
  ]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity.holographicNewton_comptonNagaoLeviCivita_einstein_chain
  ]

#zil_formalization_lint_all
/- ZIL-END -/

end Physlib.Meta.HolographicNewtonClockContourGravityZil
