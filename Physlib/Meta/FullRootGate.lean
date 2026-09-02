/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib
public import Physlib.Meta.AffineProjectionTensorGeometryAudit
public import Physlib.Meta.AsymptoticFreedomOneLoopAudit
public import Physlib.Meta.BlochPhaseEvolutionAudit
public import Physlib.Meta.BornCompositionCorrelationAudit
public import Physlib.Meta.BornCompositionProductStateAudit
public import Physlib.Meta.BoundaryCentralChargeElectrograviticResidualAudit
public import Physlib.Meta.CausalAutomorphismConformalInvariantsAudit
public import Physlib.Meta.CausalEventHistoryAudit
public import Physlib.Meta.ChannelEntropyProductionAudit
public import Physlib.Meta.ComptonClockMalamentProperTimeAudit
public import Physlib.Meta.ComptonPhysicalDataAudit
public import Physlib.Meta.ConformalWeylCurvatureLiouvilleAudit
public import Physlib.Meta.CosmologicalConstantConstancyAudit
public import Physlib.Meta.CosmologicalConstantGlobalConstancyAudit
public import Physlib.Meta.CovariantDerivativeCurvatureAudit
public import Physlib.Meta.CovariantDerivativeEndomorphismAudit
public import Physlib.Meta.CurvatureTwoFormBianchiAudit
public import Physlib.Meta.CyclicVectorRigidityAudit
public import Physlib.Meta.DZeroDSixLorentzForceAudit
public import Physlib.Meta.EinsteinCartanReductionAudit
public import Physlib.Meta.EinsteinEntanglementDynamicsGrounding
public import Physlib.Meta.EinsteinEquationOfStateAudit
public import Physlib.Meta.ElectrograviticResidualConservationAudit
public import Physlib.Meta.EntropicNewtonFiniteAtOriginAudit
public import Physlib.Meta.EntropicNewtonHydrogenBoundStateAudit
public import Physlib.Meta.EntropicWepDepthGate
public import Physlib.Meta.EuclideanTensorCompositionIsoAudit
public import Physlib.Meta.GKPWittenConformalCovarianceAudit
public import Physlib.Meta.GaussBonnetScalarInvariantAudit
public import Physlib.Meta.GaussianFisherGravitationalResponseAudit
public import Physlib.Meta.GegenbauerAllOrderEigenfunctionAudit
public import Physlib.Meta.GegenbauerFamilyConsistencyAudit
public import Physlib.Meta.GegenbauerGeneralRecurrenceAudit
public import Physlib.Meta.GluonFieldStrengthBianchiAudit
public import Physlib.Meta.GravitonSelfEnergyLorentzInvariantAudit
public import Physlib.Meta.GuptaFeynmanTracelessGravitonAudit
public import Physlib.Meta.HolographicComptonNewtonEquivalenceAudit
public import Physlib.Meta.HolographicElectrograviticResidualAudit
public import Physlib.Meta.HolographicNewtonFromBlackHoleHorizonAudit
public import Physlib.Meta.JacobsonClausiusEinsteinAudit
public import Physlib.Meta.KerrNewmanCosmicCensorshipAudit
public import Physlib.Meta.KerrNewmanHorizonQuantitiesAudit
public import Physlib.Meta.KerrNewmanHorizonsAudit
public import Physlib.Meta.KerrNewmanIrreducibleMassAudit
public import Physlib.Meta.KerrNewmanSmarrFormulaAudit
public import Physlib.Meta.KerrNewmanThirdLawAudit
public import Physlib.Meta.L2KetAdapterAudit
public import Physlib.Meta.L2StatePresentationAudit
public import Physlib.Meta.LeviCivitaUniquenessAudit
public import Physlib.Meta.LiouvilleAdSArcSynthesisAudit
public import Physlib.Meta.LiouvilleComplexityElectrograviticResidualAudit
public import Physlib.Meta.LiouvilleComplexityHolographicSpineAudit
public import Physlib.Meta.LiouvilleHyperbolicAdSSliceAudit
public import Physlib.Meta.LorentzForceDerivationAudit
public import Physlib.Meta.MalamentConformalProperTimeBridgeAudit
public import Physlib.Meta.MassiveStringAnomalousDimensionLimitAudit
public import Physlib.Meta.MaximallyEntangledEntropyAudit
public import Physlib.Meta.MaxwellChernSimonsIIBSolitonsAudit
public import Physlib.Meta.MaxwellStressEnergyPropertiesAudit
public import Physlib.Meta.NariaiHorizonHolographicAudit
public import Physlib.Meta.OneLevelFixedPointUniquenessAudit
public import Physlib.Meta.PageWoottersLeggettGargAudit
public import Physlib.Meta.PeriodicSchrodingerContinuumBridgeAudit
public import Physlib.Meta.ProjectedCovariantDerivativeAudit
public import Physlib.Meta.ProjectedRicciDecompositionAudit
public import Physlib.Meta.ProjectedRiemannDecompositionAudit
public import Physlib.Meta.ProjectionGradientDecompositionAudit
public import Physlib.Meta.ProjectionTensorRestSpaceAudit
public import Physlib.Meta.ProperTimeLorentzInvarianceAudit
public import Physlib.Meta.ProperTimeWorldlineIntegralAudit
public import Physlib.Meta.ReissnerNordstromCosmicCensorshipAudit
public import Physlib.Meta.ReissnerNordstromEntropyAreaAudit
public import Physlib.Meta.ReissnerNordstromFirstLawAudit
public import Physlib.Meta.ReissnerNordstromHorizonsAudit
public import Physlib.Meta.ReissnerNordstromIrreducibleMassBoundAudit
public import Physlib.Meta.ReissnerNordstromMassFormulaAudit
public import Physlib.Meta.ReissnerNordstromRadialThermodynamicsAudit
public import Physlib.Meta.ReissnerNordstromSmarrFormulaAudit
public import Physlib.Meta.ReissnerNordstromSurfaceGravityAudit
public import Physlib.Meta.RelativisticScreenKinematicsAudit
public import Physlib.Meta.RicciSecondBianchiFromConnectionAudit
public import Physlib.Meta.SchwarzschildDeSitterHorizonBoundAudit
public import Physlib.Meta.SchwarzschildDeSitterHorizonsAudit
public import Physlib.Meta.SchwarzschildDeSitterNariaiAudit
public import Physlib.Meta.SchwingerDysonChernSimonsNonRenormalizationAudit
public import Physlib.Meta.SecondBianchiFromConnectionAudit
public import Physlib.Meta.SourcedTTWaveComptonCouplingAudit
public import Physlib.Meta.SourcedTTWaveHolographicCouplingAudit
public import Physlib.Meta.SourcedTransverseTracelessWaveAudit
public import Physlib.Meta.StrongPoissonHomogeneousDensityAudit
public import Physlib.Meta.UnifiedRelationalDissipativeCarrierAudit
public import Physlib.Meta.VerlindeCovariantGravityAudit
public import Physlib.Meta.WilsonLoopConfinementCriterionAudit
public import Physlib.Meta.YangMillsActionSpacetimeIntegralAudit
public import Physlib.Meta.YangMillsActionVariationAudit
public import Physlib.Meta.YangMillsCovariantCurrentConservationAudit
public import Physlib.Meta.YangMillsCurrentConservationAudit
public import Physlib.Meta.YangMillsFieldEquationAudit
public import Physlib.Meta.ZilDiscovery
public import Physlib.Meta.ZilGraph
public import Physlib.Meta.AxiomWhitelistCheck
public import Physlib.Meta.ClaimMaturity
public import Physlib.Meta.DyadicCalderonScaleLadderZil
public import Physlib.Meta.EntropicDynamicsFullEinsteinSource
public import Physlib.Meta.EntropicDynamicsThesis
public import Physlib.Meta.EntropicDynamicsThesisConditionals
public import Physlib.Meta.EntropicSpineZil
public import Physlib.Meta.EvidenceIntegrity
public import Physlib.Meta.HolographicNewtonClockContourGravityZil
public import Physlib.Meta.M9CriterionReductionAudit
public import Physlib.Meta.MultiNormSection4PaperZil
public import Physlib.Meta.OneLevelChannelCalibrationAudit
public import Physlib.Meta.SpineAxiomAudit
public import Physlib.Meta.YukawaMadelungOpenProblemsZil
public import Physlib.Meta.ZilTypedRef

/-!
# Authoritative full-root merge gate

Building this one target forces a build of the entire `Physlib` root **together with** every fast
build-time honesty gate — axiom-cleanliness, non-vacuity, ZIL file contracts, ZIL formalization lints,
and the `ZilGraph` decide-proofs. A module that fails to compile or trips a gate fails THIS target, even
when it is only reachable through `EntropicSpine` or is an orphaned `Meta` leaf that the root manifest
never imports.

Why it exists: a scoped build is not a full-root verification. `import Physlib` alone already reaches the
`EntropicSpine → M9CriterionReductionAudit` chain (so it would have caught the M9 modules that were merged
without compiling), but several `Meta` gate leaves sit entirely outside the root closure and so run
nowhere by default. This target pulls them all in. Run `lake build Physlib.Meta.FullRootGate` before merge.

The only intentional omission is the informational, on-demand set whose O(n²) closures are impractical at
full-root scale and which log rather than fail: `#zil_graph_report`, `#physlib_program_health`,
`#zil_intent_audit`.
-/

/-! ## A.1. Repo-wide Gaussian–Fisher evidence boundary -/

#zil_assert_primitive "assumption:compton-cell-screen-tiling-is-the-independent-bit-count"
