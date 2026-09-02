/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

-- Information geometry / probability metrics
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ProbabilityMetricInformationGeometry
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ProbabilityMetricTranslationKillingFlow
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.SymmetricStableProcessMetricEntropy

-- Entropic-dynamics probability flow → free energy → equilibrium
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.GibbsEquilibriumComplexReversibility

-- Hamilton–Killing → quantum mechanics (wave function, Born rule, Schrödinger, Kähler)
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsEvolutionSchrodingerEhrenfest
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingNormalizationInformationMetric
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingComplexStructureSchrodinger
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaCurvedQuantumPotential
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaSchrodingerNagaoNielsen
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaInteractingFunctionalMeasurement
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormConeCoverage
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormDominance
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormDottedRegionCharacterization
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormDyadicTube
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormMaximalFloorCriterion
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormUniqueMaximalApex
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTubePartition
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTubeProximity
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormApexDensity
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTubeColoring
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormFrequencyBlock
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothCutoff
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormSmoothSupportColoring
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteSmoothSquareBound
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalFrequencyCover
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteNormalizedPartition
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormFiniteReproducingFormula
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalLocalFiniteness
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalNormalizedPartition
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalReproducingFormula
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGlobalComplexReproducingFormula
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormSchwartzKernel
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTemperedCalderon
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormPhysicalCalderon
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormMomentDerivative
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormDualCalderon
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovDual
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovLimit
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSpatial
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovSupport
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovCancellation
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormRychkovEstimates
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorCalderon
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormTensorRegrouping
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormBlockGaugeComparison
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormGeometry
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedCone
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormMarkedConeCoordinates
public import Physlib.Mathematics.HarmonicAnalysis.MultiNormMinimalDottedSet
public import Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteLittlewoodPaley
public import Physlib.QuantumMechanics.Schrodinger.EuclideanFiniteOverlapLittlewoodPaley
public import Physlib.QuantumMechanics.Schrodinger.EuclideanL2FreeEvolution
public import Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerLocalization
public import Physlib.QuantumMechanics.Schrodinger.MultiNormSchrodingerDecoherence
public import Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicGeometry
public import Physlib.QuantumMechanics.Schrodinger.SchrodingerParabolicPhaseRescaling
public import Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
public import Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery

-- Compton clock / de Broglie / Nagao–Nielsen contour
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronMadelungDeBroglieMomentum

-- Reversibility / arrow of time
public import Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum
public import Physlib.QuantumMechanics.Lindblad.SpohnVariationalHTheorem
public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelPageWootters
public import Physlib.Thermodynamics.QuantumRelativeEntropyArrow

-- QM → GR: complex Einstein, curvature, second Bianchi
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinSchrodingerNonrelLimit
public import Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiFromConnection
public import
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravityField
public import
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonEnclosingSphereFlux
public import
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourceResolvedFlux
public import
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux
public import
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits

-- Holography / AdS-CFT
public import Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussHolographicReduction
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussLipschitzExtension
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussEpsilonNetPacking
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
public import Physlib.Mathematics.Geometry.StereographicRiemannSphere

-- Double copy / Maxwell
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.HodgeStarBivector
public import Physlib.Electromagnetism.Distributional.Dynamics.Lagrangian

-- Curved-background path integrals and algebraic QFT
public import Physlib.QFT.PathIntegral.CurvedMeasurePathIntegral
public import Physlib.QFT.PathIntegral.SchwarzschildFeynmanPropagator
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.CurvedCausalHistoryPathIntegral
public import
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.RetardedDeltaMeasure
public import Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral
public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeFormula
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenCutoffFreeFunctionalIntegral
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersVacuumModularLinks
public import
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity
public import
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KleinGordonProgram
public import
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaIntrinsicMaxwellGreen
public import
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardTypeIIIAQFT
public import
  Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CatichaHadamardMaxwellMicrocausality
public import
  Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.BennettCatichaBassettoBridge
public import
  Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.FourDimensionalBoundStateCompleteness
public import
  Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.EntropicLoopFunctionalSynthesis

-- Entropic gravity
public import Physlib.Thermodynamics.VerlindeNewtonGravity
public import Physlib.Thermodynamics.VerlindeCovariantGravity

-- Thermodynamics of computation / H-theorem
public import Physlib.Thermodynamics.SecondLawQuantumBoltzmann
public import Physlib.Thermodynamics.ComputationLandauer
public import
  Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.ContinuumSemigroupClosure
public import
  Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.TraceClassDensityOperatorIdeal
public import
  Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.TraceClassDensityOperatorIdeal

-- Entropically damped Euclidean / Stokes evolution
public import Physlib.QFT.PathIntegral.DampedHeatSemigroup
public import
  Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup
public import
  Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierIntegratedDissipationCascade
public import
  Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierRiemannSumBridge
public import
  Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierSobolevDissipationCascade

-- Information dimension [I] + scalar-action no-go
public import Physlib.Units.Dimension
public import Physlib.Units.ComplexActionDimension

/-!
# The entropic-dynamics QM→GR spine (real modules)

A curated aggregator of the **genuine** formalizations that constitute the entropic-dynamics
Quantum-Mechanics-to-General-Relativity spine — the real content that the `entropic-physlib`
(public) repository is meant to expose. Every module imported above is the actual formalization in
this repository (grounded in its real infrastructure), not a Mathlib-only restatement.

The curated surface now also exposes the shared-density Caticha ED → curved-measure/gauge-source bridge,
the Einstein--Maxwell bit-form equations, the Caticha--Hadamard--global-Maxwell causal carrier, the
finite-carrier Verch quasifree/Klein--Gordon modular program, and the continuum distributional
antisymmetric-tensor gauge sector. On the thermodynamic side it keeps the unconditional discrete CPTP
relative-entropy arrow separate from the finite differential Spohn theorem, whose derivative identity is
an explicit model obligation. The discrete layer exposes genuine equilibrium-relative Spohn production and
its exact accumulated-production telescope. The algebraic positive-time CPTP-semigroup layer proves
time-ordered contraction, fixed-trajectory vanishing, and the exact adjacent-interval production cocycle.
The new `CPTPC0Semigroup` layer adds strong continuity, initial-state recovery, and a right infinitesimal
generator predicate; an explicitly identified GKLS generator sends semigroup fixed points to GKLS steady
states. The one-level loss/gain model now supplies the nontrivial realization: its explicit channels form a
genuine `C₀` CPTP semigroup, its right generator is exactly `oneLevelGKSLMatrix`, and its exact diagonal
orbit instantiates the domain-aware differential Spohn interface with the binary-KL production density.
This does not identify the repository's positive jump intensity with relative-entropy production; indeed,
the symmetric qubit NESS proves that this intensity equals one at a genuine steady state. Full
coherence-carrying operator-relative-entropy differentiability remains separate. Grad's homogeneous BGK model now
provides the classical control case: the binary collision H-kernel is nonnegative with detailed-balance
equality, the explicit affine relaxation is a strongly continuous semigroup with its BGK generator, and its
one-mode quadratic Hermite entropy has exact exponential decay and an unconditional interval-production
rate. This does not assert the nonlinear Boltzmann--Grad limit or propagation of molecular chaos. All
hypotheses and finite/model-level scope remain explicit in the theorem statements and ZIL contracts.

The Coulomb mean-field layer now exposes the exact `1/N` pair normalization from Golse--Paul, a reusable
modulated-energy carrier driven by Mathlib's right-derivative Gronwall estimate, and joint-parameter
convergence of that controlled energy. On the entropic-dynamics side, the pointwise Fisher/Bohm quantum
potential is proved to vanish as `ℏ → 0`. A separate conditional bridge identifies a monokinetic current
with the existing Caticha current and combines the repository's homogeneous Poisson potential with the
holographic-bit rewriting of the Einstein coupling. This bridge does not identify repulsive Coulomb
dynamics with attractive Newtonian gravity, does not construct the paper's Wigner measures or singular
Serfaty estimate, and does not turn collisionless Euler--Poisson into Navier--Stokes or a Boltzmann
collision H-theorem.

The open-system spine now also exposes a genuine infinite-dimensional
`L²(X × X)` Hilbert--Schmidt-kernel carrier. Bounded continuum generators and
reservoir sandwiches construct exponential strongly continuous semigroups with
identified right infinitesimal generators; norm-convergent approximants converge
in Mathlib's weak-operator topology. Densely-defined closable generators receive
their canonical closed densely-defined extension. This does not silently promote
an arbitrary closed operator to a semigroup generator: unbounded GKLS evolution
still requires explicit Hille--Yosida or maximal-dissipativity data.

For the continuum Caticha--AQFT--Maxwell carrier, equal source and field types no longer require a separately
supplied encoding object. `ContinuumCatichaIntrinsicMaxwellAdapter.ofSameCarrier` constructs the identity
adapter from pointwise equality of the Maxwell and Caticha wave, retarded, and advanced operators. The direct
same-carrier capstone then proves equality of the two Pauli--Jordan propagators and reuses the existing global
Maxwell, functional-evolution, CCR, positivity, and microlocal conclusions. This removes an artificial adapter
premise. On a selected intrinsic-Maxwell carrier where the wave and Green maps are proved complex-linear,
`ComplexLinearIntrinsicMaxwellCarrier.toContinuumCatichaKGData` now constructs the complete Caticha/KG datum
from those maps and proves that the KG operator is exactly the intrinsic Maxwell operator. The two-point layer
also now has a correct conjugate-linear-first-slot carrier:
`ContinuumSesquilinearHadamardTwoPoint.ofInnerProduct` constructs its Hermitian positive pairing and real CCR
form, with nonzero self-pairing for nonzero fields. `WellPosedIntrinsicMaxwellCauchyData` now derives linear
retarded and advanced Green maps from causal solution existence, support-sector closure, and uniqueness;
`wellPosedCauchy_catichaKG_intrinsicMaxwell_chain` feeds those maps into the common Caticha/Maxwell carrier.
The microlocal layer no longer equates two freely declared sets:
`Distribution.distributionalWavefrontSet` is computed from rapid localized-Fourier decay of an actual
distribution. `DistributionalHadamardData.wavefront_eq_iff` proves that identification with the
positive-frequency Hadamard cone exactly when regularity off the cone and singularity on it are established;
the data carrier stores neither equality nor certificate. Global-hyperbolic PDE existence and completeness
of a concrete chart/cutoff probe family remain explicit analytic obligations rather than consequences of geometry alone.

The optional development/CI modules `Physlib.Meta.EntropicSpineZil` and
`Physlib.Meta.HolographicNewtonClockContourGravityZil` supply machine-checkable
scope contracts for representative theorems and the end-to-end holographic
`G`/clock/contour/gravity bridge. They are deliberately separate so production
users can import this scientific aggregator without importing ZIL metadata.
-/
