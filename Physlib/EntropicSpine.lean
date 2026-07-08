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
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingNormalizationInformationMetric
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingComplexStructureSchrodinger

-- Compton clock / de Broglie / Nagao–Nielsen contour
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronMadelungDeBroglieMomentum

-- Reversibility / arrow of time
public import Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum

-- QM → GR: complex Einstein, curvature, second Bianchi
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
public import Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily

-- Holography / AdS-CFT
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalBoundaryRepoLinks
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussHolographicReduction
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussLipschitzExtension
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussEpsilonNetPacking
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiHolographicEntropy
public import Physlib.Mathematics.Geometry.StereographicRiemannSphere

-- Double copy / Maxwell
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant

-- Thermodynamics of computation / H-theorem
public import Physlib.Thermodynamics.SecondLawQuantumBoltzmann
public import Physlib.Thermodynamics.ComputationLandauer

-- Information dimension [I] + scalar-action no-go
public import Physlib.Units.Dimension
public import Physlib.Units.ComplexActionDimension

/-!
# The entropic-dynamics QM→GR spine (real modules)

A curated aggregator of the **genuine** formalizations that constitute the entropic-dynamics
Quantum-Mechanics-to-General-Relativity spine — the real content that the `entropic-physlib`
(public) repository is meant to expose. Every module imported above is the actual formalization in
this repository (grounded in its real infrastructure), not a Mathlib-only restatement.
-/
