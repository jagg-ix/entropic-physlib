/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.EinsteinEntanglementDynamics
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of entanglement-entropy dynamics from linearized AdS3 gravity
-/

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.EinsteinEntanglementDynamics

#physlib_axiom_clean_all [
  rtAreaEntropy_firstOrderVariation,
  fgBoundaryStressCoefficient_two,
  roundBallEntanglingTemperature_two_half_width,
  ads3LeadingEntropy_firstLaw,
  ads3EntropyKernelNumerator_hasDerivAt,
  ads3EntropyKernelNumeratorDeriv_hasDerivAt,
  ads3EntropyFourierKernel_hasDerivAt,
  ads3EntropyFourierKernelDeriv_hasDerivAt,
  ads3EntropyFourierKernel_radialEquation,
  ads3EntropyFourierMode_timeEquation,
  ads3EinsteinMode_induces_entropyDynamics ]

#physlib_non_vacuous_all [
  rtAreaEntropy_firstOrderVariation,
  fgBoundaryStressCoefficient_two,
  roundBallEntanglingTemperature_two_half_width,
  ads3LeadingEntropy_firstLaw,
  ads3EntropyKernelNumerator_hasDerivAt,
  ads3EntropyKernelNumeratorDeriv_hasDerivAt,
  ads3EntropyFourierKernel_hasDerivAt,
  ads3EntropyFourierKernelDeriv_hasDerivAt,
  ads3EntropyFourierKernel_radialEquation,
  ads3EntropyFourierMode_timeEquation,
  ads3EinsteinMode_induces_entropyDynamics ]
