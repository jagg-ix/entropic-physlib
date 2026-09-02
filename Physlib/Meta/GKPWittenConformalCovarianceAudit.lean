/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenConformalCovariance
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of GKPWittenConformalCovariance -/

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenConformalCovariance

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenConformalCovariance.bulkToBoundaryKernel_translation,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenConformalCovariance.cftTwoPointSep_translation,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenConformalCovariance.cftTwoPointSep_dilation,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenConformalCovariance.cftTwoPointSep_inversion ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenConformalCovariance.bulkToBoundaryKernel_translation,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenConformalCovariance.cftTwoPointSep_translation,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenConformalCovariance.cftTwoPointSep_dilation,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenConformalCovariance.cftTwoPointSep_inversion ]
