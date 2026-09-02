/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.MaxwellStressEnergyProperties
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the Maxwell stress-energy properties -/

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.MaxwellStressEnergyProperties

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.MaxwellStressEnergyProperties.maxwellStressEnergy_symm,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.MaxwellStressEnergyProperties.maxwellStressEnergy_faraday_symm ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.MaxwellStressEnergyProperties.maxwellStressEnergy_symm,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.MaxwellStressEnergyProperties.maxwellStressEnergy_faraday_symm ]
