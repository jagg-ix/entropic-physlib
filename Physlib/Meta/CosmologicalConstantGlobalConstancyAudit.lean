/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantGlobalConstancy
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the global cosmological-constant constancy -/

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantGlobalConstancy

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantGlobalConstancy.cosmologicalConstant_globally_constant ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantGlobalConstancy.cosmologicalConstant_globally_constant ]
