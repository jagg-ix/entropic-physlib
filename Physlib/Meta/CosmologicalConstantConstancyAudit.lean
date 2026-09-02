/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantConstancy
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the cosmological-constant constancy -/

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantConstancy

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantConstancy.cosmologicalConstant_gradient_zero,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantConstancy.cosmologicalConstant_gradient_zero_matrix ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantConstancy.cosmologicalConstant_gradient_zero,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantConstancy.cosmologicalConstant_gradient_zero_matrix ]
