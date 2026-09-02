/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectrograviticResidualConservation
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the electrogravitic residual conservation -/

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectrograviticResidualConservation

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectrograviticResidualConservation.electrogravitic_residual_conservation ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectrograviticResidualConservation.electrogravitic_residual_conservation ]
