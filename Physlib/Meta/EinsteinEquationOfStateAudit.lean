/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the Jacobson Einstein equation of state -/

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState.nullVanishing_eq_smul_metric,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState.equationOfState_ricci_decomposition,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState.einstein_equation_of_state ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState.nullVanishing_eq_smul_metric,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState.equationOfState_ricci_decomposition,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState.einstein_equation_of_state ]
