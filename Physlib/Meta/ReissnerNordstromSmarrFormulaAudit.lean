/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromIrreducibleMassBound
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the Reissner-Nordstrom Smarr formula -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSmarrFormula

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSmarrFormula.smarrGeometricTerm_eq,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSmarrFormula.rn_smarr_formula ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSmarrFormula.smarrGeometricTerm_eq,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromSmarrFormula.rn_smarr_formula ]
