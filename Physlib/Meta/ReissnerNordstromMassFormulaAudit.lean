/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromIrreducibleMassBound
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the Christodoulou-Ruffini mass formula -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula.christodoulou_horizon_relation,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula.christodoulou_mass_formula,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula.irreducibleMass_extremal ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula.christodoulou_horizon_relation,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula.christodoulou_mass_formula,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromMassFormula.irreducibleMass_extremal ]
