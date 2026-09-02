/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanIrreducibleMass
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of KerrNewmanIrreducibleMass -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanIrreducibleMass

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanIrreducibleMass.knIrreducibleMass_sq,
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanIrreducibleMass.knHorizonArea_eq_irreducible,
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanIrreducibleMass.knMass_ge_irreducibleMass ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanIrreducibleMass.knIrreducibleMass_sq,
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanIrreducibleMass.knHorizonArea_eq_irreducible,
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanIrreducibleMass.knMass_ge_irreducibleMass ]
