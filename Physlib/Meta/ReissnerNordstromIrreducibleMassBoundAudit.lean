/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromIrreducibleMassBound
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of ReissnerNordstromIrreducibleMassBound -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromIrreducibleMassBound

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromIrreducibleMassBound.extractableEnergy_nonneg,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromIrreducibleMassBound.mass_ge_irreducibleMass,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromIrreducibleMassBound.mass_eq_irreducibleMass_iff_uncharged ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromIrreducibleMassBound.extractableEnergy_nonneg,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromIrreducibleMassBound.mass_ge_irreducibleMass,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromIrreducibleMassBound.mass_eq_irreducibleMass_iff_uncharged ]
