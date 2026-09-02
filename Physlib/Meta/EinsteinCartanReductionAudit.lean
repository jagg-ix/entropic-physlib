/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the Einstein-Cartan to Einstein reduction -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.EinsteinCartanReduction

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.EinsteinCartanReduction.torsionFree_metricCompatible_eq_leviCivita,
  Physlib.QuantumMechanics.ComplexAction.Curvature.EinsteinCartanReduction.einsteinCartan_spinless_eq_leviCivita ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.EinsteinCartanReduction.torsionFree_metricCompatible_eq_leviCivita,
  Physlib.QuantumMechanics.ComplexAction.Curvature.EinsteinCartanReduction.einsteinCartan_spinless_eq_leviCivita ]
