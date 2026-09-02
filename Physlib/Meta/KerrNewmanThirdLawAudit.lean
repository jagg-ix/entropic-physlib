/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizonQuantities
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of KerrNewmanThirdLaw -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanThirdLaw

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanThirdLaw.kn_hawkingTemperature_extremal,
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanThirdLaw.knExtremalArea ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanThirdLaw.kn_hawkingTemperature_extremal,
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanThirdLaw.knExtremalArea ]
