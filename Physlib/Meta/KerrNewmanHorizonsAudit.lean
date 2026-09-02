/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of KerrNewmanHorizons -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knHorizon_product,
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knHorizon_sum,
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knHorizon_extremal,
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knOuterHorizon_reissnerNordstrom ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knHorizon_product,
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knHorizon_sum,
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knHorizon_extremal,
  Physlib.QuantumMechanics.ComplexAction.Curvature.KerrNewmanHorizons.knOuterHorizon_reissnerNordstrom ]
