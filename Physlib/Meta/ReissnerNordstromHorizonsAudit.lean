/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the Reissner-Nordstrom horizons -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.reissnerNordstromF_uncharged,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.reissnerNordstromF_outerHorizon,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.reissnerNordstromF_innerHorizon,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.horizon_product,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.extremal_horizons_eq ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.reissnerNordstromF_uncharged,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.reissnerNordstromF_outerHorizon,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.horizon_product,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromHorizons.extremal_horizons_eq ]
