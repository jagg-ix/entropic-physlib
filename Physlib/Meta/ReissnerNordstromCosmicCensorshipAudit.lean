/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromCosmicCensorship
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of ReissnerNordstromCosmicCensorship -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromCosmicCensorship

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromCosmicCensorship.innerHorizon_lt_outerHorizon,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromCosmicCensorship.innerHorizon_nonneg,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromCosmicCensorship.no_horizon_of_naked ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromCosmicCensorship.innerHorizon_lt_outerHorizon,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromCosmicCensorship.innerHorizon_nonneg,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ReissnerNordstromCosmicCensorship.no_horizon_of_naked ]
