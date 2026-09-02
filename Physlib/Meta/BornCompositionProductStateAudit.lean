/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.BornCompositionCorrelation
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the entropic product-state constructor -/

open Physlib.QuantumMechanics.BornCompositionProductState

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.BornCompositionProductState.bornDist_l2Prod,
  Physlib.QuantumMechanics.BornCompositionProductState.totalCorrelation_l2Prod_zero ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.BornCompositionProductState.bornDist_l2Prod,
  Physlib.QuantumMechanics.BornCompositionProductState.totalCorrelation_l2Prod_zero ]
