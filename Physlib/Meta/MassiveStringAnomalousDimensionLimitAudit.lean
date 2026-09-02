/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensions
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of MassiveStringAnomalousDimensionLimit -/

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensionLimit

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensionLimit.dimension_excess_tendsto,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensionLimit.dimension_excess_ratio_tendsto ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensionLimit.dimension_excess_tendsto,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.MassiveStringAnomalousDimensionLimit.dimension_excess_ratio_tendsto ]
