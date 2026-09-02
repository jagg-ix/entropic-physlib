/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Meta.AxiomWhitelistCheck
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor

/-! # Audit of the Mayr--Stieberger dilaton/tensor one-loop bridge -/

open Physlib.QuantumMechanics.ComplexAction.ChernSimons.MayrStiebergerDilatonTensor

#physlib_axiom_clean_all [
  genusWeight_succ,
  dilaton_threshold_scale_shift,
  greenSchwarzTensorFieldStrength_gauge_invariant,
  extDeriv_greenSchwarzTensorFieldStrength,
  oneLoop1PI_vanishes_iff_smatrix_is_external ]

#physlib_non_vacuous_all [
  genusWeight_succ,
  dilaton_threshold_scale_shift,
  greenSchwarzTensorFieldStrength_gauge_invariant,
  extDeriv_greenSchwarzTensorFieldStrength,
  oneLoop1PI_vanishes_iff_smatrix_is_external ]

