/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCurrentConservation
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the Abelian Yang-Mills current conservation -/

open Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCurrentConservation

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCurrentConservation.sum_sum_antisymm_zero,
  Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCurrentConservation.abelian_current_conservation ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCurrentConservation.sum_sum_antisymm_zero,
  Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCurrentConservation.abelian_current_conservation ]
