/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCovariantCurrentConservation
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of YangMillsCovariantCurrentConservation -/

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCovariantCurrentConservation.fieldStrength_self_commutator_zero,
  Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCovariantCurrentConservation.nonabelian_current_conservation ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCovariantCurrentConservation.fieldStrength_self_commutator_zero,
  Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsCovariantCurrentConservation.nonabelian_current_conservation ]
