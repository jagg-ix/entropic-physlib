/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.AsymptoticFreedomOneLoop
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of AsymptoticFreedomOneLoop -/

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Particles.AsymptoticFreedomOneLoop.betaZeroOneLoop_pos_iff,
  Physlib.QuantumMechanics.ComplexAction.Particles.AsymptoticFreedomOneLoop.qcd_asymptotically_free,
  Physlib.QuantumMechanics.ComplexAction.Particles.AsymptoticFreedomOneLoop.betaFunction_neg_of_asymptoticFreedom ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Particles.AsymptoticFreedomOneLoop.betaZeroOneLoop_pos_iff,
  Physlib.QuantumMechanics.ComplexAction.Particles.AsymptoticFreedomOneLoop.qcd_asymptotically_free,
  Physlib.QuantumMechanics.ComplexAction.Particles.AsymptoticFreedomOneLoop.betaFunction_neg_of_asymptoticFreedom ]
