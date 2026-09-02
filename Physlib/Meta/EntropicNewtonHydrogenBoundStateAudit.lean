/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the entropic-Newton gravitational hydrogen bound state -/

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState.hasDerivAt_radialWave,
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState.deriv2_radialWave,
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState.groundStateEnergy_eq_neg_hbar_sq_div,
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState.entropicNewtonGroundState_solves ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState.hasDerivAt_radialWave,
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState.deriv2_radialWave,
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState.groundStateEnergy_eq_neg_hbar_sq_div,
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonHydrogenBoundState.entropicNewtonGroundState_solves ]
