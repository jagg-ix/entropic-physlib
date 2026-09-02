/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonFiniteAtOrigin
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the entropic-Newton finiteness -/

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonFiniteAtOrigin

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonFiniteAtOrigin.entropicShellPotential_exterior_eq_newton,
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonFiniteAtOrigin.entropicShellPotential_interior_finite,
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonFiniteAtOrigin.entropicShellPotential_bounded_below ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonFiniteAtOrigin.entropicShellPotential_exterior_eq_newton,
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonFiniteAtOrigin.entropicShellPotential_interior_finite,
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicNewtonFiniteAtOrigin.entropicShellPotential_bounded_below ]
