/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the Jacobson–Clausius Einstein derivation -/

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.area_secondDeriv_at_equilibrium,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.clausius_equation_of_state,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.eq_of_integral_eq,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.clausius_density_from_integrated,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.einstein_from_clausius ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.area_secondDeriv_at_equilibrium,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.clausius_equation_of_state,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.eq_of_integral_eq,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.clausius_density_from_integrated,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.einstein_from_clausius ]
