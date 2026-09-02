/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GuptaFeynmanTracelessGraviton
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the Gupta-Feynman traceless graviton -/

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GuptaFeynmanTracelessGraviton

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GuptaFeynmanTracelessGraviton.guptaFeynman_traceless_massless_graviton ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.GuptaFeynmanTracelessGraviton.guptaFeynman_traceless_massless_graviton ]
