/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of SchwarzschildDeSitterHorizons -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons.kottlerF_schwarzschild,
  Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons.kottlerF_deSitter,
  Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons.kottlerF_zero_iff ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons.kottlerF_schwarzschild,
  Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons.kottlerF_deSitter,
  Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildDeSitterHorizons.kottlerF_zero_iff ]
