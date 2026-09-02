/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.NariaiHorizonHolographic
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of NariaiHorizonHolographic -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.NariaiHorizonHolographic

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.NariaiHorizonHolographic.nariaiHorizonArea_eq,
  Physlib.QuantumMechanics.ComplexAction.Curvature.NariaiHorizonHolographic.nariai_bekensteinHawking_eq_holographicBits_div_four,
  Physlib.QuantumMechanics.ComplexAction.Curvature.NariaiHorizonHolographic.nariai_newtonG_holographic_from_horizonBits ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.NariaiHorizonHolographic.nariaiHorizonArea_eq,
  Physlib.QuantumMechanics.ComplexAction.Curvature.NariaiHorizonHolographic.nariai_bekensteinHawking_eq_holographicBits_div_four,
  Physlib.QuantumMechanics.ComplexAction.Curvature.NariaiHorizonHolographic.nariai_newtonG_holographic_from_horizonBits ]
