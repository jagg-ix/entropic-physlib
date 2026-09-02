/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.HolographicNewtonFromBlackHoleHorizon
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the holographic Newton constant from a black-hole horizon -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.HolographicNewtonFromBlackHoleHorizon

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.HolographicNewtonFromBlackHoleHorizon.bekensteinHawking_eq_holographicBits_div_four,
  Physlib.QuantumMechanics.ComplexAction.Curvature.HolographicNewtonFromBlackHoleHorizon.kn_bekensteinHawking_eq_holographicBits_div_four,
  Physlib.QuantumMechanics.ComplexAction.Curvature.HolographicNewtonFromBlackHoleHorizon.kn_newtonG_holographic_from_horizonBits,
  Physlib.QuantumMechanics.ComplexAction.Curvature.HolographicNewtonFromBlackHoleHorizon.rn_newtonG_holographic_from_horizonBits ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.HolographicNewtonFromBlackHoleHorizon.bekensteinHawking_eq_holographicBits_div_four,
  Physlib.QuantumMechanics.ComplexAction.Curvature.HolographicNewtonFromBlackHoleHorizon.kn_bekensteinHawking_eq_holographicBits_div_four,
  Physlib.QuantumMechanics.ComplexAction.Curvature.HolographicNewtonFromBlackHoleHorizon.kn_newtonG_holographic_from_horizonBits,
  Physlib.QuantumMechanics.ComplexAction.Curvature.HolographicNewtonFromBlackHoleHorizon.rn_newtonG_holographic_from_horizonBits ]
