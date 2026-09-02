/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.RelationalTime.RadarLightConeEquivalencePrinciple
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the radar-light-cone / Einstein-Equivalence-Principle link

Gates the null light-leg, its boost-invariant masslessness (Local Lorentz
Invariance), the Nagao–Nielsen cone-boundary membership, and the loop back onto the
reconstructed radar distance.
-/

open Physlib.QuantumMechanics.RelationalTime

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.RelationalTime.radarLightLegCT_eq_distance,
  Physlib.QuantumMechanics.RelationalTime.radarLightLeg_restMassSq_zero,
  Physlib.QuantumMechanics.RelationalTime.radarLightLeg_massless_boost_invariant,
  Physlib.QuantumMechanics.RelationalTime.radarLightLeg_nnLorentzForm_zero,
  Physlib.QuantumMechanics.RelationalTime.not_nnConverges_radarLightLeg,
  Physlib.QuantumMechanics.RelationalTime.radarDistance_lightLeg_null ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.RelationalTime.radarLightLegCT_eq_distance,
  Physlib.QuantumMechanics.RelationalTime.radarLightLeg_restMassSq_zero,
  Physlib.QuantumMechanics.RelationalTime.radarLightLeg_massless_boost_invariant,
  Physlib.QuantumMechanics.RelationalTime.radarLightLeg_nnLorentzForm_zero,
  Physlib.QuantumMechanics.RelationalTime.not_nnConverges_radarLightLeg,
  Physlib.QuantumMechanics.RelationalTime.radarDistance_lightLeg_null ]
