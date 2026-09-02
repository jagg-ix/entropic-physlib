/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.RelationalTime.SignalDelayCausalReach
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the operational radar-distance reconstruction

Gates the round-trip identity, the distance-reconstruction inversion, its strict
monotonicity, and the flat null-leg interval consistency.
-/

open Physlib.QuantumMechanics.RelationalTime

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.RelationalTime.roundTripTime_eq,
  Physlib.QuantumMechanics.RelationalTime.radarDistance_roundTripTime,
  Physlib.QuantumMechanics.RelationalTime.roundTripTime_radarDistance,
  Physlib.QuantumMechanics.RelationalTime.radarDistance_strictMono,
  Physlib.QuantumMechanics.RelationalTime.lightLeg_null_interval ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.RelationalTime.roundTripTime_eq,
  Physlib.QuantumMechanics.RelationalTime.radarDistance_roundTripTime,
  Physlib.QuantumMechanics.RelationalTime.roundTripTime_radarDistance,
  Physlib.QuantumMechanics.RelationalTime.radarDistance_strictMono,
  Physlib.QuantumMechanics.RelationalTime.lightLeg_null_interval ]
