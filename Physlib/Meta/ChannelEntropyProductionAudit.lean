/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the reversible/irreversible channel sector

Unitary CPTP channels are entropy-preserving (necessary direction), the mixing
replacement channel is not, relative entropy contracts under every CPTP map (the
GKLS irreversibility bridge), and a Koopman step is the unitary
channel `ofEquiv`.
-/

open Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction

#check @Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction.IsEntropyPreserving
#check @Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction.cptp_qRelativeEnt_le

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction.isUnitary_isEntropyPreserving,
  Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction.ofUnitary_isEntropyPreserving,
  Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction.ofEquiv_isEntropyPreserving,
  Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction.replacement_not_isEntropyPreserving,
  Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction.cptp_qRelativeEnt_le,
  Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction.pureState_zero_vonNeumann,
  Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction.koopmanStep_zero_entropyProduction ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction.isUnitary_isEntropyPreserving,
  Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction.ofEquiv_isEntropyPreserving,
  Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction.replacement_not_isEntropyPreserving,
  Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction.cptp_qRelativeEnt_le,
  Physlib.QuantumMechanics.OpenSystems.ChannelEntropyProduction.koopmanStep_zero_entropyProduction ]
