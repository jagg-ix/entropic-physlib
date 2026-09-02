/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.RetardedGreenCausalSupport
public import Physlib.QuantumMechanics.RelationalTime.SignalDelayCausalReach
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of finite causal propagation

Applies the axiom and non-vacuity gates to the finite-propagation upgrades:
the finite-sum and continuum-Bochner retarded-response support inclusions
`supp(G⁺f) ⊆ J⁺(supp f)` and the
operational signal-delay law with its light-cone bound and spacelike-no-signal
consequence.
-/

open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen
open Physlib.QuantumMechanics.RelationalTime

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.retardedGreen_ne_zero_imp_later,
  Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.retardedResponse_support_subset_causalFuture,
  Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.retardedResponse_zero,
  Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.retardedIntegralResponse_eq_zero_of_not_mem_causalFuture,
  Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.retardedIntegralResponse_support_subset_causalFuture,
  Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.retardedIntegralResponse_zero,
  Physlib.QuantumMechanics.RelationalTime.lightTime_le_signalDelay,
  Physlib.QuantumMechanics.RelationalTime.signalDelay_eq_lightTime_iff,
  Physlib.QuantumMechanics.RelationalTime.signalDelay_relay,
  Physlib.QuantumMechanics.RelationalTime.signalDelay_canSignalReach,
  Physlib.QuantumMechanics.RelationalTime.not_canSignalReach_of_spacelike ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.retardedGreen_ne_zero_imp_later,
  Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.retardedResponse_support_subset_causalFuture,
  Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.retardedIntegralResponse_eq_zero_of_not_mem_causalFuture,
  Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen.retardedIntegralResponse_support_subset_causalFuture,
  Physlib.QuantumMechanics.RelationalTime.lightTime_le_signalDelay,
  Physlib.QuantumMechanics.RelationalTime.signalDelay_eq_lightTime_iff,
  Physlib.QuantumMechanics.RelationalTime.signalDelay_relay,
  Physlib.QuantumMechanics.RelationalTime.not_canSignalReach_of_spacelike ]
