/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the Compton-clock entropic-time arrow
-/

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow.entropicTime_rate_nonneg,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow.ħ_comptonPhase_eq_restEnergy_properTime,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow.comptonPhase_monotone,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow.comptonPhase_strictMono ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow.entropicTime_rate_nonneg,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow.ħ_comptonPhase_eq_restEnergy_properTime,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow.comptonPhase_monotone,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockEntropicArrow.comptonPhase_strictMono ]
