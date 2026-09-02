/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the Compton–de Broglie clock on Malament's proper time
-/

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime.comptonClock_luminal,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime.comptonPhase_ratio_causalAutomorphism ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime.comptonClock_luminal,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonClockMalamentProperTime.comptonPhase_ratio_causalAutomorphism ]
