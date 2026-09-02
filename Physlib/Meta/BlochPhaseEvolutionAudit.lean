/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the free-Bloch phase evolution

This leaf audit applies the repository axiom and non-vacuity gates to the
reciprocal-mode Bloch phase group law, the mode-wise Schrödinger generator law,
and the independent integer clock.  The continuum coefficient-identification
boundary is retained as an explicit obligation.
-/

open Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution

#check @Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution.unitPhaseStep
#check @Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution.ContinuumCoefficientIdentification

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution.modePhase_add,
  Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution.periodicStateStep_add,
  Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution.integerClockAge_step,
  Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution.modePhase_hasDerivAt,
  Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution.periodic_mode_schrodinger ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution.modePhase_add,
  Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution.periodicStateStep_add,
  Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution.integerClockAge_step,
  Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution.modePhase_hasDerivAt,
  Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution.periodic_mode_schrodinger ]
