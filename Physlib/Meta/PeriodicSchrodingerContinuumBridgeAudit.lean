/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.PeriodicSchrodinger.Continuum
public import Physlib.QuantumMechanics.Schrodinger.SpectralDynamics
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the periodic-mode finite-to-continuum Fourier bridge
-/

open Physlib.QuantumMechanics.PeriodicSchrodinger

#check @Physlib.QuantumMechanics.PeriodicSchrodinger.modeCircleEquiv

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.PeriodicSchrodinger.modeCircleEquiv,
  Physlib.QuantumMechanics.PeriodicSchrodinger.modeCircleEquiv_norm,
  Physlib.QuantumMechanics.PeriodicSchrodinger.modeCircleEquiv_inner,
  Physlib.QuantumMechanics.Schrodinger.SpectralDynamics.perepelkinTheta_antiperiodic,
  Physlib.QuantumMechanics.Schrodinger.SpectralDynamics.perepelkinTheta_periodic_two ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.PeriodicSchrodinger.modeCircleEquiv_norm,
  Physlib.QuantumMechanics.PeriodicSchrodinger.modeCircleEquiv_inner,
  Physlib.QuantumMechanics.Schrodinger.SpectralDynamics.perepelkinTheta_antiperiodic,
  Physlib.QuantumMechanics.Schrodinger.SpectralDynamics.perepelkinTheta_periodic_two ]
