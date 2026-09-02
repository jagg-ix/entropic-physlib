/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTTWaveComptonCoupling
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the holographic-coupling re-evaluation of the sourced TT wave
-/

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.einsteinTTCoupling_bitForm,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.newtonG_holographic_holographicBits,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.einsteinTTCoupling_holographicNewton,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.sourcedTTWave_holographic ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.einsteinTTCoupling_bitForm,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.newtonG_holographic_holographicBits,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.einsteinTTCoupling_holographicNewton,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.sourcedTTWave_holographic ]
