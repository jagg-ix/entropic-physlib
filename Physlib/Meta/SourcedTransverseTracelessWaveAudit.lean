/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the sourced transverse-traceless gravitational wave
-/

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.dalembertian_offshell,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.dalembertian_offshell_onshell,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.einsteinTTCoupling_eq_neg_two_mul,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.sourcedTTWave_retarded_solution,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.sourcedTTWave_vacuum ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.dalembertian_offshell,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.dalembertian_offshell_onshell,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.einsteinTTCoupling_eq_neg_two_mul,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTransverseTracelessWave.sourcedTTWave_retarded_solution ]
