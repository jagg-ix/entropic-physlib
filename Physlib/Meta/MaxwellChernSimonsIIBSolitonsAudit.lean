/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Meta.AxiomWhitelistCheck
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.MaxwellChernSimonsIIBSolitons

/-!
# Audit of the type-IIB Maxwell--Chern--Simons soliton bridge

The audit keeps the paper-specific equation, limit, vacuum, vortex, and mirror-map witnesses behind
the repository's kernel-clean and non-vacuity gates.
-/

open Physlib.QuantumMechanics.ComplexAction.ChernSimons.MaxwellChernSimonsIIBSolitons

#physlib_axiom_clean_all [
  iibStringTension_nonneg,
  iibFStringTension,
  iibDStringTension_axion_eq_neg_coupling,
  iibDStringTension_minimal_at_zero,
  vectorMultipletMass_eq_djtTopologicalMass,
  pureChernSimons_vectorMass_tendsto_atTop,
  pureChernSimons_maxwellCoefficient_tendsto_zero,
  pureChernSimons_decoupling_limit,
  compactification_vectorMass_tendsto_atTop,
  mcsPotential_nonneg,
  mcsPotential_eq_zero_iff,
  mcsPotential_brokenVacuum,
  mcsPotential_unbrokenVacuum,
  nThreeMCSPotential_nonneg,
  complexNormSq_add_eq_zero_iff,
  sq_add_complexNormSq_eq_zero_iff,
  nThreeMCSPotential_eq_zero_iff,
  nThreeMCSPotential_brokenVacuum,
  nThreeMCSPotential_unbrokenVacuum_of_constraints,
  nThreeMCSPotential_unbrokenVacuum,
  topologicalVortexMass_eq_zeroModes,
  nontopologicalVortexFlux_eq_deserFlux,
  nontopologicalVortexFlux_charge_chain,
  nontopologicalVortexFlux_pos,
  leeAlphaHat_lt,
  le_leeAlphaHat_iff,
  nontopologicalVortexZeroModes_ge_four_mul,
  mirrorCoupling_involutive,
  mirrorStringCharge_primitive_iff,
  mirrorStringCharge_sq,
  mirrorStringCharge_four,
  nThreeMCSPotentialMetricSource_eq_zero_iff,
  leeMCS_dim3_lovelockTensor_classification,
  metricTrace_nThreeMCSPotentialMetricSource,
  leeMCS_dim3_lovelockFieldEquation,
  leeMCS_dim3_lovelockFieldEquation_effectiveLambda,
  leeMCS_dim3_lovelockEinsteinTrace,
  leeMCS_dim3_zeroVacuum_lovelockFieldEquation ]

#physlib_non_vacuous_all [
  iibDStringTension_axion_eq_neg_coupling,
  iibDStringTension_minimal_at_zero,
  vectorMultipletMass_eq_djtTopologicalMass,
  pureChernSimons_vectorMass_tendsto_atTop,
  pureChernSimons_decoupling_limit,
  compactification_vectorMass_tendsto_atTop,
  mcsPotential_eq_zero_iff,
  nThreeMCSPotential_eq_zero_iff,
  nThreeMCSPotential_brokenVacuum,
  nThreeMCSPotential_unbrokenVacuum,
  topologicalVortexMass_eq_zeroModes,
  nontopologicalVortexFlux_charge_chain,
  nontopologicalVortexFlux_pos,
  le_leeAlphaHat_iff,
  nontopologicalVortexZeroModes_ge_four_mul,
  mirrorCoupling_involutive,
  mirrorStringCharge_primitive_iff,
  mirrorStringCharge_four,
  nThreeMCSPotentialMetricSource_eq_zero_iff,
  leeMCS_dim3_lovelockTensor_classification,
  metricTrace_nThreeMCSPotentialMetricSource,
  leeMCS_dim3_lovelockFieldEquation,
  leeMCS_dim3_lovelockFieldEquation_effectiveLambda,
  leeMCS_dim3_lovelockEinsteinTrace,
  leeMCS_dim3_zeroVacuum_lovelockFieldEquation ]
