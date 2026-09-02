/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.L2KetAdapter
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the normalized Ket adapter

The adapter's content is definitional (the Ket carries the same amplitudes,
and its Born weights are the Born boundary), so only the axiom gate
applies here; the formalization-lint gate runs in the module itself.
-/

open Physlib.QuantumMechanics.L2KetAdapter

#check @Physlib.QuantumMechanics.L2KetAdapter.ketOfL2State
#check @Physlib.QuantumMechanics.L2KetAdapter.bornDist_eq_ketBorn

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.L2KetAdapter.ketOfL2State,
  Physlib.QuantumMechanics.L2KetAdapter.ketOfL2State_apply,
  Physlib.QuantumMechanics.L2KetAdapter.bornDist_eq_ketBorn,
  Physlib.QuantumMechanics.L2KetAdapter.l2OfKet,
  Physlib.QuantumMechanics.L2KetAdapter.l2OfKet_norm_one,
  Physlib.QuantumMechanics.L2KetAdapter.ketOfL2State_l2OfKet,
  Physlib.QuantumMechanics.L2KetAdapter.l2OfKet_ketOfL2State,
  Physlib.QuantumMechanics.L2KetAdapter.pureOfL2State,
  Physlib.QuantumMechanics.L2KetAdapter.bornDist_eq_pure_diagonal,
  Physlib.QuantumMechanics.L2KetAdapter.demoJoint_sum_one,
  Physlib.QuantumMechanics.L2KetAdapter.stateOfDemo_norm_one,
  Physlib.QuantumMechanics.L2KetAdapter.coupledOutput_norm_one,
  Physlib.QuantumMechanics.L2KetAdapter.ket_isProd_totalCorrelation_zero,
  Physlib.QuantumMechanics.L2KetAdapter.coupledOutput_ketEntangled,
  Physlib.QuantumMechanics.L2KetAdapter.ketRelabel,
  Physlib.QuantumMechanics.L2KetAdapter.ketOfL2State_koopman,
  Physlib.QuantumMechanics.L2KetAdapter.pureOfL2State_koopman,
  Physlib.QuantumMechanics.L2KetAdapter.diagonalMeasurement,
  Physlib.QuantumMechanics.L2KetAdapter.diagonalMeasurement_pureOfL2State,
  Physlib.QuantumMechanics.L2KetAdapter.coupling_correlation_is_diagonalMeasurement,
  Physlib.QuantumMechanics.L2KetAdapter.bornProbDistribution,
  Physlib.QuantumMechanics.L2KetAdapter.diagonalProbDistribution ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.L2KetAdapter.l2OfKet_norm_one,
  Physlib.QuantumMechanics.L2KetAdapter.ketOfL2State_l2OfKet,
  Physlib.QuantumMechanics.L2KetAdapter.l2OfKet_ketOfL2State,
  Physlib.QuantumMechanics.L2KetAdapter.bornDist_eq_pure_diagonal,
  Physlib.QuantumMechanics.L2KetAdapter.ket_isProd_totalCorrelation_zero,
  Physlib.QuantumMechanics.L2KetAdapter.coupledOutput_ketEntangled,
  Physlib.QuantumMechanics.L2KetAdapter.diagonalMeasurement_pureOfL2State,
  Physlib.QuantumMechanics.L2KetAdapter.coupling_correlation_is_diagonalMeasurement ]
