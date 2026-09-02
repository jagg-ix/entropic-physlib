/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.DZeroDSixLorentzForce
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit for the D0--D6 Lorentz-force bridge -/

open Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.DZeroDSixLorentzForce

#physlib_axiom_clean_all [
  dZeroDSix_hodge_gradients_orthogonal,
  dZeroDSix_hodge_gradients_equal_norm,
  dZeroDSix_chargeNormalizedPotential_eq,
  dZeroDSixLorentzPotential_eq_force_component,
  dZeroDSixLorentzPotential_timeReversal,
  dZeroDSixLorentzPotential_hasDerivAt,
  dZeroDSix_radius_mul_potential,
  dZeroDSix_matrix_velocity_gaussian_identity,
  dZeroDSix_probe_string_matrix_lorentz_closure,
  dZeroDSixOddEuclideanAction_eq_neg_time_mul_potential,
  dZeroDSixOddEuclideanAction_nonneg,
  dZeroDSixOddEuclideanAction_monotone_time,
  dZeroDSixNagaoNielsenWeight_norm,
  dZeroDSixNagaoNielsenWeight_norm_antitone_time,
  iibOvv_dZeroDSix_entropicClock_chain,
  iibOvv_dZeroDSix_rapidity_chain,
  dZeroDSix_wittenVerlindeTrefoil_contour_chain,
  dZeroDSix_braidingWilsonIntegral_eq_verlinde_mul_partition ]

#physlib_non_vacuous_all [
  dZeroDSix_hodge_gradients_orthogonal,
  dZeroDSix_hodge_gradients_equal_norm,
  dZeroDSix_chargeNormalizedPotential_eq,
  dZeroDSixLorentzPotential_eq_force_component,
  dZeroDSixLorentzPotential_timeReversal,
  dZeroDSixLorentzPotential_hasDerivAt,
  dZeroDSix_radius_mul_potential,
  dZeroDSix_matrix_velocity_gaussian_identity,
  dZeroDSix_probe_string_matrix_lorentz_closure,
  dZeroDSixOddEuclideanAction_eq_neg_time_mul_potential,
  dZeroDSixOddEuclideanAction_nonneg,
  dZeroDSixOddEuclideanAction_monotone_time,
  dZeroDSixNagaoNielsenWeight_norm,
  dZeroDSixNagaoNielsenWeight_norm_antitone_time,
  iibOvv_dZeroDSix_entropicClock_chain,
  iibOvv_dZeroDSix_rapidity_chain,
  dZeroDSix_wittenVerlindeTrefoil_contour_chain,
  dZeroDSix_braidingWilsonIntegral_eq_verlinde_mul_partition ]
