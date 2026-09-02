/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.LorentzForceElectrograviticBridge
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit for the potential-derived Lorentz-force chain -/

set_option maxRecDepth 8000

open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.LorentzForceElectrograviticBridge

#physlib_axiom_clean_all [
  potentialDerivativeCandidate_antisymmetric_iff,
  potentialLorentzForceNumerator_apply_eq_derivatives,
  potentialLorentzForceNumerator_gauge_invariant,
  potentialLorentzForce_orthogonal,
  potentialLorentzForceDual_nonneg,
  potentialLorentzForceDual_eq,
  potentialElectricField_longitudinal_boost,
  lorentzThreeForce_power,
  magneticLorentzForce_no_work,
  lorentzThreeForce_work_energy,
  pureMagnetic_lorentz_energy_conserved,
  potential_faraday_lenz,
  potential_lorentz_force_derivation_closure,
  derive_electrogravitic_field_equation_with_lorentz_bcj,
  lorentzForce_bcj_electrogravitic_bianchi_closure,
  lorentzForce_bcj_electrogravitic_bit_closure,
  potentialLorentzForceNumerator_reindex,
  potential_lorentzForce_bcj_electrogravitic ]

#physlib_axiom_clean_all [
  potentialFieldStrengthFin4_eq_faraday_of_momentumMode,
  potentialFieldStrengthFin4_gauge_invariant,
  potential_lorentzForce_bcj_electrogravitic_of_momentumMode,
  gaugeTransformed_potential_lorentzForce_bcj_electrogravitic ]

#physlib_axiom_clean_all [
  raisedMomentumPhaseCLM_basis,
  affineMomentumPotential_deriv,
  affineMomentumPotential_isMode,
  affineMomentumPotential_contDiff,
  affineMomentumPotential_fieldStrength,
  affineMomentumPotential_bcj_electrogravitic ]

#physlib_axiom_clean_all [
  gibbonsWells_lorentz_bcj_electrogravitic,
  gibbonsWells_lorentz_bcj_electrogravitic_bianchi_closure,
  lorentzForce_operatorDoubleCopy_electrogravitic,
  gibbonsWells_lorentz_bcj_zeno_interval,
  lorentzForce_operatorDoubleCopy_zeno_interval,
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.mandelstamTamm_repeated_survival_tendsto_one,
  gibbonsWells_lorentz_bcj_zeno_freeze,
  lorentzForce_operatorDoubleCopy_zeno_freeze ]

#physlib_non_vacuous_all [
  potentialDerivativeCandidate_antisymmetric_iff,
  potentialLorentzForceNumerator_apply_eq_derivatives,
  potentialLorentzForceNumerator_gauge_invariant,
  potentialLorentzForce_orthogonal,
  potentialLorentzForceDual_nonneg,
  lorentzThreeForce_power,
  magneticLorentzForce_no_work,
  lorentzThreeForce_work_energy,
  pureMagnetic_lorentz_energy_conserved,
  potential_faraday_lenz,
  potential_lorentz_force_derivation_closure,
  derive_electrogravitic_field_equation_with_lorentz_bcj,
  lorentzForce_bcj_electrogravitic_bianchi_closure,
  lorentzForce_bcj_electrogravitic_bit_closure,
  potentialLorentzForceNumerator_reindex,
  potential_lorentzForce_bcj_electrogravitic ]

-- This theorem deliberately exposes the exact repository boost theorem under the paper-facing name;
-- the substantive equivariance proof is already audited in the electromagnetic geometry layer.
-- Keep the adapter axiom-clean-only rather than pretending it adds a second proof obligation.

#physlib_non_vacuous potentialFieldStrengthFin4_eq_faraday_of_momentumMode
-- The `Fin 4` gauge theorem is a representation transport of the already-audited smooth theorem;
-- keep the wrapper in the axiom-clean gate and gate the substantive gauge closure below.
#physlib_non_vacuous potential_lorentzForce_bcj_electrogravitic_of_momentumMode
#physlib_non_vacuous gaugeTransformed_potential_lorentzForce_bcj_electrogravitic

#physlib_non_vacuous raisedMomentumPhaseCLM_basis
#physlib_non_vacuous affineMomentumPotential_deriv
#physlib_non_vacuous affineMomentumPotential_isMode
-- Smoothness is inherited directly from the bundled continuous-linear map; the derivative and
-- field-strength consequences below carry the substantive witness obligations.
#physlib_non_vacuous affineMomentumPotential_fieldStrength
#physlib_non_vacuous affineMomentumPotential_bcj_electrogravitic

#physlib_non_vacuous gibbonsWells_lorentz_bcj_electrogravitic
#physlib_non_vacuous gibbonsWells_lorentz_bcj_electrogravitic_bianchi_closure
#physlib_non_vacuous lorentzForce_operatorDoubleCopy_electrogravitic
#physlib_non_vacuous gibbonsWells_lorentz_bcj_zeno_interval
#physlib_non_vacuous lorentzForce_operatorDoubleCopy_zeno_interval
#physlib_non_vacuous Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.mandelstamTamm_repeated_survival_tendsto_one
#physlib_non_vacuous gibbonsWells_lorentz_bcj_zeno_freeze
#physlib_non_vacuous lorentzForce_operatorDoubleCopy_zeno_freeze
