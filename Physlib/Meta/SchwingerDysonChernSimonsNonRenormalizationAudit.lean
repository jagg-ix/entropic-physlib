/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Meta.AxiomWhitelistCheck
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.SchwingerDysonNonRenormalization

/-!
# Audit of Chern--Simons Schwinger--Dyson non-renormalization

The audit gates the equation-comparison result, the genuine improper-integral argument, the exact
two-point conclusion, the continuum Dyson adapter, and the anomalous level-shift branch.
-/

open Physlib.QuantumMechanics.ComplexAction.ChernSimons.SchwingerDysonNonRenormalization

#physlib_axiom_clean_all [
  DanielVectorWardHierarchy.twoPointWardInsertion_eq_zero,
  DanielVectorWardHierarchy.threePointWardInsertion_eq_zero,
  DanielVectorWardHierarchy.twoPointWard_relation,
  DanielVectorWardHierarchy.threePointWard_relation,
  danielGhostVertex_leviCivita_contraction,
  danielSU2_adjointCasimir_contraction,
  DanielWardSchwingerDysonData.residualVertexKernel_eq_zero,
  danielCutoffRadialConstraint_const,
  constant_eq_one_of_danielCutoffRadialConstraint_zero,
  IsMomentumScaleInvariant.eq_at_one_of_pos,
  DanielContinuumRadialConstraint.eq_zero,
  daniel_loopIntegral_momentumShift,
  DanielFubiniMomentumShiftData.radialIntegral_eq_zero,
  waveFunction_eq_one_on_positive_of_scaleInvariant_continuumConstraint,
  waveFunction_eq_one_on_positive_of_scaleInvariant_fubiniReduction,
  waveFunction_hasDerivAt_zero_of_scaleInvariant_fubiniReduction,
  danielBetaFunction_eq_zero_of_scaleInvariant_fubiniReduction,
  danielBareGaugeTensor_transverse,
  danielExactGaugeTensor_transverse,
  daniel_twoPointFunctions_eq_bare,
  daniel_csw_twoPoint_nonrenormalization,
  daniel_concrete_twoPointFunctions_eq_bare,
  danielExactGhostPropagator_inv_eq_momentumNormSq,
  danielWardKernel_continuumDyson_dressed_eq_free,
  daniel_gaugeInvariantRegulator_levelShift ]

#physlib_non_vacuous_all [
  DanielVectorWardHierarchy.twoPointWardInsertion_eq_zero,
  DanielVectorWardHierarchy.threePointWardInsertion_eq_zero,
  DanielVectorWardHierarchy.twoPointWard_relation,
  DanielVectorWardHierarchy.threePointWard_relation,
  danielGhostVertex_leviCivita_contraction,
  danielSU2_adjointCasimir_contraction,
  DanielWardSchwingerDysonData.residualVertexKernel_eq_zero,
  danielCutoffRadialConstraint_const,
  constant_eq_one_of_danielCutoffRadialConstraint_zero,
  daniel_loopIntegral_momentumShift,
  DanielFubiniMomentumShiftData.radialIntegral_eq_zero,
  waveFunction_eq_one_on_positive_of_scaleInvariant_continuumConstraint,
  waveFunction_eq_one_on_positive_of_scaleInvariant_fubiniReduction,
  waveFunction_hasDerivAt_zero_of_scaleInvariant_fubiniReduction,
  danielBetaFunction_eq_zero_of_scaleInvariant_fubiniReduction,
  danielBareGaugeTensor_transverse,
  danielExactGaugeTensor_transverse,
  daniel_twoPointFunctions_eq_bare,
  daniel_csw_twoPoint_nonrenormalization,
  daniel_concrete_twoPointFunctions_eq_bare,
  danielExactGhostPropagator_inv_eq_momentumNormSq,
  danielWardKernel_continuumDyson_dressed_eq_free,
  daniel_gaugeInvariantRegulator_levelShift ]
