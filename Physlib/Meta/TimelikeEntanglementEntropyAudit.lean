/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.TimelikeEntanglementEntropy
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of timelike CFT2/AdS3 entanglement entropy
-/

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.TimelikeEntanglementEntropy

#physlib_axiom_clean_all [
  timelikePoincareLorentzSpeedSq_eq,
  timelikePoincareLineDensity_eq,
  complexLog_neg_sq,
  timelikeCFTEntropyFromRatio_eq,
  timelikeCFTEntropyMinkowski_eq,
  timelikeCFTEntropyVacuumLine_eq,
  timelikeCFTEntropyVacuumLine_re,
  timelikeCFTEntropyVacuumLine_im,
  timelikeCFTEntropyCircle_eq,
  timelikeCFTEntropyFiniteT_eq,
  timelikeAdS3GeodesicImaginaryEntropy_eq,
  timelikeCFTEntropyVacuumLine_brownHenneaux,
  transitionDyad_traceRight,
  timelikeTransitionHalfAmplitude_sq,
  timelikeTransitionDyad_traceRight,
  timelikeReducedTransition_trace_one,
  diagonalPseudoEntropy_eq_neg_trace,
  timelikePseudoEntropy_eq_neg_trace,
  timelikeReducedTransition_not_hermitian,
  timelikeTransitionWeight_at_R_zero_eq_tfd,
  timelikeEntropy_entropicProperTime,
  timelikeEntropy_nnWeight_norm,
  trace_mconj,
  diagonalizableTransition_mul_log,
  diagonalizablePseudoEntropy_eq,
  diagonalizablePseudoEntropy_basis_independent,
  diagonalizableTransition_qNormal,
  timelikeEntropyCalibratedDuration_pos,
  timelikeEntropyCalibratedDuration_action,
  timelikeEntropyCalibratedDuration_operational,
  universalTimelikeEntropyActionAlong_increment,
  universalTimelikeEntropyActionAlong_not_clock,
  higherDimTimelikeSurfaceCoefficient_pos,
  higherDimTimelikeSurfaceCoefficient_two,
  higherDimTimelikeSurfaceEntropy_im,
  higherDimTimelikeSurfaceEntropy_two ]

#physlib_non_vacuous_all [
  timelikePoincareLorentzSpeedSq_eq,
  timelikePoincareLineDensity_eq,
  complexLog_neg_sq,
  timelikeCFTEntropyFromRatio_eq,
  timelikeCFTEntropyMinkowski_eq,
  timelikeCFTEntropyVacuumLine_eq,
  timelikeCFTEntropyVacuumLine_re,
  timelikeCFTEntropyVacuumLine_im,
  timelikeCFTEntropyCircle_eq,
  timelikeCFTEntropyFiniteT_eq,
  timelikeAdS3GeodesicImaginaryEntropy_eq,
  timelikeCFTEntropyVacuumLine_brownHenneaux,
  transitionDyad_traceRight,
  timelikeTransitionHalfAmplitude_sq,
  timelikeTransitionDyad_traceRight,
  timelikeReducedTransition_trace_one,
  timelikeReducedTransition_not_hermitian,
  timelikeTransitionWeight_at_R_zero_eq_tfd,
  timelikeEntropy_entropicProperTime,
  timelikeEntropy_nnWeight_norm,
  diagonalizablePseudoEntropy_eq,
  diagonalizablePseudoEntropy_basis_independent,
  diagonalizableTransition_qNormal,
  timelikeEntropyCalibratedDuration_action,
  timelikeEntropyCalibratedDuration_operational,
  universalTimelikeEntropyActionAlong_not_clock,
  higherDimTimelikeSurfaceCoefficient_pos,
  higherDimTimelikeSurfaceCoefficient_two,
  higherDimTimelikeSurfaceEntropy_two ]
