/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Meta.AxiomWhitelistCheck
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.M9ChargeKleinOrbitalCriteria

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.M9ChargeKleinOrbitalCriteria

#physlib_axiom_clean_all [
  chargeQuantizationCriterion,
  chargeCreationOperatorGrading,
  kleinGordonFrequency_sq,
  kleinGordonModePosition_zero,
  kleinGordonModeMomentum_zero,
  kleinGordonModeEnergy_conserved,
  kleinGordonFiniteModeCriterion,
  hydrogenicEnergy_neg,
  orbitalQuantizationCriterion ]

#physlib_non_vacuous_all [
  chargeQuantizationCriterion,
  chargeCreationOperatorGrading,
  kleinGordonFrequency_sq,
  kleinGordonModePosition_zero,
  kleinGordonModeMomentum_zero,
  kleinGordonModeEnergy_conserved,
  kleinGordonFiniteModeCriterion,
  hydrogenicEnergy_neg,
  orbitalQuantizationCriterion ]
