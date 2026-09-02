/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionVariation
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of YangMillsActionSpacetimeIntegral -/

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionSpacetimeIntegral.covariant_integration_by_parts,
  Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionSpacetimeIntegral.stationary_action_implies_field_equation ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionSpacetimeIntegral.covariant_integration_by_parts,
  Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionSpacetimeIntegral.stationary_action_implies_field_equation ]
