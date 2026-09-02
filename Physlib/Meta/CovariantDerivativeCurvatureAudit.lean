/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of CovariantDerivativeCurvature -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature.curvatureTwoForm_antisymm,
  Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature.ricci_identity,
  Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature.ricci_identity_flat ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature.curvatureTwoForm_antisymm,
  Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature.ricci_identity,
  Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeCurvature.ricci_identity_flat ]
