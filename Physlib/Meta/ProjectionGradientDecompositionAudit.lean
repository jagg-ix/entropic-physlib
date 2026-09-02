/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the projection gradient decomposition -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition.projection_hh_zero,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition.projection_vv_zero,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition.projectionGradient_decomposition,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition.extrinsicCurvature_projection_identity ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition.projection_hh_zero,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition.projection_vv_zero,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition.projectionGradient_decomposition,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition.extrinsicCurvature_projection_identity ]
