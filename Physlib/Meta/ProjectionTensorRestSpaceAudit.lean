/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.AffineProjectionTensorGeometry
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of ProjectionTensorRestSpace -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionTensorRestSpace

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionTensorRestSpace.restSpaceProjector_isProjection,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionTensorRestSpace.worldlineProjector_eq_complement,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionTensorRestSpace.restSpaceProjector_isNormal ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionTensorRestSpace.restSpaceProjector_isProjection,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionTensorRestSpace.worldlineProjector_eq_complement,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionTensorRestSpace.restSpaceProjector_isNormal ]
