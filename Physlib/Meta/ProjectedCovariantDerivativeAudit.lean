/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of ProjectedCovariantDerivative -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedCovariantDerivative

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedCovariantDerivative.covariantDeriv_split,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedCovariantDerivative.projectedCovariantDeriv_idem,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedCovariantDerivative.covariantDerivEndo_projection_decomposition ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedCovariantDerivative.covariantDeriv_split,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedCovariantDerivative.projectedCovariantDeriv_idem,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedCovariantDerivative.covariantDerivEndo_projection_decomposition ]
