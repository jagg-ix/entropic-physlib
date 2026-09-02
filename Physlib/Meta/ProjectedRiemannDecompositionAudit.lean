/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRiemannDecomposition
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of ProjectedRiemannDecomposition -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRiemannDecomposition

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRiemannDecomposition.projectRiemannFirst_one,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRiemannDecomposition.riemann_first_decomposition,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRiemannDecomposition.projectRiemannFirst_antisymm_right ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRiemannDecomposition.projectRiemannFirst_one,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRiemannDecomposition.riemann_first_decomposition,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRiemannDecomposition.projectRiemannFirst_antisymm_right ]
