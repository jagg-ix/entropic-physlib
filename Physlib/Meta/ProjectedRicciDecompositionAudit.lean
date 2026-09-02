/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRicciDecomposition
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of ProjectedRicciDecomposition -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRicciDecomposition

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRicciDecomposition.projectRicci_symm,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRicciDecomposition.projectRicci_idem,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRicciDecomposition.ricci_projection_decomposition ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRicciDecomposition.projectRicci_symm,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRicciDecomposition.projectRicci_idem,
  Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectedRicciDecomposition.ricci_projection_decomposition ]
