/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.EuclideanTensorCompositionIso
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the coordinate-product tensor isomorphism -/

open Physlib.QuantumMechanics.EuclideanTensorCompositionIso

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.EuclideanTensorCompositionIso.euclideanTensorEquiv_basisFun ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.EuclideanTensorCompositionIso.euclideanTensorEquiv_basisFun ]
