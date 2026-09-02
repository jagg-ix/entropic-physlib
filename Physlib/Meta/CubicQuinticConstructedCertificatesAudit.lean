/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Meta.AxiomWhitelistCheck
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticConstructedCertificates

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.CubicQuinticConstructedCertificates

#physlib_axiom_clean_all [
  freeHOneFlow_zero,
  freeHOneFlow_add,
  norm_freeHOneFlow,
  freeHOneFlow_tendsto_zero,
  exists_identifiedTargetBranchCertificate,
  exists_identifiedStableMinimizingBranch ]

#physlib_non_vacuous_all [
  freeHOneFlow_zero,
  freeHOneFlow_add,
  norm_freeHOneFlow,
  freeHOneFlow_tendsto_zero,
  exists_identifiedTargetBranchCertificate,
  exists_identifiedStableMinimizingBranch ]
