/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.BoundaryCentralChargeElectrograviticResidual
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the Liouville-complexity / electrogravitic-residual central-charge tie
-/

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.LiouvilleComplexityElectrograviticResidual

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.LiouvilleComplexityElectrograviticResidual.boundaryCentralCharge_governs_residual_and_liouvilleComplexity,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.LiouvilleComplexityElectrograviticResidual.liouvilleComplexity_times_residualCoupling_centralChargeInvariant ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.LiouvilleComplexityElectrograviticResidual.boundaryCentralCharge_governs_residual_and_liouvilleComplexity,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.LiouvilleComplexityElectrograviticResidual.liouvilleComplexity_times_residualCoupling_centralChargeInvariant ]
