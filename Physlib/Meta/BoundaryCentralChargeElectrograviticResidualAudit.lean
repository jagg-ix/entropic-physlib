/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.BoundaryCentralChargeElectrograviticResidual
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the boundary-central-charge electrogravitic-residual dictionary
-/

open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.BoundaryCentralChargeElectrograviticResidual

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.BoundaryCentralChargeElectrograviticResidual.boundaryCentralCharge_electrograviticResidual_vanishing,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.BoundaryCentralChargeElectrograviticResidual.boundaryCentralCharge_governs_einsteinMaxwell_and_entropicResidual ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.BoundaryCentralChargeElectrograviticResidual.boundaryCentralCharge_electrograviticResidual_vanishing,
  Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.BoundaryCentralChargeElectrograviticResidual.boundaryCentralCharge_governs_einsteinMaxwell_and_entropicResidual ]
