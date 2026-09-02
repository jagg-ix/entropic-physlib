/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiFromConnection
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the Ricci second Bianchi from a connection -/

open Physlib.QuantumMechanics.ComplexAction.Curvature.RicciSecondBianchiFromConnection

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.RicciSecondBianchiFromConnection.ricci_secondBianchi ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.RicciSecondBianchiFromConnection.ricci_secondBianchi ]
