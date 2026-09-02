/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the general-α Gegenbauer recurrence family
-/

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence.gegenbauerP_recurrence,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence.gegenbauerP_two ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence.gegenbauerP_recurrence,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence.gegenbauerP_two ]
