/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerFamilyConsistency
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the Gegenbauer recurrence-family consistency bridge
-/

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerFamilyConsistency

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerFamilyConsistency.gegenbauerP_eval_zero,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerFamilyConsistency.gegenbauerP_eval_one,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerFamilyConsistency.gegenbauerP_eval_two,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerFamilyConsistency.gegenbauerP_one_eq_chebyshevU ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerFamilyConsistency.gegenbauerP_eval_zero,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerFamilyConsistency.gegenbauerP_eval_one,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerFamilyConsistency.gegenbauerP_eval_two,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerFamilyConsistency.gegenbauerP_one_eq_chebyshevU ]
