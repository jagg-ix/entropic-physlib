/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the all-order general-α Gegenbauer eigenfunction theorem
-/

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction.gegenbauerP_deriv_recurrence,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction.gegenbauer_derivativeRelations,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction.gegenbauerP_ode,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction.gegenbauerP_solves,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction.gegenbauerP_solves_all,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction.gegenbauerP_legendre_solves_all ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction.gegenbauerP_deriv_recurrence,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction.gegenbauer_derivativeRelations,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction.gegenbauerP_ode,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction.gegenbauerP_solves,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction.gegenbauerP_solves_all,
  Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction.gegenbauerP_legendre_solves_all ]
