/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Varlamov Clifford--Lorentz audit

Focused kernel, non-vacuity, and ZIL-contract gate for the Clifford symmetry,
Pin-reflection, and bundled `SL(2,C)` cover results extracted from Varlamov's
*Clifford Algebras and Lorentz Group*.
-/

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CliffordPinReflection

#physlib_axiom_clean_all [
  cliffordFundamentalSymmetry_card,
  cliffordFundamentalAction_comp,
  cliffordFundamentalAction_involutive,
  cliffordFundamentalAction_full_eq_star,
  clifford_triple_eq,
  clifford_pin_sandwich_eq_reflect,
  sl2cBundledCover_neg,
  sl2c_negOne_ne_one,
  sl2c_negOne_mem_restrictedCover_kernel,
  sl2cBundledCover_eq_one_iff,
  sl2c_restrictedCover_mem_kernel_iff,
  sl2cBundledCover_eq_iff
]

#physlib_non_vacuous_all [
  cliffordFundamentalAction_comp,
  cliffordFundamentalAction_involutive,
  clifford_triple_eq,
  clifford_pin_sandwich_eq_reflect,
  sl2cBundledCover_neg,
  sl2c_negOne_ne_one,
  sl2c_negOne_mem_restrictedCover_kernel,
  sl2cBundledCover_eq_one_iff,
  sl2c_restrictedCover_mem_kernel_iff,
  sl2cBundledCover_eq_iff
]

#zil_formalization_lint physlib.varlamovCliffordLorentz
