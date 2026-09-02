/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleHyperbolicAdSSlice
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the Liouville-optimized hyperbolic AdS slice
-/

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleHyperbolicAdSSlice

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleHyperbolicAdSSlice.adSPoincareFactor_eq_exp_two_liouvilleField,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleHyperbolicAdSSlice.log_adSPoincareFactor_eq_two_liouvilleField,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleHyperbolicAdSSlice.liouville_optimized_hyperbolic_slice ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleHyperbolicAdSSlice.adSPoincareFactor_eq_exp_two_liouvilleField,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleHyperbolicAdSSlice.log_adSPoincareFactor_eq_two_liouvilleField,
  Physlib.QuantumMechanics.ComplexAction.AdSCFT.LiouvilleHyperbolicAdSSlice.liouville_optimized_hyperbolic_slice ]
