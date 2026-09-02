/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalPreorder
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the Minkowski causal preorder

Gates the closed-cone reverse Cauchy–Schwarz inequality, closure of the future causal
cone under addition, reflexivity and transitivity of the causal order, and the
identification of the causal diamond with the order interval.
-/

open Lorentz.Vector

#physlib_axiom_clean_all [
  Lorentz.Vector.minkowskiProduct_nonneg_of_futureCausal,
  Lorentz.Vector.causallyFollows_iff_isFutureCausal,
  Lorentz.Vector.isFutureCausal_add,
  Lorentz.Vector.causallyFollows_refl,
  Lorentz.Vector.causallyFollows_trans,
  Lorentz.Vector.causalDiamond_eq_Icc ]

#physlib_non_vacuous_all [
  Lorentz.Vector.minkowskiProduct_nonneg_of_futureCausal,
  Lorentz.Vector.causallyFollows_iff_isFutureCausal,
  Lorentz.Vector.isFutureCausal_add,
  Lorentz.Vector.causallyFollows_refl,
  Lorentz.Vector.causallyFollows_trans ]
