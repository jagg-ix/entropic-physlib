/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalAutomorphismConformalInvariants
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the causal-automorphism conformal invariants
-/

open Lorentz.Vector

#physlib_axiom_clean_all [
  Lorentz.Vector.intervalSq_causalAutomorphism,
  Lorentz.Vector.causalCharacter_causalAutomorphism,
  Lorentz.Vector.properTime_ratio_causalAutomorphism ]

#physlib_non_vacuous_all [
  Lorentz.Vector.intervalSq_causalAutomorphism,
  Lorentz.Vector.causalCharacter_causalAutomorphism,
  Lorentz.Vector.properTime_ratio_causalAutomorphism ]
