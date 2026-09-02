/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.MalamentConformalProperTimeBridge
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the Malament conformal / proper-time bridge
-/

open Lorentz.Vector

#physlib_axiom_clean_all [
  Lorentz.Vector.same_null_cone_iff_proportional,
  Lorentz.Vector.causalAutomorphism_decomposition_with_properTime,
  Lorentz.Vector.properTime_causalAutomorphism ]

#physlib_non_vacuous_all [
  Lorentz.Vector.same_null_cone_iff_proportional,
  Lorentz.Vector.causalAutomorphism_decomposition_with_properTime,
  Lorentz.Vector.properTime_causalAutomorphism ]
