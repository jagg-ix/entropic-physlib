/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Special.ProperTimeWorldlineIntegral
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the proper-time worldline integral -/

open SpaceTime

#physlib_axiom_clean_all [
  SpaceTime.properTimeIntegral_straight,
  SpaceTime.properTimeIntegral_straight_lorentz_invariant ]

#physlib_non_vacuous_all [
  SpaceTime.properTimeIntegral_straight,
  SpaceTime.properTimeIntegral_straight_lorentz_invariant ]
