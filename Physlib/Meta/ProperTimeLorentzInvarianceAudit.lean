/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Special.ProperTimeWorldlineIntegral
public import Physlib.SpaceAndTime.GalileanGroup.Basic
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of kinematic invariance boundaries

This audit covers proper-time Lorentz invariance and the complementary fact
that a scalar invariant under every Galilean velocity translation must be
constant.
-/

open SpaceTime

#physlib_axiom_clean_all [
  SpaceTime.intervalSq_lorentz_invariant,
  SpaceTime.properTime_lorentz_invariant,
  SpaceTime.causalCharacter_sub_lorentz_invariant,
  GalileanGroup.velocityTranslationInvariant_iff_constant ]

#physlib_non_vacuous_all [
  SpaceTime.intervalSq_lorentz_invariant,
  SpaceTime.properTime_lorentz_invariant,
  SpaceTime.causalCharacter_sub_lorentz_invariant,
  GalileanGroup.velocityTranslationInvariant_iff_constant ]
