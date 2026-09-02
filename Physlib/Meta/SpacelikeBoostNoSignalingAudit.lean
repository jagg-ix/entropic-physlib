/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bell.NoSignaling
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the boost-invariant light cone → locality / Bell no-signaling upgrade

Gates the Local Lorentz Invariance of the Minkowski form, boost-invariance of the
causal character, relativity of simultaneity for spacelike separation, frame-invariant
causal order for timelike separation, and the frame-covariance of the CHSH/no-signaling
contract.
-/

open Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.boostBy_preserves_lorentzianForm,
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.coshSinhBoost_preserves_lorentzianForm,
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.boostBy_preserves_spacelike,
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.boostBy_preserves_timelike,
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.spacelike_exists_simultaneity_frame,
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.boostBy_preserves_timelikeFuture,
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.coshSinhBoost_preserves_timelikeFuture,
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.spacelike_chsh_noSignaling_frame_covariant ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.boostBy_preserves_lorentzianForm,
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.boostBy_preserves_spacelike,
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.boostBy_preserves_timelike,
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.spacelike_exists_simultaneity_frame,
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.boostBy_preserves_timelikeFuture,
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.coshSinhBoost_preserves_timelikeFuture,
  Physlib.QuantumMechanics.ComplexAction.Bell.SpacelikeBoostNoSignaling.spacelike_chsh_noSignaling_frame_covariant ]
