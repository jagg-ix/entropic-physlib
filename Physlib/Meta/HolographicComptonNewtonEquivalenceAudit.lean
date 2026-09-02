/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.SourcedTTWaveComptonCoupling
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the holographic-Compton Newton-constant equivalence -/

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HolographicComptonNewtonEquivalence

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HolographicComptonNewtonEquivalence.newtonG_holographic_eq_comptonNewton,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HolographicComptonNewtonEquivalence.comptonSpatialNewtonG_dim ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HolographicComptonNewtonEquivalence.newtonG_holographic_eq_comptonNewton,
  Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.HolographicComptonNewtonEquivalence.comptonSpatialNewtonG_dim ]
