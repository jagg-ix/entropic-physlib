/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.GluonFieldStrengthBianchi
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the gluon field strength and Bianchi identity -/

open Physlib.QuantumMechanics.ComplexAction.Particles.GluonFieldStrengthBianchi

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Particles.GluonFieldStrengthBianchi.gluonFieldStrength_antisymm,
  Physlib.QuantumMechanics.ComplexAction.Particles.GluonFieldStrengthBianchi.gluonFieldStrength_abelian,
  Physlib.QuantumMechanics.ComplexAction.Particles.GluonFieldStrengthBianchi.abelianGluon_homogeneous_maxwell ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Particles.GluonFieldStrengthBianchi.gluonFieldStrength_antisymm,
  Physlib.QuantumMechanics.ComplexAction.Particles.GluonFieldStrengthBianchi.gluonFieldStrength_abelian,
  Physlib.QuantumMechanics.ComplexAction.Particles.GluonFieldStrengthBianchi.abelianGluon_homogeneous_maxwell ]
