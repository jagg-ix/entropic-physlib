/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.CyclicVectorRigidity
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of cyclic-vector rigidity

This leaf module checks declaration reachability and applies the repository's
axiom/non-vacuity gates to the derived coordinate and iterate theorems.  The
constructor `toStandardConjugacy` is checked as the produced witness; the audit
does not relabel the separate simple-spectrum-to-cyclic-basis existence problem.
-/

open Physlib.QuantumMechanics.CyclicVectorRigidity

#check Physlib.QuantumMechanics.Conjugacy.UnitaryConjugacy
#check Physlib.QuantumMechanics.Conjugacy.UnitaryConjugacy.trans
#check Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis
#check Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis.toStandardConjugacy
#check Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis.conjugacyBetween

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.Conjugacy.UnitaryConjugacy.conjugation_apply,
  Physlib.QuantumMechanics.Conjugacy.UnitaryConjugacy.intertwines_iterate,
  Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis.coordinates_step_apply,
  Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis.coordinates_intertwine,
  Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis.coordinates_iterate,
  Physlib.QuantumMechanics.CyclicVectorRigidity.standardCyclicOrbitBasis,
  Physlib.QuantumMechanics.CyclicVectorRigidity.shiftStateStep_conjugate_cyclicStateStep,
  Physlib.QuantumMechanics.CyclicVectorRigidity.inner_fourierOrbitVector,
  Physlib.QuantumMechanics.CyclicVectorRigidity.step_fourierOrbitVector,
  Physlib.QuantumMechanics.CyclicVectorRigidity.fourierOrbitVector_orthogonal_eq_bot,
  Physlib.QuantumMechanics.CyclicVectorRigidity.cyclicOrbitBasisOfCharacterEigenbasis,
  Physlib.QuantumMechanics.CyclicVectorRigidity.gnsForm_vectorState,
  Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis.basis_eq_stepCLM_pow,
  Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis.gnsForm_vectorState_stepPow,
  Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis.gnsForm_presentation_invariant,
  Physlib.QuantumMechanics.CyclicVectorRigidity.sum_characterProjector,
  Physlib.QuantumMechanics.CyclicVectorRigidity.isometryCLM_mul_characterProjector,
  Physlib.QuantumMechanics.CyclicVectorRigidity.characterProjector_eigen,
  Physlib.QuantumMechanics.CyclicVectorRigidity.stdAddChar_ne_one,
  Physlib.QuantumMechanics.CyclicVectorRigidity.eigenvector_orthogonal,
  Physlib.QuantumMechanics.CyclicVectorRigidity.spectralComponent_orthonormal,
  Physlib.QuantumMechanics.CyclicVectorRigidity.spectralComponent_orthogonal_eq_bot,
  Physlib.QuantumMechanics.CyclicVectorRigidity.cyclicOrbitBasisOfSpectralComponents ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis.coordinates_step_apply,
  Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis.coordinates_intertwine,
  Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis.coordinates_iterate,
  Physlib.QuantumMechanics.CyclicVectorRigidity.standardCyclicOrbitBasis,
  Physlib.QuantumMechanics.CyclicVectorRigidity.shiftStateStep_conjugate_cyclicStateStep,
  Physlib.QuantumMechanics.CyclicVectorRigidity.inner_fourierOrbitVector,
  Physlib.QuantumMechanics.CyclicVectorRigidity.step_fourierOrbitVector,
  Physlib.QuantumMechanics.CyclicVectorRigidity.fourierOrbitVector_orthogonal_eq_bot,
  Physlib.QuantumMechanics.CyclicVectorRigidity.cyclicOrbitBasisOfCharacterEigenbasis,
  Physlib.QuantumMechanics.CyclicVectorRigidity.gnsForm_vectorState,
  Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis.basis_eq_stepCLM_pow,
  Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis.gnsForm_vectorState_stepPow,
  Physlib.QuantumMechanics.CyclicVectorRigidity.CyclicOrbitBasis.gnsForm_presentation_invariant,
  Physlib.QuantumMechanics.CyclicVectorRigidity.sum_characterProjector,
  Physlib.QuantumMechanics.CyclicVectorRigidity.isometryCLM_mul_characterProjector,
  Physlib.QuantumMechanics.CyclicVectorRigidity.characterProjector_eigen,
  Physlib.QuantumMechanics.CyclicVectorRigidity.stdAddChar_ne_one,
  Physlib.QuantumMechanics.CyclicVectorRigidity.eigenvector_orthogonal,
  Physlib.QuantumMechanics.CyclicVectorRigidity.spectralComponent_orthonormal,
  Physlib.QuantumMechanics.CyclicVectorRigidity.spectralComponent_orthogonal_eq_bot,
  Physlib.QuantumMechanics.CyclicVectorRigidity.cyclicOrbitBasisOfSpectralComponents ]
