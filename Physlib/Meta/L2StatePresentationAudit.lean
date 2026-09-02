/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.L2StatePresentation
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of state presentations and proved bridges

Applies the axiom and non-vacuity gates to the presentation-bridge abstraction
and its `ℓ²`/`Ket` equivalence instance; the formalization-lint gate runs in the
module itself.
-/

open Physlib.QuantumMechanics.L2StatePresentation

#check @Physlib.QuantumMechanics.L2StatePresentation.StatePresentationBridge
#check @Physlib.QuantumMechanics.L2StatePresentation.l2KetEquiv
#check @Physlib.QuantumMechanics.L2StatePresentation.PointedDynamicalPresentation.exists_unique_minimal_equiv

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.L2StatePresentation.StatePresentationBridge.born_eq,
  Physlib.QuantumMechanics.L2StatePresentation.StatePresentationBridge.totalCorrelation_eq,
  Physlib.QuantumMechanics.L2StatePresentation.normalizedL2Presentation,
  Physlib.QuantumMechanics.L2StatePresentation.ketPresentation,
  Physlib.QuantumMechanics.L2StatePresentation.l2KetEquiv,
  Physlib.QuantumMechanics.L2StatePresentation.dynamicalL2Presentation,
  Physlib.QuantumMechanics.L2StatePresentation.dynamicalKetPresentation,
  Physlib.QuantumMechanics.L2StatePresentation.l2KetNaturalBridge,
  Physlib.QuantumMechanics.L2StatePresentation.PointedNaturalEquiv.toEquiv_unique,
  Physlib.QuantumMechanics.L2StatePresentation.PointedDynamicalPresentation.exists_unique_minimal_equiv ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.L2StatePresentation.StatePresentationBridge.totalCorrelation_eq,
  Physlib.QuantumMechanics.L2StatePresentation.PointedNaturalEquiv.toEquiv_unique,
  Physlib.QuantumMechanics.L2StatePresentation.PointedDynamicalPresentation.exists_unique_minimal_equiv ]
