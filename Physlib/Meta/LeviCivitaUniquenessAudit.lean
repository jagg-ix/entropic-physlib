/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the Levi-Civita uniqueness and constant-rescaling invariance
-/

open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness.christoffel_unique_of_torsionFree_metricCompatible,
  Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness.christoffelFromMetric_const_rescale_invariant ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness.christoffel_unique_of_torsionFree_metricCompatible,
  Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaUniqueness.christoffelFromMetric_const_rescale_invariant ]
