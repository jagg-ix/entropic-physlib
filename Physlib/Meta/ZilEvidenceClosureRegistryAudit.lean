/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Meta.AxiomWhitelistCheck
public import Physlib.Meta.ZilEvidenceClosureRegistry

open Physlib.Meta.ZilEvidenceClosureRegistry
open Physlib.QuantumMechanics.Schrodinger.EuclideanSobolevFrequencyLocalization
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NewtonianInteractionEnergy
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.SelfBoundSchrodingerNewtonPDE

/-!
# ZIL evidence registry audit

The Boolean registry invariants prevent lifecycle drift. The theorem lists below
tie the registry's closed CAT/EPT claims to actual Lean declarations and subject
them to the repository's axiom-clean and non-vacuity checks.
-/

#physlib_axiom_clean_all [
  newtonianSelfEnergy_tendsto_of_lsixFifths,
  hOneAttractiveNewtonInteraction_tendsto_of_lsixFifths,
  hOne_tendsto_of_minimizing_energySplit,
  hOneLTwoNormalized_of_tendsto,
  bounded_normalized_hOne_firstMoment_has_energyMinimizer,
  isCompact_hOneBorn_energyMinimizers_of_interactionClosure,
  exists_hOneBorn_minimizingOrbit_uniformlyStable,
  registry_ids_nodup,
  implemented_records_have_witness,
  rejected_claims_have_resolution,
  open_obligations_have_no_proof_witness,
  required_closure_coverage ]

#physlib_non_vacuous_all [
  newtonianSelfEnergy_tendsto_of_lsixFifths,
  hOneAttractiveNewtonInteraction_tendsto_of_lsixFifths,
  hOne_tendsto_of_minimizing_energySplit,
  hOneLTwoNormalized_of_tendsto,
  bounded_normalized_hOne_firstMoment_has_energyMinimizer,
  isCompact_hOneBorn_energyMinimizers_of_interactionClosure,
  exists_hOneBorn_minimizingOrbit_uniformlyStable,
  registry_ids_nodup ]
