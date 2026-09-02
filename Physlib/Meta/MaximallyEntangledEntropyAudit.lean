/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.Entanglement.MaximallyEntangledEntropy
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the maximally entangled / Bell-singlet entropy composition

Applies the axiom and non-vacuity gates to the reusable entropy-composition core,
its maximally entangled instance, and the explicit Bell singlet density matrix
`|Ψ⁻⟩⟨Ψ⁻|` with mutual information `2 log 2`.
-/

open Physlib.QuantumMechanics.Entanglement

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.Entanglement.Sᵥₙ_uniform,
  Physlib.QuantumMechanics.Entanglement.entropy_composition_of_traceRight_uniform,
  Physlib.QuantumMechanics.Entanglement.MES_entropy_composition,
  Physlib.QuantumMechanics.Entanglement.MES_isEntangled,
  Physlib.QuantumMechanics.Entanglement.bellSinglet_entropy_composition,
  Physlib.QuantumMechanics.Entanglement.bellSinglet_qMutualInfo,
  Physlib.QuantumMechanics.Entanglement.bellSinglet_reducedEntropy_pos ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.Entanglement.entropy_composition_of_traceRight_uniform,
  Physlib.QuantumMechanics.Entanglement.MES_entropy_composition,
  Physlib.QuantumMechanics.Entanglement.bellSinglet_entropy_composition,
  Physlib.QuantumMechanics.Entanglement.bellSinglet_reducedEntropy_pos ]
