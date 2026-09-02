/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.RelationalTime.CausalEventHistory
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of deterministic causal histories

Kernel and non-vacuity checks for execution uniqueness, scheduling invariance,
finite causal confluence, minimal causal depth, and normalized-clock uniqueness.
-/

open Physlib.QuantumMechanics.RelationalTime.CausalEventHistory

#check @CausalEventSystem
#check @CausalEventSystem.IndependentSwaps
#check @CausalEventSystem.NormalizedCausalClock

#physlib_axiom_clean_all [
  CausalEventSystem.executes_unique,
  CausalEventSystem.run_eq_of_independentSwaps,
  CausalEventSystem.independentSwaps_of_perm_causalLinearizations,
  CausalEventSystem.run_eq_of_perm_causalLinearizations,
  CausalEventSystem.causalDepth_minimal,
  CausalEventSystem.NormalizedCausalClock.eq_causalDepth ]

#physlib_non_vacuous_all [
  CausalEventSystem.executes_unique,
  CausalEventSystem.run_eq_of_independentSwaps,
  CausalEventSystem.independentSwaps_of_perm_causalLinearizations,
  CausalEventSystem.run_eq_of_perm_causalLinearizations,
  CausalEventSystem.causalDepth_minimal,
  CausalEventSystem.NormalizedCausalClock.eq_causalDepth ]
