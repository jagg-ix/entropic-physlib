/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.FiniteMarkovEntropyProductionStrict
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the strict finite-Markov entropy-production arrow

Gates the Schnakenberg symmetrization, nonnegativity, and the strict
entropy-production law (positive unless detailed balance) beyond the binary carrier.
-/

open Physlib.Thermodynamics.KullbackLeiblerInformationGain

#physlib_axiom_clean_all [
  Physlib.Thermodynamics.KullbackLeiblerInformationGain.markovEntropyProduction_forward_form,
  Physlib.Thermodynamics.KullbackLeiblerInformationGain.markovEntropyProduction_symmetrized,
  Physlib.Thermodynamics.KullbackLeiblerInformationGain.markovEntropyProduction_nonneg,
  Physlib.Thermodynamics.KullbackLeiblerInformationGain.markovEntropyProduction_pos_of_not_detailedBalance ]

#physlib_non_vacuous_all [
  Physlib.Thermodynamics.KullbackLeiblerInformationGain.markovEntropyProduction_symmetrized,
  Physlib.Thermodynamics.KullbackLeiblerInformationGain.markovEntropyProduction_nonneg,
  Physlib.Thermodynamics.KullbackLeiblerInformationGain.markovEntropyProduction_pos_of_not_detailedBalance ]
