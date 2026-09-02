/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.RelationalTime.UnifiedRelationalDissipativeCarrier
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of the unified constrained system–clock–bath carrier

Applies the axiom and non-vacuity gates to the two-limit reductions of the
unified carrier: the reversible Page–Wootters (`𝓛 = 0`) conditional evolution,
the strict relaxation to a unique Gibbs equilibrium, their joint statement, and
the nonzero constrained one-level inhabitant.  It also gates the Gaussian
continuum collision-bath capstone joining Davies-scale unitary reduction, the
`C₀` GKSL generator, linewidth, relaxation time and exact KL production.
-/

open Physlib.QuantumMechanics.RelationalTime
open Physlib.QuantumMechanics.RelationalTime.UnifiedRelationalDissipativeCarrier

#check @Physlib.QuantumMechanics.RelationalTime.UnifiedRelationalDissipativeCarrier
#check @Physlib.QuantumMechanics.RelationalTime.unifiedCarrierOfOneLevel
#check @Physlib.QuantumMechanics.RelationalTime.unifiedCarrierOfDissipativeOneLevel
#check @Physlib.QuantumMechanics.RelationalTime.unifiedCarrierOfGaussianBath

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.RelationalTime.UnifiedRelationalDissipativeCarrier.morevaLimit_unitaryConditional,
  Physlib.QuantumMechanics.RelationalTime.UnifiedRelationalDissipativeCarrier.morevaLimit_entropyPreserving,
  Physlib.QuantumMechanics.RelationalTime.UnifiedRelationalDissipativeCarrier.kl_contracts_to_gibbs,
  Physlib.QuantumMechanics.RelationalTime.UnifiedRelationalDissipativeCarrier.quantumDotLimit_uniqueEquilibrium,
  Physlib.QuantumMechanics.RelationalTime.UnifiedRelationalDissipativeCarrier.entropicProduction_nonneg,
  Physlib.QuantumMechanics.RelationalTime.UnifiedRelationalDissipativeCarrier.reduces_to_both_limits,
  Physlib.QuantumMechanics.RelationalTime.unifiedCarrierOfOneLevel_strictArrow,
  Physlib.QuantumMechanics.RelationalTime.unifiedCarrierOfDissipativeOneLevel_nontrivial_gksl,
  Physlib.QuantumMechanics.RelationalTime.gaussianBath_davies_relational_linewidth_KL_capstone ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.RelationalTime.UnifiedRelationalDissipativeCarrier.kl_contracts_to_gibbs,
  Physlib.QuantumMechanics.RelationalTime.UnifiedRelationalDissipativeCarrier.quantumDotLimit_uniqueEquilibrium,
  Physlib.QuantumMechanics.RelationalTime.UnifiedRelationalDissipativeCarrier.reduces_to_both_limits,
  Physlib.QuantumMechanics.RelationalTime.unifiedCarrierOfDissipativeOneLevel_nontrivial_gksl,
  Physlib.QuantumMechanics.RelationalTime.gaussianBath_davies_relational_linewidth_KL_capstone ]
