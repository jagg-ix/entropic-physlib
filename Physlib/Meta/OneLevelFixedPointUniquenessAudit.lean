/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelChannelStrictArrow
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit of strictly-contracting fixed-point uniqueness

The generic uniqueness of a strictly-relative-entropy-contracting channel's fixed
point, and the one-level stationary-state instantiation.
-/

#check @QuantumMechanics.LindbladDrivenLeads.fixedPoint_unique_of_strict_qRelativeEnt

#physlib_axiom_clean_all [
  QuantumMechanics.LindbladDrivenLeads.fixedPoint_unique_of_strict_qRelativeEnt,
  QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_fixedPoint_unique ]

#physlib_non_vacuous_all [
  QuantumMechanics.LindbladDrivenLeads.fixedPoint_unique_of_strict_qRelativeEnt,
  QuantumMechanics.LindbladDrivenLeads.oneLevelChannel_fixedPoint_unique ]
