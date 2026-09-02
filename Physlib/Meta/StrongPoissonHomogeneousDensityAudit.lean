/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.GeneralDensityRadialPoisson
public import Physlib.Meta.AxiomWhitelistCheck

/-! # Audit of the strong-form homogeneous-density Poisson equation -/

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.StrongPoissonHomogeneousDensity

#physlib_axiom_clean_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.StrongPoissonHomogeneousDensity.laplacian_const_mul_norm_sq,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.StrongPoissonHomogeneousDensity.strongPoisson_homogeneousDensity ]

#physlib_non_vacuous_all [
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.StrongPoissonHomogeneousDensity.laplacian_const_mul_norm_sq,
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.StrongPoissonHomogeneousDensity.strongPoisson_homogeneousDensity ]
