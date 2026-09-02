/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OhmicMicroscopicRate
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit for the finite-Ohmic origin of the one-level LDDL rate

The audited surface includes the exact coupling-law inversion, the constructed
`RateData`, the finite bath renormalization cancellation, Lorentzian half-width,
coherence-width growth, and the inherited binary-KL production coefficient.
-/

#physlib_axiom_clean_all
  [QuantumMechanics.LindbladDrivenLeads.gammaFromOhmicCoupling_couplingSq,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.couplingSq_derivedGamma,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.relaxationCoefficient_eq_coupling,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.occupationVectorField_eq_microscopic,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.renormalizationShift_eq_closed,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.lorentzPeak_at_halfWidth,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.lorentzianFWHM_eq_coupling,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.gammaOffdiagLinear_eq_coupling]

#physlib_non_vacuous_all
  [QuantumMechanics.LindbladDrivenLeads.gammaFromOhmicCoupling_couplingSq,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.couplingSq_derivedGamma,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.relaxationCoefficient_eq_coupling,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.occupationVectorField_eq_microscopic,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.renormalizationShift_eq_closed,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.lorentzPeak_at_halfWidth,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.lorentzianFWHM_eq_coupling,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.gammaOffdiagLinear_eq_coupling]
