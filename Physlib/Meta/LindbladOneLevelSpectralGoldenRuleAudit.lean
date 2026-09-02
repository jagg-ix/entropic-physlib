/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OhmicMicroscopicRate
public import Physlib.Meta.AxiomWhitelistCheck

/-!
# Audit for the on-shell spectral golden-rule rate bridge

The audited surface covers the thermal occupation algebra, loss/gain and total
rates, detailed balance, the occupation vector field, linewidth, and the exact
agreement between the finite-Ohmic and effective on-shell parameterizations.
-/

#physlib_axiom_clean_all
  [QuantumMechanics.LindbladDrivenLeads.fermiOccupation_eq_exp_neg_mul_complement,
   QuantumMechanics.LindbladDrivenLeads.OnShellSpectralBathData.lossRate_eq_goldenRule,
   QuantumMechanics.LindbladDrivenLeads.OnShellSpectralBathData.gainRate_eq_goldenRule,
   QuantumMechanics.LindbladDrivenLeads.OnShellSpectralBathData.totalRate_eq_goldenRule,
   QuantumMechanics.LindbladDrivenLeads.OnShellSpectralBathData.occupationVectorField_eq_goldenRule,
   QuantumMechanics.LindbladDrivenLeads.OnShellSpectralBathData.lorentzianFWHM_eq_goldenRule,
   QuantumMechanics.LindbladDrivenLeads.ThermalSpectralBathData.gainRate_eq_exp_neg_mul_lossRate,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.goldenRuleGamma_eq_derivedGamma,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.occupationVectorField_eq_spectralOhmic,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.spectralFWHM_eq_ohmicFWHM]

#physlib_non_vacuous_all
  [QuantumMechanics.LindbladDrivenLeads.fermiOccupation_eq_exp_neg_mul_complement,
   QuantumMechanics.LindbladDrivenLeads.OnShellSpectralBathData.totalRate_eq_goldenRule,
   QuantumMechanics.LindbladDrivenLeads.OnShellSpectralBathData.occupationVectorField_eq_goldenRule,
   QuantumMechanics.LindbladDrivenLeads.OnShellSpectralBathData.lorentzianFWHM_eq_goldenRule,
   QuantumMechanics.LindbladDrivenLeads.ThermalSpectralBathData.gainRate_eq_exp_neg_mul_lossRate,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.goldenRuleGamma_eq_derivedGamma,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.occupationVectorField_eq_spectralOhmic,
   QuantumMechanics.LindbladDrivenLeads.FiniteOhmicBathRateData.spectralFWHM_eq_ohmicFWHM]
