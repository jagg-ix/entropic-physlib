/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Meta.AxiomWhitelistCheck
public import Physlib.QFT.PerturbationTheory.FieldStatistics.PauliExchange
public import Physlib.Electromagnetism.Vacuum.HarmonicWaveCertificate
public import Physlib.Mathematics.HarmonicAnalysis.FiniteSpectralHeatFlow

open Physlib.QFT.PerturbationTheory.FieldStatistics.PauliExchange
open Physlib.Mathematics.HarmonicAnalysis.FiniteSpectralHeatFlow
open Electromagnetism.ElectromagneticPotential

/-!
# M9 criterion-reduction audit

Registers the three theorem surfaces that permit criterion-scoped OpenWave
promotion without claiming particle identity, photon quantization, microscopic
thermodynamics, calibration, or external validation.
-/

#physlib_axiom_clean_all [
  antisymmetrize_swap,
  antisymmetrize_self,
  fermionic_exchange_involution,
  harmonicWaveX_maxwell_planeWave,
  harmonicWaveX_transverse_electric_component,
  flow_zero,
  flow_add,
  flow_zero_diffusivity,
  flow_preserves_zero_mode ]

#physlib_non_vacuous_all [
  antisymmetrize_swap,
  antisymmetrize_self,
  fermionic_exchange_involution,
  harmonicWaveX_maxwell_planeWave,
  harmonicWaveX_transverse_electric_component,
  flow_zero,
  flow_add,
  flow_zero_diffusivity,
  flow_preserves_zero_mode ]
