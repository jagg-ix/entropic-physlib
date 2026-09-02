/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.Basic
public import Mathlib.Probability.Distributions.Cauchy

/-!
# Cauchy realization of LDDL level broadening

The normalized Lorentz function used for broadened discretized lead levels in
Schwarz et al. is exactly the real Cauchy probability density. This file links
the LDDL definitions to Mathlib's existing Cauchy-distribution API and inherits
its measurability, integrability, positivity, and unit-integral theorem.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace LindbladDrivenLeads

open scoped NNReal

/-- The positive driving rate as an `NNReal` Cauchy scale. -/
def RateData.gammaNNReal (r : RateData) : ℝ≥0 :=
  ⟨r.gamma, r.gamma_pos.le⟩

/-- The normalized broadened level as Mathlib's Cauchy density. -/
def cauchyLorentzian (r : RateData) (epsilon omega : ℝ) : ℝ :=
  ProbabilityTheory.cauchyPDFReal epsilon r.gammaNNReal omega

/-- The Cauchy density is the same normalized Lorentzian introduced in the
LDDL module. -/
theorem cauchyLorentzian_eq_lorentzian (r : RateData) (epsilon omega : ℝ) :
    cauchyLorentzian r epsilon omega = lorentzian r.gamma epsilon omega := by
  rw [cauchyLorentzian, ProbabilityTheory.cauchyPDFReal_def, lorentzian, lorentzPeak]
  change Real.pi⁻¹ * r.gamma * ((omega - epsilon) ^ 2 + r.gamma ^ 2)⁻¹ =
    r.gamma / ((omega - epsilon) ^ 2 + r.gamma ^ 2) / Real.pi
  field_simp [Real.pi_ne_zero, (greenDenominator_pos r epsilon omega).ne']

/-- The normalized broadened level is strictly positive at every energy. -/
theorem cauchyLorentzian_pos (r : RateData) (epsilon omega : ℝ) :
    0 < cauchyLorentzian r epsilon omega := by
  apply ProbabilityTheory.cauchyPDF_pos
  intro h
  have hcoe := congrArg Subtype.val h
  change r.gamma = 0 at hcoe
  exact r.gamma_pos.ne' hcoe

/-- The normalized broadened level is measurable. -/
theorem measurable_cauchyLorentzian (r : RateData) (epsilon : ℝ) :
    Measurable (cauchyLorentzian r epsilon) := by
  exact ProbabilityTheory.measurable_cauchyPDFReal epsilon r.gammaNNReal

/-- The normalized broadened level is integrable. -/
theorem integrable_cauchyLorentzian (r : RateData) (epsilon : ℝ) :
    MeasureTheory.Integrable (cauchyLorentzian r epsilon) := by
  exact ProbabilityTheory.integrable_cauchyPDFReal epsilon

/-- Equation (34)'s Lorentzian has total spectral weight one. -/
theorem integral_cauchyLorentzian_eq_one (r : RateData) (epsilon : ℝ) :
    ∫ omega, cauchyLorentzian r epsilon omega = 1 := by
  apply ProbabilityTheory.integral_cauchyPDFReal_eq_one
  intro h
  have hcoe := congrArg Subtype.val h
  change r.gamma = 0 at hcoe
  exact r.gamma_pos.ne' hcoe

/-- The original LDDL Lorentzian definition therefore also integrates to one. -/
theorem integral_lorentzian_eq_one (r : RateData) (epsilon : ℝ) :
    ∫ omega, lorentzian r.gamma epsilon omega = 1 := by
  rw [← integral_cauchyLorentzian_eq_one r epsilon]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with omega
  exact (cauchyLorentzian_eq_lorentzian r epsilon omega).symm

end LindbladDrivenLeads
end QuantumMechanics
