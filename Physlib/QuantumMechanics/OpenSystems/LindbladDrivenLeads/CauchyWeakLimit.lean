/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.CauchyBroadening
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Weak zero-width limit of Cauchy broadening

The finite-width Lorentzian used in Lindblad-driven discretized leads is a
Cauchy density. This file formalizes the zero-width limit through the existing
convergence-in-distribution API: an affine Cauchy sample
`x ↦ ε + γ x` converges almost surely to the constant `ε` when `γ → 0`, so its
law converges weakly to the Dirac law at `ε`.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace LindbladDrivenLeads

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- Standard Cauchy probability measure, used as the reference law for all
location-scale broadenings. -/
def standardCauchyMeasure : Measure ℝ :=
  ProbabilityTheory.cauchyMeasure 0 1

instance : IsProbabilityMeasure standardCauchyMeasure := by
  unfold standardCauchyMeasure
  infer_instance

/-- Affine realization of a broadened level with center `epsilon` and width
`gamma`. -/
def affineCauchySample (epsilon gamma x : ℝ) : ℝ :=
  epsilon + gamma * x

/-- Affine Cauchy samples are measurable functions of the reference sample. -/
theorem measurable_affineCauchySample (epsilon gamma : ℝ) :
    Measurable (affineCauchySample epsilon gamma) := by
  change Measurable (fun x : ℝ => epsilon + gamma * x)
  fun_prop

/-- If the width tends to zero, affine Cauchy samples converge almost surely
to the constant level energy. -/
theorem affineCauchySample_ae_tendsto (epsilon : ℝ) {gamma : ℕ → ℝ}
    (hgamma : Tendsto gamma atTop (𝓝 0)) :
    ∀ᵐ x ∂standardCauchyMeasure,
      Tendsto (fun n => affineCauchySample epsilon (gamma n) x) atTop
        (𝓝 epsilon) := by
  filter_upwards with x
  simpa [affineCauchySample] using
    tendsto_const_nhds.add (hgamma.mul_const x)

/-- The zero-width affine Cauchy family converges in distribution to the
constant level energy. -/
theorem affineCauchySample_tendstoInDistribution (epsilon : ℝ)
    {gamma : ℕ → ℝ} (hgamma : Tendsto gamma atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n => affineCauchySample epsilon (gamma n))
      atTop
      (fun _ : ℝ => epsilon)
      (fun _ => standardCauchyMeasure)
      standardCauchyMeasure := by
  apply tendstoInDistribution_of_ae_tendsto
  · intro n
    exact (measurable_affineCauchySample epsilon (gamma n)).aemeasurable
  · exact measurable_const.aemeasurable
  · exact affineCauchySample_ae_tendsto epsilon hgamma

/-- The probability laws of the broadened levels converge weakly to the law of
the constant level. -/
theorem affineCauchyLaw_tendsto (epsilon : ℝ) {gamma : ℕ → ℝ}
    (hgamma : Tendsto gamma atTop (𝓝 0)) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n =>
        ⟨standardCauchyMeasure.map
          (affineCauchySample epsilon (gamma n)),
          Measure.isProbabilityMeasure_map
            (measurable_affineCauchySample epsilon (gamma n)).aemeasurable⟩)
      atTop
      (𝓝
        ⟨standardCauchyMeasure.map (fun _ : ℝ => epsilon),
          Measure.isProbabilityMeasure_map measurable_const.aemeasurable⟩) :=
  (affineCauchySample_tendstoInDistribution epsilon hgamma).tendsto

/-- The law of the constant level under the standard Cauchy probability space
is the Dirac measure at that level. -/
theorem standardCauchyMeasure_map_const (epsilon : ℝ) :
    standardCauchyMeasure.map (fun _ : ℝ => epsilon) =
      Measure.dirac epsilon := by
  simp [standardCauchyMeasure]

/-- Therefore the broadened Cauchy laws converge weakly to the Dirac law at the
level energy. -/
theorem affineCauchyLaw_tendsto_dirac (epsilon : ℝ) {gamma : ℕ → ℝ}
    (hgamma : Tendsto gamma atTop (𝓝 0)) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n =>
        ⟨standardCauchyMeasure.map
          (affineCauchySample epsilon (gamma n)),
          Measure.isProbabilityMeasure_map
            (measurable_affineCauchySample epsilon (gamma n)).aemeasurable⟩)
      atTop
      (𝓝 ⟨Measure.dirac epsilon, inferInstance⟩) := by
  simpa [standardCauchyMeasure_map_const] using
    affineCauchyLaw_tendsto epsilon hgamma

end LindbladDrivenLeads
end QuantumMechanics
