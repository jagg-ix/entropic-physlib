/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.CauchyWeakLimit

/-!
# Finite broadened hybridization families

This file lifts the single-level Cauchy weak limit to a finite weighted family.
For every bounded continuous complex test function, the weighted sum of
integrals against broadened level laws converges to the corresponding weighted
sum of evaluations at sharp level energies.

This is the fixed-discretization version of the hybridization replacement in
Schwarz et al. The separate grid-refinement limit determines whether the sharp
weighted levels approximate a prescribed continuum spectral measure.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace LindbladDrivenLeads

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction Topology

/-- Probability law of one affine Cauchy-broadened level. -/
def affineCauchyLaw (epsilon gamma : ℝ) : ProbabilityMeasure ℝ :=
  ⟨standardCauchyMeasure.map (affineCauchySample epsilon gamma),
    Measure.isProbabilityMeasure_map
      (measurable_affineCauchySample epsilon gamma).aemeasurable⟩

/-- Sharp probability law concentrated at one level energy. -/
def sharpLevelLaw (epsilon : ℝ) : ProbabilityMeasure ℝ :=
  ⟨Measure.dirac epsilon, inferInstance⟩

/-- The affine-law wrapper agrees with the law used by the weak-limit theorem. -/
theorem affineCauchyLaw_tendsto_sharp (epsilon : ℝ) {gamma : ℕ → ℝ}
    (hgamma : Tendsto gamma atTop (𝓝 0)) :
    Tendsto (fun n => affineCauchyLaw epsilon (gamma n)) atTop
      (𝓝 (sharpLevelLaw epsilon)) := by
  simpa [affineCauchyLaw, sharpLevelLaw] using
    affineCauchyLaw_tendsto_dirac epsilon hgamma

/-- Weak convergence of one broadened level implies convergence of every
bounded continuous complex test integral to evaluation at the level energy. -/
theorem integral_affineCauchyLaw_tendsto (epsilon : ℝ) {gamma : ℕ → ℝ}
    (hgamma : Tendsto gamma atTop (𝓝 0)) (test : ℝ →ᵇ ℂ) :
    Tendsto
      (fun n => ∫ omega, test omega ∂(affineCauchyLaw epsilon (gamma n) : Measure ℝ))
      atTop
      (𝓝 (test epsilon)) := by
  have hmeasure := affineCauchyLaw_tendsto_sharp epsilon hgamma
  have htest :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
      hmeasure test
  simpa [sharpLevelLaw] using htest

/-- Weighted spectral observable for a finite family of broadened lead levels. -/
def finiteBroadenedObservable {Q : Type*} [Fintype Q]
    (weight : Q → ℂ) (epsilon : Q → ℝ) (gamma : ℕ → Q → ℝ)
    (test : ℝ →ᵇ ℂ) (n : ℕ) : ℂ :=
  ∑ q, weight q *
    ∫ omega, test omega ∂(affineCauchyLaw (epsilon q) (gamma n q) : Measure ℝ)

/-- Sharp-level observable obtained after sending every width to zero. -/
def finiteSharpObservable {Q : Type*} [Fintype Q]
    (weight : Q → ℂ) (epsilon : Q → ℝ) (test : ℝ →ᵇ ℂ) : ℂ :=
  ∑ q, weight q * test (epsilon q)

/-- A finite weighted family of broadened levels converges, against every
bounded continuous complex test function, to the corresponding sharp family. -/
theorem finiteBroadenedObservable_tendsto_sharp
    {Q : Type*} [Fintype Q] (weight : Q → ℂ) (epsilon : Q → ℝ)
    (gamma : ℕ → Q → ℝ) (hgamma : ∀ q, Tendsto (fun n => gamma n q) atTop (𝓝 0))
    (test : ℝ →ᵇ ℂ) :
    Tendsto (finiteBroadenedObservable weight epsilon gamma test) atTop
      (𝓝 (finiteSharpObservable weight epsilon test)) := by
  unfold finiteBroadenedObservable finiteSharpObservable
  apply tendsto_finset_sum
  intro q hq
  exact tendsto_const_nhds.mul
    (integral_affineCauchyLaw_tendsto (epsilon q) (hgamma q) test)

end LindbladDrivenLeads
end QuantumMechanics
