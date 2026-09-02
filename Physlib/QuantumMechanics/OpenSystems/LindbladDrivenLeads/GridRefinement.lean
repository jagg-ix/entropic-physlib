/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.FiniteHybridization
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Spectral-grid refinement for Lindblad-driven leads

A discretized lead is represented by a probability mass function on a type of
level labels together with a measurable energy map. Pushing the PMF measure
forward along the energy map gives the sharp spectral-grid probability law.

The main theorem states that weak convergence of these native grid laws to a
continuum spectral law implies convergence of every bounded-continuous complex
spectral observable. For finite grids, the observable integral is exactly the
PMF-weighted finite sum.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace LindbladDrivenLeads

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction Topology

/-- A normalized discrete spectral grid: probability weights on level labels
and a measurable map assigning each label its energy. -/
structure SpectralGrid (Q : Type*) [MeasurableSpace Q] where
  /-- Normalized weights of the discrete lead levels. -/
  weights : PMF Q
  /-- Energy represented by each level label. -/
  energy : Q → ℝ
  /-- Measurability of the energy map. -/
  measurable_energy : Measurable energy

/-- Sharp spectral law obtained by pushing the PMF measure to energy space. -/
def SpectralGrid.law {Q : Type*} [MeasurableSpace Q]
    (grid : SpectralGrid Q) : ProbabilityMeasure ℝ :=
  ⟨grid.weights.toMeasure.map grid.energy,
    Measure.isProbabilityMeasure_map grid.measurable_energy.aemeasurable⟩

/-- A bounded-continuous complex observable evaluated on a sharp spectral
grid. -/
def SpectralGrid.observable {Q : Type*} [MeasurableSpace Q]
    (grid : SpectralGrid Q) (test : ℝ →ᵇ ℂ) : ℂ :=
  ∫ omega, test omega ∂(grid.law : Measure ℝ)

/-- On a finite grid, the spectral observable is exactly the PMF-weighted sum
of the test function evaluated at the level energies. -/
theorem SpectralGrid.observable_eq_sum {Q : Type*} [Fintype Q]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (grid : SpectralGrid Q) (test : ℝ →ᵇ ℂ) :
    grid.observable test =
      ∑ q, (grid.weights q).toReal • test (grid.energy q) := by
  change (∫ omega, test omega ∂(grid.weights.toMeasure.map grid.energy)) = _
  rw [integral_map grid.measurable_energy.aemeasurable
    test.continuous.aestronglyMeasurable]
  exact PMF.integral_eq_sum grid.weights (fun q => test (grid.energy q))

/-- Weak convergence of sharp spectral-grid laws is precisely sufficient for
convergence of every bounded-continuous complex spectral observable. -/
theorem spectralGridObservable_tendsto_continuum
    {Q : Type*} [MeasurableSpace Q] (grids : ℕ → SpectralGrid Q)
    (continuum : ProbabilityMeasure ℝ)
    (hgrid : Tendsto (fun n => (grids n).law) atTop (𝓝 continuum))
    (test : ℝ →ᵇ ℂ) :
    Tendsto (fun n => (grids n).observable test) atTop
      (𝓝 (∫ omega, test omega ∂(continuum : Measure ℝ))) := by
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
    hgrid test

/-- Pointwise formulation of grid refinement: if every bounded-continuous
complex test integral converges, then the pushed-forward PMF laws converge
weakly to the continuum spectral law. -/
theorem spectralGridLaw_tendsto_of_observables
    {Q : Type*} [MeasurableSpace Q] (grids : ℕ → SpectralGrid Q)
    (continuum : ProbabilityMeasure ℝ)
    (hobs : ∀ test : ℝ →ᵇ ℂ,
      Tendsto (fun n => (grids n).observable test) atTop
        (𝓝 (∫ omega, test omega ∂(continuum : Measure ℝ)))) :
    Tendsto (fun n => (grids n).law) atTop (𝓝 continuum) := by
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mpr
    hobs

/-- The weak grid-refinement criterion and convergence of all complex bounded
continuous observables are equivalent. -/
theorem spectralGridLaw_tendsto_iff_observables
    {Q : Type*} [MeasurableSpace Q] (grids : ℕ → SpectralGrid Q)
    (continuum : ProbabilityMeasure ℝ) :
    Tendsto (fun n => (grids n).law) atTop (𝓝 continuum) ↔
      ∀ test : ℝ →ᵇ ℂ,
        Tendsto (fun n => (grids n).observable test) atTop
          (𝓝 (∫ omega, test omega ∂(continuum : Measure ℝ))) := by
  exact ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ

end LindbladDrivenLeads
end QuantumMechanics
