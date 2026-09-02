/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.SpectralDynamics

/-!
# Finite pure-point Schrödinger initial-data recovery

This module formalizes the finite pure-point analogue of the initial-value
recovery statements that motivate the Schrödinger Carleson problem in Jonathan
Hickman's exposition of the Du--Zhang theorem (arXiv:2304.02507).

For the existing diagonal spectral evolution

`c_i(t) = exp(-i E_i t / ℏ) c_i`,

we prove:

* every coefficient is continuous in time and converges to its initial value as
  `t → 0`;
* the finite squared `ℓ²` error converges to zero;
* summing the conserved spectral energy over any finite set of sampled times
  gives an exact sampled space--time energy identity.

The two-sided limit proved here is stronger than the `t → 0⁺` formulation for
this finite model.

## Scope boundary

These results do **not** formalize the Du--Zhang almost-everywhere theorem.  In
particular, this file does not claim the Euclidean Sobolev threshold
`s > n / (2(n+1))`, an `L²` maximal estimate, fractal restriction estimates, or
decoupling.  Those require an infinite-dimensional Fourier/Sobolev and maximal
operator layer not currently supplied by Physlib.  This module establishes the
finite spectral recovery base on which such an extension can later be built.

## Reference

Jonathan Hickman, *Pointwise convergence for the Schrödinger equation (after
Xiumin Du and Ruixiang Zhang)*, arXiv:2304.02507, 2023.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Filter Topology
open scoped BigOperators

namespace Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery

open SpectralDynamics

variable {ι : Type*}

/-! ## A. Pointwise recovery of spectral coefficients -/

/-- The scalar spectral phase depends continuously on real time. -/
lemma continuous_spectralPhase (E hbar : ℝ) :
    Continuous (fun t : ℝ => spectralPhase E hbar t) := by
  unfold spectralPhase Physlib.QuantumMechanics.NonHermitian.WickRotation.reversiblePhase
  exact Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal)

/-- Every coefficient of a finite pure-point Schrödinger evolution is
continuous in real time.  Finiteness is not needed for this componentwise
statement. -/
lemma continuous_finiteSpectralEvolution_component
    (E : ι → ℝ) (hbar : ℝ) (c : ι → ℂ) (i : ι) :
    Continuous (fun t : ℝ => finiteSpectralEvolution E hbar t c i) := by
  unfold finiteSpectralEvolution
  exact (continuous_spectralPhase (E i) hbar).mul continuous_const

/-- Pointwise initial-data recovery for every spectral coefficient.  This is a
two-sided real-time limit, and therefore implies the one-sided `t → 0⁺`
finite-model statement. -/
lemma finiteSpectralEvolution_component_tendsto_zero
    (E : ι → ℝ) (hbar : ℝ) (c : ι → ℂ) (i : ι) :
    Tendsto (fun t : ℝ => finiteSpectralEvolution E hbar t c i)
      (𝓝 0) (𝓝 (c i)) := by
  have h :
      Tendsto (fun t : ℝ => finiteSpectralEvolution E hbar t c i)
        (𝓝 0) (𝓝 (finiteSpectralEvolution E hbar 0 c i)) :=
    (continuous_finiteSpectralEvolution_component E hbar c i).continuousAt
  simpa only [finiteSpectralEvolution_zero] using h

/-- The whole coefficient function converges in the product topology to its
initial value. -/
lemma finiteSpectralEvolution_tendsto_zero
    (E : ι → ℝ) (hbar : ℝ) (c : ι → ℂ) :
    Tendsto (fun t : ℝ => finiteSpectralEvolution E hbar t c)
      (𝓝 0) (𝓝 c) := by
  exact tendsto_pi_nhds.2 fun i =>
    finiteSpectralEvolution_component_tendsto_zero E hbar c i

/-! ## B. Finite `ℓ²` initial-data recovery -/

/-- Squared finite `ℓ²` distance between the evolved spectral coefficients and
their initial values. -/
def finiteSpectralL2ErrorSq [Fintype ι]
    (E : ι → ℝ) (hbar t : ℝ) (c : ι → ℂ) : ℝ :=
  ∑ i, ‖finiteSpectralEvolution E hbar t c i - c i‖ ^ 2

/-- The squared finite `ℓ²` recovery error is nonnegative. -/
lemma finiteSpectralL2ErrorSq_nonneg [Fintype ι]
    (E : ι → ℝ) (hbar t : ℝ) (c : ι → ℂ) :
    0 ≤ finiteSpectralL2ErrorSq E hbar t c := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- At zero time the finite `ℓ²` recovery error vanishes exactly. -/
@[simp] lemma finiteSpectralL2ErrorSq_zero [Fintype ι]
    (E : ι → ℝ) (hbar : ℝ) (c : ι → ℂ) :
    finiteSpectralL2ErrorSq E hbar 0 c = 0 := by
  simp [finiteSpectralL2ErrorSq]

/-- The squared finite `ℓ²` distance from the initial data converges to zero as
`t → 0`.  This is the finite pure-point analogue of strong `L²` recovery. -/
lemma finiteSpectralL2ErrorSq_tendsto_zero [Fintype ι]
    (E : ι → ℝ) (hbar : ℝ) (c : ι → ℂ) :
    Tendsto (fun t : ℝ => finiteSpectralL2ErrorSq E hbar t c)
      (𝓝 0) (𝓝 0) := by
  have hcontinuous :
      Continuous (fun t : ℝ => finiteSpectralL2ErrorSq E hbar t c) := by
    unfold finiteSpectralL2ErrorSq
    refine continuous_finsetSum Finset.univ fun i _hi => ?_
    exact
      (((continuous_finiteSpectralEvolution_component E hbar c i).sub
        continuous_const).norm.pow 2)
  have h :
      Tendsto (fun t : ℝ => finiteSpectralL2ErrorSq E hbar t c)
        (𝓝 0) (𝓝 (finiteSpectralL2ErrorSq E hbar 0 c)) :=
    hcontinuous.continuousAt
  simpa only [finiteSpectralL2ErrorSq_zero] using h

/-! ## C. Exact sampled space--time energy -/

/-- Total spectral energy sampled over a finite set of real times. -/
def finiteSampledSpacetimeEnergy [Fintype ι]
    (times : Finset ℝ) (E : ι → ℝ) (hbar : ℝ) (c : ι → ℂ) : ℝ :=
  ∑ t ∈ times, ∑ i, ‖finiteSpectralEvolution E hbar t c i‖ ^ 2

/-- In the finite pure-point unitary model, sampled space--time energy is
exactly the number of samples times the initial spectral energy. -/
lemma finiteSampledSpacetimeEnergy_eq [Fintype ι]
    (times : Finset ℝ) (E : ι → ℝ) (hbar : ℝ) (c : ι → ℂ) :
    finiteSampledSpacetimeEnergy times E hbar c =
      (times.card : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
  unfold finiteSampledSpacetimeEnergy
  calc
    (∑ t ∈ times, ∑ i, ‖finiteSpectralEvolution E hbar t c i‖ ^ 2) =
        ∑ _t ∈ times, ∑ i, ‖c i‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro t _ht
          exact finiteSpectralEvolution_total_probability E hbar t c
    _ = (times.card : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
      simp

/-! ## D. Recovery and energy certificate -/

/-- A single certificate collecting the finite pointwise recovery, finite
`ℓ²` recovery, and exact sampled space--time energy identity.

This is the bounded finite pure-point target extracted from the foundational
part of the Schrödinger Carleson program; it is deliberately not stated as the
Du--Zhang Euclidean almost-everywhere theorem. -/
lemma finiteSchrodinger_initialRecovery_and_sampledEnergy [Fintype ι]
    (E : ι → ℝ) (hbar : ℝ) (c : ι → ℂ) :
    (∀ i, Tendsto (fun t : ℝ => finiteSpectralEvolution E hbar t c i)
        (𝓝 0) (𝓝 (c i))) ∧
    Tendsto (fun t : ℝ => finiteSpectralL2ErrorSq E hbar t c)
      (𝓝 0) (𝓝 0) ∧
    ∀ times : Finset ℝ,
      finiteSampledSpacetimeEnergy times E hbar c =
        (times.card : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
  refine ⟨?_, finiteSpectralL2ErrorSq_tendsto_zero E hbar c, ?_⟩
  · intro i
    exact finiteSpectralEvolution_component_tendsto_zero E hbar c i
  · intro times
    exact finiteSampledSpacetimeEnergy_eq times E hbar c

end Physlib.QuantumMechanics.Schrodinger.FiniteCarlesonRecovery
