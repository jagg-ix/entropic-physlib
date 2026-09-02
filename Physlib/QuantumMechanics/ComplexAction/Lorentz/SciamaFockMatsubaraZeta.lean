/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HurwitzZetaRegularization

/-!
# The thermal Fock oscillator on the Matsubara circle, ζ-regularized

The single Fock oscillator of the Sciama arc appears in three infrastructures at once, and this module makes
the identifications concrete:

* **Matsubara circle `S¹_β` (manifold).** The thermal (KMS) state is periodic in imaginary time with period
  `β` — Euclidean time is the circle `S¹` of circumference `β`, whose Fourier dual is the tower of **bosonic
  Matsubara frequencies** `ω_n = 2πn/β` (`ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraFreqBoson`).
  The Gibbs distribution of `SciamaThermalDensityMatrix` is built from the Matsubara Boltzmann weight
  `w = e^{−βE}` (`matsubaraBoltzmannWeight`):
  `thermalProbability_eq_matsubara` — `pₙ = wⁿ(1 − w)`.
* **Fock space (the Sciama arc).** The mean occupation is the shared Bose–Einstein `n̄ = 1/(e^{βE}−1)`:
  `thermal_mean_occupation_eq_matsubara` — `Σₙ n·pₙ = MatsubaraThermalOscillator.boseEinstein β E`, tying the
  arc's `thermal_mean_occupation` to the Matsubara-oscillator occupation.
* **Γ-pole (ζ-regularization).** The oscillator's zero-point sum `½ω Σₙ (n+½)` is divergent and is regularized
  by the **Hurwitz zeta** of its `n+½` spectrum (`OperatorAlgebra.HurwitzZetaRegularization`, the Γ-pole
  `ζ`-function determinant of Hawking):
  `oscillator_spectralZeta_eq_hurwitz` — `ζ_H(s) = Σₙ (ω(n+½))^{−s} = ω^{−s} ζ(s, ½)`.

So the thermal circle carries the Fock oscillator, whose imaginary-time partition function has its poles at the
Matsubara frequencies and whose vacuum energy is Γ-pole / ζ-regularized by `ζ(s, ½)` — one oscillator, three
infrastructures.

Honest scope: the coefficient- and series-level identifications (Gibbs weight = Matsubara Boltzmann geometric law,
mean occupation = Matsubara Bose–Einstein, oscillator spectral zeta = `ω^{−s}·ζ(s,½)`).  The full analytic
continuation of `ζ(s,½)` to `s = −1` (the finite `−ω/24` Casimir vacuum energy) and the Matsubara-frequency
pole structure of the propagator are contextualized, not re-derived here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockMatsubaraZeta

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HurwitzZetaRegularization

/-- **[Gibbs weight = Matsubara Boltzmann geometric law] `pₙ = wⁿ(1 − w)`, `w = e^{−βE}`.**  The Gibbs
distribution of the thermal Fock state is the geometric distribution of the Matsubara Boltzmann weight
`w = ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraBoltzmannWeight β E`. -/
theorem thermalProbability_eq_matsubara (β E : ℝ) (n : ℕ) :
    thermalProbability β E n
      = Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraBoltzmannWeight β E ^ n
        * (1 - Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraBoltzmannWeight β E) := by
  rw [thermalProbability,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraBoltzmannWeight]

/-- **[Mean occupation = Matsubara Bose–Einstein] `Σₙ n·pₙ = n̄`.**  The mean occupation of the thermal Fock
state is the Matsubara-oscillator Bose–Einstein occupation `1/(e^{βE}−1)` — the arc's `thermal_mean_occupation`
and the Matsubara `boseEinstein` are the same Planckian number. -/
theorem thermal_mean_occupation_eq_matsubara (β E : ℝ) (h : 0 < β * E) :
    ∑' n : ℕ, (n : ℝ) * thermalProbability β E n
      = Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator.boseEinstein β E := by
  rw [thermal_mean_occupation β E h]
  rfl

/-- **[Fock vacuum ζ-regularization] `ζ_H(s) = Σₙ (ω(n+½))^{−s} = ω^{−s} ζ(s, ½)`.**  The spectral zeta of the
Fock oscillator's `E_n = ω(n+½)` spectrum is `ω^{−s}` times the Hurwitz zeta at `a = ½`, so the divergent
zero-point energy `½Σ E_n` is Γ-pole / ζ-regularized by `ζ(s, ½)` (the Hawking `ζ`-function determinant). -/
theorem oscillator_spectralZeta_eq_hurwitz (ω s : ℝ) (hω : 0 < ω) :
    spectralZeta (fun n => ω * ((n : ℝ) + 1 / 2)) s = ω ^ (-s) * hurwitzZetaSeries s (1 / 2) := by
  rw [← spectralZeta_linear_eq_hurwitz (1 / 2) s (by norm_num), spectralZeta, spectralZeta,
    ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [Real.mul_rpow hω.le (by positivity)]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockMatsubaraZeta

end
