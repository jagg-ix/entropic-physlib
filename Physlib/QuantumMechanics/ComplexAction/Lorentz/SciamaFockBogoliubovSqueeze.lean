/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockSqueezedVacuum
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockThermofieldDouble
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDBogoliubovHopf
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic

/-!
# The Bogoliubov squeeze: linking the squeezed vacuum and thermofield double to the thermal-time group

The single-mode squeezed vacuum (`SciamaFockSqueezedVacuum`) and the two-mode thermofield double
(`SciamaFockThermofieldDouble`) are the two faces of one structure — the **su(1,1) Bogoliubov squeeze** already
carried by the thermofield-dynamics arc as the `2×2` boost `U_B(θ) = [[cosh θ, sinh θ],[sinh θ, cosh θ]]`
(`ThermoFieldDynamics.TFDImaginaryPart.thermoBogoliubov`, the exponential `e^{θK}` of the involutive generator
`K = [[0,1],[1,0]]`, `TFDBogoliubovHopf`).  This module makes the links concrete:

* `squeeze_annihilation_via_bogoliubov` — the squeezed vacuum is annihilated by `b = a·U_B₀₀ + a†·U_B₀₁ =
  a cosh r + a† sinh r`, the Bogoliubov-rotated annihilation operator whose coefficients are **the entries of
  `thermoBogoliubov r`**.  The squeeze parameter `r` is the Bogoliubov boost angle `θ`.
* `bogoliubov_preserves_ccr` — `U_B₀₀² − U_B₀₁² = cosh²r − sinh²r = 1`: the boost is on the Lorentz mass shell
  (`thermoBogoliubov_det`), which is exactly the statement that `b, b†` still obey the CCR — a *canonical* (CCR-
  preserving) transformation.
* `thermalProbability_eq_thermalWeight_pow` — the thermofield double is the **two-mode** squeezed vacuum: its
  Gibbs weight `pₙ = (1 − w²)w^{2n}` with `w = ThermoFieldDynamics.Basic.thermalWeight = e^{−βE/2}`, and
  `w = tanh θ` is the two-mode squeeze parameter (`w² = e^{−βE}` = the Boltzmann weight).  The single-mode
  `tanh r` and the two-mode `tanh θ = e^{−βE/2}` are the same Bogoliubov `tanh`.

This is where the Fock states meet the entropic-time / three-clock program: the Bogoliubov boost angle `θ` is
the **thermal (modular) time** parameter — `w = e^{−βE/2}` fixes the KMS `β` and hence the Unruh/Hawking
temperature — the same `β = 2π` modular flow that drives the coherent clock-hand of
`SciamaFockCoherentEvolution` (Connes–Rovelli physical time `= β ×` modular time).  Displacement (coherent),
squeeze, and thermofield doubling are the three canonical (CCR-preserving) motions of the single mode; the
squeeze/boost is the one that carries temperature.

Honest scope: the concrete coefficient-level links — the squeeze annihilation in Bogoliubov-matrix form, its
CCR/mass-shell preservation, and the thermofield-double Gibbs weight as a two-mode squeeze in the repo's
`thermalWeight`.  The operator identities `b = S(r)aS(r)†` and `S₂(θ)|0,0⟩ = |TFD⟩` are contextualized, not
built at the operator level.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockBogoliubovSqueeze

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockSqueezedVacuum
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart

/-- The `(0,0)` entry of the Bogoliubov boost is `cosh θ`. -/
theorem thermoBogoliubov_zero_zero (r : ℝ) : thermoBogoliubov r 0 0 = Real.cosh r := by
  simp [thermoBogoliubov]

/-- The `(0,1)` entry of the Bogoliubov boost is `sinh θ`. -/
theorem thermoBogoliubov_zero_one (r : ℝ) : thermoBogoliubov r 0 1 = Real.sinh r := by
  simp [thermoBogoliubov]

/-- The squeeze recurrence in Bogoliubov (`cosh`/`sinh`) form: `cosh r·√(2n+2) c_{2n+2} = −sinh r·√(2n+1)
c_{2n}`, i.e. `(a cosh r + a† sinh r) S(r)|0⟩ = 0`. -/
theorem sqCoeffR_bogoliubov_annihilation (r : ℝ) (n : ℕ) :
    Real.cosh r * Real.sqrt (2 * (n : ℝ) + 2) * sqCoeffR r (n + 1)
      = -(Real.sinh r) * Real.sqrt (2 * (n : ℝ) + 1) * sqCoeffR r n := by
  have hc : Real.cosh r ≠ 0 := (Real.cosh_pos r).ne'
  rw [show Real.cosh r * Real.sqrt (2 * (n : ℝ) + 2) * sqCoeffR r (n + 1)
      = Real.cosh r * (Real.sqrt (2 * (n : ℝ) + 2) * sqCoeffR r (n + 1)) from by ring,
    sqCoeffR_recurrence, Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- **[Squeeze = Bogoliubov boost] `U_B₀₀·√(2n+2) c_{2n+2} = −U_B₀₁·√(2n+1) c_{2n}`.**  The squeezed vacuum is
annihilated by `b = a·(thermoBogoliubov r)₀₀ + a†·(thermoBogoliubov r)₀₁`, the Bogoliubov-rotated annihilation
operator of the thermofield-dynamics boost `U_B(r)`.  The squeeze parameter is the boost angle. -/
theorem squeeze_annihilation_via_bogoliubov (r : ℝ) (n : ℕ) :
    (thermoBogoliubov r 0 0) * Real.sqrt (2 * (n : ℝ) + 2) * sqCoeffR r (n + 1)
      = -(thermoBogoliubov r 0 1) * Real.sqrt (2 * (n : ℝ) + 1) * sqCoeffR r n := by
  rw [thermoBogoliubov_zero_zero, thermoBogoliubov_zero_one]
  exact sqCoeffR_bogoliubov_annihilation r n

/-- **[Canonical / CCR-preserving] `U_B₀₀² − U_B₀₁² = 1`.**  `cosh²r − sinh²r = 1` — the Bogoliubov boost is
unimodular (`thermoBogoliubov_det`), i.e. the rotated `b, b†` still satisfy `[b, b†] = 1`; the squeeze is a
*canonical* transformation. -/
theorem bogoliubov_preserves_ccr (r : ℝ) :
    (thermoBogoliubov r 0 0) ^ 2 - (thermoBogoliubov r 0 1) ^ 2 = 1 := by
  rw [thermoBogoliubov_zero_zero, thermoBogoliubov_zero_one, Real.cosh_sq, Real.sinh_sq]
  ring

/-- **[Thermofield double = two-mode squeeze] `pₙ = (1 − w²)w^{2n}`, `w = e^{−βE/2}`.**  The thermofield-double
Gibbs weight is the two-mode squeezed-vacuum weight with squeeze parameter `tanh θ = w =
ThermoFieldDynamics.Basic.thermalWeight β E = e^{−βE/2}` (`w² = e^{−βE}`, the Boltzmann weight): the same
Bogoliubov `tanh` as the single-mode squeeze, now setting the KMS temperature. -/
theorem thermalProbability_eq_thermalWeight_pow (β E : ℝ) (n : ℕ) :
    thermalProbability β E n
      = (1 - Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic.thermalWeight β E ^ 2)
        * (Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic.thermalWeight β E) ^ (2 * n) := by
  rw [pow_mul, Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic.thermalWeight_sq,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraBoltzmannWeight,
    thermalProbability]
  ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockBogoliubovSqueeze

end
