/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondThreeClocks

/-!
# The relativistic-equation list on the diamond mode

Closing the special-relativity equation list (Wikipedia, *List of relativistic equations*) against the
diamond three-clock framework.  Everything is a function of the one rapidity `θ` (`γ = cosh θ`, `β = tanh θ`),
and the three additions here are the lines the earlier arc had not yet reached:

* **Velocity addition = rapidity additivity.**  `tanh(θ₁+θ₂) = (β₁+β₂)/(1+β₁β₂)`: diamond velocities compose
  relativistically while rapidities *add* — the modular/boost composition law.
* **Longitudinal Doppler = the modular boost factor.**  `ν'/ν = √((1−β)/(1+β)) = e^{−θ} = cosh θ − sinh θ`:
  the relativistic redshift is the eigenvalue of the boost on the outgoing null coordinate `x⁻ = t − x`.
  Since the wedge boost is the Bisognano–Wichmann modular flow, this `e^{−θ}` is the real-rapidity companion
  of the imaginary-rapidity KMS period `2π` of `DiamondBisognanoWichmannKMS` (both are `exp` of the boost).
* **Length contraction of the Compton wavelength.**  `λ_C(m·cosh θ) = λ_C/cosh θ = √(1 − BCJ dual)·λ_C` —
  the reciprocal of the de Broglie frequency boost / time dilation.

* `rapidity_velocity_addition` — `tanh(θ₁+θ₂) = (tanh θ₁ + tanh θ₂)/(1 + tanh θ₁ tanh θ₂)`.
* `diamond_null_boost_factor` — `cosh θ − sinh θ = e^{−θ}`.
* `diamond_longitudinal_doppler`, `diamond_longitudinal_doppler_eq_null_boost` — the redshift is `e^{−θ}`.
* `comptonWavelength_energy_scaling`, `diamond_comptonWavelength_contraction` — length contraction of `λ_C`.
* `diamond_lengthContraction_factor` — the contraction factor `1/cosh θ = √(1 − lorentzForceDual)`.

Honest scope: the algebraic special-relativity identities at the diamond mode; the modular reading of the
longitudinal Doppler is stated as the `exp`-of-rapidity companion of the KMS period, cited not reproved.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondRelativisticEquations

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamondMassShell
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-- **[Velocity addition = rapidity additivity] `tanh(θ₁+θ₂) = (β₁+β₂)/(1+β₁β₂)`.**  The relativistic
velocity-addition law: diamond velocities `β = tanh θ` compose this way, i.e. rapidities add. -/
theorem rapidity_velocity_addition (θ₁ θ₂ : ℝ) :
    Real.tanh (θ₁ + θ₂)
      = (Real.tanh θ₁ + Real.tanh θ₂) / (1 + Real.tanh θ₁ * Real.tanh θ₂) := by
  have ha : Real.cosh θ₁ ≠ 0 := (Real.cosh_pos θ₁).ne'
  have hb : Real.cosh θ₂ ≠ 0 := (Real.cosh_pos θ₂).ne'
  have hab : Real.cosh θ₁ * Real.cosh θ₂ + Real.sinh θ₁ * Real.sinh θ₂ ≠ 0 := by
    rw [← Real.cosh_add]; exact (Real.cosh_pos _).ne'
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    Real.sinh_add, Real.cosh_add]
  field_simp

/-- **[Null boost factor] `cosh θ − sinh θ = e^{−θ}`.**  The eigenvalue of the boost by rapidity `θ` on the
outgoing null coordinate `x⁻ = t − x`. -/
theorem diamond_null_boost_factor (θ : ℝ) : Real.cosh θ - Real.sinh θ = Real.exp (-θ) := by
  rw [Real.cosh_eq, Real.sinh_eq, Real.exp_neg]; ring

/-- **The longitudinal relativistic Doppler factor** `√((1−β)/(1+β))` (emitter and observer along the line
of motion). -/
def dopplerLongitudinal (β : ℝ) : ℝ := Real.sqrt ((1 - β) / (1 + β))

/-- **[Longitudinal Doppler = `e^{−θ}`] `√((1−tanh θ)/(1+tanh θ)) = e^{−θ}`.**  The relativistic redshift at
diamond velocity `β = tanh θ` is the null-boost eigenvalue — the real-rapidity companion of the
Bisognano–Wichmann KMS period `2π` (both `exp` of the boost generator). -/
theorem diamond_longitudinal_doppler (θ : ℝ) :
    dopplerLongitudinal (Real.tanh θ) = Real.exp (-θ) := by
  unfold dopplerLongitudinal
  rw [show (1 - Real.tanh θ) / (1 + Real.tanh θ) = (Real.exp (-θ)) ^ 2 from by
    rw [Real.tanh_eq_sinh_div_cosh, Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
    have he : Real.exp θ ≠ 0 := (Real.exp_pos θ).ne'
    field_simp
    ring]
  exact Real.sqrt_sq (Real.exp_nonneg _)

/-- **[Longitudinal Doppler is the null-boost factor] `√((1−tanh θ)/(1+tanh θ)) = cosh θ − sinh θ`.**  The
redshift is exactly the boost eigenvalue on the null coordinate. -/
theorem diamond_longitudinal_doppler_eq_null_boost (θ : ℝ) :
    dopplerLongitudinal (Real.tanh θ) = Real.cosh θ - Real.sinh θ := by
  rw [diamond_longitudinal_doppler, diamond_null_boost_factor]

/-- **[Compton wavelength scales inversely with energy] `λ_C(m·E) = λ_C/E`.** -/
theorem comptonWavelength_energy_scaling (m E c ħ : ℝ) :
    comptonWavelength (m * E) c ħ = comptonWavelength m c ħ / E := by
  unfold comptonWavelength
  rw [div_div]
  congr 1
  ring

/-- **[Length contraction of the Compton wavelength] `λ_C(m·cosh θ) = λ_C/cosh θ`.**  The diamond-boosted
Compton wavelength is the rest wavelength contracted by the Lorentz factor — the reciprocal of the de Broglie
frequency boost. -/
theorem diamond_comptonWavelength_contraction (m c ħ θ : ℝ) :
    comptonWavelength (m * bogoliubovEnergy (Real.sinh θ) 1) c ħ
      = comptonWavelength m c ħ / bogoliubovEnergy (Real.sinh θ) 1 :=
  comptonWavelength_energy_scaling m (bogoliubovEnergy (Real.sinh θ) 1) c ħ

/-- **[Contraction factor from the BCJ dual] `1/cosh θ = √(1 − lorentzForceDual)`.**  The length-contraction
factor is the square root of `1` minus the BCJ gravitational dual `v² = tanh²θ` — the reciprocal Lorentz
factor `√(1 − v²)`. -/
theorem diamond_lengthContraction_factor (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4)
    (θ : ℝ) (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    1 / bogoliubovEnergy (Real.sinh θ) 1
      = Real.sqrt (1 - lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2)) := by
  rw [diamond_dual_one_sub F V μ θ hnum, diamond_horizon_energy, one_div (Real.cosh θ ^ 2),
    Real.sqrt_inv, Real.sqrt_sq (Real.cosh_pos θ).le, one_div]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondRelativisticEquations

end
