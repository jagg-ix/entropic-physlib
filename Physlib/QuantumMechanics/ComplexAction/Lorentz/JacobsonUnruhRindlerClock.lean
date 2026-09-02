/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondRelativisticEquations
public import Physlib.Thermodynamics.VerlindeEntropicForce

/-!
# Jacobson's local Rindler horizon read by the three clocks

Jacobson, *Thermodynamics of Spacetime: The Einstein Equation of State* (arXiv:gr-qc/9504004): the Einstein
equation follows from the Clausius relation `δQ = T dS` imposed on every **local Rindler horizon**, with the
**Unruh temperature** `T = κ/2π` and area–entropy `dS = dA/4G` (the full derivation is
`ComplexEinstein.JacobsonClausiusEinstein`).  This connects the *observer* side of that construction — the
uniformly accelerated (local Rindler) observer generating the horizon by a boost — to the three diamond
clocks.

The accelerated observer has boost rapidity `θ = κτ` (proper acceleration `κ`, proper time `τ`), so:

* **Modular clock.**  The horizon boost is the Bisognano–Wichmann wedge modular flow; the Unruh temperature
  `T = κ/2π` and the KMS inverse temperature `β = 2π` (`SummersRelativisticVacuum.unruhInverseTemperature`)
  satisfy `T·β = κ` — the Unruh temperature is the rapidity rate `κ` divided by the modular period `2π`.
* **Doppler clock.**  The **Rindler redshift** `e^{−θ} = e^{−κτ}` between the accelerated observer and its
  horizon is exactly the null-boost eigenvalue `cosh θ − sinh θ` (`diamond_null_boost_factor`) and the
  longitudinal relativistic Doppler `√((1−β)/(1+β))` (`diamond_longitudinal_doppler`) at the observer's
  velocity `β = tanh(κτ)`.
* **Misra/age clock.**  The proper time `τ` along the accelerated worldline is the age parameter; `θ = κτ`.

* `rindlerRapidity`, `rindlerVelocity`, `unruhTemperature`, `rindlerRedshift` — the accelerated observer.
* `unruhTemperature_mul_kmsPeriod` — `T·β = κ` (`β = 2π`).
* `rindlerRedshift_eq_null_boost`, `rindlerRedshift_eq_longitudinalDoppler` — the redshift is the
  null-boost factor and the longitudinal Doppler.

Honest scope: the kinematic identification of Jacobson's Rindler observer with the diamond rapidity, the
Unruh temperature, and the redshift/Doppler; the Clausius→Einstein derivation itself is
`JacobsonClausiusEinstein`, cited not reproved.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.JacobsonUnruhRindlerClock

open Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondRelativisticEquations
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum

/-- **Jacobson's local Rindler observer's boost rapidity** `θ = κτ` (proper acceleration `κ`, proper time
`τ`). -/
def rindlerRapidity (κ τ : ℝ) : ℝ := κ * τ

/-- **The Rindler observer's velocity** `β = tanh(κτ)`. -/
def rindlerVelocity (κ τ : ℝ) : ℝ := Real.tanh (rindlerRapidity κ τ)

/-- **The Unruh temperature of the local Rindler horizon** `T = κ/2π` (Jacobson) — the
geometric-convention carrier (`ℏ = c = k_B = 1`); the SI carrier is
`Physlib.Thermodynamics.unruhTemperature`, related by `si_unruhTemperature_eq_scaled`. -/
def unruhTemperature (κ : ℝ) : ℝ := κ / (2 * Real.pi)

/-- **Convention bridge**: the SI-carrier Unruh temperature is `ℏ/(k_B c)` times the geometric
`κ/2π` form — setting `ℏ = c = k_B = 1` restores it.  Records the conversion between the two
surviving `unruhTemperature` carriers (SI and geometric), the same pattern as
`gibbonsHawkingTemperatureSI_kB_eq` for the energy convention. -/
lemma si_unruhTemperature_eq_scaled (ℏ kB c κ : ℝ) :
    Physlib.Thermodynamics.unruhTemperature ℏ kB c κ = (ℏ / (kB * c)) * unruhTemperature κ := by
  unfold Physlib.Thermodynamics.unruhTemperature unruhTemperature
  ring

/-- **The Rindler redshift factor** `e^{−θ} = e^{−κτ}` between the accelerated observer and its horizon. -/
def rindlerRedshift (κ τ : ℝ) : ℝ := Real.exp (-(rindlerRapidity κ τ))

/-- **[Unruh temperature = rapidity rate over the modular period] `T·β = κ`.**  With the Bisognano–Wichmann
KMS inverse temperature `β = 2π`, the Unruh temperature `T = κ/2π` satisfies `T·β = κ` — the Unruh
temperature is the acceleration (rapidity rate) divided by the modular period. -/
theorem unruhTemperature_mul_kmsPeriod (κ : ℝ) :
    unruhTemperature κ * unruhInverseTemperature = κ := by
  unfold unruhTemperature unruhInverseTemperature
  rw [div_mul_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0)]

/-- **[Rindler redshift = null-boost eigenvalue] `e^{−κτ} = cosh(κτ) − sinh(κτ)`.**  The redshift between the
Rindler observer and its horizon is the boost eigenvalue on the null coordinate. -/
theorem rindlerRedshift_eq_null_boost (κ τ : ℝ) :
    rindlerRedshift κ τ = Real.cosh (rindlerRapidity κ τ) - Real.sinh (rindlerRapidity κ τ) :=
  (diamond_null_boost_factor (rindlerRapidity κ τ)).symm

/-- **[Rindler redshift = longitudinal Doppler] `e^{−κτ} = √((1−β)/(1+β))`.**  The Rindler horizon redshift
is exactly the longitudinal relativistic Doppler shift at the accelerated observer's velocity — the same
`e^{−θ}` whose imaginary-rapidity `2π`-period is the Unruh/KMS temperature. -/
theorem rindlerRedshift_eq_longitudinalDoppler (κ τ : ℝ) :
    rindlerRedshift κ τ = dopplerLongitudinal (rindlerVelocity κ τ) := by
  unfold rindlerRedshift rindlerVelocity
  exact (diamond_longitudinal_doppler (rindlerRapidity κ τ)).symm

end Physlib.QuantumMechanics.ComplexAction.Lorentz.JacobsonUnruhRindlerClock

end
