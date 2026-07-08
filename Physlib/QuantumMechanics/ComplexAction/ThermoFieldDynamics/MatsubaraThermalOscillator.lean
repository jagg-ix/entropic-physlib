/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannThermalOscillator

/-!
# The Matsubara path integral: temperature as the imaginary-time circle

This file links the thermal-oscillator results (`StatisticalMechanics.BoltzmannThermalOscillator`,
`ComplexOscillator.ComplexHarmonicOscillatorBoson`) to the **Matsubara (imaginary-time) finite-temperature path
integral**. The previous step established *temperature = imaginary time* via the heat kernel
`∂_T Ψ = D∇²Ψ`; the Matsubara formalism makes this precise: finite-temperature QFT is the
Euclidean path integral on the **imaginary-time circle of circumference `β = 1/(k_B T)`**, with
the thermal partition function `Z = Tr e^{−βĤ}` and bosonic periodicity `G(τ+β) = G(τ)`.

## The identifications proven here

* **Inverse temperature `β = 1/(k_B T)`** (`matsubaraBeta`) is the imaginary-time extent. It is
  conjugate to temperature (`matsubaraBeta_mul`), and the QIF thermal rate is the Matsubara
  `λ_KMS = 1/(βℏ)` (`kmsThermalRate_eq_matsubara`, linking
  `QuantumInertialFrame.kmsThermalRate`).
* **Bosonic Matsubara frequencies `ω_n = 2πn/β`** (`matsubaraFreqBoson`) — the discrete Fourier
  modes of a `β`-periodic (KMS) imaginary-time correlator, with uniform spacing `2π/β`
  (`matsubaraFreqBoson_succ_sub`).
* **The Matsubara/Euclidean Boltzmann weight `e^{−βE}`** (`matsubaraBoltzmannWeight`) is exactly
  the heat-semigroup at imaginary time `β` (`matsubaraBoltzmannWeight_eq_heatMode`) and the
  modulus of the complex/thermodynamic action weight
  (`matsubaraBoltzmannWeight_eq_thermoActionWeight`: `e^{−βE} = ‖thermoActionWeight‖` with
  imaginary action `S_I = b̄·βE`). So the Matsubara path-integral weight is the entropic damping
  `e^{−S_I/b̄}` of the whole arc.
* **The bosonic oscillator** (`oscillator_matsubaraWeight`): the `n`-th quantum has Boltzmann
  weight `e^{−βℏω(n+½)}`, and the thermal occupation is Bose–Einstein `n_B = 1/(e^{βℏω}−1)`
  (`boseEinstein`, `boseEinstein_pos`).
* **No-information limit** (`matsubaraBoltzmannWeight_eq_one_iff`): the Euclidean weight is
  trivial iff `βE = 0` (no imaginary action) — the Matsubara face of
  `ThermoFieldDynamics.ThermodynamicCanonicalQuantization.thermoActionWeight_norm_one_iff`.

## References

* T. Matsubara, *A new approach to quantum-statistical mechanics*, Prog. Theor. Phys. 14
  (1955) 351 — imaginary-time finite-`T` formalism (`β`-periodicity, `ω_n = 2πn/β`).
* KMS / imaginary-time periodicity: `QuantumMechanics.FiniteTarget.KMSDetailedBalance`,
  Connes–Rovelli thermal time (`kmsThermalRate`).
* `StatisticalMechanics.BoltzmannThermalOscillator`, `ComplexOscillator.ComplexHarmonicOscillatorBoson`,
  `ThermoFieldDynamics.ThermodynamicCanonicalQuantization` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.ThermodynamicCanonicalQuantization
open QuantumMechanics.FiniteTarget

namespace Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator

/-! ## §A — the imaginary-time circle `β = 1/(k_B T)` -/

/-- **Matsubara inverse temperature** `β = 1/(k_B T)` — the circumference of the imaginary-time
circle. -/
def matsubaraBeta (kB T : ℝ) : ℝ := 1 / (kB * T)

/-- The Matsubara inverse temperature is positive at positive temperature. -/
theorem matsubaraBeta_pos (kB T : ℝ) (hkB : 0 < kB) (hT : 0 < T) :
    0 < matsubaraBeta kB T := by
  unfold matsubaraBeta; positivity

/-- **`β·(k_B T) = 1`**: inverse temperature is conjugate to temperature. -/
theorem matsubaraBeta_mul (kB T : ℝ) (hkB : 0 < kB) (hT : 0 < T) :
    matsubaraBeta kB T * (kB * T) = 1 := by
  unfold matsubaraBeta
  exact one_div_mul_cancel (by positivity)

/-- **The QIF thermal rate is the Matsubara `1/(βℏ)`**: `λ_KMS = k_B T/ℏ = 1/(βℏ)` (Connes–
Rovelli thermal time meets the Matsubara circle). -/
theorem kmsThermalRate_eq_matsubara (kB T ℏ : ℝ) (hkB : 0 < kB) (hT : 0 < T) (hℏ : 0 < ℏ) :
    kmsThermalRate kB T ℏ = kmsThermalRate_of_beta (matsubaraBeta kB T) ℏ := by
  unfold kmsThermalRate kmsThermalRate_of_beta matsubaraBeta
  rw [eq_comm]
  have hkBT : kB * T ≠ 0 := by positivity
  field_simp

/-! ## §B — bosonic Matsubara frequencies (KMS periodicity) -/

/-- **Bosonic Matsubara frequency** `ω_n = 2πn/β` — the Fourier modes of a `β`-periodic
imaginary-time correlator (`n ∈ ℤ`). -/
def matsubaraFreqBoson (β : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * n / β

/-- **The zero (static) Matsubara mode** `ω_0 = 0`. -/
theorem matsubaraFreqBoson_zero (β : ℝ) : matsubaraFreqBoson β 0 = 0 := by
  unfold matsubaraFreqBoson; simp

/-- **Uniform Matsubara spacing** `ω_{n+1} − ω_n = 2π/β` (the inverse imaginary-time period). -/
theorem matsubaraFreqBoson_succ_sub (β : ℝ) (hβ : β ≠ 0) (n : ℤ) :
    matsubaraFreqBoson β (n + 1) - matsubaraFreqBoson β n = 2 * Real.pi / β := by
  unfold matsubaraFreqBoson
  push_cast
  field_simp
  ring

/-! ## §C — the Matsubara Boltzmann weight = heat-semigroup = action-weight modulus -/

/-- **The Matsubara / Euclidean Boltzmann weight** `e^{−βE}` — the imaginary-time amplitude of
a mode of energy `E` over the circle of circumference `β`. -/
def matsubaraBoltzmannWeight (β E : ℝ) : ℝ := Real.exp (-(β * E))

/-- **The Matsubara weight is the heat-semigroup at imaginary time `β`**: with mode energy
`E = Dκ²`, `e^{−βE} = heatMode D κ β`. -/
theorem matsubaraBoltzmannWeight_eq_heatMode (D κ β : ℝ) :
    heatMode D κ β = matsubaraBoltzmannWeight β (D * κ ^ 2) := by
  unfold heatMode matsubaraBoltzmannWeight
  congr 1; ring

/-- **The Matsubara weight is the complex/thermodynamic action-weight modulus**:
`e^{−βE} = ‖thermoActionWeight S_R (b̄·βE) b̄‖` (imaginary action `S_I = b̄·βE`). So the
Matsubara path-integral weight is the entropic damping `e^{−S_I/b̄}`. -/
theorem matsubaraBoltzmannWeight_eq_thermoActionWeight (β E S_R b : ℝ) (hb : b ≠ 0) :
    matsubaraBoltzmannWeight β E = ‖thermoActionWeight S_R (b * (β * E)) b‖ := by
  unfold matsubaraBoltzmannWeight
  rw [norm_thermoActionWeight]
  congr 1
  rw [mul_comm b (β * E), mul_div_assoc, div_self hb, mul_one]

/-- **The bosonic oscillator's Matsubara weight** `e^{−βℏω(n+½)}` for the `n`-th quantum. -/
theorem oscillator_matsubaraWeight (β ℏ ω : ℝ) (n : ℕ) :
    matsubaraBoltzmannWeight β (oscillatorEnergyReal ℏ ω n)
      = Real.exp (-(β * (ℏ * ω * (n + 1 / 2)))) := by
  unfold matsubaraBoltzmannWeight oscillatorEnergyReal
  rfl

/-! ## §D — Bose–Einstein occupation and the no-information limit -/

/-- **Bose–Einstein occupation** `n_B(ω) = 1/(e^{βℏω} − 1)` — the thermal population of the
bosonic oscillator mode. -/
def boseEinstein (β ℏω : ℝ) : ℝ := 1 / (Real.exp (β * ℏω) - 1)

/-- The Bose–Einstein occupation is positive for `βℏω > 0`. -/
theorem boseEinstein_pos (β ℏω : ℝ) (h : 0 < β * ℏω) : 0 < boseEinstein β ℏω := by
  unfold boseEinstein
  have h1 : (1 : ℝ) < Real.exp (β * ℏω) := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr h
  exact div_pos one_pos (by linarith)

/-- **The Matsubara weight is trivial iff there is no imaginary action** `βE = 0` (infinite
temperature `β = 0`, or zero energy `E = 0` — massless/ground): the Matsubara face of the
no-information condition `thermoActionWeight_norm_one_iff`. -/
theorem matsubaraBoltzmannWeight_eq_one_iff (β E : ℝ) (hE : E ≠ 0) :
    matsubaraBoltzmannWeight β E = 1 ↔ β = 0 := by
  unfold matsubaraBoltzmannWeight
  rw [Real.exp_eq_one_iff, neg_eq_zero, mul_eq_zero]
  simp [hE]

end Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator

end

end
