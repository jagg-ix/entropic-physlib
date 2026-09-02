/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhPowerSpectrum

/-!
# Sciama–Candelas–Deutsch §3.4: the De Sitter thermal spectrum

In §3.4 the paper shows that in De Sitter space **even an inertially moving detector** registers black-body
radiation — the De Sitter vacuum is intrinsically thermal for *all* observers, unlike Minkowski where only
accelerated detectors are excited.  From the De Sitter Feynman propagator the response is (Eq. 23)

`Π(ω) = (1/2π) · ω/(exp(2π K^{−1/2} ω) − 1)`,

a Planck spectrum at the Gibbons–Hawking temperature `T = (2π K^{−1/2})^{−1} = √K/2π` (`K` the curvature
scale).  This is *structurally identical* to the accelerated response `Π_accelerated` of `§2`
(`SciamaUnruhPowerSpectrum`) — the same `−K/(16π² sinh²(t/2−iε))` correlator — with the proper acceleration
`α` replaced by the De Sitter scale `√K`.

* `deSitterTemperature` — `T = √K/2π`.
* `deSitterPowerSpectrum` — Eq. 23.
* `deSitterPowerSpectrum_eq_bose` — the `(ω/2π)·n(ω)` Planck factorization.
* `deSitterPowerSpectrum_detailedBalance` — `Π(ω)/Π(−ω) = e^{−2πω/√K}` (KMS at `T = √K/2π`).

Honest scope: the algebraic Planck structure and detailed balance of the De Sitter response and its
identification with the Unruh form; the De Sitter propagator itself is upstream.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaDeSitterThermal

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation

/-- **The De Sitter (Gibbons–Hawking) temperature** `T = √K/2π`. -/
def deSitterTemperature (K : ℝ) : ℝ := Real.sqrt K / (2 * Real.pi)

/-- **The De Sitter detector power spectrum** `Π(ω) = (1/2π)·ω/(e^{2πω/√K} − 1)` (Eq. 23). -/
def deSitterPowerSpectrum (K ω : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ω / (Real.exp (2 * Real.pi * ω / Real.sqrt K) - 1)

/-- **[Planck factorization] `Π(ω) = (ω/2π)·n(ω)`** with `n` the Bose occupation at inverse temperature
`β = 2π/√K`. -/
theorem deSitterPowerSpectrum_eq_bose (K ω : ℝ) :
    deSitterPowerSpectrum K ω = (ω / (2 * Real.pi)) * boseEinstein (2 * Real.pi / Real.sqrt K) ω := by
  unfold deSitterPowerSpectrum boseEinstein
  rw [show 2 * Real.pi / Real.sqrt K * ω = 2 * Real.pi * ω / Real.sqrt K from by ring]
  ring

/-- **[Detailed balance] `Π(ω)/Π(−ω) = e^{−2πω/√K}`.**  The De Sitter response obeys the KMS Boltzmann ratio
at the Gibbons–Hawking temperature `T = √K/2π` — an inertial detector in De Sitter sits in a thermal bath. -/
theorem deSitterPowerSpectrum_detailedBalance (K ω : ℝ) (hK : 0 < K) (hω : ω ≠ 0) :
    deSitterPowerSpectrum K ω / deSitterPowerSpectrum K (-ω) = Real.exp (-(2 * Real.pi * ω / Real.sqrt K)) := by
  unfold deSitterPowerSpectrum
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hne : 2 * Real.pi * ω / Real.sqrt K ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hω) hsK.ne'
  have he1 : Real.exp (2 * Real.pi * ω / Real.sqrt K) ≠ 1 := by
    rw [← Real.exp_zero]; exact fun h => hne (Real.exp_injective h)
  rw [show 2 * Real.pi * -ω / Real.sqrt K = -(2 * Real.pi * ω / Real.sqrt K) from by ring, Real.exp_neg]
  set e := Real.exp (2 * Real.pi * ω / Real.sqrt K) with he
  have he0 : e - 1 ≠ 0 := sub_ne_zero.mpr he1
  have hei0 : e⁻¹ - 1 ≠ 0 := by rw [sub_ne_zero, ne_eq, inv_eq_one]; exact he1
  have hex : e ≠ 0 := by rw [he]; exact Real.exp_ne_zero _
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaDeSitterThermal

end
