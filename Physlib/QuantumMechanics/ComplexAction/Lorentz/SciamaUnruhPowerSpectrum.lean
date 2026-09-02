/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation

/-!
# The Sciama accelerated-detector power spectrum and its KMS-periodic correlator

Sciama–Candelas–Deutsch (1981), §2.  The uniformly accelerated detector's response is the power spectrum

`Π_accelerated(ω) = (1/απ) · ω/(exp(2πω/α) − 1)`

(a Planck spectrum at the Unruh temperature `T = α/2π`), obtained as the Fourier transform of the
accelerated autocorrelation `⟨0|φ̂(τ)φ̂(0)|0⟩ = −α²/(16π² sinh²(τ/2 − iε))`.  Two structural facts:

* the power spectrum factors as `(ω/απ)` times the Planck occupation `n(ω)` (`SciamaFluctuationDissipation`),
  and obeys **detailed balance** `Π(ω)/Π(−ω) = e^{−2πω/α}`;
* the autocorrelation is **periodic in imaginary proper time with period `2πi`** — the residue at `τ = 2πi`
  (Fig. 2) is what produces the thermal `exp(2πω/α) − 1`, so the KMS period is the mechanism, not a
  by-product.

* `unruhPowerSpectrum`, `unruhPowerSpectrum_eq_bose` — the spectrum and its `(ω/απ)·n(ω)` factorization.
* `unruhPowerSpectrum_detailedBalance` — `Π(ω)/Π(−ω) = e^{−2πω/α}`.
* `sinh_add_pi_mul_I`, `acceleratedCorrelator`, `acceleratedCorrelator_kms_periodic` — the correlator's `2πi`
  periodicity.

Honest scope: the algebraic power-spectrum factorization, its detailed balance, and the analytic `2πi`
periodicity of the correlator; the contour integral producing `Π` from the correlator is not carried.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhPowerSpectrum

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFluctuationDissipation

/-- **The accelerated-detector power spectrum** `Π(ω) = (1/απ)·ω/(e^{2πω/α}−1)` (§2). -/
def unruhPowerSpectrum (α ω : ℝ) : ℝ := (1 / (α * Real.pi)) * ω / (Real.exp (2 * Real.pi * ω / α) - 1)

/-- **[Power spectrum = `(ω/απ)·n(ω)`] the Planckian factorization.**  The spectrum is the prefactor `ω/απ`
times the Bose–Einstein occupation at the Unruh inverse temperature `β = 2π/α`. -/
theorem unruhPowerSpectrum_eq_bose (α ω : ℝ) :
    unruhPowerSpectrum α ω = (ω / (α * Real.pi)) * boseEinstein (2 * Real.pi / α) ω := by
  unfold unruhPowerSpectrum boseEinstein
  rw [show 2 * Real.pi / α * ω = 2 * Real.pi * ω / α from by ring]
  ring

/-- **[Detailed balance] `Π(ω)/Π(−ω) = e^{−2πω/α}`.**  The accelerated power spectrum obeys the KMS
detailed-balance / Boltzmann ratio — the detector is in a thermal bath at `T = α/2π`. -/
theorem unruhPowerSpectrum_detailedBalance (α ω : ℝ) (hα : 0 < α) (hω : ω ≠ 0) :
    unruhPowerSpectrum α ω / unruhPowerSpectrum α (-ω) = Real.exp (-(2 * Real.pi * ω / α)) := by
  unfold unruhPowerSpectrum
  have hne : 2 * Real.pi * ω / α ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hω) hα.ne'
  have he1 : Real.exp (2 * Real.pi * ω / α) ≠ 1 := by
    rw [← Real.exp_zero]; exact fun h => hne (Real.exp_injective h)
  rw [show 2 * Real.pi * -ω / α = -(2 * Real.pi * ω / α) from by ring, Real.exp_neg]
  set e := Real.exp (2 * Real.pi * ω / α) with he
  have he0 : e - 1 ≠ 0 := sub_ne_zero.mpr he1
  have hei0 : e⁻¹ - 1 ≠ 0 := by rw [sub_ne_zero, ne_eq, inv_eq_one]; exact he1
  have hex : e ≠ 0 := by rw [he]; exact Real.exp_ne_zero _
  have hα' : α ≠ 0 := hα.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **[Half-period reflection of `sinh`] `sinh(z + πi) = −sinh z`.** -/
theorem sinh_add_pi_mul_I (z : ℂ) : Complex.sinh (z + (Real.pi : ℂ) * Complex.I) = -Complex.sinh z := by
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_pi, Complex.sin_pi]
  ring

/-- **The accelerated autocorrelation** `−α²/(16π² sinh²(τ/2))` (§2). -/
def acceleratedCorrelator (α : ℝ) (τ : ℂ) : ℂ :=
  -(α : ℂ) ^ 2 / (16 * (Real.pi : ℂ) ^ 2 * Complex.sinh (τ / 2) ^ 2)

/-- **[KMS periodicity of the correlator] `G(τ + 2πi) = G(τ)`.**  The accelerated autocorrelation is periodic
in imaginary proper time with the Unruh/KMS period `2πi`: shifting `τ → τ + 2πi` sends `sinh(τ/2) → −sinh
(τ/2)`, whose square is unchanged.  This periodicity is the analytic origin of the thermal spectrum. -/
theorem acceleratedCorrelator_kms_periodic (α : ℝ) (τ : ℂ) :
    acceleratedCorrelator α (τ + 2 * (Real.pi : ℂ) * Complex.I) = acceleratedCorrelator α τ := by
  unfold acceleratedCorrelator
  rw [show (τ + 2 * (Real.pi : ℂ) * Complex.I) / 2 = τ / 2 + (Real.pi : ℂ) * Complex.I from by ring,
    sinh_add_pi_mul_I, neg_sq]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhPowerSpectrum

end
