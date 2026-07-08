/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QFTPathIntegralComplexAction
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator

/-!
# Wick rotation: the Lorentzian and Matsubara path integrals of the complex oscillator

This file links the **Lorentzian (Minkowski, real-time) complex path integral**
(`PathIntegral.QFTPathIntegralComplexAction`: `lorentzianKernel`, `greenKernel`, weight `e^{iS/ℏ}`) to
the **Matsubara (Euclidean, imaginary-time) path integral**
(`ThermoFieldDynamics.MatsubaraThermalOscillator`: `matsubaraBoltzmannWeight`, weight `e^{−βE}`) through the
**Wick rotation** `t = −iℏβ`. Both are values of one complex-time kernel.

## The unifying object: the complex-time kernel

`wickKernel E ℏ z = exp(−i E z/ℏ)` is the `H_C`-propagator (`greenKernel`) continued to
complex time `z`:

* **Real time `z = t`** — the **Lorentzian / Minkowski** amplitude `e^{−iEt/ℏ}`
  (`wickKernel_real_time`). For real energy it is a pure oscillatory phase, `‖·‖ = 1`
  (`norm_wickKernel_real_time`): unitary evolution, the modulus of the Nagao–Nielsen Lorentzian
  kernel (`norm_wickKernel_real_eq_lorentzian`).
* **Imaginary time `z = −iℏβ`** (Wick rotation) — the **Matsubara / Euclidean** weight
  `e^{−βE}` (`wickKernel_imaginary_time`): the thermal Boltzmann factor, the modulus of the
  thermodynamic action weight `e^{−S_I/b̄}`.

So `t = −iℏβ` rotates the unitary Lorentzian propagator (real axis) into the thermal Matsubara
weight (imaginary axis) — the standard real-time ↔ imaginary-time correspondence, here for the
complex action theory's `H_C = H_R − iH_I`.

## The complex oscillator

For `E_n = ℏω(n+½)` (`oscillatorEnergyReal`):

* Lorentzian: `‖wickKernel E_n ℏ t‖ = 1` — unitary evolution `e^{−iω(n+½)t}`
  (`oscillator_wickKernel_lorentzian`).
* Matsubara: `wickKernel E_n ℏ (−iℏβ) = e^{−βℏω(n+½)}` — the thermal Boltzmann weight
  (`oscillator_wickKernel_matsubara`).

The two path integrals of the same oscillator, related by Wick rotation; at the reversible /
no-information point (real `E`, `βE = 0`) the Lorentzian is unimodular and the Matsubara weight
is trivial.

## References

* Nagao–Nielsen complex action theory (`H_C = H_R − iH_I`); Matsubara 1955 (imaginary time).
* `PathIntegral.QFTPathIntegralComplexAction`, `ThermoFieldDynamics.MatsubaraThermalOscillator`,
  `NonHermitianComplexAction.GreenFunction` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QFTPathIntegralComplexAction
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson
open Physlib.QFT.PathIntegral

namespace Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.LorentzianMatsubaraWick

/-! ## §A — the complex-time kernel and its two faces -/

/-- **The complex-time kernel** `e^{−iEz/ℏ}` — the `H_C`-propagator `greenKernel` continued to
complex time `z`. Real `z` is Lorentzian (real-time), imaginary `z` is Matsubara
(imaginary-time). -/
def wickKernel (E ℏ : ℝ) (z : ℂ) : ℂ := Complex.exp (-Complex.I * (E : ℂ) * z / (ℏ : ℂ))

/-- **Real time = Lorentzian propagator**: `wickKernel E ℏ t = greenKernel E ℏ t`, the
Minkowski real-time amplitude. -/
theorem wickKernel_real_time (E ℏ t : ℝ) :
    wickKernel E ℏ (t : ℂ) = greenKernel (E : ℂ) ℏ t := rfl

/-- **The Lorentzian amplitude is unimodular** for real energy: `‖wickKernel E ℏ t‖ = 1` — a
pure oscillatory phase, unitary real-time evolution. -/
theorem norm_wickKernel_real_time (E ℏ t : ℝ) :
    ‖wickKernel E ℏ (t : ℂ)‖ = 1 := by
  rw [wickKernel_real_time, norm_greenKernel]
  simp

/-- **The Lorentzian amplitude is the Nagao–Nielsen Lorentzian kernel's modulus**:
`‖wickKernel E ℏ t‖ = ‖lorentzianKernel S_R (−(Im E)·t) ℏ‖`. -/
theorem norm_wickKernel_real_eq_lorentzian (E ℏ t S_R : ℝ) :
    ‖wickKernel E ℏ (t : ℂ)‖ = ‖lorentzianKernel S_R (-(E : ℂ).im * t) ℏ‖ := by
  rw [wickKernel_real_time, norm_greenKernel_eq_lorentzianKernel]

/-- **Imaginary time = Matsubara weight** (Wick rotation `t = −iℏβ`):
`wickKernel E ℏ (−iℏβ) = e^{−βE} = matsubaraBoltzmannWeight β E`. The Lorentzian propagator
continued to imaginary time is the Euclidean / thermal Boltzmann weight. -/
theorem wickKernel_imaginary_time (E ℏ β : ℝ) (hℏ : ℏ ≠ 0) :
    wickKernel E ℏ (-Complex.I * ((ℏ * β : ℝ) : ℂ))
      = ((matsubaraBoltzmannWeight β E : ℝ) : ℂ) := by
  unfold wickKernel matsubaraBoltzmannWeight
  rw [Complex.ofReal_exp]
  congr 1
  have hℏc : (ℏ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℏ
  have key : -Complex.I * (E : ℂ) * (-Complex.I * ((ℏ * β : ℝ) : ℂ)) / (ℏ : ℂ)
      = (Complex.I * Complex.I) * ((E : ℂ) * ((ℏ * β : ℝ) : ℂ) / (ℏ : ℂ)) := by ring
  rw [key, Complex.I_mul_I]
  push_cast
  field_simp

/-! ## §B — the complex oscillator's two path integrals -/

/-- **Lorentzian (real-time) oscillator**: `‖wickKernel E_n ℏ t‖ = 1` — unitary evolution
`e^{−iω(n+½)t}` of the `n`-th quantum. -/
theorem oscillator_wickKernel_lorentzian (ℏ ω t : ℝ) (n : ℕ) :
    ‖wickKernel (oscillatorEnergyReal ℏ ω n) ℏ (t : ℂ)‖ = 1 :=
  norm_wickKernel_real_time _ ℏ t

/-- **Matsubara (imaginary-time) oscillator**: `wickKernel E_n ℏ (−iℏβ) = e^{−βℏω(n+½)}` — the
thermal Boltzmann weight of the `n`-th quantum (Wick rotation of the unitary evolution). -/
theorem oscillator_wickKernel_matsubara (ℏ ω β : ℝ) (hℏ : ℏ ≠ 0) (n : ℕ) :
    wickKernel (oscillatorEnergyReal ℏ ω n) ℏ (-Complex.I * ((ℏ * β : ℝ) : ℂ))
      = ((matsubaraBoltzmannWeight β (oscillatorEnergyReal ℏ ω n) : ℝ) : ℂ) :=
  wickKernel_imaginary_time _ ℏ β hℏ

end Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.LorentzianMatsubaraWick

end

end
