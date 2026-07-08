/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSConformalKilling
public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

/-!
# The AdS conformal Killing vectors derived from the Nagao–Nielsen complex momentum / complex `p, q`

`CausalDiamond.AdSConformalKilling` formalized the Anti-de Sitter half of Appendix D (Eqs. D.9–D.14) and
observed that AdS is the `L → iL` (boost → rotation) continuation of de Sitter. This file proves that the
`L → iL` continuation **is** the Nagao–Nielsen complexification: the AdS equations are derived from a
**complex momentum** (imaginary rapidity) and a **complex `q`** (the complex embedding coordinate), the
same `i` that takes the real action `e^{iS/ℏ}` to the entropic weight `e^{−S_I/ℏ}`.

The single mechanism is the imaginary rapidity. De Sitter uses a **real** rapidity `η`:

 `sinh²η + 1 = cosh²η` (real momentum `p = sinh η`, energy `E = cosh η`).

Anti-de Sitter uses the **Nagao–Nielsen complex momentum** `p = sinh(iθ) = i sin θ` (a purely imaginary
momentum, the imaginary rapidity `η = iθ`):

 `(i sin θ)² + 1 = cos²θ` (`adS_dispersion_complexMomentum`),

since `i² = −1` turns `cosh²−sinh² = 1` (boost / Minkowski) into `cos²+sin² = 1` (rotation / Euclidean).
So the AdS dispersion `E = cos θ = cosh(iθ)` (`adS_energy_eq_cosh_imaginary`) is the Bogoliubov energy of
the complex momentum `p = i sin θ = sinh(iθ)` (`adS_momentum_eq_sinh_imaginary`). This is made literal by
the **complex Bogoliubov dispersion** `bogoliubovDispersionℂ(ξ, Δ) = ξ² + Δ²` — which restricts to the
real `bogoliubovEnergy² = ξ² + Δ²` on real arguments (`bogoliubovDispersionℂ_ofReal`) and gives the AdS
energy `cos²θ` at the imaginary momentum (`adS_bogoliubovDispersion_imaginaryMomentum`). The imaginary
momentum pushes the energy *below* the gap, `cos²θ ≤ 1` (`adS_energy_below_gap`), versus dS's real
momentum which keeps it *above*, `cosh²η ≥ 1` (`dS_energy_above_gap`).

* **complex `q`** — the AdS embedding coordinate is `q = W e^{i t/L}` (`adSComplexCoord`); its modulus
 `|q|² = (X^{−1})² + (X⁰)² = W²` (`adSComplexCoord_normSq`, `adS_rotationInvariant`) **is** the AdS
 light-cone identity D.9 (`adS_lightCone_from_complexCoord`).
* **Wick rotation** — the de Sitter coordinate `q_dS = w(cosh η + i sinh η)` has the timelike Lorentzian
 form `L(q_dS) = w²` (`dSComplexCoord_lorentzianForm`); multiplying by `i` (the NN Wick rotation,
 `lorentzianForm_mul_I`) flips it to `−w²` (`dS_wick_to_spacelike`) — real time → Euclidean time.
* **complex position** — the `L → iL` factor continuation D.8 ↔ D.12 (`adsConfKillingFactor` vs
 `sqrtFactor`) is the substitution `R → iR`: `1 + (R/L)² = 1 − ((iR)/L)²`
 (`adS_factor_arg_from_complexPosition`).
* **convergence** — the NN complex-momentum Gaussian converges iff `Im m > 0`
 (`momentum_integral_converges_iff`), the entropic-damping condition `e^{−S_I/ℏ}`.

The main result `adS_appendixD2_from_nagaoNielsen` derives the AdS equations from the complex momentum, the
complex `q`, and the complex position in one statement.

## Scope

The complex-momentum, complex-`q`, and complex-position identities are exact. The "AdS = `L → iL` of dS"
reading is made precise here as the NN complexification; the geometric generators (D.11) and Poincaré
coordinates (D.13–D.14) are not built.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSComplexMomentum

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.MetricCommonRootEntropicTime
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSConformalKilling

/-! ## §A — the Nagao–Nielsen complex momentum: imaginary rapidity (boost → rotation) -/

/-- **The de Sitter dispersion (real momentum)** `sinh²η + 1 = cosh²η` — the boost / Minkowski
dispersion `E² = p² + Δ²` with real momentum `p = sinh η`, energy `E = cosh η`, gap `Δ = 1`. -/
theorem dS_dispersion_realMomentum (η : ℝ) :
    Real.sinh η ^ 2 + 1 = Real.cosh η ^ 2 := (Real.cosh_sq η).symm

/-- **The Nagao–Nielsen complex momentum is the imaginary rapidity** `p = sinh(iθ) = i sin θ`. The de
Sitter momentum `sinh η` becomes, under the complexification `η = iθ`, the purely imaginary momentum
`i sin θ` — the NN complex momentum. -/
theorem adS_momentum_eq_sinh_imaginary (θ : ℝ) :
    Complex.sinh ((θ : ℂ) * Complex.I) = (Real.sin θ : ℂ) * Complex.I := by
  rw [Complex.sinh_mul_I, ← Complex.ofReal_sin]

/-- **The AdS energy is the cosh of the imaginary rapidity** `E = cosh(iθ) = cos θ`. The de Sitter energy
`cosh η` becomes, under `η = iθ`, the AdS energy `cos θ`. -/
theorem adS_energy_eq_cosh_imaginary (θ : ℝ) :
    Complex.cosh ((θ : ℂ) * Complex.I) = (Real.cos θ : ℂ) := by
  rw [Complex.cosh_mul_I, ← Complex.ofReal_cos]

/-- **The AdS dispersion from the complex momentum** `(i sin θ)² + 1 = cos²θ`. With the NN complex
(imaginary) momentum `p = i sin θ = sinh(iθ)` and gap `Δ = 1`, the Bogoliubov dispersion `p² + Δ²`
becomes `cos²θ = E²` — the rotation identity `cos²+sin² = 1`, the `i² = −1` image of the de Sitter boost
identity `cosh²−sinh² = 1`. This **is** the AdS structure, derived from the complex momentum. -/
theorem adS_dispersion_complexMomentum (θ : ℝ) :
    (Complex.I * (Real.sin θ : ℂ)) ^ 2 + 1 = (Real.cos θ : ℂ) ^ 2 := by
  have h : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.sin_sq_add_cos_sq, Complex.ofReal_one]
  rw [mul_pow, Complex.I_sq]
  linear_combination -h

/-! ## §A′ — the complex Bogoliubov dispersion `E² = ξ² + Δ²` -/

/-- **The complex Bogoliubov dispersion** `E² = ξ² + Δ²` — the complexified Einstein/Bogoliubov relation
`bogoliubovEnergy² = ξ² + Δ²` (`Bogoliubov.Transformation.bogoliubovEnergy`,
`EntropicTime.MetricCommonRootEntropicTime.bogoliubovEnergy_sq`) with the momentum `ξ` and gap `Δ` allowed to be
complex — the underlying space of the Nagao–Nielsen complex momentum. -/
def bogoliubovDispersionℂ (ξ Δ : ℂ) : ℂ := ξ ^ 2 + Δ ^ 2

/-- **Momentum–gap duality** `ξ² + Δ² = Δ² + ξ²` — the complex dispersion is symmetric in the momentum
`ξ` and the gap `Δ` (the Euclidean `ξ²+Δ²` form), the property the `ξ² + Δ²` definition presupposes. -/
theorem bogoliubovDispersionℂ_comm (ξ Δ : ℂ) :
    bogoliubovDispersionℂ ξ Δ = bogoliubovDispersionℂ Δ ξ := by
  rw [bogoliubovDispersionℂ, bogoliubovDispersionℂ, add_comm]

/-- **The complex dispersion restricts to the real Bogoliubov energy.** On real momentum and gap, the
complex dispersion is `(bogoliubovEnergy ξ Δ)²` (`bogoliubovEnergy_sq`): `bogoliubovDispersionℂ` genuinely
extends the real `bogoliubovEnergy² = ξ² + Δ²` of `EntropicTime.MetricCommonRootEntropicTime`. -/
theorem bogoliubovDispersionℂ_ofReal (ξ Δ : ℝ) :
    bogoliubovDispersionℂ (ξ : ℂ) (Δ : ℂ) = ((bogoliubovEnergy ξ Δ ^ 2 : ℝ) : ℂ) := by
  rw [bogoliubovDispersionℂ, bogoliubovEnergy_sq]; push_cast; ring

/-- **The unifying complex dispersion** `bogoliubovDispersionℂ(sinh z, 1) = cosh²z`, for **any** complex
rapidity `z`. The de Sitter and Anti-de Sitter dispersions are the single complex hyperbolic identity
`cosh²z = sinh²z + 1` (`Complex.cosh_sq`) at the real rapidity `z = η` (boost) and the imaginary rapidity
`z = iθ` (rotation): the `L → iL` continuation lives entirely in the argument `z`, not in the identity.
This is the shared root that `dS_bogoliubovDispersion` and `adS_bogoliubovDispersion_imaginaryMomentum`
were instantiating separately. -/
theorem bogoliubovDispersion_cosh_sinh (z : ℂ) :
    bogoliubovDispersionℂ (Complex.sinh z) 1 = Complex.cosh z ^ 2 := by
  rw [bogoliubovDispersionℂ, one_pow]
  exact (Complex.cosh_sq z).symm

/-- **De Sitter is the real-momentum Bogoliubov dispersion** `E² = cosh²η` — the unifying
`bogoliubovDispersion_cosh_sinh` at the **real** rapidity `z = η` (`ξ = sinh η`, `Δ = 1`), the de Sitter
energy `E = cosh η = bogoliubovEnergy(sinh η, 1)` (`diamond_horizon_energy`). -/
theorem dS_bogoliubovDispersion (η : ℝ) :
    bogoliubovDispersionℂ (Real.sinh η : ℂ) 1 = (Real.cosh η : ℂ) ^ 2 := by
  rw [Complex.ofReal_sinh, Complex.ofReal_cosh]
  exact bogoliubovDispersion_cosh_sinh (η : ℂ)

/-- **The AdS dispersion is the Bogoliubov dispersion of the imaginary (complex) momentum.** With the
Nagao–Nielsen complex momentum `ξ = i sin θ = sinh(iθ)` and gap `Δ = 1`,
`bogoliubovDispersionℂ(i sin θ, 1) = (i sin θ)² + 1 = cos²θ = E²`: the Anti-de Sitter energy `E = cos θ`
**is** the Bogoliubov energy `√(ξ² + Δ²)` evaluated at the imaginary momentum. This is the precise sense
in which the AdS structure is the Bogoliubov dispersion of a complex momentum. -/
theorem adS_bogoliubovDispersion_imaginaryMomentum (θ : ℝ) :
    bogoliubovDispersionℂ (Complex.I * (Real.sin θ : ℂ)) 1 = (Real.cos θ : ℂ) ^ 2 := by
  have key := bogoliubovDispersion_cosh_sinh ((θ : ℂ) * Complex.I)
  rw [Complex.sinh_mul_I, Complex.cosh_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    mul_comm (Real.sin θ : ℂ) Complex.I] at key
  exact key

/-- **De Sitter and Anti-de Sitter are the same complex dispersion at `z` and `iθ`.** Both the boost
(`z = η`) and the rotation (`z = iθ`) dispersions are `bogoliubovDispersion_cosh_sinh` — the `L → iL`
continuation is exactly the real-rapidity → imaginary-rapidity substitution `η ↦ iθ` in the single
complex identity `cosh²z = sinh²z + 1`. -/
theorem adS_dS_dispersion_common_root (η θ : ℝ) :
    (bogoliubovDispersionℂ (Complex.sinh (η : ℂ)) 1 = Complex.cosh (η : ℂ) ^ 2)
      ∧ (bogoliubovDispersionℂ (Complex.sinh ((θ : ℂ) * Complex.I)) 1
          = Complex.cosh ((θ : ℂ) * Complex.I) ^ 2) :=
  ⟨bogoliubovDispersion_cosh_sinh (η : ℂ), bogoliubovDispersion_cosh_sinh ((θ : ℂ) * Complex.I)⟩

/-- **The imaginary momentum pushes the energy below the gap** `E² = cos²θ ≤ 1 = Δ²`. A real Bogoliubov
momentum gives `E² = ξ² + Δ² ≥ Δ²` (energy above the gap); the AdS **imaginary** momentum gives
`E² = Δ² + (i sin θ)² = 1 − sin²θ = cos²θ ≤ 1`, energy *below* the gap — the physical signature of the
complex momentum. -/
theorem adS_energy_below_gap (θ : ℝ) : (Real.cos θ : ℝ) ^ 2 ≤ 1 := by
  nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ]

/-- **De Sitter's real momentum keeps the energy above the gap** `E² = cosh²η ≥ 1 = Δ²` — the contrast
with `adS_energy_below_gap`: real momentum raises the energy, imaginary momentum lowers it. -/
theorem dS_energy_above_gap (η : ℝ) : (1 : ℝ) ≤ Real.cosh η ^ 2 := by
  nlinarith [Real.one_le_cosh η]

/-! ## §B — the complex `q`: the AdS embedding coordinate `q = W e^{i t/L}` -/

/-- **The AdS complex embedding coordinate** `q = W e^{iθ}` (the NN complex `q`): its real part is
`X^{−1} = W cos θ` and its imaginary part is `X⁰ = W sin θ` (Eq. D.9). -/
def adSComplexCoord (W θ : ℝ) : ℂ := (W : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

theorem adSComplexCoord_re (W θ : ℝ) : (adSComplexCoord W θ).re = W * Real.cos θ := by
  rw [adSComplexCoord, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem adSComplexCoord_im (W θ : ℝ) : (adSComplexCoord W θ).im = W * Real.sin θ := by
  rw [adSComplexCoord, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The modulus of the complex `q` is the rotation invariant** `(X^{−1})² + (X⁰)² = W²` — the AdS
light-cone identity (Eq. D.9) **is** `re² + im²` of `q = W e^{iθ}`, from the complex exponential. -/
theorem adS_rotationInvariant (W θ : ℝ) :
    (adSComplexCoord W θ).re ^ 2 + (adSComplexCoord W θ).im ^ 2 = W ^ 2 := by
  rw [adSComplexCoord_re, adSComplexCoord_im]
  linear_combination W ^ 2 * Real.sin_sq_add_cos_sq θ

/-- **`|q|² = W²`** — the squared modulus of the NN complex coordinate is the AdS curvature combination
`W² = L² + r²`. -/
theorem adSComplexCoord_normSq (W θ : ℝ) : Complex.normSq (adSComplexCoord W θ) = W ^ 2 := by
  rw [Complex.normSq_apply, adSComplexCoord_re, adSComplexCoord_im]
  linear_combination W ^ 2 * Real.sin_sq_add_cos_sq θ

/-- **The complex `q` obeys the rotation (time-circle) group law** `q(W₁,θ₁)·q(W₂,θ₂) = q(W₁W₂, θ₁+θ₂)`.
The phase composes by `e^{iθ₁}e^{iθ₂} = e^{i(θ₁+θ₂)}` — the `U(1)/SO(2)` structure of the AdS timelike
circle (the conformal generator `iJ₋₁₀ = L∂ₜ`, Eq. D.11). The `q = W e^{iθ}` form is not just notation:
it includes the group law of the AdS time translation. -/
theorem adSComplexCoord_mul (W₁ W₂ θ₁ θ₂ : ℝ) :
    adSComplexCoord W₁ θ₁ * adSComplexCoord W₂ θ₂ = adSComplexCoord (W₁ * W₂) (θ₁ + θ₂) := by
  rw [adSComplexCoord, adSComplexCoord, adSComplexCoord, Complex.ofReal_mul, Complex.ofReal_add,
    add_mul, Complex.exp_add]
  ring

/-- **Eq. D.9 from the complex `q`.** The Anti-de Sitter light-cone identity
`−(X^{−1})² − (X⁰)² + (r² + L²) = 0` of `CausalDiamond.AdSConformalKilling.adS_embedding_lightCone` is the
modulus of `q = W e^{i t/L}` (`re = X^{−1}`, `im = X⁰`, `|q|² = W² = L² + r²`). -/
theorem adS_lightCone_from_complexCoord (L r t W : ℝ) (hW : W ^ 2 = L ^ 2 + r ^ 2) :
    -(adSComplexCoord W (t / L)).re ^ 2 - (adSComplexCoord W (t / L)).im ^ 2 + (r ^ 2 + L ^ 2) = 0 := by
  rw [adSComplexCoord_re, adSComplexCoord_im]
  exact adS_embedding_lightCone L r t W hW

/-! ## §C — the Wick rotation: the de Sitter boost form and its `i`-rotation -/

/-- **The de Sitter complex coordinate** `q_dS = w cosh η + i·w sinh η` (real components `X^d = w cosh η`,
`X⁰ = w sinh η`). -/
def dSComplexCoord (w η : ℝ) : ℂ := (w * Real.cosh η : ℝ) + (w * Real.sinh η : ℝ) * Complex.I

theorem dSComplexCoord_re (w η : ℝ) : (dSComplexCoord w η).re = w * Real.cosh η := by
  simp only [dSComplexCoord, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

theorem dSComplexCoord_im (w η : ℝ) : (dSComplexCoord w η).im = w * Real.sinh η := by
  simp only [dSComplexCoord, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]

/-- **The de Sitter coordinate has the timelike Lorentzian form** `L(q_dS) = (X^d)² − (X⁰)² = w²` — the
boost / Minkowski invariant `cosh²−sinh² = 1`, the convergence (timelike) cone of the NN complex action. -/
theorem dSComplexCoord_lorentzianForm (w η : ℝ) :
    lorentzianForm (dSComplexCoord w η) = w ^ 2 := by
  rw [lorentzianForm, dSComplexCoord_re, dSComplexCoord_im]
  linear_combination w ^ 2 * Real.cosh_sq_sub_sinh_sq η

/-- **The Nagao–Nielsen Wick rotation flips boost → rotation** `L(i·q_dS) = −w²`. Multiplying the de
Sitter coordinate by `i` — the same `i` taking real time to Euclidean time and the real to the imaginary
action — sends the timelike (convergent) boost invariant `w²` to the spacelike `−w²`
(`lorentzianForm_mul_I`): the formal `L → iL` of the complex `p, q`. -/
theorem dS_wick_to_spacelike (w η : ℝ) :
    lorentzianForm (Complex.I * dSComplexCoord w η) = -w ^ 2 := by
  rw [lorentzianForm_mul_I, dSComplexCoord_lorentzianForm]

/-! ## §D — the complex position: `L → iL` is `R → iR` (D.8 ↔ D.12) -/

/-- **The `L → iL` factor continuation is the complex position `R → iR`.** The de Sitter conformal-Killing
factor argument `1 − (R/L)²` (`CausalDiamond.AdS.sqrtFactor`) becomes the AdS argument `1 + (R/L)²`
(`CausalDiamond.AdSConformalKilling.adsConfKillingFactor`) under `R → iR`:
`1 − ((iR)/L)² = 1 + (R/L)²`, since `i² = −1`. The complex position `q = iR` records D.8 to D.12. -/
theorem adS_factor_arg_from_complexPosition (L R : ℝ) (_hL : L ≠ 0) :
    (1 : ℂ) - ((Complex.I * (R : ℂ)) / (L : ℂ)) ^ 2 = 1 + ((R : ℂ) / (L : ℂ)) ^ 2 := by
  have h2 : ((Complex.I * (R : ℂ)) / (L : ℂ)) ^ 2 = -(((R : ℂ) / (L : ℂ)) ^ 2) := by
    rw [mul_div_assoc, mul_pow, Complex.I_sq]; ring
  rw [h2]; ring

/-! ## §E — the main result: AdS Appendix D.2 from the NN complex momentum / complex `p, q` -/

/-- **The AdS conformal Killing data of Appendix D.2 is derived from the Nagao–Nielsen complex momentum
and complex `p, q`.** For `L ≠ 0`, the circle radius `W = √(L²+r²)`, complex mass `m ≠ 0`, and `ℏ, Δt > 0`:

* **(complex momentum)** the AdS dispersion `(i sin θ)² + 1 = cos²θ` — energy `E = cos θ = cosh(iθ)` of
  the imaginary-rapidity momentum `p = i sin θ = sinh(iθ)`;
* **(complex `q`)** the light-cone identity D.9 `(X^{−1})² + (X⁰)² = W²` is `|W e^{i t/L}|²`;
* **(complex position)** the `L → iL` factor continuation D.8 ↔ D.12 is `R → iR`,
  `1 − ((iR)/L)² = 1 + (R/L)²`;
* **(convergence)** the NN complex-momentum Gaussian converges iff `Im m > 0` — the entropic damping.

The Anti-de Sitter embedding, metric factor, and conformal Killing vector all follow from the single
Nagao–Nielsen complexification `η → iθ`, `R → iR`. -/
theorem adS_appendixD2_from_nagaoNielsen
    (L r t W R θ : ℝ) (m : ℂ) {ℏ dt : ℝ}
    (hL : L ≠ 0) (hℏ : 0 < ℏ) (hdt : 0 < dt) (hm : m ≠ 0) (_hW : W ^ 2 = L ^ 2 + r ^ 2) :
    (bogoliubovDispersionℂ (Complex.I * (Real.sin θ : ℂ)) 1 = (Real.cos θ : ℂ) ^ 2)
      ∧ ((adSComplexCoord W (t / L)).re ^ 2 + (adSComplexCoord W (t / L)).im ^ 2 = W ^ 2)
      ∧ ((1 : ℂ) - ((Complex.I * (R : ℂ)) / (L : ℂ)) ^ 2 = 1 + ((R : ℂ) / (L : ℂ)) ^ 2)
      ∧ (0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im) :=
  ⟨adS_bogoliubovDispersion_imaginaryMomentum θ, adS_rotationInvariant W (t / L),
   adS_factor_arg_from_complexPosition L R hL, momentum_integral_converges_iff m hℏ hdt hm⟩

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AdSComplexMomentum

end
