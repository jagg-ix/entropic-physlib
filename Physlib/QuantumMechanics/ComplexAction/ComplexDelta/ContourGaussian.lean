/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourShift
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Contour independence for the Gaussian, by direct evaluation (proving the DUI route)

`ComplexDelta.ContourShift` reduced the general-`f` contour identity to differentiation
under the integral sign (`hdui`). For the **Gaussian class** `h(z) = e^{−c z²}` (`c > 0`),
which is the complex-action regularised delta `δ_c^ε` up to the constant prefactor `√(1/4πε)`
(`c = 1/4ε`), that hypothesis is unnecessary: the contour integral can be **evaluated in
closed form** and is a manifestly `θ`-independent constant.

* `gaussH` — the Gaussian `h(z) = e^{−c z²}`.
* `gaussianContourIntegral` — **`∫ contourIntegrand (gaussH c) θ = √(π/c)`** for every
  permitted ray `|θ| < π/4`: the rotation phase `e^{iθ}` and the principal root
  `(π/b)^{1/2} = √(π/c)·e^{−iθ}` cancel (the same mechanism as
  `ComplexDelta.Contour.contour_normalization`, here without the `δ_c^ε` prefactor).
* `gaussianContourIntegral_indep` — **contour independence**: the integral is the same at
  any two permitted angles. This is `hdui`'s intended conclusion, obtained directly.

So for the physically central Gaussian weight, the contour identity `∫_γ = ∫_ℝ` holds
*unconditionally* — no differentiation under the integral needed. `hdui` is only required
for general entire `f` whose integral is not evaluable in closed form; there the uniform
Gaussian domination of `ComplexDelta.ContourShift.contourDeriv` (a polynomial × Gaussian
envelope, finite because `cos 2θ` is bounded below on a sub-cone) feeds Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

Reference: K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor.
Phys. **126**(6) (2011) 1021–1049, §2.5, doi:10.1143/PTP.126.1021.
-/

set_option autoImplicit false

open Real Complex MeasureTheory
open scoped Real

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourGaussian

open ComplexDelta.ContourShift

/-- **The Gaussian** `h(z) = e^{−c z²}` (the complex-action delta `δ_c^ε` up to the prefactor, with
`c = 1/4ε`). -/
noncomputable def gaussH (c : ℝ) (z : ℂ) : ℂ := Complex.exp (-(c : ℂ) * z ^ 2)

/-- **The Gaussian contour integral is the constant `√(π/c)`** along every permitted ray
`|θ| < π/4`. Direct evaluation via `integral_gaussian_complex`: the rotation phase and the
principal square root of `π/b` cancel exactly. -/
theorem gaussianContourIntegral {c θ : ℝ} (hc : 0 < c) (hθ : |θ| < π / 4) :
    ∫ s : ℝ, contourIntegrand (gaussH c) θ s = (Real.sqrt (π / c) : ℂ) := by
  rw [abs_lt] at hθ
  obtain ⟨hθ1, hθ2⟩ := hθ
  have hcosθ : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcos2 : 0 < Real.cos (2 * θ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  set b : ℂ := (c : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) with hb_def
  have hbre : 0 < b.re := by
    rw [hb_def, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]; exact mul_pos hc hcos2
  have hE : Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hb_ne : b ≠ 0 := by
    rw [hb_def]; exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne') hE
  have hsq : Complex.exp ((θ : ℂ) * Complex.I) ^ 2
      = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
    rw [sq, ← Complex.exp_add]; congr 1; push_cast; ring
  -- integrand = e^{iθ}·cexp(-b s²)
  have hint : ∀ s : ℝ, contourIntegrand (gaussH c) θ s
      = Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-b * (s : ℂ) ^ 2) := by
    intro s
    have harg : -(c : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * (s : ℂ)) ^ 2
        = -b * (s : ℂ) ^ 2 := by rw [hb_def, mul_pow, hsq]; ring
    simp only [contourIntegrand, gaussH]
    rw [harg, mul_comm]
  simp_rw [hint]
  rw [integral_const_mul, integral_gaussian_complex hbre]
  -- (π/b)^{1/2} = √(π/c)·e^{-iθ}
  have hexp2 : Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) ^ 2 =
      (Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I))⁻¹ := by
    rw [sq, ← Complex.exp_add, ← Complex.exp_neg]; congr 1; push_cast; ring
  have hpb : (↑π / b) =
      (↑(Real.sqrt (π / c)) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)) ^ 2 := by
    rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ π / c),
      hexp2, hb_def, div_eq_iff hb_ne, mul_mul_mul_comm, inv_mul_cancel₀ hE, mul_one,
      ← Complex.ofReal_mul]
    congr 1; field_simp
  have hReζ : 0 < (↑(Real.sqrt (π / c)) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)).re := by
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    exact mul_pos (Real.sqrt_pos.2 (by positivity)) hcosθ
  have hζ : (↑π / b) ^ (1 / 2 : ℂ)
      = ↑(Real.sqrt (π / c)) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
    rw [show (1 / 2 : ℂ) = (2⁻¹ : ℂ) by norm_num, hpb]
    exact sq_cpow_two_inv hReζ
  rw [hζ]
  -- phase cancels: e^{iθ}·√(π/c)·e^{-iθ} = √(π/c)
  rw [show Complex.exp ((θ : ℂ) * Complex.I) *
        (↑(Real.sqrt (π / c)) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I))
      = ↑(Real.sqrt (π / c)) *
        (Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)) by ring,
    ← Complex.exp_add,
    show (θ : ℂ) * Complex.I + ((-θ : ℝ) : ℂ) * Complex.I = 0 by push_cast; ring,
    Complex.exp_zero, mul_one]

/-- **Contour independence of the Gaussian integral** (the conclusion `hdui` was meant to
provide, obtained directly): the contour integral is the same at any two permitted angles
`|θ₀|, |θ₁| < π/4`. -/
theorem gaussianContourIntegral_indep {c θ₀ θ₁ : ℝ} (hc : 0 < c)
    (h0 : |θ₀| < π / 4) (h1 : |θ₁| < π / 4) :
    ∫ s : ℝ, contourIntegrand (gaussH c) θ₀ s = ∫ s : ℝ, contourIntegrand (gaussH c) θ₁ s := by
  rw [gaussianContourIntegral hc h0, gaussianContourIntegral hc h1]

end Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourGaussian

end
