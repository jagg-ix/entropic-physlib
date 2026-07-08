/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The complex-action delta along complex-contour permitted paths (Nagao–Nielsen §2.5)

`ComplexDelta.Identity` proved Eq. 2.30 (`∫ f·δ_c = f(0)`) on the **real axis**, the
trivial permitted path. Nagao–Nielsen's construction is more general: the regularised
delta `δ_c^ε(q) = √(1/4πε)·e^{−q²/4ε}` is integrated along any *permitted path* — a
contour staying inside the convergence cone `L(q) = (Re q)² − (Im q)² > 0` (Eq. 2.29).
This file formalizes the **contour/principal-value content** for the canonical family of
permitted paths: the straight rays `q = e^{iθ}·s`, `s ∈ ℝ`.

The point of a *permitted* path is that the delta's defining property — its normalization
`∫ δ_c = 1` — is **contour-independent**: it gives the same value `1` along every
permitted ray, even though the integrand is now a complex (oscillatory) Gaussian. That is
the genuine analytic content, and it is what this file proves.

* `rayDir_re`, `rayDir_im`, `lorentzianForm_rayDir` — the ray direction `e^{iθ}` has
 `L(e^{iθ}) = cos 2θ`, tying "permitted" to the timelike cone of `ComplexDelta.Convergence`.
* `gaussianCoeff_re_pos` — along a permitted ray `|θ| < π/4`, the rotated Gaussian
 coefficient `b = e^{2iθ}/4ε` has `Re b = cos(2θ)/4ε > 0`: the complex Gaussian still
 converges (Mathlib's `integral_gaussian_complex` applies). This is exactly the cone
 `cos 2θ > 0`.
* `contour_normalization` — **`∫ δ_c^ε(e^{iθ}s)·e^{iθ} ds = 1`** for `|θ| < π/4`: the complex-action
 delta normalizes to `1` along every permitted ray, independent of the contour angle.
 This is Eq. 2.30 for `f ≡ 1` along the complex contour, the foundational
 contour-independence underlying the principal-value definition. The proof rotates the
 real Gaussian normalization through `integral_gaussian_complex`, with the principal
 branch `(π/b)^{1/2}` resolved by `sq_cpow_two_inv` on the right half-plane (where the
 permitted cone `cos θ > 0` lands the contributing square root).

scope: this is the `f ≡ 1` contour identity (contour independence of the
normalization). The general-`f` contour identity reduces — for `f` *entire* — to the
real-axis `tendsto_integral_deltaEps_smul` by Cauchy's theorem (deforming the ray to the
real axis, the integrand being holomorphic and Gaussian-decaying in the sector); that
deformation, with its arc-at-infinity estimate, is a further analysis step not done here.

Reference: K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor.
Phys. **126**(6) (2011) 1021–1049, §2.5, Eqs. (2.28)–(2.30), doi:10.1143/PTP.126.1021.
-/

set_option autoImplicit false

open Real Complex MeasureTheory
open scoped Real

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour

open ComplexDelta.Convergence

/-- **The complex-action regularised delta for complex argument** (Nagao–Nielsen Eq. 2.28):
`δ_c^ε(q) = √(1/4πε)·e^{−q²/4ε}`, now as a function of `q ∈ ℂ`. -/
noncomputable def deltaEpsC (ε : ℝ) (q : ℂ) : ℂ :=
  (Real.sqrt (1 / (4 * π * ε)) : ℂ) * Complex.exp (-q ^ 2 / (4 * ε))

/-! ## The ray direction and the convergence cone -/

@[simp] theorem rayDir_re (θ : ℝ) : (Complex.exp (θ * Complex.I)).re = Real.cos θ :=
  Complex.exp_ofReal_mul_I_re θ

@[simp] theorem rayDir_im (θ : ℝ) : (Complex.exp (θ * Complex.I)).im = Real.sin θ :=
  Complex.exp_ofReal_mul_I_im θ

/-- **`L(e^{iθ}) = cos 2θ`.** The Lorentzian (convergence) form of `ComplexDelta.Convergence`
evaluated on the ray direction is `cos 2θ`, so a ray is permitted (`L > 0`) exactly when
`cos 2θ > 0`, i.e. `|θ| < π/4` — the timelike cone around the real axis. -/
theorem lorentzianForm_rayDir (θ : ℝ) :
    lorentzianForm (Complex.exp (θ * Complex.I)) = Real.cos (2 * θ) := by
  rw [lorentzianForm, rayDir_re, rayDir_im, Real.cos_two_mul, Real.sin_sq]; ring

/-! ## The rotated Gaussian still converges on the permitted cone -/

/-- **`Re(e^{2iθ}/4ε) = cos(2θ)/4ε > 0`** for `ε > 0` and `cos 2θ > 0`. The coefficient of
the rotated complex Gaussian has positive real part exactly on the permitted cone, so
`integral_gaussian_complex` applies. -/
theorem gaussianCoeff_re_pos {θ ε : ℝ} (hε : 0 < ε) (hcos : 0 < Real.cos (2 * θ)) :
    0 < ((↑(1 / (4 * ε)) : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)).re := by
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  exact mul_pos (by positivity) hcos

/-! ## Contour independence of the normalization -/

/-- **`∫ δ_c^ε(e^{iθ}s)·e^{iθ} ds = 1`** for every permitted ray `|θ| < π/4`
(Nagao–Nielsen Eq. 2.30, `f ≡ 1`, complex contour). The complex-action delta normalizes to `1`
independently of the contour angle: rotating the real Gaussian normalization through
`integral_gaussian_complex`, the rotation phase `e^{iθ}` and the principal square root
`(π/b)^{1/2} = √(4πε)·e^{−iθ}` cancel exactly. -/
theorem contour_normalization {θ ε : ℝ} (hε : 0 < ε) (hθ : |θ| < π / 4) :
    ∫ s : ℝ, deltaEpsC ε (Complex.exp (θ * Complex.I) * s) * Complex.exp (θ * Complex.I)
      = 1 := by
  rw [abs_lt] at hθ
  obtain ⟨hθ1, hθ2⟩ := hθ
  have hcosθ : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcos2 : 0 < Real.cos (2 * θ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  set w : ℂ := Complex.exp (θ * Complex.I) with hw
  set b : ℂ := (↑(1 / (4 * ε)) : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) with hb_def
  have hbre : 0 < b.re := gaussianCoeff_re_pos hε hcos2
  have hE : Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hb_ne : b ≠ 0 := by
    rw [hb_def]; exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) hE
  -- the integrand is a constant times the rotated complex Gaussian `e^{-b s²}`
  have hsq : w ^ 2 = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
    rw [hw, sq, ← Complex.exp_add]; congr 1; push_cast; ring
  have hint : ∀ s : ℝ, deltaEpsC ε (w * (s : ℂ)) * w
      = (↑(Real.sqrt (1 / (4 * π * ε))) * w) * Complex.exp (-b * (s : ℂ) ^ 2) := by
    intro s
    have harg : -(w * (s : ℂ)) ^ 2 / (4 * ε) = -b * (s : ℂ) ^ 2 := by
      rw [hb_def, mul_pow, hsq]; push_cast; ring
    rw [deltaEpsC, harg, mul_right_comm]
  -- rotate the real Gaussian normalization
  simp_rw [hint]
  rw [integral_const_mul, integral_gaussian_complex hbre]
  -- resolve the principal square root `(π/b)^{1/2} = √(4πε)·e^{-iθ}`
  have hexp2 : Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) ^ 2 =
      (Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I))⁻¹ := by
    rw [sq, ← Complex.exp_add, ← Complex.exp_neg]; congr 1; push_cast; ring
  have hpb : (↑π / b) =
      (↑(Real.sqrt (4 * π * ε)) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)) ^ 2 := by
    rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 4 * π * ε),
      hexp2, hb_def, div_eq_iff hb_ne, mul_mul_mul_comm, inv_mul_cancel₀ hE, mul_one,
      ← Complex.ofReal_mul]
    congr 1; field_simp
  have hReζ : 0 < (↑(Real.sqrt (4 * π * ε)) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)).re := by
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    exact mul_pos (Real.sqrt_pos.2 (by positivity)) hcosθ
  have hζ : (↑π / b) ^ (1 / 2 : ℂ)
      = ↑(Real.sqrt (4 * π * ε)) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
    rw [show (1 / 2 : ℂ) = (2⁻¹ : ℂ) by norm_num, hpb]
    exact sq_cpow_two_inv hReζ
  -- assemble: √(1/4πε)·√(4πε)·(e^{iθ}·e^{-iθ}) = 1
  rw [hζ, hw]
  have hww : Complex.exp (↑θ * Complex.I) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add,
      show (↑θ * Complex.I + ((-θ : ℝ) : ℂ) * Complex.I) = 0 by push_cast; ring,
      Complex.exp_zero]
  calc (↑(Real.sqrt (1 / (4 * π * ε))) * Complex.exp (↑θ * Complex.I)) *
        (↑(Real.sqrt (4 * π * ε)) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I))
      = (↑(Real.sqrt (1 / (4 * π * ε))) * ↑(Real.sqrt (4 * π * ε))) *
          (Complex.exp (↑θ * Complex.I) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)) := by ring
    _ = ↑(Real.sqrt (1 / (4 * π * ε)) * Real.sqrt (4 * π * ε)) * 1 := by
          rw [hww, Complex.ofReal_mul]
    _ = 1 := by
          rw [mul_one, ← Real.sqrt_mul (by positivity),
            show 1 / (4 * π * ε) * (4 * π * ε) = 1 by
              have := Real.pi_ne_zero; field_simp,
            Real.sqrt_one, Complex.ofReal_one]

end Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour

end
