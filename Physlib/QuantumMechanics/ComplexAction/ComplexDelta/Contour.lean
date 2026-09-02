/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.MeanValue

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
* `pi_div_rotated_cpow_half` — the principal square root `(π/(r·e^{2iθ}))^{1/2} = √(π/r)·e^{−iθ}`
  on the cone `cos θ > 0`, shared with `ComplexDelta.ContourGaussian`.
* `contour_normalization` — **`∫ δ_c^ε(e^{iθ}s)·e^{iθ} ds = 1`** for `|θ| < π/4`: the complex-action
  delta normalizes to `1` along every permitted ray, independent of the contour angle.
  This is Eq. 2.30 for `f ≡ 1` along the complex contour, the foundational
  contour-independence underlying the principal-value definition. The proof rotates the
  real Gaussian normalization through `integral_gaussian_complex`, with the principal
  branch `(π/b)^{1/2}` resolved by `sq_cpow_two_inv` on the right half-plane (where the
  permitted cone `cos θ > 0` lands the contributing square root).

Scope: this is the `f ≡ 1` contour identity (contour independence of the normalization).
The general-`f` contour identity reduces — for `f` *entire* — to the
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

@[simp] lemma rayDir_re (θ : ℝ) : (Complex.exp (θ * Complex.I)).re = Real.cos θ :=
  Complex.exp_ofReal_mul_I_re θ

@[simp] lemma rayDir_im (θ : ℝ) : (Complex.exp (θ * Complex.I)).im = Real.sin θ :=
  Complex.exp_ofReal_mul_I_im θ

/-- **`L(e^{iθ}) = cos 2θ`.** The Lorentzian (convergence) form of `ComplexDelta.Convergence`
evaluated on the ray direction is `cos 2θ`, so a ray is permitted (`L > 0`) exactly when
`cos 2θ > 0`, i.e. `|θ| < π/4` — the timelike cone around the real axis. -/
lemma lorentzianForm_rayDir (θ : ℝ) :
    lorentzianForm (Complex.exp (θ * Complex.I)) = Real.cos (2 * θ) := by
  rw [lorentzianForm, rayDir_re, rayDir_im, Real.cos_two_mul, Real.sin_sq]; ring

/-! ## The rotated Gaussian still converges on the permitted cone -/

/-- **`Re(e^{2iθ}/4ε) = cos(2θ)/4ε > 0`** for `ε > 0` and `cos 2θ > 0`. The coefficient of
the rotated complex Gaussian has positive real part exactly on the permitted cone, so
`integral_gaussian_complex` applies. -/
lemma gaussianCoeff_re_pos {θ ε : ℝ} (hε : 0 < ε) (hcos : 0 < Real.cos (2 * θ)) :
    0 < ((↑(1 / (4 * ε)) : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)).re := by
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  exact mul_pos (by positivity) hcos

/-! ## The principal square root on the permitted cone -/

/-- **`(π/(r·e^{2iθ}))^{1/2} = √(π/r)·e^{−iθ}`** for `r > 0` and `cos θ > 0`: the principal square
root of `π` over the rotated Gaussian coefficient. On the permitted cone the contributing root
`√(π/r)·e^{−iθ}` lies in the right half-plane, so the principal branch selects it
(`sq_cpow_two_inv`). Shared by `contour_normalization` and
`ComplexDelta.ContourGaussian.gaussianContourIntegral`. -/
lemma pi_div_rotated_cpow_half {r θ : ℝ} (hr : 0 < r) (hcosθ : 0 < Real.cos θ) :
    ((π : ℂ) / ((r : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I))) ^ (1 / 2 : ℂ)
      = (Real.sqrt (π / r) : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
  have hrne : r ≠ 0 := hr.ne'
  have hE : Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hb_ne : (r : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hrne) hE
  have hexp2 : Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) ^ 2 =
      (Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I))⁻¹ := by
    rw [sq, ← Complex.exp_add, ← Complex.exp_neg]; congr 1; push_cast; ring
  have hpb : ((π : ℂ) / ((r : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I))) =
      (↑(Real.sqrt (π / r)) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)) ^ 2 := by
    rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ π / r),
      hexp2, div_eq_iff hb_ne, mul_mul_mul_comm, inv_mul_cancel₀ hE, mul_one,
      ← Complex.ofReal_mul]
    congr 1; field_simp
  have hReζ : 0 < (↑(Real.sqrt (π / r)) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)).re := by
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    exact mul_pos (Real.sqrt_pos.2 (by positivity)) hcosθ
  rw [show (1 / 2 : ℂ) = (2⁻¹ : ℂ) by norm_num, hpb]
  exact sq_cpow_two_inv hReζ

/-! ## Contour independence of the normalization -/

/-- **`∫ δ_c^ε(e^{iθ}s)·e^{iθ} ds = 1`** for every permitted ray `|θ| < π/4`
(Nagao–Nielsen Eq. 2.30, `f ≡ 1`, complex contour). The complex-action delta normalizes to `1`
independently of the contour angle: rotating the real Gaussian normalization through
`integral_gaussian_complex`, the rotation phase `e^{iθ}` and the principal square root
`(π/b)^{1/2} = √(4πε)·e^{−iθ}` cancel exactly. -/
lemma contour_normalization {θ ε : ℝ} (hε : 0 < ε) (hθ : |θ| < π / 4) :
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
  -- resolve the principal square root `(π/b)^{1/2} = √(4πε)·e^{-iθ}` on the permitted cone
  have hζ : (↑π / b) ^ (1 / 2 : ℂ)
      = ↑(Real.sqrt (4 * π * ε)) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
    rw [hb_def, show (4 : ℝ) * π * ε = π / (1 / (4 * ε)) by
      rw [div_div_eq_mul_div, div_one]; ring]
    exact pi_div_rotated_cpow_half (by positivity) hcosθ
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

/-! ## Contour rotation as an exact derivative -/

namespace Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourShift

variable {h h' : ℂ → ℂ}

/-- The contour integrand along the ray `q = e^{iθ}·s`: `Φ(θ,s) = h(e^{iθ}s)·e^{iθ}`
(the `e^{iθ}` is the Jacobian `dq/ds`). -/
noncomputable def contourIntegrand (h : ℂ → ℂ) (θ s : ℝ) : ℂ :=
  h (Complex.exp (θ * Complex.I) * s) * Complex.exp (θ * Complex.I)

/-- The `s`-primitive whose derivative is `∂_θ Φ`: `i·e^{iθ}·s·h(e^{iθ}s)`. -/
noncomputable def contourPrimitive (h : ℂ → ℂ) (θ s : ℝ) : ℂ :=
  Complex.I * Complex.exp (θ * Complex.I) * (s * h (Complex.exp (θ * Complex.I) * s))

/-- The common derivative value `∂_θ Φ = ∂_s (contourPrimitive)`:
`i·e^{iθ}·(h(e^{iθ}s) + s·e^{iθ}·h'(e^{iθ}s))`. -/
noncomputable def contourDeriv (h h' : ℂ → ℂ) (θ s : ℝ) : ℂ :=
  Complex.I * Complex.exp (θ * Complex.I) *
    (h (Complex.exp (θ * Complex.I) * s) +
      s * Complex.exp (θ * Complex.I) * h' (Complex.exp (θ * Complex.I) * s))

/-- `d/dθ e^{iθ} = i·e^{iθ}`. -/
lemma hasDerivAt_rayDir (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Complex.exp (θ * Complex.I)) (Complex.exp (θ * Complex.I) * Complex.I) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * Complex.I) Complex.I θ := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I
  simpa using h1.cexp

/-- **The `θ`-derivative of the contour integrand**: `∂_θ Φ(θ,s) = contourDeriv θ s`. -/
lemma hasDerivAt_contourIntegrand_theta (hh : ∀ z, HasDerivAt h (h' z) z) (θ s : ℝ) :
    HasDerivAt (fun θ : ℝ => contourIntegrand h θ s) (contourDeriv h h' θ s) θ := by
  simp only [contourIntegrand]
  have he := hasDerivAt_rayDir θ
  have hu : HasDerivAt (fun θ : ℝ => Complex.exp (θ * Complex.I) * (s : ℂ))
      (Complex.exp (θ * Complex.I) * Complex.I * s) θ := he.mul_const _
  have hcomp := (hh (Complex.exp (θ * Complex.I) * s)).comp θ hu
  have raw := hcomp.mul he
  exact raw.congr_deriv (by simp only [contourDeriv, Function.comp_apply]; ring)

/-- **The exact-derivative identity**: `∂_s (i·e^{iθ}·s·h(e^{iθ}s)) = contourDeriv θ s` —
the *same* value as `∂_θ Φ`. This is the Cauchy-Riemann structure that makes rotating the
contour an exact differential. -/
lemma hasDerivAt_contourPrimitive_s (hh : ∀ z, HasDerivAt h (h' z) z) (θ s : ℝ) :
    HasDerivAt (fun s : ℝ => contourPrimitive h θ s) (contourDeriv h h' θ s) s := by
  simp only [contourPrimitive]
  have hs : HasDerivAt (fun s : ℝ => Complex.exp (θ * Complex.I) * (s : ℂ))
      (Complex.exp (θ * Complex.I)) s := by
    exact ((Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (Complex.exp (θ * Complex.I))).congr_deriv (by simp)
  have hsid : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
    exact (Complex.ofRealCLM.hasDerivAt (x := s)).congr_deriv (by simp)
  have hcomp := (hh (Complex.exp (θ * Complex.I) * s)).comp s hs
  have raw := (hsid.mul hcomp).const_mul (Complex.I * Complex.exp (θ * Complex.I))
  exact raw.congr_deriv (by simp only [contourDeriv, Function.comp_apply]; ring)

/-- **Infinitesimal contour independence**: `∫_ℝ contourDeriv θ s ds = 0`. The
derivative-in-`θ` of the contour-integral integrand integrates to zero (the boundary
terms of the exact `s`-primitive vanish), so rotating a permitted contour does not change
the integral to first order. Requires the primitive and the derivative to be integrable. -/
lemma integral_contourDeriv_eq_zero (hh : ∀ z, HasDerivAt h (h' z) z) (θ : ℝ)
    (hP : Integrable (fun s : ℝ => contourPrimitive h θ s))
    (hD : Integrable (fun s : ℝ => contourDeriv h h' θ s)) :
    ∫ s : ℝ, contourDeriv h h' θ s = 0 :=
  integral_eq_zero_of_hasDerivAt_of_integrable
    (fun s => hasDerivAt_contourPrimitive_s hh θ s) hD hP

/-- **The contour integral is constant in the permitted angle.** If differentiation under
the integral holds on an open interval `(a,b)` of angles (`hdui`), then the contour
integral `∫ Φ(θ,·)` takes the same value at every `θ` there. -/
lemma contourIntegral_const_of_dui (hh : ∀ z, HasDerivAt h (h' z) z) {a b : ℝ}
    (hdui : ∀ θ ∈ Set.Ioo a b,
      HasDerivAt (fun θ => ∫ s, contourIntegrand h θ s) (∫ s, contourDeriv h h' θ s) θ)
    (hP : ∀ θ ∈ Set.Ioo a b, Integrable (fun s : ℝ => contourPrimitive h θ s))
    (hD : ∀ θ ∈ Set.Ioo a b, Integrable (fun s : ℝ => contourDeriv h h' θ s))
    {θ₀ θ₁ : ℝ} (h0 : θ₀ ∈ Set.Ioo a b) (h1 : θ₁ ∈ Set.Ioo a b) :
    (∫ s, contourIntegrand h θ₀ s) = (∫ s, contourIntegrand h θ₁ s) := by
  have hzero : ∀ θ ∈ Set.Ioo a b,
      HasDerivAt (fun θ => ∫ s, contourIntegrand h θ s) 0 θ := by
    intro θ hθ
    have hd := hdui θ hθ
    rwa [integral_contourDeriv_eq_zero hh θ (hP θ hθ) (hD θ hθ)] at hd
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun θ hθ => (hzero θ hθ).differentiableAt.differentiableWithinAt)
    (fun θ hθ => (hzero θ hθ).deriv) h0 h1

/-- **`∫_γ f·δ_c = ∫_ℝ f·δ_c`** (Nagao-Nielsen Eq. 2.30, finite form). Under the same
hypotheses, the contour integral along any permitted ray `θ ∈ (a,b) ∋ 0` equals the
real-axis integral `∫_ℝ h(s) ds` (the `θ = 0` value). -/
lemma contourIntegral_eq_real (hh : ∀ z, HasDerivAt h (h' z) z) {a b : ℝ}
    (hdui : ∀ θ ∈ Set.Ioo a b,
      HasDerivAt (fun θ => ∫ s, contourIntegrand h θ s) (∫ s, contourDeriv h h' θ s) θ)
    (hP : ∀ θ ∈ Set.Ioo a b, Integrable (fun s : ℝ => contourPrimitive h θ s))
    (hD : ∀ θ ∈ Set.Ioo a b, Integrable (fun s : ℝ => contourDeriv h h' θ s))
    (hmem0 : (0 : ℝ) ∈ Set.Ioo a b) {θ : ℝ} (hθ : θ ∈ Set.Ioo a b) :
    (∫ s, contourIntegrand h θ s) = ∫ s : ℝ, h (s : ℂ) := by
  rw [contourIntegral_const_of_dui hh hdui hP hD hθ hmem0]
  simp only [contourIntegrand, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    one_mul]

end Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourShift

/-! ## Direct Gaussian contour evaluation -/

namespace Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourGaussian

open ComplexDelta.ContourShift

/-- **The Gaussian** `h(z) = e^{-c z²}` (the complex-action delta `δ_c^ε` up to the
prefactor, with `c = 1/4ε`). -/
noncomputable def gaussH (c : ℝ) (z : ℂ) : ℂ := Complex.exp (-(c : ℂ) * z ^ 2)

/-- **The Gaussian contour integral is the constant `√(π/c)`** along every permitted ray
`|θ| < π/4`. Direct evaluation via `integral_gaussian_complex`: the rotation phase and the
principal square root of `π/b` cancel exactly. -/
lemma gaussianContourIntegral {c θ : ℝ} (hc : 0 < c) (hθ : |θ| < π / 4) :
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
  have hsq : Complex.exp ((θ : ℂ) * Complex.I) ^ 2
      = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
    rw [sq, ← Complex.exp_add]; congr 1; push_cast; ring
  have hint : ∀ s : ℝ, contourIntegrand (gaussH c) θ s
      = Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-b * (s : ℂ) ^ 2) := by
    intro s
    have harg : -(c : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * (s : ℂ)) ^ 2
        = -b * (s : ℂ) ^ 2 := by rw [hb_def, mul_pow, hsq]; ring
    simp only [contourIntegrand, gaussH]
    rw [harg, mul_comm]
  simp_rw [hint]
  rw [integral_const_mul, integral_gaussian_complex hbre]
  have hζ : (↑π / b) ^ (1 / 2 : ℂ)
      = ↑(Real.sqrt (π / c)) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
    rw [hb_def]
    exact Contour.pi_div_rotated_cpow_half hc hcosθ
  rw [hζ]
  rw [show Complex.exp ((θ : ℂ) * Complex.I) *
        (↑(Real.sqrt (π / c)) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I))
      = ↑(Real.sqrt (π / c)) *
        (Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)) by ring,
    ← Complex.exp_add,
    show (θ : ℂ) * Complex.I + ((-θ : ℝ) : ℂ) * Complex.I = 0 by push_cast; ring,
    Complex.exp_zero, mul_one]

/-- **Contour independence of the Gaussian integral**: the contour integral is the same at
any two permitted angles `|θ₀|, |θ₁| < π/4`. -/
lemma gaussianContourIntegral_indep {c θ₀ θ₁ : ℝ} (hc : 0 < c)
    (h0 : |θ₀| < π / 4) (h1 : |θ₁| < π / 4) :
    ∫ s : ℝ, contourIntegrand (gaussH c) θ₀ s = ∫ s : ℝ, contourIntegrand (gaussH c) θ₁ s := by
  rw [gaussianContourIntegral hc h0, gaussianContourIntegral hc h1]

end Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourGaussian

end
