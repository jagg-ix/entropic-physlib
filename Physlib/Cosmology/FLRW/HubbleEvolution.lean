/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Cosmology.FLRW.Basic

/-!
# The Hubble evolution (`Ḣ`) equation from the Friedmann pair

Adds the **Hubble friction / `Ḣ` equation** to physlib's FLRW layer (`Cosmology.FLRW.FriedmannEquation`,
which already has both Friedmann equations and `hubbleConstant`). Combining the first and second Friedmann
equations gives the time evolution of the Hubble rate,

  `Ḣ = −4πG (ρ + p/c²) + k c²/a²`   (`deriv_hubbleConstant_eq_friedmann`),

derived **algebraically** from `deriv_hubbleConstant` (`Ḣ = (a''a − (a')²)/a² = a''/a − H²`) by substituting the
second Friedmann equation for `a''/a` and the first for `H²`. The cosmological-constant terms `Λc²/3` cancel
between the two equations, and the curvature term survives as `kc²/a²`.

This is the cosmology counterpart of the GR "matter-side Bianchi / continuity" certificate ported from
catept-main: `Ḣ` is the single relation that the two Friedmann equations are consistent with, the half-step
before the fluid continuity equation `ρ̇ = −3H(ρ + p/c²)` (which needs differentiating the first Friedmann
equation — left as the next step).

* **§A — the `Ḣ` equation** (`deriv_hubbleConstant_eq_friedmann`).

## References

* The Friedmann/Raychaudhuri equations of FLRW cosmology; the catept-main `RelativityGRFRW*` certificates.
  Carriers: `Cosmology.FLRW.FriedmannEquation` (`FirstOrderFriedmann`, `SecondOrderFriedmann`,
  `hubbleConstant`, `deriv_hubbleConstant`).


-/

set_option autoImplicit false

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Time

/-- **[The Hubble evolution equation] `Ḣ = −4πG(ρ + p/c²) + kc²/a²`.** Combining the first and second
Friedmann equations (via `deriv_hubbleConstant`, `Ḣ = a''/a − H²`) yields the time derivative of the Hubble
rate: the `Λc²/3` terms cancel, leaving the matter/pressure source `−4πG(ρ + p/c²)` and the curvature term
`kc²/a²`. -/
lemma deriv_hubbleConstant_eq_friedmann
    {a ρ p : Time → ℝ} {k Λ G c : ℝ} {t : Time}
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0)
    (hfirst : FirstOrderFriedmann a ρ k Λ G c t)
    (hsecond : SecondOrderFriedmann a ρ p Λ G c t) :
    ∂ₜ (hubbleConstant a) t = -(4 * Real.pi * G) * (ρ t + p t / c ^ 2) + k * c ^ 2 / (a t) ^ 2 := by
  rw [deriv_hubbleConstant ha hd_a haz]
  -- a''/a from the second Friedmann equation; (a')² from the first
  have hA'' : ∂ₜ (∂ₜ a) t = a t * (-(4 * Real.pi * G / 3) * (ρ t + 3 * p t / c ^ 2) + Λ * c ^ 2 / 3) := by
    rw [← hsecond]; field_simp
  have hA' : (∂ₜ a t) ^ 2
      = (a t) ^ 2 * ((8 * Real.pi * G) / 3 * ρ t - k * c ^ 2 / (a t) ^ 2 + Λ * c ^ 2 / 3) := by
    rw [← hfirst, div_pow]; field_simp
  rw [hA'', hA']
  field_simp
  ring

/-- **[The deceleration parameter from matter content] `q = −(1 + Ḣ/H²)`** with `Ḣ` the Friedmann source.
Combining the `Ḣ` equation (`deriv_hubbleConstant_eq_friedmann`) with physlib's
`decelerationParameter_eq_one_plus_hubbleConstant` expresses the deceleration parameter `q` — an observable —
directly in terms of the energy density, pressure and curvature:

  `q = −(1 + (−4πG(ρ + p/c²) + kc²/a²)/H²)`.

So accelerated expansion (`q < 0`) is sourced by the matter content via the Friedmann equations. -/
lemma decelerationParameter_eq_friedmann
    {a ρ p : Time → ℝ} {k Λ G c : ℝ} {t : Time}
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hd_az : ∂ₜ a t ≠ 0)
    (hfirst : FirstOrderFriedmann a ρ k Λ G c t)
    (hsecond : SecondOrderFriedmann a ρ p Λ G c t) :
    decelerationParameter a t
      = -(1 + (-(4 * Real.pi * G) * (ρ t + p t / c ^ 2) + k * c ^ 2 / (a t) ^ 2)
            / (hubbleConstant a t) ^ 2) := by
  rw [decelerationParameter_eq_one_plus_hubbleConstant ha hd_a haz hd_az,
    deriv_hubbleConstant_eq_friedmann ha hd_a haz hfirst hsecond]


/-! ## §B — the continuity equation from Bianchi -/

/-- **[The continuity equation from the two Friedmann equations]
`ρ̇ = −3H(ρ + p/c²)`** — the Bianchi-identity consistency: the first Friedmann
equation, holding along the evolution, is solved for `ρ` and differentiated;
substituting the `Ḣ` equation (`deriv_hubbleConstant_eq_friedmann`), the curvature
terms cancel against `ȧ = Ha` and the cosmological constant drops out, leaving
exactly the covariant conservation of the total stress-energy. -/
theorem continuity_from_friedmann (a ρ p : Time → ℝ) (k Λ G c : ℝ) (t : Time)
    (ha : DifferentiableAt ℝ a t) (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (haz : a t ≠ 0) (hH : DifferentiableAt ℝ (hubbleConstant a) t)
    (hG : G ≠ 0) (hc : c ≠ 0)
    (hfirstAll : ∀ s, FirstOrderFriedmann a ρ k Λ G c s)
    (hsecond : SecondOrderFriedmann a ρ p Λ G c t) :
    ∂ₜ ρ t = -3 * hubbleConstant a t * (ρ t + p t / c ^ 2) := by
  have hfun : ρ = fun s =>
      3 / (8 * Real.pi * G)
          * ((hubbleConstant a s) ^ 2 + k * c ^ 2 / (a s) ^ 2)
        + -(Λ * c ^ 2 / (8 * Real.pi * G)) := by
    funext s
    have h := hfirstAll s
    unfold FirstOrderFriedmann at h
    simp only [hubbleConstant]
    linear_combination (-3 / (8 * Real.pi * G)) * h
      + (-(ρ s)) * mul_inv_cancel₀ Real.pi_ne_zero
      + (-(ρ s) * Real.pi * Real.pi⁻¹) * mul_inv_cancel₀ hG
  have hHsqd : DifferentiableAt ℝ (fun s => (hubbleConstant a s) ^ 2) t := hH.pow 2
  have hkerD : DifferentiableAt ℝ (fun s => k * c ^ 2 / (a s) ^ 2) t :=
    ((ha.pow 2).fun_inv (pow_ne_zero 2 haz)).const_mul _
  have hsumD : DifferentiableAt ℝ
      (fun s => (hubbleConstant a s) ^ 2 + k * c ^ 2 / (a s) ^ 2) t :=
    hHsqd.add hkerD
  have hCsumD : DifferentiableAt ℝ
      (fun s => 3 / (8 * Real.pi * G)
        * ((hubbleConstant a s) ^ 2 + k * c ^ 2 / (a s) ^ 2)) t :=
    hsumD.const_mul _
  have haSqD : DifferentiableAt ℝ (fun s => (a s) ^ 2) t := ha.pow 2
  have hadot : ∂ₜ a t = hubbleConstant a t * a t := by
    simp only [hubbleConstant]
    rw [div_mul_cancel₀ _ haz]
  have hd : ∂ₜ ρ t = ∂ₜ (fun s =>
      3 / (8 * Real.pi * G)
          * ((hubbleConstant a s) ^ 2 + k * c ^ 2 / (a s) ^ 2)
        + -(Λ * c ^ 2 / (8 * Real.pi * G))) t :=
    congrArg (fun f => ∂ₜ f t) hfun
  rw [hd,
    Time.deriv_add _ _ hCsumD (differentiableAt_const _),
    Time.deriv_const_mul _ t hsumD,
    Time.deriv_add _ _ hHsqd hkerD,
    Time.deriv_sq t hH,
    Time.deriv_div (differentiableAt_const _) haSqD (pow_ne_zero 2 haz),
    Time.deriv_sq t ha,
    deriv_hubbleConstant_eq_friedmann ha hd_a haz (hfirstAll t) hsecond,
    hadot]
  simp only [Time.deriv_const]
  field_simp
  ring

/-! ## §C — the non-linear Schrödinger form of the Friedmann equations -/

/-- **[The logarithmic derivative of the NLS wave function]** for `u = a^{−n/2}`
(Gumjudpai Eq. (11)), `u̇/u`-form: `∂ₜ(a^{−n/2}) = −(n/2)·H·a^{−n/2}` — the wave
function of the Schrödinger-type formulation of FLRW cosmology evolves at
`−(n/2)` times the Hubble rate. -/
theorem nls_log_derivative (a : Time → ℝ) (n : ℝ) (t : Time)
    (ha : DifferentiableAt ℝ a t) (hapos : 0 < a t) :
    ∂ₜ (fun s => a s ^ (-(n / 2))) t
      = -(n / 2) * hubbleConstant a t * a t ^ (-(n / 2)) := by
  rw [Time.deriv_rpow_const t ha (Or.inl hapos.ne')]
  simp only [hubbleConstant]
  have key : a t ^ (-(n / 2) - 1) = a t ^ (-(n / 2)) / a t := by
    rw [eq_div_iff hapos.ne']
    calc a t ^ (-(n / 2) - 1) * a t
        = a t ^ (-(n / 2) - 1) * a t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = a t ^ (-(n / 2) - 1 + 1) := (Real.rpow_add hapos _ _).symm
      _ = a t ^ (-(n / 2)) := by norm_num
  rw [key]
  ring

/-- **[The non-linear Schrödinger equation from the Friedmann pair]** (Gumjudpai,
Gen. Relativ. Gravit. 41 (2009) 249, Eqs. (11)–(14), in the paper's `c = 1`,
`Λ = 0` conventions with `κ² = 8πG`).  Along the cosmological trajectory, with
wave function `u = a^{−n/2}`, Schrödinger energy `E = −κ²n²D/12` and potential
`P = (κ²n/4)·aⁿ·εφ̇²`, the two Friedmann equations for a barotropic fluid
(`ρ_γ = D·a^{−n}`, `w_γ = (n−3)/3`) plus canonical scalar field are *exactly* the
NLS-type equation in cosmic-time form,

  `∂ₜ(u̇/u) + (E − P)u² = −(nk/2)·u^{4/n}`,

(here written with `u² = a^{−n}` and `u^{4/n} = a^{−2}`); under the coordinate map
`dx = u dt` this is Eq. (14), `u″(x) + [E − P(x)]u = −(nk/2)u^{(4−n)/n}`.  The
`x ↦ t` inverse map (Eqs. (27)–(28)) is the quoted analytic content; the equation
itself is Friedmann algebra. -/
theorem nls_equation_from_friedmann (a ργ ρtot ptot φ : Time → ℝ) (V : ℝ → ℝ)
    (ε n k G D : ℝ) (t : Time)
    (hadAll : ∀ s, DifferentiableAt ℝ a s) (haAll : ∀ s, 0 < a s)
    (hd_a : DifferentiableAt ℝ (∂ₜ a) t)
    (hH : DifferentiableAt ℝ (hubbleConstant a) t)
    (hγ : ργ t = D * a t ^ (-n))
    (hρtot : ∀ s, ρtot s = ργ s + (ε * (∂ₜ φ s) ^ 2 / 2 + V (φ s)))
    (hptot : ∀ s, ptot s = (n - 3) / 3 * ργ s + (ε * (∂ₜ φ s) ^ 2 / 2 - V (φ s)))
    (hfirst : FirstOrderFriedmann a ρtot k 0 G 1 t)
    (hsecond : SecondOrderFriedmann a ρtot ptot 0 G 1 t) :
    ∂ₜ (fun s => ∂ₜ (fun r => a r ^ (-(n / 2))) s / a s ^ (-(n / 2))) t
      + (-(8 * Real.pi * G) * n ^ 2 * D / 12
          - 8 * Real.pi * G * n / 4 * a t ^ n * (ε * (∂ₜ φ t) ^ 2)) * a t ^ (-n)
      = -(n * k / 2) * a t ^ (-2 : ℝ) := by
  have hlog : (fun s => ∂ₜ (fun r => a r ^ (-(n / 2))) s / a s ^ (-(n / 2)))
      = fun s => -(n / 2) * hubbleConstant a s := by
    funext s
    rw [nls_log_derivative a n s (hadAll s) (haAll s), mul_div_assoc,
      div_self (Real.rpow_pos_of_pos (haAll s) _).ne', mul_one]
  have hprod : a t ^ n * a t ^ (-n) = 1 := by
    rw [← Real.rpow_add (haAll t)]
    norm_num
  have h2 : a t ^ (-2 : ℝ) = ((a t) ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (haAll t).le, Real.rpow_natCast]
  rw [congrArg (fun f => ∂ₜ f t) hlog,
    Time.deriv_const_mul _ t hH,
    deriv_hubbleConstant_eq_friedmann (hadAll t) hd_a (haAll t).ne' hfirst hsecond,
    hρtot t, hptot t, hγ, h2]
  linear_combination (-(2 * Real.pi * G * n * ε * (∂ₜ φ t) ^ 2)) * hprod

end Cosmology.FLRW.FriedmannEquation

end
