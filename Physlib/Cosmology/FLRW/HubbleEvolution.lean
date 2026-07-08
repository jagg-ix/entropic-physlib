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
  structures: `Cosmology.FLRW.FriedmannEquation` (`FirstOrderFriedmann`, `SecondOrderFriedmann`,
  `hubbleConstant`, `deriv_hubbleConstant`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Time

/-- **[The Hubble evolution equation] `Ḣ = −4πG(ρ + p/c²) + kc²/a²`.** Combining the first and second
Friedmann equations (via `deriv_hubbleConstant`, `Ḣ = a''/a − H²`) yields the time derivative of the Hubble
rate: the `Λc²/3` terms cancel, leaving the matter/pressure source `−4πG(ρ + p/c²)` and the curvature term
`kc²/a²`. -/
theorem deriv_hubbleConstant_eq_friedmann
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
theorem decelerationParameter_eq_friedmann
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

end Cosmology.FLRW.FriedmannEquation

end
