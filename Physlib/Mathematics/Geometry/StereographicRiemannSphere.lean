/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.LinearCombination

/-!
# Stereographic projection: the Riemann sphere `S² ↔ ℂ`

The explicit stereographic dictionary between the unit sphere `S² ⊂ ℝ³` and the complex plane `ℂ`
(the Riemann sphere / dual-sphere mapping), projecting from the north pole `(0,0,1)`:

 * **projection** `π(X,Y,Z) = (X + iY)/(1 − Z) ∈ ℂ` (`stereoProj`);
 * **inverse** `π⁻¹(w) = (2·Re w, 2·Im w, |w|² − 1)/(|w|² + 1) ∈ ℝ³` (`stereoInv`).

Proved exactly over Mathlib's `ℂ`:

 * `stereoInv` always lands on the unit sphere, `‖π⁻¹(w)‖² = 1` (`stereoInv_mem_sphere`), from the
 identity `4|w|² + (|w|²−1)² = (|w|²+1)²`;
 * `π ∘ π⁻¹ = id` on `ℂ` (`stereoProj_stereoInv`): projecting the inverse image back recovers `w`;
 * `π⁻¹ ∘ π = id` on the sphere minus the north pole (`stereoInv_stereoProj`): so `π` is a genuine
 **bijection** `S²∖{N} ≃ ℂ` — the sphere minus its north pole literally *is* the complex plane.

Proven: the inverse map lands on `S²`, and `π` and `π⁻¹` are mutually inverse (a
bijection between `ℂ` and the punctured sphere). Interpretive:
the identification of `ℂ ∪ {∞}` with `S²` (the north pole `(0,0,1)` as the point at infinity, where the
projection's denominator `1 − Z` vanishes) is the standard one-point-compactification picture.

## References

* B. Riemann, the Riemann sphere; the stereographic projection `(X+iY)/(1−Z)` and its inverse. Mathlib's
 `stereographic` gives the abstract inner-product-space version; here the explicit complex formula.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Mathematics.Geometry.StereographicRiemannSphere

/-- **Stereographic projection from the north pole** `π(X,Y,Z) = (X + iY)/(1 − Z)`: the unit-sphere
point `(X,Y,Z)` (with `Z ≠ 1`) maps to the complex plane. -/
noncomputable def stereoProj (X Y Z : ℝ) : ℂ :=
  ((X : ℂ) + (Y : ℂ) * Complex.I) / ((1 - Z : ℝ) : ℂ)

/-- **Inverse stereographic projection** `π⁻¹(w) = (2 Re w, 2 Im w, |w|² − 1)/(|w|² + 1)`: the complex
number `w` maps back to a point of the unit sphere. -/
noncomputable def stereoInv (w : ℂ) : ℝ × ℝ × ℝ :=
  (2 * w.re / (Complex.normSq w + 1),
   2 * w.im / (Complex.normSq w + 1),
   (Complex.normSq w - 1) / (Complex.normSq w + 1))

/-- **The inverse projection lands on the unit sphere** `‖π⁻¹(w)‖² = 1`: from the exact identity
`4|w|² + (|w|² − 1)² = (|w|² + 1)²`. -/
theorem stereoInv_mem_sphere (w : ℂ) :
    (stereoInv w).1 ^ 2 + (stereoInv w).2.1 ^ 2 + (stereoInv w).2.2 ^ 2 = 1 := by
  have hd' : (0 : ℝ) < w.re * w.re + w.im * w.im + 1 := by
    nlinarith [mul_self_nonneg w.re, mul_self_nonneg w.im]
  simp only [stereoInv, Complex.normSq_apply]
  field_simp [hd'.ne']
  ring

/-- **Projection inverts the inverse** `π(π⁻¹(w)) = w`: stereographic projection is a genuine inverse of
the inverse map (so the sphere minus the north pole is in bijection with `ℂ`). -/
theorem stereoProj_stereoInv (w : ℂ) :
    stereoProj (stereoInv w).1 (stereoInv w).2.1 (stereoInv w).2.2 = w := by
  have hd : Complex.normSq w + 1 ≠ 0 :=
    (by have := Complex.normSq_nonneg w; linarith : (0 : ℝ) < Complex.normSq w + 1).ne'
  have h1Z : ((1 - (stereoInv w).2.2 : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    show (1 : ℝ) - (Complex.normSq w - 1) / (Complex.normSq w + 1) ≠ 0
    have heq : (1 : ℝ) - (Complex.normSq w - 1) / (Complex.normSq w + 1)
        = 2 / (Complex.normSq w + 1) := by
      field_simp
      ring
    rw [heq]; exact div_ne_zero (by norm_num) hd
  rw [stereoProj, div_eq_iff h1Z, Complex.ext_iff]
  refine ⟨?_, ?_⟩
  all_goals
    simp only [stereoInv, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one,
      sub_zero, add_zero, zero_add]
  all_goals field_simp
  all_goals ring

/-- **The inverse inverts the projection on the sphere** `π⁻¹(π(X,Y,Z)) = (X,Y,Z)` for a sphere point
`(X,Y,Z)` with `X²+Y²+Z²=1` and `Z ≠ 1` (i.e. not the north pole). Together with `stereoProj_stereoInv`
this makes stereographic projection a genuine **bijection** between `ℂ` and the sphere minus its north
pole: the boundary sphere `S²∖{N}` literally *is* the complex plane of the Riemann sphere. -/
theorem stereoInv_stereoProj (X Y Z : ℝ) (hsph : X ^ 2 + Y ^ 2 + Z ^ 2 = 1) (hN : Z ≠ 1) :
    stereoInv (stereoProj X Y Z) = (X, Y, Z) := by
  have hZ : (1 : ℝ) - Z ≠ 0 := sub_ne_zero.mpr (Ne.symm hN)
  have hre : (stereoProj X Y Z).re = X / (1 - Z) := by
    rw [stereoProj, Complex.div_ofReal_re]; simp
  have him : (stereoProj X Y Z).im = Y / (1 - Z) := by
    rw [stereoProj, Complex.div_ofReal_im]; simp
  have hns : Complex.normSq (stereoProj X Y Z) = (1 + Z) / (1 - Z) := by
    rw [stereoProj, Complex.normSq_div, Complex.normSq_add_mul_I, Complex.normSq_ofReal,
      div_eq_div_iff (mul_ne_zero hZ hZ) hZ]
    linear_combination (1 - Z) * hsph
  have h1 : (stereoInv (stereoProj X Y Z)).1 = X := by
    show 2 * (stereoProj X Y Z).re / (Complex.normSq (stereoProj X Y Z) + 1) = X
    rw [hre, hns]; field_simp; ring
  have h2 : (stereoInv (stereoProj X Y Z)).2.1 = Y := by
    show 2 * (stereoProj X Y Z).im / (Complex.normSq (stereoProj X Y Z) + 1) = Y
    rw [him, hns]; field_simp; ring
  have h3 : (stereoInv (stereoProj X Y Z)).2.2 = Z := by
    show (Complex.normSq (stereoProj X Y Z) - 1) / (Complex.normSq (stereoProj X Y Z) + 1) = Z
    rw [hns]; field_simp; ring
  exact Prod.ext h1 (Prod.ext h2 h3)

end Physlib.Mathematics.Geometry.StereographicRiemannSphere
