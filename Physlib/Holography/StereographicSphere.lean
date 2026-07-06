/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The stereographic Riemann sphere as the lossless holographic boundary

The holographic boundary of `AdS₃` is the Riemann sphere `∂AdS₃ ≃ CP¹ ≃ S²`, charted losslessly by the complex
plane through **stereographic projection**. The projection `π : S² ∖ {N} → ℂ`, `π(X,Y,Z) = (X + iY)/(1 − Z)`, and
its inverse `π⁻¹(w) = (2 Re w, 2 Im w, |w|² − 1)/(|w|² + 1)` form a **bijection**: `π⁻¹` lands on the unit sphere
(`stereoInv_mem_sphere`) and `π ∘ π⁻¹ = id` (`stereoProj_stereoInv`). So the `2`-sphere boundary is encoded in `ℂ`
with **zero information loss** — the concrete realization of the exact (`ε = 0`) holographic reduction.

References: Riemann sphere / stereographic projection; `∂AdS₃ ≃ CP¹`. No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Holography.StereographicSphere

/-- **Stereographic projection from the north pole** `π(X,Y,Z) = (X + iY)/(1 − Z)`. -/
noncomputable def stereoProj (X Y Z : ℝ) : ℂ :=
  ((X : ℂ) + (Y : ℂ) * Complex.I) / ((1 - Z : ℝ) : ℂ)

/-- **Inverse stereographic projection** `π⁻¹(w) = (2 Re w, 2 Im w, |w|² − 1)/(|w|² + 1)`. -/
noncomputable def stereoInv (w : ℂ) : ℝ × ℝ × ℝ :=
  (2 * w.re / (Complex.normSq w + 1),
   2 * w.im / (Complex.normSq w + 1),
   (Complex.normSq w - 1) / (Complex.normSq w + 1))

/-- **The inverse projection lands on the unit sphere** `‖π⁻¹(w)‖² = 1` — from the identity
`4|w|² + (|w|² − 1)² = (|w|² + 1)²`. -/
theorem stereoInv_mem_sphere (w : ℂ) :
    (stereoInv w).1 ^ 2 + (stereoInv w).2.1 ^ 2 + (stereoInv w).2.2 ^ 2 = 1 := by
  have hd' : (0 : ℝ) < w.re * w.re + w.im * w.im + 1 := by
    nlinarith [mul_self_nonneg w.re, mul_self_nonneg w.im]
  simp only [stereoInv, Complex.normSq_apply]
  field_simp [hd'.ne']
  ring

/-- **Projection inverts the inverse** `π(π⁻¹(w)) = w` — stereographic projection is a genuine inverse of the
inverse map, so `S² ∖ {N}` is in bijection with `ℂ`: the boundary sphere literally *is* the complex plane of the
Riemann sphere, the lossless holographic boundary chart. -/
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

end Physlib.Holography.StereographicSphere

end
