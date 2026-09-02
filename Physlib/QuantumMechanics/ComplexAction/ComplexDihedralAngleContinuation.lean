/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MinkowskianDihedralAngles

/-!
# Theorem II.1 — the two Lorentzian dihedral-angle versions and `θ⁺ = −θ⁻`

Asante–Dittrich–Padua-Argüelles Theorem II.1: the analytical continuations of `θ⁺` and `θ⁻` in the
Wick angle `φ` are periodic functions on `(−2π, 2π]`, and satisfy **`θ⁺ = −θ⁻`**. This module
formalizes the branch-independent algebraic core of that statement, on the dihedral angle
`MinkowskianDihedralAngles.dihedralAngle`.

The two versions `θ±` use the two branch roots `±√disc` of the discriminant (Eq. 2.15). Because the
discriminant is `num² − s_a s_b` (the Heron form), the two angle arguments are **reciprocal**:

  `z⁺ · z⁻ = ((num − √disc)(num + √disc)) / (s_a s_b) = (num² − disc)/(s_a s_b) = 1`
  (`angleArgs_reciprocal`),

and since `exp(iθ) = z` (`exp_dihedralAngle`), the two versions satisfy
`exp(i(θ⁺ + θ⁻)) = z⁺ z⁻ = 1`, i.e. **`θ⁺ + θ⁻ ∈ 2πℤ`** — the exponentiated, branch-independent form
of `θ⁺ = −θ⁻`, which is exactly the source of the `(−2π, 2π]` periodicity (`dihedralAngle_versions_sum`).

* **§A — the angle exponential** `exp(iθ) = z` (`exp_dihedralAngle`, from `Complex.exp_log`).
* **§B — the reciprocal branch arguments** `z⁺ z⁻ = 1` (`angleArgs_reciprocal`).
* **§C — Theorem II.1** `exp(i(θ⁺ + θ⁻)) = 1`, `θ⁺ = −θ⁻ (mod 2π)` (`dihedralAngle_versions_sum`).
* **§D — the Regge instance** for the Wick dihedral angle, with branch roots squaring to the edge
  lengths (`reggeDihedral_versions_sum`).

**Honest layering.** Proven: `exp(iθ) = z`, the reciprocity `z⁺ z⁻ = 1`, and hence
`exp(i(θ⁺+θ⁻)) = 1`. This is `θ⁺ = −θ⁻` *modulo `2π`* — the branch-independent content; the precise
`(−2π, 2π]` fundamental domain and the even/odd `φ`-parity of `Re/Im θ±` are the analytic-continuation
refinements of the same reciprocity, carried by the branch-root parametrization.

## References

* S. K. Asante, B. Dittrich, J. Padua-Argüelles, "Complex actions and causality violations",
  arXiv:2112.15387 [`Asante:2021zzh`], Theorem II.1, Eqs. (2.11)–(2.15). Reuses
  `MinkowskianDihedralAngles` (`dihedralAngle`) and `ComplexReggeActionCausality` (`wickDiscriminant`).


-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexDihedralAngleContinuation

open Physlib.QuantumMechanics.ComplexAction.MinkowskianDihedralAngles
open Physlib.QuantumMechanics.ComplexAction.ComplexReggeActionCausality


/-- **The dihedral-angle argument** `z = (num + √disc)/(√s_a √s_b)`, the argument of the logarithm in
`θ = −i log z`. -/
noncomputable def angleArg (num sqrtDisc sqrtSa sqrtSb : ℂ) : ℂ := (num + sqrtDisc) / (sqrtSa * sqrtSb)

/-- **`exp(iθ) = z`**: the dihedral angle exponentiates to its argument (`Complex.exp_log`, for a
nonzero argument). -/
lemma exp_dihedralAngle (num sqrtDisc sqrtSa sqrtSb : ℂ) (h : angleArg num sqrtDisc sqrtSa sqrtSb ≠ 0) :
    Complex.exp (Complex.I * dihedralAngle num sqrtDisc sqrtSa sqrtSb)
      = angleArg num sqrtDisc sqrtSa sqrtSb := by
  unfold dihedralAngle angleArg
  rw [← mul_assoc,
    show Complex.I * -Complex.I = 1 from by rw [mul_neg, Complex.I_mul_I]; ring, one_mul]
  exact Complex.exp_log h


/-- **The two branch arguments are reciprocal** `z⁺ z⁻ = 1`: with the `±√disc` branch roots and the
discriminant `disc = num² − s_a s_b` (the Heron form), the `θ⁺` and `θ⁻` arguments multiply to one. -/
lemma angleArgs_reciprocal (num sqrtDisc sqrtSa sqrtSb : ℂ)
    (hdisc : sqrtDisc ^ 2 = num ^ 2 - sqrtSa ^ 2 * sqrtSb ^ 2) (hab : sqrtSa * sqrtSb ≠ 0) :
    angleArg num (-sqrtDisc) sqrtSa sqrtSb * angleArg num sqrtDisc sqrtSa sqrtSb = 1 := by
  unfold angleArg
  rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hab hab)]
  linear_combination -hdisc


/-- **Theorem II.1** (Asante–Dittrich–Padua-Argüelles): the two Lorentzian dihedral-angle versions
satisfy `exp(i(θ⁺ + θ⁻)) = 1`, i.e. **`θ⁺ = −θ⁻ (mod 2π)`** — the two branch choices are negatives,
the source of the `(−2π, 2π]` periodicity of the analytical continuation. -/
lemma dihedralAngle_versions_sum (num sqrtDisc sqrtSa sqrtSb : ℂ)
    (hdisc : sqrtDisc ^ 2 = num ^ 2 - sqrtSa ^ 2 * sqrtSb ^ 2) (hab : sqrtSa * sqrtSb ≠ 0)
    (h1 : angleArg num (-sqrtDisc) sqrtSa sqrtSb ≠ 0) (h2 : angleArg num sqrtDisc sqrtSa sqrtSb ≠ 0) :
    Complex.exp (Complex.I * (dihedralAngle num (-sqrtDisc) sqrtSa sqrtSb
      + dihedralAngle num sqrtDisc sqrtSa sqrtSb)) = 1 := by
  rw [mul_add, Complex.exp_add, exp_dihedralAngle num (-sqrtDisc) sqrtSa sqrtSb h1,
    exp_dihedralAngle num sqrtDisc sqrtSa sqrtSb h2, angleArgs_reciprocal num sqrtDisc sqrtSa sqrtSb hdisc hab]


/-- **Theorem II.1 for the Wick–Regge dihedral angle**: with the numerator `a⋆b` and branch roots
squaring to the discriminant and the edge lengths, the two Lorentzian Regge-angle versions satisfy
`exp(i(θ⁺ + θ⁻)) = 1`, `θ⁺ = −θ⁻ (mod 2π)`. -/
lemma reggeDihedral_versions_sum (φ : ℝ) (a b : Fin 2 → ℂ) (sqrtDisc sqrtSa sqrtSb : ℂ)
    (hdisc : sqrtDisc ^ 2 = wickDiscriminant φ a b) (hsa : sqrtSa ^ 2 = wickInner φ a a)
    (hsb : sqrtSb ^ 2 = wickInner φ b b) (hab : sqrtSa * sqrtSb ≠ 0)
    (h1 : angleArg (wickInner φ a b) (-sqrtDisc) sqrtSa sqrtSb ≠ 0)
    (h2 : angleArg (wickInner φ a b) sqrtDisc sqrtSa sqrtSb ≠ 0) :
    Complex.exp (Complex.I * (dihedralAngle (wickInner φ a b) (-sqrtDisc) sqrtSa sqrtSb
      + dihedralAngle (wickInner φ a b) sqrtDisc sqrtSa sqrtSb)) = 1 := by
  refine dihedralAngle_versions_sum (wickInner φ a b) sqrtDisc sqrtSa sqrtSb ?_ hab h1 h2
  rw [hdisc, hsa, hsb]
  unfold wickDiscriminant; ring

end Physlib.QuantumMechanics.ComplexAction.ComplexDihedralAngleContinuation
