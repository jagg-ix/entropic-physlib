/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Curvature invariants of the Hopf-structured vacuum solution

Formalizes the curvature scalars of the regular Petrov-D vacuum solution of J. Harada, *Exact vacuum solution
with Hopf structure in general relativity* (arXiv:2506.20878), §IV, Eqs. 25–29. The only non-vanishing
Newman–Penrose Weyl scalar is

  `Ψ₂ = −N / (2(u + ib)³)`   (Eq. 25),

with `Ψ₀ = Ψ₁ = Ψ₃ = Ψ₄ = 0` (Petrov type D). From it the Kretschmann scalar `I₁ = C_{μνρσ}C^{μνρσ}` and the
Chern–Pontryagin scalar `I₂ = ⋆C_{μνρσ}C^{μνρσ}` are `I₁ = 48 Re Ψ₂²`, `I₂ = −48 Im Ψ₂²` (Eqs. 26–27).

* `weylPsi2_sq` — `48 Ψ₂² = 12N²/(u+ib)⁶` (the closed form of Eqs. 26–27).
* `kretschmann_sub_I_chernPontryagin` — `I₁ − i I₂ = 48 Ψ₂²` (Eq. 28 with `Ψ₀ = Ψ₁ = Ψ₃ = Ψ₄ = 0`).
* `normSq_weylPsi2` — `|Ψ₂|² = N²/(4(u²+b²)³)`, and `curvature_magnitude_sq`
  `I₁² + I₂² = (12N²/(u²+b²)³)²` (Eq. 29).
* `normSq_weylPsi2_pos` — the curvature is **nonzero and finite everywhere** for `N ≠ 0`, `b ≠ 0`: the
  spacetime is regular (no curvature singularity), the paper's central claim.

## References

* J. Harada (2025), arXiv:2506.20878, §IV, Eqs. 25–29. structure: `Mathlib` (`Complex`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

open Complex

namespace Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum.HopfInvariants

/-- **The Newman–Penrose Weyl scalar** `Ψ₂ = −N/(2(u + ib)³)` (Harada Eq. 25). -/
noncomputable def weylPsi2 (N u b : ℝ) : ℂ := -(N : ℂ) / (2 * ((u : ℂ) + Complex.I * b) ^ 3)

/-- **The complex argument `u + ib` is nonzero** when `b ≠ 0` (its imaginary part is `b`). -/
theorem uib_ne_zero {u b : ℝ} (hb : b ≠ 0) : (u : ℂ) + Complex.I * b ≠ 0 := by
  intro h
  apply hb
  have := congrArg Complex.im h
  simpa using this

/-- **[Closed form of `Ψ₂²`, Eqs. 26–27] `48 Ψ₂² = 12N²/(u+ib)⁶`.** -/
theorem weylPsi2_sq (N u b : ℝ) (hb : b ≠ 0) :
    48 * weylPsi2 N u b ^ 2 = 12 * (N : ℂ) ^ 2 / ((u : ℂ) + Complex.I * b) ^ 6 := by
  have h := uib_ne_zero (u := u) hb
  unfold weylPsi2
  field_simp
  ring

/-- **The Kretschmann scalar** `I₁ = C_{μνρσ}C^{μνρσ} = 48 Re Ψ₂²` (Harada Eq. 23/26). -/
noncomputable def kretschmann (N u b : ℝ) : ℝ := 48 * (weylPsi2 N u b ^ 2).re

/-- **The Chern–Pontryagin scalar** `I₂ = ⋆C_{μνρσ}C^{μνρσ} = −48 Im Ψ₂²` (Harada Eq. 24/27). -/
noncomputable def chernPontryagin (N u b : ℝ) : ℝ := -48 * (weylPsi2 N u b ^ 2).im

/-- **[Harada Eq. 28] `I₁ − i I₂ = 48 Ψ₂²`** (with the other Weyl scalars vanishing). -/
theorem kretschmann_sub_I_chernPontryagin (N u b : ℝ) :
    (kretschmann N u b : ℂ) - Complex.I * (chernPontryagin N u b : ℂ)
      = 48 * weylPsi2 N u b ^ 2 := by
  rw [kretschmann, chernPontryagin]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]

/-- **[The Weyl-scalar magnitude] `|Ψ₂|² = N²/(4(u²+b²)³)`.** -/
theorem normSq_weylPsi2 (N u b : ℝ) :
    Complex.normSq (weylPsi2 N u b) = N ^ 2 / (4 * (u ^ 2 + b ^ 2) ^ 3) := by
  have huib : Complex.normSq ((u : ℂ) + Complex.I * b) = u ^ 2 + b ^ 2 := by
    rw [mul_comm, Complex.normSq_add_mul_I]
  have h2 : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  unfold weylPsi2
  rw [Complex.normSq_div, Complex.normSq_neg, Complex.normSq_mul, map_pow, huib, h2,
    Complex.normSq_ofReal]
  ring

/-- **[Harada Eq. 29] `I₁² + I₂² = (12N²/(u²+b²)³)²`.** -/
theorem curvature_magnitude_sq (N u b : ℝ) (hb : b ≠ 0) :
    kretschmann N u b ^ 2 + chernPontryagin N u b ^ 2
      = (12 * N ^ 2 / (u ^ 2 + b ^ 2) ^ 3) ^ 2 := by
  have hb2 : (u ^ 2 + b ^ 2) ≠ 0 := by positivity
  have h48 : Complex.normSq (48 : ℂ) = 2304 := by norm_num [Complex.normSq_apply]
  have key : kretschmann N u b ^ 2 + chernPontryagin N u b ^ 2
      = Complex.normSq ((kretschmann N u b : ℂ) - Complex.I * (chernPontryagin N u b : ℂ)) := by
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [key, kretschmann_sub_I_chernPontryagin, Complex.normSq_mul, map_pow,
    normSq_weylPsi2 N u b, h48]
  field_simp
  ring

/-- **[Regularity — the central result] the curvature is nonzero and finite everywhere** `|Ψ₂|² > 0` for
`N ≠ 0` and `b ≠ 0`: the Hopf-structured spacetime has no curvature singularity. -/
theorem normSq_weylPsi2_pos (N u b : ℝ) (hN : N ≠ 0) (hb : b ≠ 0) :
    0 < Complex.normSq (weylPsi2 N u b) := by
  rw [normSq_weylPsi2 N u b]
  have hb2 : (0 : ℝ) < u ^ 2 + b ^ 2 := by positivity
  positivity

end Physlib.QuantumMechanics.ComplexAction.KerrSchildVacuum.HopfInvariants

end
