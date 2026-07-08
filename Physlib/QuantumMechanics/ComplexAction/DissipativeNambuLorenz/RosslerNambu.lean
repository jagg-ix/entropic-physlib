/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeNambu
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.Linarith

/-!
# The Rössler attractor as dissipative Nambu mechanics (Axenides–Floratos §4)

The Rössler system (Axenides, Floratos, JHEP 04 (2010) 036, §4, Eq. 4.1)

  `ẋ = −y − z`,  `ẏ = x + ay`,  `ż = b + z(x − c)`

admits the *same* dissipative Nambu split `ẋ = ∇H₁ × ∇H₂ + ∇D` as the Lorenz system, but with a quadratic
correction in the first equation (Eqs. 4.4–4.5):

  `v_ND = (−y − z − z²/2, x, b)`,  `v_D = ∇D = (z²/2, ay, z(x − c))`,  `D = ½[ay² + (x − c)z²]`.

The non-dissipative sector `ẋ = v_ND` integrates **explicitly in the complex plane** (Eqs. 4.15–4.20): the
combination `w = w₁ + i w₂` with `w₁ = x + b(1 + z)`, `w₂ = y + z + z²/2 − b²` rotates as `w(t) = w₀ e^{it}`,
so `|w|² = 2H₁` is conserved (the first Nambu Hamiltonian), and its phase gives the second (`H₂`, Eq. 4.23).
This `e^{it}` rotation is the same complex-action contour that runs through the rest of the arc.

This file works at the vector-algebra layer (`v_ND` given directly, since `H₂` is an `arctan` whose gradient
is not formalized; the cross-product origin `∇H₁ × ∇H₂ = v_ND` is Eq. 4.24):

* **§A — field reconstruction** (Eqs. 4.1, 4.4–4.5, 4.10). `rossler_reconstruction`: `v_ND + ∇D` is the full
  Rössler field. `rosslerEntropyProduction_nonneg`: `|∇D|² ≥ 0` (the second-law rate, as in the Lorenz
  contour).
* **§B — the complex constant of motion** (Eqs. 4.15–4.20). `rossler_w1_rate`/`rossler_w2_rate`:
  `ẇ₁ = −w₂`, `ẇ₂ = w₁` along `v_ND`; `rossler_complex_rotation`: `ẇ = i·w` (the `e^{it}` rotation);
  `rossler_H1_conserved`: `d/dt(½|w|²) = 0` — the first Nambu Hamiltonian `H₁ = ½|w|²` is conserved.

## References

* M. Axenides, E. Floratos, JHEP 04 (2010) 036, §4, Eqs. 4.1, 4.4–4.5, 4.10, 4.15–4.20, 4.24. `Physlib`
  (`DissipativeNambuLorenz.DissipativeNambu`).

No additional assumptions.
-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.RosslerNambu

/-! ## §A — the Rössler field as a dissipative Nambu split (Eqs. 4.1, 4.4–4.5) -/

/-- **The non-dissipative Rössler flow** `v_ND = (−y − z − z²/2, x, b)` (Eq. 4.4); equals `∇H₁ × ∇H₂`
(Eq. 4.24). -/
noncomputable def rosslerVND (b : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-(p 1) - p 2 - (p 2) ^ 2 / 2, p 0, b]

/-- **The dissipative gradient** `∇D = (z²/2, ay, z(x − c))` (Eq. 4.5), gradient of `D = ½[ay² + (x−c)z²]`
(Eq. 4.10). -/
noncomputable def rosslerGradD (a c : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(p 2) ^ 2 / 2, a * p 1, p 2 * (p 0 - c)]

/-- **The full Rössler vector field** `(−y − z, x + ay, b + z(x − c))` (Eq. 4.1). -/
noncomputable def rosslerField (a b c : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-(p 1) - p 2, p 0 + a * p 1, b + p 2 * (p 0 - c)]

/-- **[Rössler reconstruction]** `v_ND + ∇D = (−y − z, x + ay, b + z(x − c))` — the dissipative Nambu split
reconstructs the full Rössler system (Eqs. 4.1, 4.3); the quadratic `−z²/2` of `v_ND` cancels the `z²/2` of
`∇D` in the first component. -/
theorem rossler_reconstruction (a b c : ℝ) (p : Fin 3 → ℝ) :
    rosslerVND b p + rosslerGradD a c p = rosslerField a b c p := by
  funext i
  fin_cases i <;> simp [rosslerVND, rosslerGradD, rosslerField]

/-- **[Entropy production is nonnegative]** `|∇D|² ≥ 0` — the second-law rate of the Rössler dissipation,
the analogue of the Lorenz contour's entropy production. -/
theorem rosslerEntropyProduction_nonneg (a c : ℝ) (p : Fin 3 → ℝ) :
    0 ≤ rosslerGradD a c p ⬝ᵥ rosslerGradD a c p := by
  have h1 := mul_self_nonneg ((p 2) ^ 2 / 2)
  have h2 := mul_self_nonneg (a * p 1)
  have h3 := mul_self_nonneg (p 2 * (p 0 - c))
  simp only [rosslerGradD, vec3_dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  linarith

/-! ## §B — the complex constant of motion `w = w₀ e^{it}` (Eqs. 4.15–4.20) -/

/-- **`w₁ = x + b(1 + z)`** (Eq. 4.16), the real part of the complex integral `w`. -/
noncomputable def w1 (b : ℝ) (p : Fin 3 → ℝ) : ℝ := p 0 + b * (1 + p 2)

/-- **`w₂ = y + z + z²/2 − b²`** (Eq. 4.16), the imaginary part of `w`. -/
noncomputable def w2 (b : ℝ) (p : Fin 3 → ℝ) : ℝ := p 1 + p 2 + (p 2) ^ 2 / 2 - b ^ 2

/-- **`∇w₁ = (1, 0, b)`** — gradient of `w₁`. -/
noncomputable def gradW1 (b : ℝ) : Fin 3 → ℝ := ![1, 0, b]

/-- **`∇w₂ = (0, 1, 1 + z)`** — gradient of `w₂`. -/
noncomputable def gradW2 (p : Fin 3 → ℝ) : Fin 3 → ℝ := ![0, 1, 1 + p 2]

/-- **[`ẇ₁ = −w₂`]** the time derivative of `w₁` along the non-dissipative Rössler flow (Eq. 4.17). -/
theorem rossler_w1_rate (b : ℝ) (p : Fin 3 → ℝ) :
    gradW1 b ⬝ᵥ rosslerVND b p = -(w2 b p) := by
  simp [gradW1, rosslerVND, w2]
  ring

/-- **[`ẇ₂ = w₁`]** the time derivative of `w₂` along the non-dissipative Rössler flow (Eq. 4.17). -/
theorem rossler_w2_rate (b : ℝ) (p : Fin 3 → ℝ) :
    gradW2 p ⬝ᵥ rosslerVND b p = w1 b p := by
  simp [gradW2, rosslerVND, w1]
  ring

/-- **[`ẇ = i·w`]** the complex integral `w = w₁ + i w₂` rotates uniformly along the non-dissipative flow
(Eq. 4.17, `w(t) = w₀ e^{it}`): `(ẇ₁) + i(ẇ₂) = i·(w₁ + i w₂)`. This is the complex-action contour of the
Rössler non-dissipative sector. -/
theorem rossler_complex_rotation (b : ℝ) (p : Fin 3 → ℝ) :
    ((gradW1 b ⬝ᵥ rosslerVND b p : ℝ) : ℂ) + Complex.I * ((gradW2 p ⬝ᵥ rosslerVND b p : ℝ) : ℂ)
      = Complex.I * (((w1 b p : ℝ) : ℂ) + Complex.I * ((w2 b p : ℝ) : ℂ)) := by
  rw [rossler_w1_rate, rossler_w2_rate]
  rw [mul_add, ← mul_assoc, Complex.I_mul_I]
  push_cast
  ring

/-- **[`H₁ = ½|w|²` is conserved]** `d/dt(½|w|²) = w₁ẇ₁ + w₂ẇ₂ = 0` — the first Nambu Hamiltonian
`H₁ = ½|w|²` (Eq. 4.20) is a constant of motion of the non-dissipative Rössler flow (`|w(t)| = |w₀|`,
Eq. 4.19). -/
theorem rossler_H1_conserved (b : ℝ) (p : Fin 3 → ℝ) :
    w1 b p * (gradW1 b ⬝ᵥ rosslerVND b p) + w2 b p * (gradW2 p ⬝ᵥ rosslerVND b p) = 0 := by
  rw [rossler_w1_rate, rossler_w2_rate]
  ring

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.RosslerNambu

end
