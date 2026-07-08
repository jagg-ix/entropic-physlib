/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettOhmicRenormalization
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The Gaussian path integral, the complex saddle `X̄ = M⁻¹C`, and the imaginary-time bath (Nishimura–Watanabe 2408.16627)

The analytic core of Nishimura & Watanabe (arXiv:2408.16627) — completing `CaldeiraLeggettOhmicRenormalization`
(the Ohmic model setup, Eqs. 1–8) and `ComplexSaddleDecoherence` (the decoherence widths, Eqs. 22–30) with the
pieces in between: the Ohmic power law (Eq. 2), the Gaussian path integral and its **complex saddle point**
`X̄ = M⁻¹C` (Eqs. 15–21), and the imaginary-time bath action (Eq. 12).

**The Ohmic power law (Eq. 2).** The Ohmic condition `(dg/dκ)⁻¹ ∝ ω² = g²` on the frequency function `g(κ)` is
solved by the power law `g(κ) = A κ^{1/3}`: then `(dg/dκ)⁻¹ = (3/A³) g(κ)²`, a κ-independent proportionality.

**The complex saddle (Eqs. 15–21).** After integrating out the environment, the effective action is a quadratic
form in the collective integration variable `X ∈ ℂ^D` (Eq. 15):

`S_eff(X) = ½ Xᵀ M X − Cᵀ X + B`,

with `M` a `D×D` **complex symmetric** matrix. Completing the square around the **complex saddle** `X̄ = M⁻¹C`
(Eq. 18) gives (Eqs. 19–20)

`S_eff(X) = ½ (X − X̄)ᵀ M (X − X̄) + A`, `A = B − ½ Cᵀ M⁻¹ C`,

so `S_eff(X̄) = A` — the saddle is a genuine critical point, complex because `M, C` include the initial quantum
state. Integrating out the Gaussian fluctuation `Y = X − X̄` produces the reduced density matrix
`ρ_S = (det M)^{−1/2} e^{−A}` (Eq. 21), whose `Re A` is the decoherence quadratic form of `ComplexSaddleDecoherence`.

**The imaginary-time bath (Eq. 12) as a Wick rotation.** The thermal boundary condition is imposed via an
imaginary-time (Euclidean) bath action `S₀`, obtained from the real-time Lagrangian by Wick rotation `q̇ → i·v`
(`t → −iτ`), which flips the sign of the potential term: `L_Lorentz(q, i v) = −L_Euclid(q, v)`. The path-integral
weight becomes `e^{iS_L} = e^{−S_E}` — the Euclidean action is the entropic (imaginary) action of
`PathIntegral.ComplexActionPathIntegralWeight`.

* **§A — the Ohmic power law (Eq. 2).** `ohmicPowerLaw_deriv`, **`ohmic_condition`**.
* **§B — the complex saddle and completing the square (Eqs. 15–20).** `effectiveAction`, `saddleValue`;
 **`effectiveAction_complete_square`** (saddle via `M *ᵥ X̄ = C`), **`effectiveAction_at_saddle`** (`S_eff(X̄) = A`),
 `saddle_mulVec_inv`, **`effectiveAction_complete_square_inv`** (explicit `X̄ = M⁻¹C`, Eqs. 18–20).
* **§C — the Gaussian prefactor (Eq. 21).** **`gaussian_saddle_normalization`** (the `1/√det` prefactor, `D = 1`).
* **§D — the imaginary-time bath as a Wick rotation (Eq. 12).** `lagrangianLorentz`, `lagrangianEuclid`;
 **`wick_rotation_lagrangian`** (`L_L(q, i v) = −L_E(q, v)`).

Exact `HasDerivAt` / matrix-algebra / `ring` / `integral_gaussian` identities for the Ohmic
power law, the completing-the-square (the exact location `X̄ = M⁻¹C` and value `A` of the saddle), the `D = 1`
Gaussian normalization, and the single-mode Wick rotation. The full `D`-dimensional Gaussian integral giving
`(det M)^{−1/2}` (the product over eigenvalues via orthogonal diagonalization), the Lefschetz-thimble deformation
resolving the sign problem, and the `N_ℰ → ∞` continuum limit are the paper's analysis, recorded not re-derived.

## References

* J. Nishimura, H. Watanabe, arXiv:2408.16627, Eqs. 2, 12, 15–21. Completes the model setup
 (`CaldeiraLeggettOhmicRenormalization`) and the decoherence structure (`ComplexSaddleDecoherence`).

No new axioms.
-/

set_option autoImplicit false

open scoped Real
open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettGaussianSaddle

/-! ## §A — the Ohmic power law (Eq. 2) -/

/-- The **derivative of the Ohmic frequency function** `g(κ) = A κ^{1/3}` is `g'(κ) = (A/3) κ^{−2/3}`. -/
theorem ohmicPowerLaw_deriv (A κ : ℝ) (hκ : 0 < κ) :
    deriv (fun x => A * x ^ ((1 : ℝ) / 3)) κ = A / 3 * (κ ^ ((2 : ℝ) / 3))⁻¹ := by
  have hd : HasDerivAt (fun x : ℝ => A * x ^ ((1 : ℝ) / 3))
      (A * (((1 : ℝ) / 3) * κ ^ ((1 : ℝ) / 3 - 1))) κ :=
    (Real.hasDerivAt_rpow_const (Or.inl hκ.ne')).const_mul A
  rw [hd.deriv, show (1 : ℝ) / 3 - 1 = -(2 / 3) by norm_num, Real.rpow_neg hκ.le]
  ring

/-- **The Ohmic power law solves the Ohmic condition (Eq. 2)** — for `g(κ) = A κ^{1/3}` the inverse slope
`(dg/dκ)⁻¹ = (3/A³) g(κ)²` is proportional to `g² = ω²` with a κ-independent constant, i.e. `(dg/dκ)⁻¹ ∝ ω²`.
This is why the Ohmic spectrum is `ω_k = ω_cut (k/N_ℰ)^{1/3}` (`CaldeiraLeggettOhmicRenormalization.ohmicFreq`). -/
theorem ohmic_condition (A κ : ℝ) (hA : A ≠ 0) (hκ : 0 < κ) :
    (deriv (fun x => A * x ^ ((1 : ℝ) / 3)) κ)⁻¹ = 3 / A ^ 3 * (A * κ ^ ((1 : ℝ) / 3)) ^ 2 := by
  rw [ohmicPowerLaw_deriv A κ hκ]
  have hsq : (κ ^ ((1 : ℝ) / 3)) ^ 2 = κ ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast (κ ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul hκ.le]; norm_num
  have hpos : (0 : ℝ) < κ ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hκ _
  rw [mul_pow, hsq]
  field_simp

/-! ## §B — the complex saddle and completing the square (Eqs. 15–20) -/

variable {D : ℕ}

/-- The **effective action** `S_eff(X) = ½ Xᵀ M X − Cᵀ X + B` (Eq. 15) — a quadratic form in the collective
integration variable `X ∈ ℂ^D`, with `M` the `D×D` complex symmetric matrix. -/
noncomputable def effectiveAction (M : Matrix (Fin D) (Fin D) ℂ) (C : Fin D → ℂ) (B : ℂ)
    (X : Fin D → ℂ) : ℂ :=
  (1 / 2) * (X ⬝ᵥ M *ᵥ X) - C ⬝ᵥ X + B

/-- The **saddle-point value** `A = B − ½ Cᵀ X̄` (Eq. 20, with `X̄ = M⁻¹C` so `Cᵀ X̄ = Cᵀ M⁻¹ C`). -/
noncomputable def saddleValue (C Xbar : Fin D → ℂ) (B : ℂ) : ℂ := B - (1 / 2) * (C ⬝ᵥ Xbar)

/-- **Completing the square about the complex saddle (Eqs. 15 → 19)** — for a complex symmetric `M` and a saddle
`X̄` solving `M X̄ = C` (i.e. `X̄ = M⁻¹C`, Eq. 18),

`S_eff(X) = ½ (X − X̄)ᵀ M (X − X̄) + A`,   `A = B − ½ Cᵀ X̄`.

The saddle location and value are exact; complexity of `X̄` reflects that `M, C` include the initial quantum state. -/
theorem effectiveAction_complete_square (M : Matrix (Fin D) (Fin D) ℂ) (C Xbar X : Fin D → ℂ) (B : ℂ)
    (hsym : Mᵀ = M) (hsad : M *ᵥ Xbar = C) :
    effectiveAction M C B X
      = (1 / 2) * ((X - Xbar) ⬝ᵥ M *ᵥ (X - Xbar)) + saddleValue C Xbar B := by
  unfold effectiveAction saddleValue
  have hcross : Xbar ⬝ᵥ (M *ᵥ X) = C ⬝ᵥ X := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hsad]
  rw [Matrix.mulVec_sub, hsad, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, hcross, dotProduct_comm Xbar C, dotProduct_comm X C]
  ring

/-- **The saddle is a critical point** — `S_eff(X̄) = A`, the effective action at the complex saddle equals the
saddle value (the exponent of `ρ_S = (det M)^{−1/2} e^{−A}`, Eq. 21). -/
theorem effectiveAction_at_saddle (M : Matrix (Fin D) (Fin D) ℂ) (C Xbar : Fin D → ℂ) (B : ℂ)
    (hsym : Mᵀ = M) (hsad : M *ᵥ Xbar = C) :
    effectiveAction M C B Xbar = saddleValue C Xbar B := by
  rw [effectiveAction_complete_square M C Xbar Xbar B hsym hsad]
  simp

/-- **The saddle `X̄ = M⁻¹C` solves the saddle equation** `M X̄ = C` (Eq. 18) when `M` is invertible. -/
theorem saddle_mulVec_inv (M : Matrix (Fin D) (Fin D) ℂ) (C : Fin D → ℂ) [Invertible M] :
    M *ᵥ (M⁻¹ *ᵥ C) = C := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- **Completing the square with the explicit inverse (Eqs. 18–20)** — the saddle `X̄ = M⁻¹C` and value
`A = B − ½ Cᵀ M⁻¹ C` written out, for invertible complex symmetric `M`. -/
theorem effectiveAction_complete_square_inv (M : Matrix (Fin D) (Fin D) ℂ) (C X : Fin D → ℂ) (B : ℂ)
    [Invertible M] (hsym : Mᵀ = M) :
    effectiveAction M C B X
      = (1 / 2) * ((X - M⁻¹ *ᵥ C) ⬝ᵥ M *ᵥ (X - M⁻¹ *ᵥ C)) + (B - (1 / 2) * (C ⬝ᵥ (M⁻¹ *ᵥ C))) :=
  effectiveAction_complete_square M C (M⁻¹ *ᵥ C) X B hsym (saddle_mulVec_inv M C)

/-! ## §C — the Gaussian prefactor (Eq. 21) -/

/-- **The Gaussian saddle normalization (Eq. 21, `D = 1`)** `∫ e^{−½ m y²} dy = √(2π) / √m` — the one-dimensional
Gaussian fluctuation integral over `Y = X − X̄` giving the `(det M)^{−1/2}` prefactor of `ρ_S` (here `det M = m`
for `D = 1`; the general `D` case is the product over the eigenvalues of `M`). -/
theorem gaussian_saddle_normalization (m : ℝ) (hm : 0 < m) :
    ∫ y : ℝ, Real.exp (-(m / 2) * y ^ 2) = Real.sqrt (2 * π) * (Real.sqrt m)⁻¹ := by
  rw [integral_gaussian (m / 2), show π / (m / 2) = 2 * π / m by field_simp,
    Real.sqrt_div (by positivity) m, div_eq_mul_inv]

/-! ## §D — the imaginary-time bath as a Wick rotation (Eq. 12) -/

/-- The **real-time (Lorentzian) single-mode Lagrangian** `L = ½ q̇² − ½ ω² q²`. -/
noncomputable def lagrangianLorentz (ω q qdot : ℂ) : ℂ := (1 / 2) * qdot ^ 2 - (1 / 2) * ω ^ 2 * q ^ 2

/-- The **imaginary-time (Euclidean) single-mode Lagrangian** `L_E = ½ v² + ½ ω² q²` (Eq. 12) — the potential
term reverses sign relative to `lagrangianLorentz`. -/
noncomputable def lagrangianEuclid (ω q v : ℂ) : ℂ := (1 / 2) * v ^ 2 + (1 / 2) * ω ^ 2 * q ^ 2

/-- **The imaginary-time bath action is the Wick rotation of the real-time one (Eq. 12)** —
`L_Lorentz(q, i·v) = −L_Euclid(q, v)`. Substituting `q̇ = i·v` (`t → −iτ`) flips the sign of the potential term;
combined with the measure factor `dt = −i dτ` this gives `e^{iS_L} = e^{−S_E}`, so the Euclidean bath action is the
entropic (imaginary) action of `PathIntegral.ComplexActionPathIntegralWeight`. -/
theorem wick_rotation_lagrangian (ω q v : ℂ) :
    lagrangianLorentz ω q (Complex.I * v) = -lagrangianEuclid ω q v := by
  unfold lagrangianLorentz lagrangianEuclid
  rw [mul_pow, Complex.I_sq]
  ring

end Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettGaussianSaddle
