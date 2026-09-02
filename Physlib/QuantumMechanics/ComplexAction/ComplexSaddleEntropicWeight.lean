/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettGaussianSaddle

/-!
# The complex saddle is the master path-integral weight (linking Nishimura–Watanabe to the entropic weight)

This module **links** the Nishimura–Watanabe complex-saddle arc (`CaldeiraLeggettGaussianSaddle`,
`ComplexSaddleDecoherence`, `CaldeiraLeggettOhmicRenormalization`) to the repository's canonical **path-integral
weight** hub `PathIntegral.ComplexActionPathIntegralWeight` — reusing its `complexActionPathIntegralWeight`,
`kuikenWeight` and `master_modulus_is_kuiken` rather than re-deriving them.

The Gaussian saddle produces the reduced density matrix `ρ_S = (det M)^{−1/2} e^{−A}` (Eq. 21), with the
effective-action saddle value `A ∈ ℂ` (`CaldeiraLeggettGaussianSaddle.saddleValue`). The exponent `e^{−A}` is
**exactly** an instance of the master complex-action weight `exp[(i/ℏ)S_R − (1/ℏ)S_I]` with `S_R = −ℏ·Im A` and
`S_I = ℏ·Re A`: the imaginary (entropic) action is `S_I = ℏ Re A`, and the *real part* `Re A` is precisely the
decoherence quadratic form `ComplexSaddleDecoherence.reADiag` (Eqs. 22–23). Consequently the modulus of the
reduced density matrix element is the **entropic damping** `kuikenWeight ℏ (ℏ Re A) = e^{−Re A}` — the same
`exp(−S_I/ℏ)` sector that drives the whole entropic-time / decoherence-functional edifice.

* **§A — the saddle exponent is the master weight.** **`cexp_neg_eq_masterWeight`**
  (`e^{−A} = complexActionPathIntegralWeight (−ℏ Im A) (ℏ Re A) ℏ`), **`cexp_neg_modulus_is_kuiken`**
  (`‖e^{−A}‖ = kuikenWeight ℏ (ℏ Re A)`), `cexp_neg_modulus_eq_exp_neg_re`.
* **§B — the reduced density matrix element.** **`saddleValue_weight_modulus_is_kuiken`** — the modulus of
  `ρ_S ∝ e^{−A}` is the entropic damping, with `Re A` the decoherence action.
* **§C — the decoherence magnitude is a Kuiken weight.** **`rhoMagnitude_eq_kuiken`**
  (`ComplexSaddleDecoherence.rhoMagnitude = kuikenWeight 1 reADiag`) — the Gaussian off-diagonal suppression is
  literally the entropic-damping weight of the decoherence quadratic form.

**Cross-references (complementary, not duplicated).** The single-mode Wick rotation
`CaldeiraLeggettGaussianSaddle.wick_rotation_lagrangian` (`L_L(q, iv) = −L_E`) is the Lagrangian-level companion of
the spacetime quadratic-form Wick rotation `Relativity.minkowskiQuadFormC_wickRotateVec_eq_neg_euclideanQuadForm`
and the evolution-factor Wick rotation `NonHermitian.WickRotation` (`entropyDamping`,
`lorentzian_to_euclidean_wickRotation`); the real 1D Gaussian prefactor
`CaldeiraLeggettGaussianSaddle.gaussian_saddle_normalization` is the real companion of the complex saddle integral
`PathIntegral.MomentumPathIntegral.momentum_gaussian_integral`. All share the master weight as their common hub.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.CaldeiraLeggettGaussianSaddle
open Physlib.QuantumMechanics.ComplexAction.ComplexSaddleDecoherence

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexSaddleEntropicWeight


/-- **The reduced-density exponent is the master complex-action weight** — for any complex effective action `A`,

`e^{−A} = complexActionPathIntegralWeight (−ℏ·Im A) (ℏ·Re A) ℏ`,

i.e. `ρ_S ∝ e^{−A}` (Eq. 21) realizes the master path-integral weight `exp[(i/ℏ)S_R − (1/ℏ)S_I]` with real action
`S_R = −ℏ Im A` and **imaginary (entropic) action** `S_I = ℏ Re A`. -/
lemma cexp_neg_eq_masterWeight (A : ℂ) (ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    Complex.exp (-A) = complexActionPathIntegralWeight (-(ℏ * A.im)) (ℏ * A.re) ℏ := by
  rw [complexActionPathIntegralWeight]
  congr 1
  rw [show (-(ℏ * A.im) / ℏ : ℝ) = -A.im by field_simp,
    show (ℏ * A.re / ℏ : ℝ) = A.re by field_simp]
  apply Complex.ext <;> simp

/-- **The modulus of the reduced-density exponent is the entropic damping** `‖e^{−A}‖ = kuikenWeight ℏ (ℏ Re A)` —
the Gaussian-saddle reduced density matrix element decays at the entropic-damping rate `exp(−Re A)`, with the
decoherence action `Re A`. -/
lemma cexp_neg_modulus_is_kuiken (A : ℂ) (ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    ‖Complex.exp (-A)‖ = kuikenWeight ℏ (ℏ * A.re) := by
  rw [cexp_neg_eq_masterWeight A ℏ hℏ, master_modulus_is_kuiken]

/-- **The modulus is `exp(−Re A)`** — the entropic damping written out; `Re A` is the decoherence quadratic form. -/
lemma cexp_neg_modulus_eq_exp_neg_re (A : ℂ) (ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    ‖Complex.exp (-A)‖ = Real.exp (-A.re) := by
  rw [cexp_neg_modulus_is_kuiken A ℏ hℏ, kuikenWeight]
  congr 1
  field_simp


variable {D : ℕ}

/-- **The reduced density matrix element modulus is the entropic damping (Eq. 21)** — for the effective-action
saddle value `A = saddleValue C X̄ B` (`CaldeiraLeggettGaussianSaddle`), the modulus of `ρ_S ∝ e^{−A}` is the
Kuiken entropic weight with imaginary action `S_I = ℏ Re A`. Combined with `effectiveAction_at_saddle`
(`S_eff(X̄) = A`), the reduced density at the complex saddle decays at the decoherence rate `exp(−Re A)`. -/
lemma saddleValue_weight_modulus_is_kuiken (C Xbar : Fin D → ℂ) (B : ℂ) (ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    ‖Complex.exp (-(saddleValue C Xbar B))‖ = kuikenWeight ℏ (ℏ * (saddleValue C Xbar B).re) :=
  cexp_neg_modulus_is_kuiken (saddleValue C Xbar B) ℏ hℏ


/-- **The Gaussian off-diagonal suppression is the entropic-damping weight of the decoherence quadratic form** —
`ComplexSaddleDecoherence.rhoMagnitude = kuikenWeight 1 (reADiag)`. The decoherence magnitude `|ρ_S| = e^{−Re A}`
(Eqs. 22–26) is literally the master weight's Kuiken entropic damping evaluated on the decoherence action `Re A`. -/
lemma rhoMagnitude_eq_kuiken (J K x y : ℝ) :
    rhoMagnitude J K x y = kuikenWeight 1 (reADiag J K x y) := by
  rw [rhoMagnitude, kuikenWeight, div_one]

end Physlib.QuantumMechanics.ComplexAction.ComplexSaddleEntropicWeight
