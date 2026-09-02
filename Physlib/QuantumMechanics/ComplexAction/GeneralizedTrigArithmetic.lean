/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngleRemarks
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Arithmetic properties of the generalized trigonometric functions (Takeuchi 2017)

Takeuchi's *Arithmetic properties of the generalized trigonometric functions* (RIMS Kôkyûroku **2032** (2017)
76–100) studies the two-parameter `sin_{p,q}` and the generalized `π_{p,q}`. Its objects coincide with those already
formalized here: Takeuchi's `sin_{p,q}^{-1} x = ∫₀^x dt/(1−t^q)^{1/p}` **is** `PurelyNonlinearGeneralizedTrig.arcsinMN`
(with `(p,q)` ↔ our `(m,n)`), and his

`π_{p,q} = (2/q) B(1/p*, 1/q)`   with the **Hölder conjugate** `p* = p/(p−1)`   (Eq. 1.1)

**is** `PurelyNonlinearActionAngleRemarks.genPi`. This module formalizes the arithmetic core: the conjugate
exponent and its Hölder involution, `genPi` in Takeuchi's `B(1/p*, 1/q)` form, and the Beta-duplication identity

`π_{p*,p} = 2^{1−2/p} · π_{2,p}`   (Eq. 3.8),

which is the Legendre duplication `Γ(a)Γ(a+½) = 2^{1−2a}√π·Γ(2a)` (`Real.Gamma_mul_Gamma_add_half`) in disguise.

* **§A — the Hölder conjugate exponent (Takeuchi `p*`).** `conjugateExponent`; **`holder_conjugate`**
  (`1/p + 1/p* = 1`), **`conjugateExponent_involutive`** (`(p*)* = p`), `conjugateExponent_two`.
* **§B — `π_{p,q}` in Takeuchi's Beta form.** **`genPi_eq_conjugate_beta`** (`genPi m n = (2/n) B(1/m*, 1/n)`).
* **§C — the Beta-duplication of `π` (Eq. 3.8).** **`betaFn_self_dup`** (`B(a,a) = 2^{1−2a} B(½,a)`),
  **`genPi_conjugate_eq_duplication`** (`π_{p*,p} = 2^{1−2/p} π_{2,p}`).

**Honest layering.** Exact `betaFn` / `Real.Gamma` identities via the Legendre duplication. Takeuchi's
multiple-angle formulas (Thm 3.1), the Gregory–Leibniz series for `π_{p*,p}` (Thm 3.3), the `p`-Laplacian
eigenfunctions and the lemniscate/elliptic content are the paper's special-function analysis, recorded not
re-derived; `arcsinMN`/`genPi` = Takeuchi's `sin_{p,q}^{-1}`/`π_{p,q}` provide the connection.

## References

* S. Takeuchi, RIMS Kôkyûroku 2032 (2017) 76–100, Eqs. 1.1, 3.8. Arithmetic layer of
  `PurelyNonlinearGeneralizedTrig` / `PurelyNonlinearActionAngleRemarks`.


-/

set_option autoImplicit false

open scoped Real
open Physlib.QuantumMechanics.ComplexAction.GeneralizedIsotonicOscillator
open Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngleRemarks

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GeneralizedTrigArithmetic


/-- The **Hölder conjugate exponent** `p* = p/(p−1)` (Takeuchi's `p*`) — the exponent conjugate to `p` under
`1/p + 1/p* = 1`, appearing in `π_{p,q} = (2/q)B(1/p*, 1/q)`. -/
noncomputable def conjugateExponent (p : ℝ) : ℝ := p / (p - 1)

/-- **The Hölder relation** `1/p + 1/p* = 1`. -/
lemma holder_conjugate (p : ℝ) (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    1 / p + 1 / conjugateExponent p = 1 := by
  have h1 : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
  unfold conjugateExponent
  field_simp
  ring

/-- **The conjugate is an involution** `(p*)* = p`. -/
lemma conjugateExponent_involutive (p : ℝ) (hp1 : p ≠ 1) :
    conjugateExponent (conjugateExponent p) = p := by
  have h1 : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
  unfold conjugateExponent
  rw [div_sub_one h1, show p - (p - 1) = 1 from by ring, div_div_eq_mul_div, div_one,
    div_mul_cancel₀ p h1]

/-- **`2* = 2`** — the classical `π_{2,q}` case is self-conjugate. -/
lemma conjugateExponent_two : conjugateExponent 2 = 2 := by
  unfold conjugateExponent; norm_num


/-- **`π_{p,q}` is `(2/q) B(1/p*, 1/q)`** (Takeuchi Eq. 1.1) — `genPi m n = (2/n) B(1/m*, 1/n)`, since
`(m−1)/m = 1/m*`. This is `genPi` written with the Hölder conjugate exponent. -/
lemma genPi_eq_conjugate_beta (m n : ℝ) :
    genPi m n = 2 / n * betaFn (1 / conjugateExponent m) (1 / n) := by
  unfold genPi conjugateExponent
  rw [one_div_div]


/-- **The Beta duplication** `B(a,a) = 2^{1−2a} B(½, a)` (for `a > 0`) — the Legendre duplication
`Γ(a)Γ(a+½) = 2^{1−2a}√π·Γ(2a)` (`Real.Gamma_mul_Gamma_add_half`) written for the beta function. -/
lemma betaFn_self_dup (a : ℝ) (ha : 0 < a) :
    betaFn a a = (2 : ℝ) ^ (1 - 2 * a) * betaFn (1 / 2) a := by
  have hΓa : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hΓ2a : (0 : ℝ) < Real.Gamma (2 * a) := Real.Gamma_pos_of_pos (by linarith)
  have hΓah : (0 : ℝ) < Real.Gamma (a + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hleg := Real.Gamma_mul_Gamma_add_half a
  unfold betaFn
  rw [Real.Gamma_one_half_eq, show a + a = 2 * a from by ring,
    show (1 : ℝ) / 2 + a = a + 1 / 2 from by ring]
  field_simp
  rw [show (2 * a + 1) / 2 = a + 1 / 2 from by ring]
  linear_combination hleg

/-- **The generalized `π` duplication (Takeuchi Eq. 3.8)** `π_{p*,p} = 2^{1−2/p} · π_{2,p}` — for `p > 1`, the
generalized `π` at the conjugate `(p*, p)` and at `(2, p)` differ by the Legendre factor `2^{1−2/p}`. -/
lemma genPi_conjugate_eq_duplication (p : ℝ) (hp : 1 < p) :
    genPi (conjugateExponent p) p = (2 : ℝ) ^ (1 - 2 / p) * genPi 2 p := by
  have hp1 : p ≠ 1 := by linarith
  rw [genPi_eq_conjugate_beta (conjugateExponent p) p, conjugateExponent_involutive p hp1,
    genPi_eq_conjugate_beta 2 p, conjugateExponent_two,
    betaFn_self_dup (1 / p) (by positivity),
    show (1 : ℝ) - 2 * (1 / p) = 1 - 2 / p from by ring]
  ring

end Physlib.QuantumMechanics.ComplexAction.GeneralizedTrigArithmetic
