/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ThetaCharacters
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Orthogonality of the Chern–Simons–Witten level-`k` characters

Replaces the *posited* Kronecker inner product of the `HayashiOrthogonalityCarrier` /
`torusCharacterCarrier` (`ChernSimons.TorusHilbert`) with a **derived** orthogonality: the level-`K`
abelian characters are orthonormal under the genuine integral over the torus `z`-period `[0,1]`.

* **§A — the phase integral.** `∫₀¹ e^{2πi p z} dz = δ_{p,0}` for integer `p` (`integral_exp_two_pi_int`):
  the `z`-period integral of a nonzero abelian phase vanishes (the antiderivative is single-valued because
  `e^{2πi p} = 1`), and is `1` at `p = 0`. This is the analytic core the paper uses.
* **§B — character orthogonality.** The level-`K` character `χ_{K,a}(z) = e^{2πi K a z}` satisfies
  `∫₀¹ χ_{K,a}(z) · conj χ_{K,b}(z) dz = δ_{a,b}` for `K ≠ 0` (`levelKChar_orthogonal`): distinct charges are
  orthogonal because their difference contributes a nonzero phase `K(a−b) ≠ 0`. This **derives** the value
  the orthogonality structure assumes.

Advances item (8). The full Gaussian/twist integral over the continuous `(τ, z)` torus (with the theta
`τ`-Gaussian weight) and the `k = 0` degenerate case remain open.

## References

* E. Witten (1989, 1991); Hayashi (the CSW-gravity torus theorem). `Mathlib`
  (`integral_exp_mul_complex`, `Complex.exp_int_mul_two_pi_mul_I`).

No new axioms.
-/

set_option autoImplicit false

open Complex intervalIntegral

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-! ## §A — the phase integral -/

/-- **[`z`-period phase integral]** `∫₀¹ e^{2πi p z} dz = δ_{p,0}` for integer `p`. The nonzero phases
integrate to zero over the period (single-valued antiderivative, `e^{2πip}=1`); `p = 0` gives the constant
`1`. -/
theorem integral_exp_two_pi_int (p : ℤ) :
    (∫ z in (0 : ℝ)..1, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ) * z))
      = if p = 0 then 1 else 0 := by
  by_cases hp : p = 0
  · subst hp
    simp
  · rw [if_neg hp]
    have hc : (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
      · exact Complex.I_ne_zero
      · exact_mod_cast hp
    rw [integral_exp_mul_complex hc]
    have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ)) = 1 := by
      rw [show (2 * (Real.pi : ℂ) * Complex.I * (p : ℂ))
          = (p : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by ring]
      exact Complex.exp_int_mul_two_pi_mul_I p
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, hexp,
      sub_self, zero_div]

/-! ## §B — character orthogonality -/

/-- **The level-`K` abelian character** `χ_{K,a}(z) = e^{2πi K a z}` — the `z`-dependence of the
Chern–Simons–Witten theta mode at integer level. -/
noncomputable def levelKChar (K a : ℤ) (z : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (K : ℂ) * (a : ℂ) * z)

/-- **[Character orthogonality]** `∫₀¹ χ_{K,a}(z) · conj χ_{K,b}(z) dz = δ_{a,b}` for `K ≠ 0`. Distinct
charges are orthogonal because their difference contributes the nonzero phase `K(a−b)`; equal charges give
the unit-normalized character. This **derives** the Kronecker inner product the
`HayashiOrthogonalityCarrier` only posits. -/
theorem levelKChar_orthogonal (K a b : ℤ) (hK : K ≠ 0) :
    (∫ z in (0 : ℝ)..1, levelKChar K a z * (starRingEnd ℂ) (levelKChar K b z))
      = if a = b then 1 else 0 := by
  have hpoint : ∀ z : ℝ,
      levelKChar K a z * (starRingEnd ℂ) (levelKChar K b z)
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((K * (a - b) : ℤ) : ℂ) * z) := by
    intro z
    rw [levelKChar, levelKChar, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]
    push_cast
    ring
  rw [intervalIntegral.integral_congr (fun z _ => hpoint z), integral_exp_two_pi_int (K * (a - b))]
  rcases eq_or_ne a b with hab | hab
  · rw [if_pos hab, if_pos (by rw [hab, sub_self, mul_zero])]
  · rw [if_neg hab, if_neg (mul_ne_zero hK (sub_ne_zero.mpr hab))]

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end
