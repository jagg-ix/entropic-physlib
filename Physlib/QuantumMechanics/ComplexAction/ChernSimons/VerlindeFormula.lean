/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ModularRepresentation

/-!
# The Verlinde formula for `U(1)_k`, proving the obligation

`ChernSimons.ModularRepresentation` recorded the Verlinde formula as an *obligation*
(`CSWVerlindeFormulaObligation`): that the abelian fusion coefficients equal the `S`-matrix expression
`N_{ab}{}^c = Σ_x S_{ax} S_{bx} \overline{S_{cx}} / S_{0x}`. For `U(1)_k` this is **true and provable** from the
discrete Gauss-sum orthogonality `cswDFT_orthogonality`, so the obligation need not be assumed.

* `cswVerlinde_formula`: `[k ∣ a+b−c] = Σ_x S_{ax} S_{bx} \overline{S_{cx}} / S_{0x}`. Each summand collapses
  (the `1/√k` factors and `1/S_{0x} = √k` cancel to `1/k`) to `(1/k) e^{2πi(c−a−b)x/k}`, and the Gauss sum
  yields `[k ∣ a+b−c]`.
* `cswVerlindeFormulaObligation_inst`: the proved instance — the obligation is now a theorem, linking the
  new `S`-matrix / Gauss-sum results to the fusion-rule infrastructure.

## References

* E. Verlinde (1988); E. Witten (1989); Hayashi (CSW-gravity torus theorem). `Physlib`
  (`cswDFT_orthogonality`, `cswSMatrix`).

No additional assumptions.
-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-- **[Verlinde formula for `U(1)_k`]** The abelian fusion coefficient `[k ∣ a+b−c]` equals the `S`-matrix
Verlinde expression `Σ_x S_{ax} S_{bx} \overline{S_{cx}} / S_{0x}`. -/
theorem cswVerlinde_formula (k : ℕ) (hk : 0 < k) (a b c : Fin k) :
    cswFusionCoeff k a b c = cswVerlindeCoefficientByS k hk a b c := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hsqrt : (Real.sqrt k : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact (Real.sqrt_pos.mpr (by exact_mod_cast hk)).ne'
  have hp : (1 / (Real.sqrt k : ℂ)) ≠ 0 := one_div_ne_zero hsqrt
  have hscal : (1 / (Real.sqrt k : ℂ)) * (1 / (Real.sqrt k : ℂ)) * (1 / (Real.sqrt k : ℂ))
      / (1 / (Real.sqrt k : ℂ)) = 1 / (k : ℂ) := by
    rw [mul_div_assoc, div_self hp, mul_one, div_mul_div_comm, one_mul, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by positivity), Complex.ofReal_natCast]
  have hterm : ∀ x : Fin k,
      cswSMatrix k a x * cswSMatrix k b x * star (cswSMatrix k c x)
          / cswSMatrix k (cswZeroCharge k hk) x
        = (1 / (k : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I
            * (((c.val : ℤ) - (a.val : ℤ) - (b.val : ℤ) : ℤ) : ℂ) * (x.val : ℂ) / (k : ℂ)) := by
    intro x
    have hS0 : cswSMatrix k (cswZeroCharge k hk) x = 1 / (Real.sqrt k : ℂ) := by
      simp [cswSMatrix, cswZeroCharge]
    have hconjC : star (cswSMatrix k c x)
        = (1 / (Real.sqrt k : ℂ))
          * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (c.val : ℂ) * (x.val : ℂ) / (k : ℂ)) := by
      rw [← starRingEnd_apply, cswSMatrix, map_mul, map_div₀, map_one, Complex.conj_ofReal]
      congr 1
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_div₀, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast,
        map_ofNat]
      ring
    rw [cswSMatrix, cswSMatrix, hS0, hconjC,
      show (1 / (Real.sqrt k : ℂ)
            * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) * (x.val : ℂ)) / (k : ℂ)))
          * (1 / (Real.sqrt k : ℂ)
            * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (b.val : ℂ) * (x.val : ℂ)) / (k : ℂ)))
          * (1 / (Real.sqrt k : ℂ)
            * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (c.val : ℂ) * (x.val : ℂ) / (k : ℂ)))
          / (1 / (Real.sqrt k : ℂ))
        = ((1 / (Real.sqrt k : ℂ)) * (1 / (Real.sqrt k : ℂ)) * (1 / (Real.sqrt k : ℂ))
            / (1 / (Real.sqrt k : ℂ)))
          * (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) * (x.val : ℂ)) / (k : ℂ))
            * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (b.val : ℂ) * (x.val : ℂ)) / (k : ℂ))
            * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (c.val : ℂ) * (x.val : ℂ) / (k : ℂ)))
        from by ring,
      hscal, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [cswFusionCoeff, cswVerlindeCoefficientByS, Finset.sum_congr rfl (fun x _ => hterm x),
    ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun x => Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * (((c.val : ℤ) - (a.val : ℤ) - (b.val : ℤ) : ℤ) : ℂ) * (x : ℂ) / (k : ℂ))) k,
    cswDFT_orthogonality k hk ((c.val : ℤ) - (a.val : ℤ) - (b.val : ℤ))]
  have hiff : ((k : ℤ) ∣ ((c.val : ℤ) - (a.val : ℤ) - (b.val : ℤ)))
      ↔ ((k : ℤ) ∣ ((a.val : ℤ) + (b.val : ℤ) - (c.val : ℤ))) := by
    rw [show (c.val : ℤ) - (a.val : ℤ) - (b.val : ℤ)
        = -((a.val : ℤ) + (b.val : ℤ) - (c.val : ℤ)) from by ring, Int.dvd_neg]
  by_cases hdvd : (k : ℤ) ∣ ((a.val : ℤ) + (b.val : ℤ) - (c.val : ℤ))
  · rw [if_pos hdvd, if_pos (hiff.mpr hdvd), one_div_mul_cancel hk0]
  · rw [if_neg hdvd, if_neg (fun h => hdvd (hiff.mp h)), mul_zero]

/-- **[Verlinde-formula obligation proved]** The instance making the `U(1)_k` Verlinde formula a theorem
rather than an assumption. -/
def cswVerlindeFormulaObligation_inst (k : ℕ) (hk : 0 < k) :
    CSWVerlindeFormulaObligation k hk where
  verlinde_formula := cswVerlinde_formula k hk

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end
