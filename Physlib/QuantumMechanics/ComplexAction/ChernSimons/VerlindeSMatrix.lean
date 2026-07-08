/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.CharacterOrthogonality

/-!
# The level-`k` Chern–Simons–Witten Verlinde `S`-matrix and its unitarity

Formalizes the algebraic heart of the modular `S`-matrix of the level-`k` abelian Chern–Simons–Witten
theory: the discrete-Fourier / quadratic-Gauss-sum orthogonality, and the resulting **unitarity** of the
`S`-matrix `S_{ab} = (1/√k) e^{−2πi ab/k}`.

* **§A — discrete Gauss-sum orthogonality.** `Σ_{c=0}^{k−1} e^{2πi j c / k} = k·[k ∣ j]`
  (`cswDFT_orthogonality`): a geometric sum of `k`-th roots of unity collapses to `k` when the frequency `j`
  is a multiple of `k` and to `0` otherwise (single-valued cancellation, `geom_sum_eq`).
* **§B — the `S`-matrix and its unitarity.** With `S_{ab} = (1/√k) e^{−2πi ab/k}` on the `k` charges
  (`cswSMatrix`), `Σ_c S_{ac} \overline{S_{bc}} = δ_{ab}` (`cswSMatrix_unitary`): the rows are orthonormal, so
  `S` is unitary — the defining property of a modular `S`-matrix and the consistency input to the Verlinde
  formula.

This is the discrete (representation-theoretic) content of item (9)'s `S`-matrix. The **analytic** statement
that this `S` diagonalizes the theta inversion, `Θ_a(−1/τ) = Σ_b S_{ab} Θ_b(τ)` (Poisson resummation of
`cswThetaCharge_modular_S` over residues mod `k`), and the Verlinde fusion rules, remain open.

## References

* E. Witten (1989, 1991); E. Verlinde (1988); Hayashi (the CSW-gravity torus theorem). `Mathlib`
  (`geom_sum_eq`, `Complex.exp_eq_one_iff`, `Complex.exp_int_mul_two_pi_mul_I`).

No new axioms.
-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-! ## §A — discrete Gauss-sum orthogonality -/

/-- **[Discrete Gauss-sum orthogonality]** `Σ_{c=0}^{k−1} e^{2πi j c/k} = k·[k ∣ j]`. The geometric sum of
`k`-th roots of unity is `k` when the frequency is a multiple of the level and `0` otherwise. -/
theorem cswDFT_orthogonality (k : ℕ) (hk : 0 < k) (j : ℤ) :
    (∑ c ∈ Finset.range k,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (c : ℂ) / (k : ℂ)))
      = if (k : ℤ) ∣ j then (k : ℂ) else 0 := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  set x : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) / (k : ℂ)) with hxdef
  have hterm : ∀ c : ℕ,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (c : ℂ) / (k : ℂ)) = x ^ c := by
    intro c
    rw [hxdef, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  have hxk : x ^ k = 1 := by
    rw [hxdef, ← Complex.exp_nat_mul,
      show (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) / (k : ℂ))
        = (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I j
  by_cases hdvd : (k : ℤ) ∣ j
  · rw [if_pos hdvd]
    have hx1 : x = 1 := by
      obtain ⟨m, hm⟩ := hdvd
      rw [hxdef, show 2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) / (k : ℂ)
          = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by rw [hm]; push_cast; field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [hx1]
    simp [Finset.sum_const, Finset.card_range]
  · rw [if_neg hdvd]
    have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have hxne : x ≠ 1 := by
      rw [hxdef]
      intro hx1
      rw [Complex.exp_eq_one_iff] at hx1
      obtain ⟨n, hn⟩ := hx1
      refine hdvd ⟨n, ?_⟩
      have hcancel : (j : ℂ) / (k : ℂ) = (n : ℂ) := by
        apply mul_left_cancel₀ h2pi
        rw [← mul_div_assoc, hn, mul_comm]
      rw [div_eq_iff hk0] at hcancel
      exact_mod_cast (by rw [hcancel]; ring : (j : ℂ) = (k : ℂ) * (n : ℂ))
    rw [geom_sum_eq hxne k, hxk, sub_self, zero_div]

/-! ## §B — the `S`-matrix and its unitarity -/

/-- **The level-`k` Verlinde `S`-matrix** `S_{ab} = (1/√k) e^{−2πi ab/k}` on the `k` charge sectors. -/
noncomputable def cswSMatrix (k : ℕ) (a b : Fin k) : ℂ :=
  (1 / (Real.sqrt k : ℂ))
    * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) * (b.val : ℂ)) / (k : ℂ))

/-- **[The `S`-matrix is unitary]** `Σ_c S_{ac} \overline{S_{bc}} = δ_{ab}`. The rows are orthonormal — the
defining property of a modular `S`-matrix — by the discrete Gauss-sum orthogonality. -/
theorem cswSMatrix_unitary (k : ℕ) (hk : 0 < k) (a b : Fin k) :
    (∑ c : Fin k, cswSMatrix k a c * (starRingEnd ℂ) (cswSMatrix k b c))
      = if a = b then 1 else 0 := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hterm : ∀ c : Fin k,
      cswSMatrix k a c * (starRingEnd ℂ) (cswSMatrix k b c)
        = (1 / (k : ℂ))
          * Complex.exp (2 * (Real.pi : ℂ) * Complex.I
              * (((b.val : ℤ) - (a.val : ℤ) : ℤ) : ℂ) * (c.val : ℂ) / (k : ℂ)) := by
    intro c
    have hpref2 : (1 / (Real.sqrt k : ℂ)) * (1 / (Real.sqrt k : ℂ)) = 1 / (k : ℂ) := by
      rw [div_mul_div_comm, one_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity),
        Complex.ofReal_natCast]
    have hconjPref : (starRingEnd ℂ) (1 / (Real.sqrt k : ℂ)) = 1 / (Real.sqrt k : ℂ) := by
      rw [map_div₀, map_one, Complex.conj_ofReal]
    have hconjExp : (starRingEnd ℂ)
          (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (b.val : ℂ) * (c.val : ℂ)) / (k : ℂ)))
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b.val : ℂ) * (c.val : ℂ) / (k : ℂ)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_div₀, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast,
        map_ofNat]
      ring
    rw [cswSMatrix, cswSMatrix, map_mul, hconjPref, hconjExp,
      show (1 / (Real.sqrt k : ℂ)
            * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) * (c.val : ℂ)) / (k : ℂ)))
          * (1 / (Real.sqrt k : ℂ)
            * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b.val : ℂ) * (c.val : ℂ) / (k : ℂ)))
        = (1 / (Real.sqrt k : ℂ) * (1 / (Real.sqrt k : ℂ)))
            * (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) * (c.val : ℂ)) / (k : ℂ))
              * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b.val : ℂ) * (c.val : ℂ) / (k : ℂ)))
        from by ring,
      hpref2, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun c => Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * (((b.val : ℤ) - (a.val : ℤ) : ℤ) : ℂ) * (c : ℂ) / (k : ℂ))) k,
    cswDFT_orthogonality k hk ((b.val : ℤ) - (a.val : ℤ))]
  by_cases hab : a = b
  · subst hab
    rw [sub_self, if_pos (dvd_zero _), if_pos rfl, one_div_mul_cancel hk0]
  · rw [if_neg hab, if_neg, mul_zero]
    intro hdvd
    apply hab
    apply Fin.ext
    have hak : ((a.val : ℤ)) < (k : ℤ) := by exact_mod_cast a.isLt
    have hbk : ((b.val : ℤ)) < (k : ℤ) := by exact_mod_cast b.isLt
    have ha0 : (0 : ℤ) ≤ (a.val : ℤ) := Int.natCast_nonneg _
    have hb0 : (0 : ℤ) ≤ (b.val : ℤ) := Int.natCast_nonneg _
    rcases lt_trichotomy (b.val : ℤ) (a.val : ℤ) with h | h | h
    · have := Int.le_of_dvd (by omega) (dvd_sub_comm.mp hdvd)
      omega
    · omega
    · have := Int.le_of_dvd (by omega) hdvd
      omega

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end
