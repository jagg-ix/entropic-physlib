/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentState
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The squeezed vacuum: `S(r)|0⟩` as an `ℓ²` series

The single-mode squeeze operator `S(r) = exp(½ r (a² − a†²))` generates the **squeezed vacuum** `S(r)|0⟩`.
Like the coherent and thermofield-double states, this is a genuinely convergent `ℓ²` series and needs no
exponential of the unbounded generator `a² − a†²`: only the **even** number states appear, with

`S(r)|0⟩ = (1/√cosh r) Σₙ (−tanh r)ⁿ (√((2n)!)/(2ⁿ n!)) |2n⟩`.

Here the (unnormalized, `⟨0|` component `= 1`) squeezed vacuum is built as the `ℓ²` vector with those
coefficients.  Square-summability is the central-binomial estimate: `|c_{2n}|² = (tanh²r)ⁿ·binom(2n,n)/4ⁿ ≤
(tanh²r)ⁿ` (`Nat.centralBinom_le_four_pow`), a convergent geometric series since `|tanh r| < 1`.

* `squeezeCoeff`, `squeezedVacuum` — `S(r)|0⟩` as an `ℓ²` vector.
* `squeezeCoeff_odd` — `⟨2n+1|S(r)|0⟩ = 0`: only even number states are populated (photons in pairs).
* `sqCoeffR_recurrence` — the **Bogoliubov recurrence** `√(2n+2) c_{2n+2} = −tanh r·√(2n+1) c_{2n}`, i.e.
  `(a cosh r + a† sinh r) S(r)|0⟩ = 0`: the squeezed vacuum is annihilated by the Bogoliubov-rotated
  annihilation operator `b = S(r) a S(r)† = a cosh r − a† sinh r` (read `b S(r)|0⟩ = S(r) a|0⟩ = 0`).

Honest scope: the squeezed vacuum as an `ℓ²` vector, its even-only support, and the Bogoliubov coefficient
recurrence.  The full unitary `S(r)` on `ℓ²` and the exact normalization `‖S(r)|0⟩‖ = √cosh r` (which needs the
central-binomial generating function `Σ binom(2n,n)/4ⁿ xⁿ = 1/√(1−x)`) are not built; the vector and its
defining Bogoliubov relation are captured directly.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockSqueezedVacuum

open scoped ENNReal
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion

/-- The even-index squeezed-vacuum coefficient `c_{2n} = (−tanh r)ⁿ √((2n)!)/(2ⁿ n!)` (real). -/
def sqCoeffR (r : ℝ) (n : ℕ) : ℝ :=
  (-Real.tanh r) ^ n * Real.sqrt ((2 * n).factorial) / (2 ^ n * n.factorial)

/-- The squeezed-vacuum coefficient on all number states: `c_k = c_{k}` if `k` even, else `0`. -/
def squeezeCoeffR (r : ℝ) (k : ℕ) : ℝ := if Even k then sqCoeffR r (k / 2) else 0

/-- The squeezed-vacuum coefficient as a complex `ℓ²` coordinate. -/
def squeezeCoeff (r : ℝ) (k : ℕ) : ℂ := (squeezeCoeffR r k : ℂ)

theorem squeezeCoeffR_two_mul (r : ℝ) (n : ℕ) : squeezeCoeffR r (2 * n) = sqCoeffR r n := by
  rw [squeezeCoeffR, if_pos (even_two_mul n), Nat.mul_div_cancel_left n (by norm_num)]

/-- **[Only even states populated] `⟨2n+1|S(r)|0⟩ = 0`.**  A squeeze creates photons in pairs, so the odd
number states have zero amplitude. -/
theorem squeezeCoeff_odd (r : ℝ) {k : ℕ} (hk : ¬ Even k) : squeezeCoeff r k = 0 := by
  rw [squeezeCoeff, squeezeCoeffR, if_neg hk, Complex.ofReal_zero]

/-- `c_{2n}² = (tanh²r)ⁿ · (2n)!/(4ⁿ(n!)²)`. -/
theorem sqCoeffR_sq (r : ℝ) (n : ℕ) :
    (sqCoeffR r n) ^ 2 = (Real.tanh r ^ 2) ^ n * ((2 * n).factorial / (4 ^ n * (n.factorial) ^ 2)) := by
  rw [sqCoeffR, div_pow, mul_pow, Real.sq_sqrt (by positivity),
    show ((-Real.tanh r) ^ n) ^ 2 = (Real.tanh r ^ 2) ^ n from by
      rw [← pow_mul, mul_comm n 2, pow_mul, neg_sq],
    mul_pow, show ((2 : ℝ) ^ n) ^ 2 = 4 ^ n from by
      rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num]
  ring

/-- `(2n)! = binom(2n,n)·(n!)²`. -/
theorem factorial_two_mul_eq (n : ℕ) :
    ((2 * n).factorial : ℝ) = (Nat.centralBinom n : ℝ) * (n.factorial) ^ 2 := by
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n by omega] at h
  rw [Nat.centralBinom_eq_two_mul_choose]
  have h' : ((2 * n).factorial : ℝ) = ((2 * n).choose n : ℝ) * n.factorial * n.factorial := by
    exact_mod_cast h.symm
  rw [h']; ring

/-- `c_{2n}² ≤ (tanh²r)ⁿ` (central-binomial estimate, `binom(2n,n) ≤ 4ⁿ`). -/
theorem sqCoeffR_sq_le (r : ℝ) (n : ℕ) : (sqCoeffR r n) ^ 2 ≤ (Real.tanh r ^ 2) ^ n := by
  rw [sqCoeffR_sq]
  have hle : ((2 * n).factorial : ℝ) / (4 ^ n * (n.factorial) ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity), factorial_two_mul_eq]
    have hcb : (Nat.centralBinom n : ℝ) ≤ 4 ^ n := by exact_mod_cast Nat.centralBinom_le_four_pow n
    have hnf : (0 : ℝ) ≤ (n.factorial) ^ 2 := by positivity
    nlinarith [hcb, hnf]
  exact mul_le_of_le_one_right (by positivity) hle

/-- The squared coefficients are summable (geometric bound). -/
theorem sqCoeffR_sq_summable (r : ℝ) : Summable (fun n => (sqCoeffR r n) ^ 2) := by
  have htanh_sq : Real.tanh r ^ 2 < 1 := by
    nlinarith [Real.tanh_lt_one r, Real.neg_one_lt_tanh r]
  exact Summable.of_nonneg_of_le (fun n => sq_nonneg _) (sqCoeffR_sq_le r)
    (summable_geometric_of_lt_one (by positivity) htanh_sq)

/-- The squeezed-vacuum coefficients are square-summable. -/
theorem squeezeCoeff_memℓp (r : ℝ) : Memℓp (squeezeCoeff r) 2 := by
  refine memℓp_gen ?_
  have hcong : (fun k : ℕ => ‖squeezeCoeff r k‖ ^ (2 : ℝ≥0∞).toReal)
      = (fun k : ℕ => if Even k then (sqCoeffR r (k / 2)) ^ 2 else 0) := by
    funext k
    rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
      squeezeCoeff, squeezeCoeffR]
    split_ifs with hk
    · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · rw [Complex.ofReal_zero, norm_zero]; norm_num
  rw [hcong]
  refine (Function.Injective.summable_iff (g := fun n : ℕ => 2 * n)
    (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)) ?_).mp ?_
  · intro k hk
    have hne : ¬ Even k := fun hke => by obtain ⟨m, rfl⟩ := hke; exact hk ⟨m, two_mul m⟩
    rw [if_neg hne]
  · have hcomp : ((fun k : ℕ => if Even k then (sqCoeffR r (k / 2)) ^ 2 else 0) ∘ fun n : ℕ => 2 * n)
        = (fun n => (sqCoeffR r n) ^ 2) := by
      funext n
      show (if Even (2 * n) then (sqCoeffR r ((2 * n) / 2)) ^ 2 else 0) = (sqCoeffR r n) ^ 2
      rw [if_pos (even_two_mul n), Nat.mul_div_cancel_left n (by norm_num)]
    rw [hcomp]; exact sqCoeffR_sq_summable r

/-- **The squeezed vacuum** `S(r)|0⟩` as a vector in `ℓ²`. -/
def squeezedVacuum (r : ℝ) : FockHilbert := ⟨squeezeCoeff r, squeezeCoeff_memℓp r⟩

@[simp] theorem squeezedVacuum_apply (r : ℝ) (k : ℕ) : (squeezedVacuum r) k = squeezeCoeff r k := rfl

/-- **[Bogoliubov recurrence] `√(2n+2) c_{2n+2} = −tanh r·√(2n+1) c_{2n}`.**  The squeezed vacuum is annihilated
by the Bogoliubov-rotated annihilation operator `b = a cosh r + a† sinh r` (`b S(r)|0⟩ = S(r) a|0⟩ = 0`); this
is the recurrence read off coordinate `2n+1`. -/
theorem sqCoeffR_recurrence (r : ℝ) (n : ℕ) :
    Real.sqrt (2 * (n : ℝ) + 2) * sqCoeffR r (n + 1)
      = -Real.tanh r * Real.sqrt (2 * (n : ℝ) + 1) * sqCoeffR r n := by
  have e2 : Real.sqrt ((2 * (n + 1)).factorial)
      = Real.sqrt (2 * (n : ℝ) + 2) * (Real.sqrt (2 * (n : ℝ) + 1) * Real.sqrt ((2 * n).factorial)) := by
    have e1 : ((2 * (n + 1)).factorial : ℝ)
        = (2 * (n : ℝ) + 2) * ((2 * (n : ℝ) + 1) * ((2 * n).factorial)) := by
      have h1 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [h1, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    rw [e1, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have e3 : Real.sqrt (2 * (n : ℝ) + 2) * Real.sqrt (2 * (n : ℝ) + 2) = 2 * (n : ℝ) + 2 :=
    Real.mul_self_sqrt (by positivity)
  rw [sqCoeffR, sqCoeffR, e2, pow_succ (-Real.tanh r) n, pow_succ (2 : ℝ) n,
    show ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial) from by
      rw [Nat.factorial_succ]; push_cast; ring]
  rw [show Real.sqrt (2 * (n : ℝ) + 2)
        * ((-Real.tanh r) ^ n * -Real.tanh r
          * (Real.sqrt (2 * (n : ℝ) + 2) * (Real.sqrt (2 * (n : ℝ) + 1) * Real.sqrt ((2 * n).factorial)))
          / (2 ^ n * 2 * (((n : ℝ) + 1) * n.factorial)))
      = (Real.sqrt (2 * (n : ℝ) + 2) * Real.sqrt (2 * (n : ℝ) + 2))
          * ((-Real.tanh r) ^ n * -Real.tanh r
          * (Real.sqrt (2 * (n : ℝ) + 1) * Real.sqrt ((2 * n).factorial)))
          / (2 ^ n * 2 * (((n : ℝ) + 1) * n.factorial)) from by ring, e3]
  rw [show (2 : ℝ) * (n : ℝ) + 2 = 2 * ((n : ℝ) + 1) from by ring]
  field_simp

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockSqueezedVacuum

end
