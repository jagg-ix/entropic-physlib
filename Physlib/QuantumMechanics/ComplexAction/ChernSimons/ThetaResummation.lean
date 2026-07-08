/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ModularRepresentation

/-!
# Poisson resummation of the Chern–Simons–Witten theta multiplet

Mathlib's `jacobiTheta₂_functional_equation` **is** Poisson summation, and `summable_jacobiTheta₂_term_iff`
provides the convergence input. So the modular behaviour of the level-`k` characters is derivable, not an
assumed obligation. This file records the two genuine, *true* statements.

* **§A — per-character modular `S` transform** (`cswThetaBasis_modular_S`): the basis character
 `Θ_a(τ,z) = cswThetaBasis k a τ z` equals its Poisson-transformed form at the inverted parameter
 `−1/(kτ)`, **including** the automorphy factor `1/(−i kτ)^{1/2}` and the Gaussian — this is the
 specialization of `cswThetaCharge_modular_S` to the charge sector `a/k`.

* **§B — the resummation identity** (`cswSMatrix_thetaMode_resummation_term`): the heart of
 `Σ_b S_{ab} Θ_b(τ,z) = (1/√k) · jacobiTheta₂(z − a/k)(τ/k)`. Term by term, under the lattice bijection
 `m = nk + b`, the modular `S`-weighted mode `S_{ab} · θ_{n+b/k}(τ,z)` is exactly the `m`-th term of a
 single rescaled Jacobi theta at `(z − a/k, τ/k)`. Summing this over `(b, n)` (a reindexing of `ℤ`) re-sums
 the whole `S`-matrix multiplet into one theta function.

**Note on the naive obligation.** The bare statement `Θ_a(−1/τ) = Σ_b S_{ab} Θ_b(τ)` (as in
`CSWPoissonResummationObligation`) is *false* as written — at `k = 1` it would force
`jacobiTheta₂ z (−1/τ) = jacobiTheta₂ z τ`, contradicting the functional equation. The modular
identity includes the `1/(−ikτ)^{1/2}` automorphy factor recorded in §A; §B is the (factor-free, hence true)
resummation of the multiplet into a rescaled theta.

## References

* E. Witten (1989, 1991); Hayashi (CSW-gravity torus theorem). `Mathlib` (`jacobiTheta₂_functional_equation`,
 `summable_jacobiTheta₂_term_iff`).

No additional assumptions.
-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-! ## §A — per-character modular `S` transform (Poisson) -/

/-- **[Per-character modular `S` transform, from Mathlib Poisson]** The level-`k` charge-`a` character equals
its Poisson-transformed value at the inverted modular parameter `−1/(kτ)`, with the genuine automorphy factor
`1/(−i kτ)^{1/2}` and Gaussian. This is `cswThetaCharge_modular_S` (built on
`jacobiTheta₂_functional_equation`) specialized to the charge sector `a/k`. -/
theorem cswThetaBasis_modular_S (k : ℕ) (a : Fin k) (τ z : ℂ) :
    cswThetaBasis k a τ z
      = thetaChargePrefactor (k : ℂ) ((a.val : ℂ) / (k : ℂ)) τ z
        * (1 / (-Complex.I * ((k : ℂ) * τ)) ^ (1 / 2 : ℂ)
          * Complex.exp (-(Real.pi : ℂ) * Complex.I
              * ((k : ℂ) * (z + ((a.val : ℂ) / (k : ℂ)) * τ)) ^ 2 / ((k : ℂ) * τ))
          * jacobiTheta₂ (((k : ℂ) * (z + ((a.val : ℂ) / (k : ℂ)) * τ)) / ((k : ℂ) * τ))
              (-1 / ((k : ℂ) * τ))) := by
  rw [cswThetaBasis]
  exact cswThetaCharge_modular_S (k : ℂ) ((a.val : ℂ) / (k : ℂ)) τ z

/-! ## §B — the resummation identity (lattice reindexing) -/

/-- **[Resummation term identity]** Under the lattice bijection `m = nk + b`, the modular-`S`-weighted theta
mode `S_{ab} · θ_{n+b/k}(τ,z)` equals the `m`-th term of the single rescaled Jacobi theta
`(1/√k) · jacobiTheta₂(z − a/k)(τ/k)`. Summing over `(b, n) ∈ Fin k × ℤ` (a reindexing of `ℤ`) re-sums the
whole `S`-matrix multiplet `Σ_b S_{ab} Θ_b` into that one theta function. The extra phase `e^{2πi·a n} = 1`
absorbs the integer part of the charge shift. -/
theorem cswSMatrix_thetaMode_resummation_term (k : ℕ) (hk : 0 < k) (a b : Fin k) (n : ℤ) (τ z : ℂ) :
    cswSMatrix k a b * thetaMode (k : ℂ) ((n : ℂ) + (b.val : ℂ) / (k : ℂ)) τ z
      = (1 / (Real.sqrt k : ℂ))
        * jacobiTheta₂_term (n * (k : ℤ) + (b.val : ℤ)) (z - (a.val : ℂ) / (k : ℂ)) (τ / (k : ℂ)) := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  rw [cswSMatrix, thetaMode, jacobiTheta₂_term, mul_assoc, ← Complex.exp_add]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨(a.val : ℤ) * n, ?_⟩
  push_cast
  field_simp
  ring

/-! ## §C — the full multiplet resummation -/

/-- The lattice bijection `(b, n) ↦ n·k + b` identifying `Fin k × ℤ` with `ℤ` (residue mod `k` paired with
quotient). This is the reindexing that re-sums the `S`-matrix multiplet into a single theta. -/
def cswLatticeEquiv (k : ℕ) (hk : 0 < k) : Fin k × ℤ ≃ ℤ where
  toFun p := p.2 * (k : ℤ) + (p.1.val : ℤ)
  invFun m := (⟨(m % (k : ℤ)).toNat, by
      have h1 : 0 ≤ m % (k : ℤ) := Int.emod_nonneg m (by exact_mod_cast hk.ne')
      have h2 : m % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos m (by exact_mod_cast hk)
      omega⟩, m / (k : ℤ))
  left_inv := by
    rintro ⟨b, n⟩
    have hbval : ((b.val : ℤ)) % (k : ℤ) = (b.val : ℤ) :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast b.isLt)
    refine Prod.ext ?_ ?_
    · apply Fin.ext
      show ((n * (k : ℤ) + (b.val : ℤ)) % (k : ℤ)).toNat = b.val
      rw [add_comm, mul_comm n (k : ℤ), Int.add_mul_emod_self_left, hbval, Int.toNat_natCast]
    · show (n * (k : ℤ) + (b.val : ℤ)) / (k : ℤ) = n
      rw [add_comm, Int.add_mul_ediv_right _ _ (by exact_mod_cast hk.ne'),
        Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast b.isLt), zero_add]
  right_inv := by
    intro m
    have h1 : 0 ≤ m % (k : ℤ) := Int.emod_nonneg m (by exact_mod_cast hk.ne')
    show (m / (k : ℤ)) * (k : ℤ) + ((m % (k : ℤ)).toNat : ℤ) = m
    rw [Int.toNat_of_nonneg h1, Int.ediv_mul_add_emod]

@[simp] theorem cswLatticeEquiv_apply (k : ℕ) (hk : 0 < k) (b : Fin k) (n : ℤ) :
    cswLatticeEquiv k hk (b, n) = n * (k : ℤ) + (b.val : ℤ) := rfl

/-- **[Multiplet resummation]** `Σ_b S_{ab} Θ_b(τ,z) = (1/√k) · jacobiTheta₂(z − a/k)(τ/k)`. The modular
`S`-matrix sum over the `k` charge sectors re-sums — via the lattice bijection `m = nk + b` — into a single
Jacobi theta at the rescaled point `(z − a/k, τ/k)`. Requires `0 < im τ` for the lattice sums to converge. -/
theorem cswSMatrix_thetaBasis_resummation (k : ℕ) (hk : 0 < k) (a : Fin k) (τ z : ℂ) (hτ : 0 < τ.im) :
    (∑ b : Fin k, cswSMatrix k a b * cswThetaBasis k b τ z)
      = (1 / (Real.sqrt k : ℂ)) * jacobiTheta₂ (z - (a.val : ℂ) / (k : ℂ)) (τ / (k : ℂ)) := by
  set F : ℤ → ℂ :=
    fun m => (1 / (Real.sqrt k : ℂ)) * jacobiTheta₂_term m (z - (a.val : ℂ) / (k : ℂ)) (τ / (k : ℂ))
    with hF
  have hτk : 0 < (τ / (k : ℂ)).im := by
    rw [show (k : ℂ) = ((k : ℝ) : ℂ) from (Complex.ofReal_natCast k).symm, Complex.div_ofReal_im]
    exact div_pos hτ (by exact_mod_cast hk)
  have hsum : Summable F :=
    ((summable_jacobiTheta₂_term_iff _ _).mpr hτk).mul_left _
  -- LHS: each character is a lattice tsum; pull `S` in and apply the per-term identity
  have hLHS : (∑ b : Fin k, cswSMatrix k a b * cswThetaBasis k b τ z)
      = ∑ b : Fin k, ∑' n : ℤ, F (n * (k : ℤ) + (b.val : ℤ)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [cswThetaBasis, cswThetaCharge, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [hF]
    exact cswSMatrix_thetaMode_resummation_term k hk a b n τ z
  -- RHS: the target theta is the tsum of F
  have hRHS : (∑' m : ℤ, F m)
      = (1 / (Real.sqrt k : ℂ)) * jacobiTheta₂ (z - (a.val : ℂ) / (k : ℂ)) (τ / (k : ℂ)) := by
    rw [hF, tsum_mul_left]; rfl
  have hsum_e : Summable (fun c : Fin k × ℤ => F (cswLatticeEquiv k hk c)) :=
    (cswLatticeEquiv k hk).summable_iff.mpr hsum
  have hrow : ∀ b : Fin k, Summable (fun c : ℤ => F (cswLatticeEquiv k hk (b, c))) := by
    intro b
    refine hsum.comp_injective (fun c c' h => ?_)
    simp only [cswLatticeEquiv_apply, add_left_inj] at h
    exact mul_right_cancel₀ (by exact_mod_cast hk.ne') h
  rw [hLHS, ← hRHS, ← (cswLatticeEquiv k hk).tsum_eq F, hsum_e.tsum_prod' hrow, tsum_fintype]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine tsum_congr fun n => ?_
  rfl

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end
