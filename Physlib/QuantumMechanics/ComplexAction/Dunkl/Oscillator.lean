/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LinearBoltzmannOperator
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The Wigner–Dunkl oscillator on `ℝ[X]`

Concrete formalization of the algebraic core of Wigner–Dunkl quantum mechanics, following
*G. Junker, "On the Path Integral Formulation of Wigner–Dunkl Quantum Mechanics," arXiv:2312.12895*
(building on Dunkl's differential-difference operators and Wigner's deformed oscillator).

The reflection group `Z₂` acts on the line by `x ↦ -x`. The **Dunkl operator** (Junker Eq. 1)
`D_ν := ∂_x + (ν/x)(1 − R)`, with reflection `(Rf)(x) := f(-x)` (Eq. 2), deforms the derivative. We
realize it concretely on the polynomial ring `ℝ[X]`, where `(1 − R)p` has zero constant term and is
therefore divisible by `X` (`divX`), so `D_ν` is an honest endomorphism of `ℝ[X]`:

* **(Eq. 9) the Dunkl number** `[n]_ν = n + ν(1 − (−1)ⁿ)` (`dunklNumber`), with `[2m]_ν = 2m`,
  `[2m+1]_ν = 2m+1+2ν` (Eq. 10) and the key difference `[n+1]_ν − [n]_ν = 1 + 2ν(−1)ⁿ`.
* **(Eq. 19) the Dunkl operator on monomials** `D_ν Xⁿ = [n]_ν Xⁿ⁻¹` (`dunklOp_Xpow`) — the
  deformation of `∂_x Xⁿ = n Xⁿ⁻¹`, recovered at `ν = 0` (`dunklOp_zero_param`: `D₀ = ∂`).
* **(Eq. 3) the deformed Heisenberg algebra** `[D_ν, X·] = 1 + 2νR` (`dunkl_deformed_heisenberg`),
  the Wigner–Dunkl deformation of the canonical commutator `[∂, X·] = 1`.
* **the oscillator ladder** `[v + D, v − D] = 2[D, v]` (`dunkl_ladder_via_collisionStar`), written in
  the Saveliev `collisionStar` (`ad`) calculus — so the Wigner–Dunkl oscillator's raising/lowering
  commutator is `2(1 + 2νR)`, and at `ν = 0` it is Saveliev's canonical pair `[∇, v] = 1`
  (`CollisionOperatorSl2.LinearBoltzmannOperator`, §B).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.Oscillator

open Polynomial
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular


/-- **[Junker Eq. 9] The Dunkl number** `[n]_ν := n + ν(1 − (−1)ⁿ)` — a deformation of `n` that affects
only the odd integers. -/
def dunklNumber (ν : ℝ) (n : ℕ) : ℝ := n + ν * (1 - (-1) ^ n)

/-- **[Eq. 10] Even Dunkl numbers are undeformed**: `[2m]_ν = 2m`. -/
lemma dunklNumber_even (ν : ℝ) (m : ℕ) : dunklNumber ν (2 * m) = 2 * m := by
  simp [dunklNumber, pow_mul]

/-- **[Eq. 10] Odd Dunkl numbers carry the deformation**: `[2m+1]_ν = 2m + 1 + 2ν`. -/
lemma dunklNumber_odd (ν : ℝ) (m : ℕ) : dunklNumber ν (2 * m + 1) = 2 * m + 1 + 2 * ν := by
  simp [dunklNumber, pow_add, pow_mul]; ring

/-- At `ν = 0` the Dunkl number is the ordinary integer: `[n]_0 = n`. -/
lemma dunklNumber_zero_param (n : ℕ) : dunklNumber 0 n = n := by simp [dunklNumber]

/-- **The defining successor difference** `[n+1]_ν − [n]_ν = 1 + 2ν(−1)ⁿ` — the source of the reflection
term in the deformed Heisenberg algebra below. -/
lemma dunklNumber_succ_sub (ν : ℝ) (n : ℕ) :
    dunklNumber ν (n + 1) - dunklNumber ν n = 1 + 2 * ν * (-1) ^ n := by
  simp only [dunklNumber, pow_succ]; push_cast; ring


/-- **[Eq. 2] The reflection operator** `R : p(X) ↦ p(−X)` on `ℝ[X]`. -/
noncomputable def reflPoly (p : ℝ[X]) : ℝ[X] := p.comp (-X)

/-- The reflection deformation `(1 − R)p / X`. As `(1 − R)p` has zero constant term it is divisible by
`X`; `divX` performs the division. -/
noncomputable def dunklDeform (p : ℝ[X]) : ℝ[X] := divX (p - reflPoly p)

/-- **[Eq. 1] The Dunkl operator** `D_ν = ∂_x + ν·(1 − R)/x` on `ℝ[X]`. -/
noncomputable def dunklOp (ν : ℝ) (p : ℝ[X]) : ℝ[X] := derivative p + ν • dunklDeform p

/-- The reflection acts on a monomial by the sign `(−1)ⁿ`: `R Xⁿ = (−1)ⁿ Xⁿ`. -/
lemma reflPoly_Xpow (n : ℕ) : reflPoly (X ^ n) = ((-1) ^ n : ℝ) • X ^ n := by
  rw [reflPoly, pow_comp, X_comp, neg_pow, Polynomial.smul_eq_C_mul,
    show (-1 : ℝ[X]) = C (-1 : ℝ) by simp, ← C_pow]

/-- `R` is an involution: `R(R p) = p`. -/
lemma reflPoly_involutive (p : ℝ[X]) : reflPoly (reflPoly p) = p := by
  simp [reflPoly, comp_assoc]

/-- `divX Xⁿ = Xⁿ⁻¹` for `n ≥ 1`. -/
lemma divX_Xpow {n : ℕ} (hn : 1 ≤ n) : divX (X ^ n : ℝ[X]) = X ^ (n - 1) := by
  ext k; rw [coeff_divX, coeff_X_pow, coeff_X_pow]; split_ifs <;> first | rfl | omega

/-- `divX` commutes with real scalars. -/
lemma divX_smul (c : ℝ) (p : ℝ[X]) : divX (c • p) = c • divX p := by
  ext k; simp [coeff_divX]


/-- **[Junker Eq. 19] The Dunkl operator on monomials**: `D_ν Xⁿ = [n]_ν Xⁿ⁻¹` (`n ≥ 1`). This is the
reflection-deformation of the ordinary rule `∂_x Xⁿ = n Xⁿ⁻¹`; the deformation `ν(1 − (−1)ⁿ)` shifts only
the odd powers. -/
lemma dunklOp_Xpow (ν : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    dunklOp ν (X ^ n) = (dunklNumber ν n) • X ^ (n - 1) := by
  have hd : dunklDeform (X ^ n) = ((1 - (-1) ^ n : ℝ)) • X ^ (n - 1) := by
    rw [dunklDeform, reflPoly_Xpow,
      show (X ^ n - ((-1) ^ n : ℝ) • X ^ n : ℝ[X]) = ((1 - (-1) ^ n : ℝ)) • X ^ n by
        rw [sub_smul, one_smul], divX_smul, divX_Xpow hn]
  rw [dunklOp, hd, derivative_X_pow, smul_smul, ← Polynomial.smul_eq_C_mul, ← add_smul, dunklNumber]

/-- **At `ν = 0` the Dunkl operator is the ordinary derivative** `D₀ = ∂` — recovering undeformed quantum
mechanics, and the position–momentum canonical pair `(X·, ∂)` of `CollisionOperatorSl2.LinearBoltzmannOperator` §B. -/
lemma dunklOp_zero_param (p : ℝ[X]) : dunklOp 0 p = derivative p := by simp [dunklOp]


/-- The position operator times the Dunkl operator on a monomial: `X · D_ν Xⁿ = [n]_ν Xⁿ` (all `n`,
including `n = 0` where both sides vanish). -/
lemma velOp_dunklOp_Xpow (ν : ℝ) (n : ℕ) :
    X * dunklOp ν (X ^ n) = (dunklNumber ν n) • X ^ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [dunklOp, dunklDeform, reflPoly, dunklNumber]
  · rw [dunklOp_Xpow ν h, mul_smul_comm, ← pow_succ']; congr 2; omega

/-- **[Junker Eq. 3] The deformed Heisenberg algebra** `[D_ν, X·] = 1 + 2νR`, evaluated on the monomial
basis: `D_ν(X·Xⁿ) − X·(D_ν Xⁿ) = Xⁿ + 2ν·R Xⁿ`. The reflection term `2νR` is the Wigner–Dunkl
deformation of the canonical commutator `[∂, X·] = 1`; it comes directly from the successor difference
`[n+1]_ν − [n]_ν = 1 + 2ν(−1)ⁿ` (`dunklNumber_succ_sub`). -/
lemma dunkl_deformed_heisenberg (ν : ℝ) (n : ℕ) :
    dunklOp ν (X * X ^ n) - X * dunklOp ν (X ^ n)
      = X ^ n + (2 * ν) • reflPoly (X ^ n) := by
  have h1 : dunklOp ν (X * X ^ n) = dunklNumber ν (n + 1) • X ^ n := by
    rw [← pow_succ', dunklOp_Xpow ν (Nat.le_add_left 1 n), Nat.add_sub_cancel]
  rw [h1, velOp_dunklOp_Xpow, ← sub_smul, dunklNumber_succ_sub, reflPoly_Xpow,
    add_smul, one_smul, smul_smul]

/-- **The `ν = 0` Heisenberg algebra is the canonical commutator** `[∂, X·] Xⁿ = Xⁿ` — the concrete
`ℝ[X]` model of Saveliev's canonical pair `collisionStar ∇ v = 1` (`CollisionOperatorSl2.LinearBoltzmannOperator`,
§B), here obtained as the undeformed limit of the Wigner–Dunkl algebra. -/
lemma canonical_heisenberg_of_dunkl_zero (n : ℕ) :
    dunklOp 0 (X * X ^ n) - X * dunklOp 0 (X ^ n) = X ^ n := by
  rw [dunkl_deformed_heisenberg]; simp


variable {R : Type*} [Ring R]

/-- **The oscillator ladder commutator** `[v + D, v − D] = 2[D, v]`, written with Saveliev's collision
star `collisionStar a b = ab − ba` (`CollisionOperatorSl2.CollisionModular`). With the lowering/raising
operators `a = v + D`, `a† = v − D`, their commutator is twice the Heisenberg bracket — so for the
Wigner–Dunkl deformed Heisenberg algebra `[D, v] = 1 + 2νR` (Eq. 3) the ladder satisfies
`[a, a†] = 2(1 + 2νR)`, and at `ν = 0` it is `2·1`, the standard oscillator built on Saveliev's
canonical pair `collisionStar ∇ v = 1`. -/
lemma dunkl_ladder_via_collisionStar (del vel : R) :
    collisionStar (vel + del) (vel - del) = 2 * collisionStar del vel := by
  unfold collisionStar; noncomm_ring

/-- **The Wigner–Dunkl oscillator ladder commutator** is `2(1 + 2νR)`: given the deformed Heisenberg
relation in the form `collisionStar del vel = 1 + w` (with `w = 2ν·R` the reflection deformation),
`[v + D, v − D] = 2(1 + w)`. At `w = 0` (`ν = 0`) this is the undeformed oscillator `[a, a†] = 2`. -/
lemma dunkl_ladder_deformed (del vel w : R) (h : collisionStar del vel = 1 + w) :
    collisionStar (vel + del) (vel - del) = 2 * (1 + w) := by
  rw [dunkl_ladder_via_collisionStar, h]

end Physlib.QuantumMechanics.ComplexAction.Dunkl.Oscillator

end
