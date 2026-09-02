/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Moyal.BakerOperatorSplit
public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
public import Mathlib.Tactic.Abel

/-!
# The Moyal bracket is Saveliev's collision star

Links the Hiley Moyal/Baker operator split (`Moyal.BakerOperatorSplit`) to Saveliev's collision star map
(`CollisionOperatorSl2.CollisionModular`). Saveliev's star `â* : b ↦ [â, b] = a·b − b·a` (`collisionStar`, the adjoint
action `ad_â` from which the linear Boltzmann collision operator is built) is exactly the **unscaled
commutator core** of Hiley's Moyal bracket:

  `{a, b}_MB = (ab − ba)/(iℏ) = (iℏ)⁻¹ · [a, b]`   (`moyalBracket_eq_collisionStar_smul`).

The two pictures — the deformation-quantization commutator (Moyal) and the kinetic adjoint action
(Saveliev/Boltzmann) — are the same map up to the `iℏ` normalization. The Moyal bracket therefore inherits
the proven structure of `collisionStar`:

* **Operator product via the commutator** (`product_eq_baker_add_half_collisionStar`):
  `ab = {a, b}_BB + ½·[a, b]` — the symmetric Jordan/Baker part plus half the commutator (the un-`iℏ`'d form
  of `product_eq_baker_add_moyal`).
* **The Moyal bracket is a derivation** (`moyalBracket_leibniz`):
  `{a, b·c}_MB = {a, b}_MB·c + b·{a, c}_MB` — from `collisionStar_leibniz`.
* **Modular / conjugation covariance** (`moyalBracket_conj`):
  `u·{a, b}_MB·v = {u a v, u b v}_MB` when `v·u = 1` — from `conj_collisionStar`, the algebraic heart of
  modular covariance, now carried by the Moyal bracket.

(The finite-mode matrix `Moyal.BracketTodaLattice.moyalBracket` is a *different*, truncated first-order object;
this bridge concerns the full operator-algebra commutator bracket.)

## References

* B. J. Hiley (2015); A. Saveliev (collision/star calculus); J. E. Moyal. Carrier: `Physlib`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Moyal.BakerOperatorSplit

open CollisionOperatorSl2.CollisionModular

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- **[Moyal bracket = collision star / iℏ] `{a, b}_MB = (iℏ)⁻¹·[a, b]`.** Hiley's Moyal bracket is Saveliev's
adjoint-action star map normalized by `iℏ`. -/
lemma moyalBracket_eq_collisionStar_smul (ℏ : ℝ) (a b : R) :
    moyalBracket ℏ a b = (Complex.I * (ℏ : ℂ))⁻¹ • collisionStar a b := by
  rw [moyalBracket, collisionStar]

/-- **[Operator product = Baker bracket + ½·commutator] `ab = {a, b}_BB + ½·[a, b]`.** The un-`iℏ`'d form of
the product split: the symmetric (Jordan/Baker) part plus half the Saveliev commutator. -/
lemma product_eq_baker_add_half_collisionStar (a b : R) :
    a * b = bakerBracket a b + (2⁻¹ : ℂ) • collisionStar a b := by
  rw [bakerBracket, collisionStar, ← smul_add,
    (show a * b + b * a + (a * b - b * a) = (2 : ℂ) • (a * b) by
      rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]; abel),
    smul_smul, show (2⁻¹ : ℂ) * 2 = 1 by norm_num, one_smul]

/-- **[The Moyal bracket is a derivation] `{a, b·c}_MB = {a, b}_MB·c + b·{a, c}_MB`.** Inherited from the
Leibniz rule for Saveliev's star map. -/
lemma moyalBracket_leibniz (ℏ : ℝ) (a b c : R) :
    moyalBracket ℏ a (b * c) = moyalBracket ℏ a b * c + b * moyalBracket ℏ a c := by
  simp only [moyalBracket_eq_collisionStar_smul, collisionStar_leibniz, smul_add, smul_mul_assoc,
    mul_smul_comm]

/-- **[Modular / conjugation covariance of the Moyal bracket] `u·{a, b}_MB·v = {u a v, u b v}_MB`** when
`v·u = 1`. Inherited from conjugation covariance of Saveliev's star map — the algebraic heart of modular
covariance. -/
lemma moyalBracket_conj {u v : R} (huv : v * u = 1) (ℏ : ℝ) (a b : R) :
    u * moyalBracket ℏ a b * v = moyalBracket ℏ (u * a * v) (u * b * v) := by
  rw [moyalBracket_eq_collisionStar_smul ℏ a b, mul_smul_comm, smul_mul_assoc,
    conj_collisionStar huv, ← moyalBracket_eq_collisionStar_smul]

end Physlib.QuantumMechanics.ComplexAction.Moyal.BakerOperatorSplit

end
