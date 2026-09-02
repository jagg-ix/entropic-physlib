/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaBosonicFockSpace

/-!
# The bosonic Fock space ladder structure: vacuum, `(a†)ⁿ`, and the number-operator commutators

Building on `SciamaBosonicFockSpace`: the Fock space is generated from the vacuum `|0⟩` by the creation
operator, and the number operator acts as a ladder generator.

* `vacuum`, `annihilationOp_vacuum` — `|0⟩`, and `a|0⟩ = 0` (the vacuum is annihilated).
* `creationOp_pow_vacuum` — `(a†)ⁿ|0⟩ = √(n!) |n⟩`: the number states are built from the vacuum.
* `numberOp_creation_commutator` — `[N, a†] = a†` (creation raises the number by one).
* `numberOp_annihilation_commutator` — `[N, a] = −a` (annihilation lowers it).

Honest scope: the algebraic ladder identities on the finitely-supported Fock space.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockLadder

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaBosonicFockSpace

/-- **The vacuum** `|0⟩`. -/
def vacuum : FockSpace := numberKet 0

/-- **[Vacuum is annihilated] `a|0⟩ = 0`.** -/
@[simp] theorem annihilationOp_vacuum : annihilationOp vacuum = 0 := by
  rw [vacuum, annihilationOp_numberKet, annihilationKet]; simp

/-- **[Number states from the vacuum] `(a†)ⁿ|0⟩ = √(n!) |n⟩`.**  The whole Fock space is generated from the
vacuum by the creation operator. -/
theorem creationOp_pow_vacuum (n : ℕ) :
    (creationOp ^ n) vacuum = (Real.sqrt (n.factorial) : ℂ) • numberKet n := by
  induction n with
  | zero => simp [vacuum, numberKet]
  | succ m ih =>
    have hcomp : (creationOp ^ (m + 1)) vacuum = creationOp ((creationOp ^ m) vacuum) := by
      rw [pow_succ']; rfl
    rw [hcomp, ih, map_smul, creationOp_numberKet, creationKet, smul_smul]
    congr 1
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← Real.sqrt_mul (by positivity), Nat.factorial_succ]
    congr 1
    push_cast
    ring

/-- **[Raising commutator] `[N, a†] = a†`.**  Creation raises the number eigenvalue by one. -/
theorem numberOp_creation_commutator :
    numberOp ∘ₗ creationOp - creationOp ∘ₗ numberOp = creationOp := by
  refine Finsupp.basisSingleOne.ext (fun n => ?_)
  simp only [basisSingleOne_eq_numberKet, LinearMap.sub_apply, LinearMap.comp_apply,
    creationOp_numberKet, numberOp_numberKet, creationKet, map_smul, smul_smul]
  rw [← sub_smul]
  congr 1
  push_cast
  ring

/-- **[Lowering commutator] `[N, a] = −a`.**  Annihilation lowers the number eigenvalue by one. -/
theorem numberOp_annihilation_commutator :
    numberOp ∘ₗ annihilationOp - annihilationOp ∘ₗ numberOp = -annihilationOp := by
  refine Finsupp.basisSingleOne.ext (fun n => ?_)
  simp only [basisSingleOne_eq_numberKet, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.neg_apply, annihilationOp_numberKet, numberOp_numberKet, annihilationKet, map_smul,
    smul_smul]
  rcases n with _ | m
  · simp
  · rw [← neg_smul, ← sub_smul]
    congr 1
    push_cast
    ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockLadder

end
