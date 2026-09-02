/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockThermalTrace

/-!
# Adjoint relations of the Fock-space operators: `a† = a*` and the Hermiticity of `N`

The operator machinery that makes the ladder operators genuine quantum observables: the **adjoint relations**,
computed with the actual ℓ² inner product of `SciamaFockL2Completion`.

* `creation_annihilation_adjoint` — `⟨a†m|n⟩ = ⟨m|a n⟩`: the creation operator is the **adjoint** of the
  annihilation operator (`a† = a*`).  This is why `a†`/`a` are named creation/annihilation *adjoints* and why
  `N = a†a` is a positive observable.
* `numberOp_symmetric` — `⟨N m|n⟩ = ⟨m|N n⟩`: the number operator is **symmetric (Hermitian)** in the number
  basis — the operator-theoretic content of "`N` is an observable" (its diagonal `n` are real eigenvalues).

Honest scope: the adjoint/symmetry identities on the number basis (the matrix elements), which extend by
sesquilinearity to the dense core.  Full unbounded self-adjointness (domain of `N†` equal to `dom N`) and the
`LinearPMap` adjoint are the separate deep operator theory.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockAdjointness

open RCLike
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaBosonicFockSpace
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockThermalTrace

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- **[Creation is the adjoint of annihilation] `⟨a†m|n⟩ = ⟨m|a n⟩`.**  In the number basis the matrix
elements of `a†` and `a` are transposes-conjugates: `a†` is the Hilbert-space adjoint of `a` (`a† = a*`). -/
theorem creation_annihilation_adjoint (m n : ℕ) :
    ⟪incl (creationOp (numberKet m)), incl (numberKet n)⟫
      = ⟪incl (numberKet m), incl (annihilationOp (numberKet n))⟫ := by
  simp only [creationOp_numberKet, creationKet, annihilationOp_numberKet, annihilationKet,
    map_smul, incl_numberKet, inner_smul_left, inner_smul_right, fockKet_inner]
  rcases n with _ | k
  · simp
  · rw [Nat.succ_sub_one]
    by_cases h : m = k
    · subst h; simp
    · rw [if_neg (by omega : ¬ m + 1 = k + 1), if_neg h]; simp

/-- **[Number operator is Hermitian] `⟨N m|n⟩ = ⟨m|N n⟩`.**  The number operator is symmetric in the number
basis — an observable, with the real eigenvalues `n = ⟨n|N|n⟩`. -/
theorem numberOp_symmetric (m n : ℕ) :
    ⟪incl (numberOp (numberKet m)), incl (numberKet n)⟫
      = ⟪incl (numberKet m), incl (numberOp (numberKet n))⟫ := by
  simp only [numberOp_numberKet, map_smul, incl_numberKet, inner_smul_left, inner_smul_right,
    fockKet_inner]
  split_ifs with h
  · rw [h]; simp
  · simp

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockAdjointness

end
