/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The single-mode bosonic Fock space (for the Sciama thermofield-double vacuum)

The operator-level object the Sciama arc had only at the c-number level (Appendix C's thermofield double,
§3.2's density matrix): the **single bosonic mode's Fock space**, constructed algebraically as the
finitely-supported functions `ℕ →₀ ℂ` (finite linear combinations of number states `|n⟩`), with creation,
annihilation, and number operators satisfying the canonical commutation relation.

* `numberKet n = |n⟩`; `annihilationOp`, `creationOp`, `numberOp` — the mode operators.
* `annihilationOp_numberKet`, `creationOp_numberKet` — `a|n⟩ = √n|n−1⟩`, `a†|n⟩ = √(n+1)|n+1⟩`.
* `numberOp_numberKet` — `N|n⟩ = n|n⟩` (the number states are eigenstates, `N = a†a`).
* `ccr` — `[a, a†] = a a† − a† a = 1` (the canonical commutation relation).

The Fock-space number operator's eigenvalues `n` are precisely the levels whose thermal (Gibbs) weighting
gives `boseEinstein` (`SciamaThermalDensityMatrix.thermal_mean_occupation`), so this supplies the Hilbert
space on which that density matrix acts.

Honest scope: the algebraic (finitely-supported) Fock space and the CCR; the `ℓ²` completion, the unbounded
operators' domains, and the Fock-space thermal *operator* trace are not built.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaBosonicFockSpace

/-- **The Fock space** of a single bosonic mode: finite linear combinations of number states. -/
abbrev FockSpace := ℕ →₀ ℂ

/-- **The number state** `|n⟩`. -/
def numberKet (n : ℕ) : FockSpace := Finsupp.single n 1

/-- `a|n⟩ = √n |n−1⟩` (and `a|0⟩ = 0` since `√0 = 0`). -/
def annihilationKet (n : ℕ) : FockSpace := (Real.sqrt n : ℂ) • numberKet (n - 1)

/-- `a†|n⟩ = √(n+1) |n+1⟩`. -/
def creationKet (n : ℕ) : FockSpace := (Real.sqrt ((n : ℝ) + 1) : ℂ) • numberKet (n + 1)

/-- **The annihilation operator** `a`. -/
def annihilationOp : FockSpace →ₗ[ℂ] FockSpace := Finsupp.basisSingleOne.constr ℂ annihilationKet

/-- **The creation operator** `a†`. -/
def creationOp : FockSpace →ₗ[ℂ] FockSpace := Finsupp.basisSingleOne.constr ℂ creationKet

/-- **The number operator** `N = a† a`. -/
def numberOp : FockSpace →ₗ[ℂ] FockSpace := creationOp ∘ₗ annihilationOp

theorem basisSingleOne_eq_numberKet (n : ℕ) : Finsupp.basisSingleOne n = numberKet n := by
  simp [Finsupp.basisSingleOne, numberKet]

/-- `a|n⟩ = √n |n−1⟩`. -/
@[simp] theorem annihilationOp_numberKet (n : ℕ) : annihilationOp (numberKet n) = annihilationKet n := by
  rw [← basisSingleOne_eq_numberKet]; exact Module.Basis.constr_basis _ _ _ _

/-- `a†|n⟩ = √(n+1) |n+1⟩`. -/
@[simp] theorem creationOp_numberKet (n : ℕ) : creationOp (numberKet n) = creationKet n := by
  rw [← basisSingleOne_eq_numberKet]; exact Module.Basis.constr_basis _ _ _ _

/-- `a a†|n⟩ = (n+1)|n⟩`. -/
theorem annihilationOp_creationKet (n : ℕ) :
    annihilationOp (creationKet n) = ((n : ℂ) + 1) • numberKet n := by
  rw [creationKet, map_smul, annihilationOp_numberKet, annihilationKet, Nat.add_sub_cancel, smul_smul]
  congr 1
  push_cast
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

/-- `a† a|n⟩ = n|n⟩`. -/
theorem creationOp_annihilationKet (n : ℕ) :
    creationOp (annihilationKet n) = (n : ℂ) • numberKet n := by
  rw [annihilationKet, map_smul, creationOp_numberKet, creationKet, smul_smul]
  rcases n with _ | m
  · simp [numberKet]
  · rw [Nat.succ_sub_one]
    congr 1
    push_cast
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring

/-- **[Number operator eigenvalue] `N|n⟩ = n|n⟩`.**  The number states are eigenstates of `N = a†a`. -/
theorem numberOp_numberKet (n : ℕ) : numberOp (numberKet n) = (n : ℂ) • numberKet n := by
  rw [numberOp, LinearMap.comp_apply, annihilationOp_numberKet, creationOp_annihilationKet]

/-- **[Canonical commutation relation] `[a, a†] = a a† − a† a = 1`.**  The defining relation of the bosonic
mode. -/
theorem ccr : annihilationOp ∘ₗ creationOp - creationOp ∘ₗ annihilationOp = LinearMap.id := by
  refine Finsupp.basisSingleOne.ext (fun n => ?_)
  rw [basisSingleOne_eq_numberKet, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    creationOp_numberKet, annihilationOp_creationKet, annihilationOp_numberKet,
    creationOp_annihilationKet, LinearMap.id_apply, ← sub_smul,
    show ((n : ℂ) + 1) - (n : ℂ) = 1 from by ring, one_smul]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaBosonicFockSpace

end
