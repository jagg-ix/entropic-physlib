/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockNumberOperatorPMap
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Essential self-adjointness of the number operator via the deficiency-index criterion

The number operator `N` is *symmetric* on the dense core (`SciamaFockAdjointness.numberOp_symmetric`); this
module proves it is **essentially self-adjoint** there — its unique self-adjoint extension is the physical
observable — via von Neumann's criterion: a symmetric operator is essentially self-adjoint iff **both
deficiency indices vanish**, `ker(N† − i) = ker(N† + i) = {0}`.

The proof is the textbook one for a diagonal operator with a total orthonormal eigenbasis: if `N†ψ = ±iψ`
then for every number state, `adjoint_isFormalAdjoint` gives `⟨N†ψ, |n⟩⟩ = ⟨ψ, N|n⟩⟩`, i.e.
`∓i⟨ψ|n⟩ = n⟨ψ|n⟩`, so `(n ± i)⟨ψ|n⟩ = 0`; since `n ± i ≠ 0` every coordinate `⟨ψ|n⟩` vanishes, and the number
states are total, so `ψ = 0`.

* `numberPMap_deficiency_plus` — `ker(N† − i) = {0}` (`n₊ = 0`).
* `numberPMap_deficiency_minus` — `ker(N† + i) = {0}` (`n₋ = 0`).

Together with symmetry these are von Neumann's sufficient condition for essential self-adjointness.

Honest scope: the two deficiency spaces are trivial (the criterion).  Assembling this into a Mathlib
`IsSelfAdjoint (closure)` term is not done — Mathlib carries no essential-self-adjointness / closure API for
`LinearPMap`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockEssentialSelfAdjoint

open RCLike
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaBosonicFockSpace
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockThermalTrace
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockNumberOperatorPMap

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- If every coordinate `⟨|n⟩, ψ⟩` of a vector vanishes, the vector is `0` (the number states are total). -/
theorem eq_zero_of_forall_inner_fockKet {ψ : FockHilbert} (h : ∀ n : ℕ, ⟪fockKet n, ψ⟫ = 0) :
    ψ = 0 := by
  apply lp.ext
  funext n
  have hn := h n
  rw [fockKet, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] at hn
  simpa using hn

/-- **[Deficiency index `n₊ = 0`] `ker(N† − i) = {0}`.**  No nonzero vector satisfies `N†ψ = iψ`. -/
theorem numberPMap_deficiency_plus (ψ : ↥(numberPMap.adjoint).domain)
    (hψ : numberPMap.adjoint ψ = Complex.I • (ψ : FockHilbert)) : (ψ : FockHilbert) = 0 := by
  refine eq_zero_of_forall_inner_fockKet (fun n => ?_)
  have hn : fockKet n ∈ numberPMap.domain := ⟨numberKet n, incl_numberKet n⟩
  have hap : numberPMap ⟨fockKet n, hn⟩ = (n : ℂ) • fockKet n := numberPMap_apply_fockKet n hn
  have e : ⟪Complex.I • (ψ : FockHilbert), fockKet n⟫ = ⟪(ψ : FockHilbert), (n : ℂ) • fockKet n⟫ := by
    have hfa := numberPMap.adjoint_isFormalAdjoint numberPMap_denseDefined ψ ⟨fockKet n, hn⟩
    rw [hψ, hap] at hfa
    exact hfa
  rw [inner_smul_left, inner_smul_right, Complex.conj_I] at e
  have hne : ((n : ℂ) + Complex.I) ≠ 0 := by
    intro hc0
    have him := congrArg Complex.im hc0
    simp [Complex.add_im, Complex.I_im, Complex.natCast_im] at him
  have hc : ((n : ℂ) + Complex.I) * ⟪(ψ : FockHilbert), fockKet n⟫ = 0 := by linear_combination -e
  have hzero : ⟪(ψ : FockHilbert), fockKet n⟫ = 0 := (mul_eq_zero.mp hc).resolve_left hne
  rw [← inner_conj_symm, hzero, map_zero]

/-- **[Deficiency index `n₋ = 0`] `ker(N† + i) = {0}`.**  No nonzero vector satisfies `N†ψ = −iψ`. -/
theorem numberPMap_deficiency_minus (ψ : ↥(numberPMap.adjoint).domain)
    (hψ : numberPMap.adjoint ψ = (-Complex.I) • (ψ : FockHilbert)) : (ψ : FockHilbert) = 0 := by
  refine eq_zero_of_forall_inner_fockKet (fun n => ?_)
  have hn : fockKet n ∈ numberPMap.domain := ⟨numberKet n, incl_numberKet n⟩
  have hap : numberPMap ⟨fockKet n, hn⟩ = (n : ℂ) • fockKet n := numberPMap_apply_fockKet n hn
  have e : ⟪(-Complex.I) • (ψ : FockHilbert), fockKet n⟫ = ⟪(ψ : FockHilbert), (n : ℂ) • fockKet n⟫ := by
    have hfa := numberPMap.adjoint_isFormalAdjoint numberPMap_denseDefined ψ ⟨fockKet n, hn⟩
    rw [hψ, hap] at hfa
    exact hfa
  rw [inner_smul_left, inner_smul_right, map_neg, Complex.conj_I] at e
  have hne : ((n : ℂ) - Complex.I) ≠ 0 := by
    intro hc0
    have him := congrArg Complex.im hc0
    simp [Complex.sub_im, Complex.I_im, Complex.natCast_im] at him
  have hc : ((n : ℂ) - Complex.I) * ⟪(ψ : FockHilbert), fockKet n⟫ = 0 := by linear_combination -e
  have hzero : ⟪(ψ : FockHilbert), fockKet n⟫ = 0 := (mul_eq_zero.mp hc).resolve_left hne
  rw [← inner_conj_symm, hzero, map_zero]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockEssentialSelfAdjoint

end
