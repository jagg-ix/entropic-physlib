/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockAdjointness
public import Mathlib.LinearAlgebra.LinearPMap

/-!
# The number operator as a densely-defined unbounded operator (`LinearPMap`)

The formal packaging of the unbounded number operator `N` as a **partially-defined linear map**
(`LinearPMap`) on `ℓ²`, with domain the dense core `fockCore` (the image of the algebraic Fock space).  Since
the number states are orthonormal they are linearly independent, so `incl` is injective and the operator is
well-defined on its range.

* `numberPMap` — the number operator as `FockHilbert →ₗ.[ℂ] FockHilbert`, with `domain = range incl`.
* `numberPMap_domain`, `numberPMap_denseDefined` — the domain is `fockCore`, and it is **dense**: `N` is a
  densely-defined operator.
* `numberPMap_apply_fockKet` — `N|n⟩ = n|n⟩` at the `LinearPMap` level.

Honest scope: the densely-defined `LinearPMap` and its eigen-action.  Its adjoint `N†`
(`LinearPMap.adjoint`), closedness, and essential self-adjointness (`dom N† = dom N`) are the separate deep
unbounded-operator theory; the symmetry `⟨Nx|y⟩ = ⟨x|Ny⟩` is in `SciamaFockAdjointness`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockNumberOperatorPMap

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaBosonicFockSpace
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockThermalTrace

/-- `incl` is injective: the number states are linearly independent (being orthonormal). -/
theorem incl_injective : Function.Injective incl :=
  fockKet_orthonormal.linearIndependent

/-- The linear equivalence of the algebraic Fock space with the range of `incl`. -/
def inclEquiv : (ℕ →₀ ℂ) ≃ₗ[ℂ] ↥(LinearMap.range incl) :=
  LinearEquiv.ofInjective incl incl_injective

theorem inclEquiv_symm_incl (x : ℕ →₀ ℂ) :
    inclEquiv.symm ⟨incl x, LinearMap.mem_range_self incl x⟩ = x := by
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [inclEquiv, LinearEquiv.ofInjective_apply]

/-- **The number operator** `N` as a densely-defined unbounded operator on `ℓ²`, with domain the dense core
`range incl = fockCore`. -/
def numberPMap : FockHilbert →ₗ.[ℂ] FockHilbert where
  domain := LinearMap.range incl
  toFun := incl ∘ₗ numberOp ∘ₗ (inclEquiv.symm : ↥(LinearMap.range incl) →ₗ[ℂ] (ℕ →₀ ℂ))

/-- **[Domain is the core]** `dom N = range incl = fockCore`. -/
theorem numberPMap_domain : numberPMap.domain = fockCore := incl_range

/-- **[Densely defined]** the number operator's domain is dense in `ℓ²`. -/
theorem numberPMap_denseDefined : Dense (numberPMap.domain : Set FockHilbert) := by
  rw [numberPMap_domain]
  exact fockCore_dense

theorem numberPMap_toFun_incl (x : ℕ →₀ ℂ) :
    numberPMap.toFun ⟨incl x, LinearMap.mem_range_self incl x⟩ = incl (numberOp x) := by
  show incl (numberOp (inclEquiv.symm ⟨incl x, LinearMap.mem_range_self incl x⟩)) = incl (numberOp x)
  rw [inclEquiv_symm_incl]

/-- **[Eigen-action] `N|n⟩ = n|n⟩`** at the `LinearPMap` level: the number states are eigenstates of the
densely-defined number operator. -/
theorem numberPMap_apply_fockKet (n : ℕ) (hn : fockKet n ∈ numberPMap.domain) :
    numberPMap.toFun ⟨fockKet n, hn⟩ = (n : ℂ) • fockKet n := by
  have hsub : (⟨fockKet n, hn⟩ : ↥numberPMap.domain)
      = ⟨incl (numberKet n), LinearMap.mem_range_self incl (numberKet n)⟩ :=
    Subtype.ext (incl_numberKet n).symm
  rw [hsub, numberPMap_toFun_incl, numberOp_numberKet, map_smul, incl_numberKet]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockNumberOperatorPMap

end
