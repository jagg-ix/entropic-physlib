/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockHamiltonian
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The ℓ² completion of the single-mode Fock space

`SciamaBosonicFockSpace` built the algebraic Fock space `ℕ →₀ ℂ` (finite superpositions of number states).
Its Hilbert-space completion is `ℓ²(ℕ; ℂ) = lp (fun _ : ℕ => ℂ) 2`: a genuine complete inner-product space in
which the number states `|n⟩` become an **orthonormal Hilbert basis**, and the algebraic Fock space sits as a
dense subspace (the core on which the unbounded ladder/number operators are defined).

* `FockHilbert` — `ℓ²(ℕ; ℂ)`, a `CompleteSpace` and `InnerProductSpace ℂ` (instances).
* `fockKet n = |n⟩` — the number states as ℓ² vectors; `fockKet_norm`, `fockKet_inner` — `‖|n⟩‖ = 1`,
  `⟨m|n⟩ = δ_{mn}`.
* `fockKet_orthonormal` — the number states are an orthonormal family.
* `fockHilbertBasis` — they are a **Hilbert basis** of `ℓ²` (their orthogonal complement is trivial): the
  completion is the closed span of the number states.
* `fockCore`, `fockCore_dense` — the algebraic span of the number states is **dense** in `ℓ²`; this is the
  dense domain (core) for the number and ladder operators.

Honest scope: the ℓ² completion, the orthonormal Hilbert basis, and the dense core.  The operators' explicit
`LinearPMap` packaging and self-adjointness are separate.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion

open RCLike Submodule

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- **The ℓ² completion** `ℓ²(ℕ; ℂ)` of the single-mode Fock space. -/
abbrev FockHilbert : Type := lp (fun _ : ℕ => ℂ) 2

example : CompleteSpace FockHilbert := inferInstance
example : InnerProductSpace ℂ FockHilbert := inferInstance

/-- **The number state** `|n⟩` as an ℓ² vector. -/
def fockKet (n : ℕ) : FockHilbert := lp.single 2 n (1 : ℂ)

/-- **[Normalized] `‖|n⟩‖ = 1`.** -/
theorem fockKet_norm (n : ℕ) : ‖fockKet n‖ = 1 := by
  rw [fockKet, lp.norm_single (by norm_num)]
  simp

/-- **[Orthonormal inner products] `⟨m|n⟩ = δ_{mn}`.** -/
theorem fockKet_inner (i j : ℕ) : ⟪fockKet i, fockKet j⟫ = if i = j then (1 : ℂ) else 0 := by
  rw [fockKet, fockKet, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one,
    lp.coeFn_single, Pi.single_apply]

/-- **[Orthonormal family] the number states `|n⟩` form an orthonormal family in `ℓ²`.** -/
theorem fockKet_orthonormal : Orthonormal ℂ fockKet :=
  orthonormal_iff_ite.mpr fockKet_inner

/-- **[Trivial orthogonal complement]** the only ℓ² vector orthogonal to every number state is `0` — the
number states are total. -/
theorem fockKet_orthogonal_eq_bot :
    (span ℂ (Set.range fockKet))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [Submodule.mem_orthogonal] at hf
  rw [lp.eq_zero_iff_coeFn_eq_zero]
  funext n
  have h := hf (fockKet n) (Submodule.subset_span (Set.mem_range_self n))
  rw [fockKet, lp.inner_single_left] at h
  simpa [RCLike.inner_apply, Pi.zero_apply] using h

/-- **[Hilbert basis] the number states `|n⟩` are a Hilbert basis of `ℓ²(ℕ; ℂ)`.**  The ℓ² completion is the
closed span of the number states — the genuine Hilbert space of the single mode. -/
def fockHilbertBasis : HilbertBasis ℕ ℂ FockHilbert :=
  HilbertBasis.mkOfOrthogonalEqBot fockKet_orthonormal fockKet_orthogonal_eq_bot

@[simp] theorem fockHilbertBasis_coe : ⇑fockHilbertBasis = fockKet :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- **The dense core** — the algebraic span of the number states (the image of the algebraic Fock space
`ℕ →₀ ℂ`), on which the unbounded number/ladder operators are defined. -/
def fockCore : Submodule ℂ FockHilbert := span ℂ (Set.range fockKet)

/-- **[Core is dense]** the closed span of the number states is all of `ℓ²`. -/
theorem fockCore_topologicalClosure : fockCore.topologicalClosure = ⊤ :=
  Submodule.topologicalClosure_eq_top_iff.mpr fockKet_orthogonal_eq_bot

/-- **[Dense domain] the algebraic Fock space is dense in `ℓ²`.**  The number/ladder operators are densely
defined: their domain (the finite superpositions) is dense in the completion. -/
theorem fockCore_dense : Dense (fockCore : Set FockHilbert) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr fockCore_topologicalClosure

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion

end
