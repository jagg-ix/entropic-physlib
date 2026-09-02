/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentState

/-!
# Uniqueness of the coherent state: the annihilation eigenstate is unique up to scale

The representation-uniqueness mechanism (the third of the arc's uniqueness mechanisms, alongside the
irreversible-equilibrium `SciamaFockGibbsUniqueness` and the finite `OneLevelChannel` fixed-point) at the
coherent-state level: the eigenvalue equation `a ψ = α ψ` has, up to a scalar, a *unique* solution — the
coherent state.  The eigen-equation reads coordinate-wise `√(n+1) ψ_{n+1} = α ψₙ`
(`SciamaFockCoherentState.coherentCoeff_shift`), and this first-order recurrence pins every coordinate to the
zeroth:

* `annihilationEigen_coord_unique` — any `ψ : ℕ → ℂ` obeying the eigen-recurrence has `ψₙ = ⟨n|α⟩·ψ₀`
  (`⟨n|α⟩ = αⁿ/√(n!) = coherentCoeff`): the coherent-state coefficients are the unique solution up to `ψ₀`.
* `annihilationEigen_lp_unique` — at the `ℓ²` level, `ψ = ψ₀ • |α⟩`: the coherent state is the unique
  annihilation eigenvector with eigenvalue `α`, up to scale — the eigenspace is one-dimensional.
* `vacuum_coord_unique` — the `α = 0` case (`a ψ = 0`) forces `ψ_{n+1} = 0`: the vacuum is the unique
  annihilation-kernel state (the kernel of `a` is one-dimensional).
* `annihilationEigen_proportional` — any two eigenstates with the same eigenvalue are proportional,
  `ψₙ·φ₀ = φₙ·ψ₀` — the one-dimensionality read off directly.

Honest scope: the coordinate-recurrence uniqueness of the annihilation eigenstate and its `ℓ²` lift.  Full
irreducibility of the CCR representation (Stone–von Neumann) is contextualized, not built; this is its
coherent-state / vacuum shadow.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentUniqueness

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentState

/-- The number-basis coefficient `√(n+1)` is nonzero. -/
private theorem sqrt_succ_ne_zero (n : ℕ) : (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 := by
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))

/-- **[Coherent state = unique annihilation eigenstate, coordinates] `ψₙ = ⟨n|α⟩·ψ₀`.**  Any solution of the
annihilation eigen-recurrence `√(n+1)ψ_{n+1} = α ψₙ` is fixed by its zeroth coordinate — the coherent-state
coefficients `⟨n|α⟩ = αⁿ/√(n!)`. -/
theorem annihilationEigen_coord_unique (α : ℂ) (ψ : ℕ → ℂ)
    (hψ : ∀ n : ℕ, (Real.sqrt ((n : ℝ) + 1) : ℂ) * ψ (n + 1) = α * ψ n) (n : ℕ) :
    ψ n = coherentCoeff α n * ψ 0 := by
  induction n with
  | zero => simp [coherentCoeff]
  | succ k ih =>
    have key : (Real.sqrt ((k : ℝ) + 1) : ℂ) * ψ (k + 1)
        = (Real.sqrt ((k : ℝ) + 1) : ℂ) * (coherentCoeff α (k + 1) * ψ 0) := by
      rw [hψ, ih,
        show (Real.sqrt ((k : ℝ) + 1) : ℂ) * (coherentCoeff α (k + 1) * ψ 0)
          = ((Real.sqrt ((k : ℝ) + 1) : ℂ) * coherentCoeff α (k + 1)) * ψ 0 from by ring,
        coherentCoeff_shift]
      ring
    exact mul_left_cancel₀ (sqrt_succ_ne_zero k) key

/-- **[Coherent state = unique annihilation eigenvector, `ℓ²`] `ψ = ψ₀ • |α⟩`.**  Any `ℓ²` vector obeying the
annihilation eigen-recurrence is a scalar multiple of the coherent state: the `α`-eigenspace of `a` is
one-dimensional. -/
theorem annihilationEigen_lp_unique (α : ℂ) (ψ : FockHilbert)
    (hψ : ∀ n : ℕ, (Real.sqrt ((n : ℝ) + 1) : ℂ) * ψ (n + 1) = α * ψ n) :
    ψ = (ψ 0) • coherentState α := by
  apply lp.ext
  funext n
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, coherentState_apply,
    annihilationEigen_coord_unique α (⇑ψ) hψ n, mul_comm]

/-- **[Vacuum = unique annihilation kernel] `a ψ = 0 ⟹ ψ_{n+1} = 0`.**  Only the zeroth coordinate survives:
the kernel of the annihilation operator is one-dimensional (the vacuum). -/
theorem vacuum_coord_unique (ψ : ℕ → ℂ)
    (hψ : ∀ n : ℕ, (Real.sqrt ((n : ℝ) + 1) : ℂ) * ψ (n + 1) = 0) (n : ℕ) :
    ψ (n + 1) = 0 :=
  (mul_eq_zero.mp (hψ n)).resolve_left (sqrt_succ_ne_zero n)

/-- **[One-dimensional eigenspace] `ψₙ·φ₀ = φₙ·ψ₀`.**  Any two annihilation eigenstates with the same
eigenvalue `α` are proportional. -/
theorem annihilationEigen_proportional (α : ℂ) (ψ φ : ℕ → ℂ)
    (hψ : ∀ n : ℕ, (Real.sqrt ((n : ℝ) + 1) : ℂ) * ψ (n + 1) = α * ψ n)
    (hφ : ∀ n : ℕ, (Real.sqrt ((n : ℝ) + 1) : ℂ) * φ (n + 1) = α * φ n) (n : ℕ) :
    ψ n * φ 0 = φ n * ψ 0 := by
  rw [annihilationEigen_coord_unique α ψ hψ n, annihilationEigen_coord_unique α φ hφ n]
  ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentUniqueness

end
