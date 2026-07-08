/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation

/-!
# Dirac spinors and the rest-frame Dirac equation

This file formalizes the **Dirac spinors** on which the 4×4 Dirac matrices of
`Dirac.CompleteDiracEquation` act, and the rest-frame Dirac equation `H ψ = E ψ`.

A Dirac spinor is a 4-component object `ψ ∈ ℂ⁴`, here `Fin 2 ⊕ Fin 2 → ℂ` (matching the
block structure of `diracAlpha`, `diracBeta`). It splits into an **upper** 2-spinor (positive
energy) and a **lower** 2-spinor (negative energy); each 2-spinor `χ ∈ ℂ²` includes the **spin**.

## Main results

* `DiracSpinor`; `restPositiveSpinor χ = (χ, 0)`, `restNegativeSpinor χ = (0, χ)`.
* `diracBeta_mulVec_restPositive` / `_restNegative` — these are the `±1` eigenspinors of `β`.
* `diracHamiltonian_rest` — at `p = 0`, `H = mc²·β`.
* `diracHamiltonian_rest_positive_energy` / `_negative_energy` — the rest-frame Dirac equation:
  the upper spinor has energy `+mc²`, the lower `−mc²` (the four solutions = 2 spin × 2
  particle/antiparticle).
* `rest_energy_kleinGordon` — the rest energies `±mc²` satisfy the Klein–Gordon relation at
  `p = 0` (`E² = (mc²)²`), the `p = 0` Dirac branches `±Δ` of `Dirac.ConfinedPhotonDiracDispersion`.

## References

* P. A. M. Dirac (1928); the four-component Dirac spinor.
* `Dirac.CompleteDiracEquation`, `Dirac.KleinGordonDiracFactorization` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

open Matrix PauliMatrix
open Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.Spinors

/-! ## §A — the Dirac spinor space -/

/-- **A Dirac spinor**: a 4-component object `ψ ∈ ℂ⁴`, as `Fin 2 ⊕ Fin 2 → ℂ` (upper ⊕ lower
2-spinors). -/
abbrev DiracSpinor : Type := Fin 2 ⊕ Fin 2 → ℂ

/-- **Upper (positive-energy) Dirac spinor** `(χ, 0)` with 2-spinor (spin) part `χ`. -/
def restPositiveSpinor (χ : Fin 2 → ℂ) : DiracSpinor := Sum.elim χ 0

/-- **Lower (negative-energy) Dirac spinor** `(0, χ)`. -/
def restNegativeSpinor (χ : Fin 2 → ℂ) : DiracSpinor := Sum.elim 0 χ

/-! ## §B — `β` eigenspinors (positive/negative energy) -/

/-- **The upper spinor is a `+1` eigenspinor of `β`** (`β (χ,0) = (χ,0)`). -/
theorem diracBeta_mulVec_restPositive (χ : Fin 2 → ℂ) :
    diracBeta *ᵥ restPositiveSpinor χ = restPositiveSpinor χ := by
  unfold diracBeta restPositiveSpinor
  rw [fromBlocks_mulVec]
  ext i
  rcases i with i | i <;>
    simp [Matrix.one_mulVec, Matrix.zero_mulVec]

/-- **The lower spinor is a `−1` eigenspinor of `β`** (`β (0,χ) = −(0,χ)`). -/
theorem diracBeta_mulVec_restNegative (χ : Fin 2 → ℂ) :
    diracBeta *ᵥ restNegativeSpinor χ = -restNegativeSpinor χ := by
  unfold diracBeta restNegativeSpinor
  rw [fromBlocks_mulVec]
  ext i
  rcases i with i | i <;>
    simp [Matrix.one_mulVec, Matrix.zero_mulVec, Matrix.neg_mulVec]

/-! ## §C — the rest-frame Dirac equation `H ψ = E ψ` -/

/-- **The rest-frame Dirac Hamiltonian** `H(p=0) = mc²·β` (the `α·p` term vanishes). -/
theorem diracHamiltonian_rest (c mc2 : ℝ) :
    diracHamiltonian c 0 0 0 mc2 = ((mc2 : ℝ) : ℂ) • diracBeta := by
  unfold diracHamiltonian
  simp

/-- **Positive-energy rest solution**: `H ψ₊ = +mc²·ψ₊` for the upper spinor — the rest-frame
Dirac equation with energy `+mc²`. -/
theorem diracHamiltonian_rest_positive_energy (c mc2 : ℝ) (χ : Fin 2 → ℂ) :
    diracHamiltonian c 0 0 0 mc2 *ᵥ restPositiveSpinor χ
      = ((mc2 : ℝ) : ℂ) • restPositiveSpinor χ := by
  rw [diracHamiltonian_rest, Matrix.smul_mulVec, diracBeta_mulVec_restPositive]

/-- **Negative-energy rest solution**: `H ψ₋ = −mc²·ψ₋` for the lower spinor — energy `−mc²`. -/
theorem diracHamiltonian_rest_negative_energy (c mc2 : ℝ) (χ : Fin 2 → ℂ) :
    diracHamiltonian c 0 0 0 mc2 *ᵥ restNegativeSpinor χ
      = -(((mc2 : ℝ) : ℂ) • restNegativeSpinor χ) := by
  rw [diracHamiltonian_rest, Matrix.smul_mulVec, diracBeta_mulVec_restNegative, smul_neg]

/-- **The rest energies satisfy Klein–Gordon at `p = 0`**: `(±mc²)² = (mc²)²` — the `p = 0`
Dirac branches `±Δ` (gap `Δ = mc²`) of `Dirac.ConfinedPhotonDiracDispersion`. -/
theorem rest_energy_kleinGordon (mc2 v₀ : ℝ) :
    Dirac.KleinGordonDiracFactorization.kleinGordonRelation mc2 v₀ 0 mc2 := by
  unfold Dirac.KleinGordonDiracFactorization.kleinGordonRelation
  ring

end Physlib.QuantumMechanics.ComplexAction.Dirac.Spinors

end
