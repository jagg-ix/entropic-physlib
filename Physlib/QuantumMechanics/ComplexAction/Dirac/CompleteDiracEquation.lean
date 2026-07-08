/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
public import Physlib.Relativity.PauliMatrices.Basic

/-!
# The complete (3+1)D Dirac equation: 4×4 Dirac matrices and the Clifford algebra

This file formalizes the **complete Dirac equation** in (3+1) dimensions — the 4×4 Dirac
matrices `αⁱ, β` and their full Clifford anticommutation algebra — generalizing the 2×2
confined-photon Dirac of `Dirac.KleinGordonDiracFactorization` to the full electron/photon spinor.

The Dirac Hamiltonian is `H = c α·p + β mc²`. To make `H² = (c²|p|² + m²c⁴)·I` (the Klein–Gordon
energy–momentum relation), the 4×4 matrices, built from the physlib Pauli matrices `σⁱ`
(`Relativity.PauliMatrices`) in the Dirac representation

  `αⁱ = !![0, σⁱ; σⁱ, 0]`,   `β = !![1, 0; 0, −1]`   (2×2 blocks),

must satisfy the **complete Clifford algebra**

  `(αⁱ)² = 1`,  `β² = 1`,  `{αⁱ, β} = 0`,  `{αⁱ, αʲ} = 0` (i ≠ j).

## Main results

* `diracAlpha`, `diracBeta` — the 4×4 Dirac matrices (as `Fin 2 ⊕ Fin 2` block matrices).
* `diracAlpha_sq`, `diracBeta_sq` — `(αⁱ)² = 1`, `β² = 1`.
* `diracAlpha_beta_anticomm` — `{αⁱ, β} = 0`.
* `diracAlpha_anticomm` — `{αⁱ, αʲ} = 0` when the Pauli blocks anticommute; instantiated for the
  three pairs (`alpha12_anticomm`, `alpha13_anticomm`, `alpha23_anticomm`) from physlib's
  `σ2_mul_σ1` etc.
* `diracGamma0`, `diracGamma0_sq` — the time gamma `γ⁰ = β`, `(γ⁰)² = 1`.

Together these are the complete Clifford algebra `{γ^μ, γ^ν} = 2η^μν` that *is* the Dirac
equation: the matrix square root of Klein–Gordon. The 2×2 `Dirac.KleinGordonDiracFactorization` is its
(1+1)D reduction.

## References

* P. A. M. Dirac, Proc. R. Soc. A 117 (1928) 610; the Dirac representation of `αⁱ, β`.
* `Dirac.KleinGordonDiracFactorization` (2×2 reduction), `Relativity.PauliMatrices` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

open Matrix PauliMatrix

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation

/-! ## §A — the 4×4 Dirac matrices (Dirac representation, Pauli blocks) -/

/-- **The Dirac `α` matrix** for a Pauli block `s`: `α = !![0, s; s, 0]` (off-diagonal). -/
def diracAlpha (s : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  fromBlocks 0 s s 0

/-- **The Dirac `β` matrix**: `β = !![1, 0; 0, −1]` (diagonal). -/
def diracBeta : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  fromBlocks 1 0 0 (-1)

/-! ## §B — the complete Clifford anticommutation algebra -/

/-- **`(αⁱ)² = 1`** when the Pauli block squares to `1`. -/
theorem diracAlpha_sq (s : Matrix (Fin 2) (Fin 2) ℂ) (hs : s * s = 1) :
    diracAlpha s * diracAlpha s = 1 := by
  unfold diracAlpha
  rw [fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, zero_add, hs, fromBlocks_one]

/-- **`β² = 1`**. -/
theorem diracBeta_sq : diracBeta * diracBeta = 1 := by
  unfold diracBeta
  rw [fromBlocks_multiply]
  simp only [mul_one, mul_zero, add_zero, zero_add, mul_neg, neg_neg, neg_zero,
    fromBlocks_one]

/-- **`{αⁱ, β} = 0`**: the Dirac `α` and `β` anticommute. -/
theorem diracAlpha_beta_anticomm (s : Matrix (Fin 2) (Fin 2) ℂ) :
    diracAlpha s * diracBeta + diracBeta * diracAlpha s = 0 := by
  unfold diracAlpha diracBeta
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add]
  simp only [mul_zero, zero_mul, mul_one, one_mul, mul_neg_one, neg_one_mul, add_zero, zero_add,
    neg_add_cancel, add_neg_cancel, fromBlocks_zero]

/-- **`{αⁱ, αʲ} = 0`** when the Pauli blocks anticommute (`s·t + t·s = 0`). -/
theorem diracAlpha_anticomm (s t : Matrix (Fin 2) (Fin 2) ℂ) (hst : s * t + t * s = 0) :
    diracAlpha s * diracAlpha t + diracAlpha t * diracAlpha s = 0 := by
  unfold diracAlpha
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add]
  simp only [mul_zero, zero_mul, add_zero, zero_add, hst, fromBlocks_zero]

/-! ## §C — instantiation for the physlib Pauli matrices `σ1, σ2, σ3` -/

/-- `(α¹)² = 1` (from `σ1² = 1`). -/
theorem alpha1_sq : diracAlpha σ1 * diracAlpha σ1 = 1 := diracAlpha_sq _ (pauliMatrix_mul_self _)

/-- `(α²)² = 1`. -/
theorem alpha2_sq : diracAlpha σ2 * diracAlpha σ2 = 1 := diracAlpha_sq _ (pauliMatrix_mul_self _)

/-- `(α³)² = 1`. -/
theorem alpha3_sq : diracAlpha σ3 * diracAlpha σ3 = 1 := diracAlpha_sq _ (pauliMatrix_mul_self _)

/-- `{α¹, α²} = 0` (from `σ2 σ1 = −σ1 σ2`). -/
theorem alpha12_anticomm :
    diracAlpha σ1 * diracAlpha σ2 + diracAlpha σ2 * diracAlpha σ1 = 0 :=
  diracAlpha_anticomm _ _ (by simp [σ2_mul_σ1])

/-- `{α¹, α³} = 0`. -/
theorem alpha13_anticomm :
    diracAlpha σ1 * diracAlpha σ3 + diracAlpha σ3 * diracAlpha σ1 = 0 :=
  diracAlpha_anticomm _ _ (by simp [σ3_mul_σ1])

/-- `{α², α³} = 0`. -/
theorem alpha23_anticomm :
    diracAlpha σ2 * diracAlpha σ3 + diracAlpha σ3 * diracAlpha σ2 = 0 :=
  diracAlpha_anticomm _ _ (by simp [σ3_mul_σ2])

/-! ## §D — the time gamma matrix `γ⁰ = β` -/

/-- **The time Dirac gamma matrix** `γ⁰ = β`. -/
def diracGamma0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := diracBeta

/-- **`(γ⁰)² = 1`** (the timelike Clifford relation `{γ⁰,γ⁰} = 2η⁰⁰ = 2`). -/
theorem diracGamma0_sq : diracGamma0 * diracGamma0 = 1 := diracBeta_sq

/-! ## §E — the Dirac Hamiltonian `H = c α·p + β mc²` -/

/-- **The Dirac Hamiltonian** `H = c(p₁α¹ + p₂α² + p₃α³) + mc² β` (`c, pᵢ, mc²` real). Its
square is `(c²|p|² + m²c⁴)·I` by the Clifford algebra above — the Klein–Gordon factorisation. -/
noncomputable def diracHamiltonian (c p₁ p₂ p₃ mc2 : ℝ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  ((c * p₁ : ℝ) : ℂ) • diracAlpha σ1 + ((c * p₂ : ℝ) : ℂ) • diracAlpha σ2
    + ((c * p₃ : ℝ) : ℂ) • diracAlpha σ3 + ((mc2 : ℝ) : ℂ) • diracBeta

end Physlib.QuantumMechanics.ComplexAction.Dirac.CompleteDiracEquation

end
