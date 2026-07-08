/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Greaves–Thomas §7 (Example 9): the `SL(2,ℂ)` cover of the Lorentz group

Formalizes Example 9 of §7 of *H. Greaves, T. Thomas, "The CPT Theorem"* (arXiv:1204.4674) — the explicit
four-dimensional realization of the covering groups. The double cover `L̃↑₊ ≅ SL(2,ℂ)` of the proper
orthochronous Lorentz group `L↑₊` is exhibited via the **Hermitian-matrix encoding** of a 4-vector
(their Eq. 16) and the spinor action (Eqs. 17–18):

  `⟨x⟩ = [[x₀+x₃, x₁−ix₂], [x₁+ix₂, x₀−x₃]]`,   `⟨π(A)x⟩ = A⟨x⟩Āᵀ`,   `⟨π(A,B)x⟩ = A⟨x⟩Bᵀ`.

The Minkowski norm is `det⟨x⟩`, preserved because `det A = det Āᵀ = 1`, so `π` lands in the Lorentz group;
`π` is two-to-one (`π(A) = π(−A)`), and the four-fold cover `L̃₊(ℂ) → L₊(ℂ)` is four-to-one
(`π(A,B) = π(−A,−B) = π(iA,−iB) = π(−iA,iB)`).

* **§A — the Hermitian encoding** (`bracket`, `bracket_isHermitian`, `det_bracket`, `det_bracket_planar`).
  `⟨x⟩` is Hermitian and `det⟨x⟩ = x₀²−x₁²−x₂²−x₃²` is the Minkowski norm; on the `(x₀,x₃)` plane this is
  the repo's complex-action lightcone form `ComplexDelta.Convergence.lorentzianForm (x₀ + i x₃)`.
* **§B — the `SL(2,ℂ)` action** (`coverAction`, `det_coverAction`, `coverAction_neg`). `A⟨x⟩Aᴴ` preserves
  `det⟨x⟩` when `det A = 1` (the cover lands in the Lorentz group), and `π(−A) = π(A)` — the two-to-one
  double cover `SL(2,ℂ) → L↑₊`.
* **§C — the four-fold cover** (`coverAction2`, `coverAction2_neg`, `coverAction2_iScale`). The action
  `A⟨x⟩Bᵀ` of `L̃₊(ℂ) ≅ {(A,B) : det A = det B}` over `L₊(ℂ)` is four-to-one: invariant under
  `(A,B) ↦ (−A,−B)` and `(A,B) ↦ (iA,−iB)`.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §7 (Example 9; Eqs. 16–18, the `SL(2,ℂ)`
  cover and the four-fold cover `L̃₊(ℂ)`).
* Repo structure: `ComplexDelta.Convergence.lorentzianForm` (the complex-action `re²−im²` lightcone form).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.SL2CCover

open Matrix Complex
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

/-! ## §A — the Hermitian-matrix encoding of a 4-vector (Eq. 16) -/

/-- **[Greaves–Thomas Eq. 16] The Hermitian encoding** `⟨x⟩` of a 4-vector `x = (x₀,x₁,x₂,x₃)` — the
self-adjoint `2×2` complex matrix `[[x₀+x₃, x₁−ix₂], [x₁+ix₂, x₀−x₃]]`. -/
noncomputable def bracket (x : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x 0 : ℂ) + x 3, (x 1 : ℂ) - I * x 2; (x 1 : ℂ) + I * x 2, (x 0 : ℂ) - x 3]

/-- **`⟨x⟩` is Hermitian** `⟨x⟩ᴴ = ⟨x⟩`. -/
theorem bracket_isHermitian (x : Fin 4 → ℝ) : (bracket x).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bracket, Matrix.conjTranspose_apply, Complex.ext_iff]

/-- **[Greaves–Thomas] `det⟨x⟩` is the Minkowski norm** `x₀² − x₁² − x₂² − x₃²`. -/
theorem det_bracket (x : Fin 4 → ℝ) :
    (bracket x).det = ((x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2 : ℝ) : ℂ) := by
  simp only [bracket, Matrix.det_fin_two_of]; push_cast
  linear_combination (x 2 : ℂ) ^ 2 * Complex.I_sq

/-- **[Link to the complex-action lightcone] On the `(x₀,x₃)` plane, `det⟨x⟩` is the repo's `lorentzianForm`.** With
`x₁ = x₂ = 0`, `det⟨x⟩ = x₀² − x₃² = lorentzianForm (x₀ + i x₃)` — the `1+1`-dimensional complex-action lightcone form
of `ComplexDelta.Convergence`. -/
theorem det_bracket_planar (x : Fin 4 → ℝ) (h1 : x 1 = 0) (h2 : x 2 = 0) :
    (bracket x).det = ((lorentzianForm ((x 0 : ℂ) + I * x 3) : ℝ) : ℂ) := by
  rw [det_bracket, lorentzianForm]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  push_cast [h1, h2]; ring

/-! ## §B — the `SL(2,ℂ)` action and the double cover (Eq. 17) -/

/-- **[Greaves–Thomas Eq. 17] The `SL(2,ℂ)` action** `⟨π(A)x⟩ = A ⟨x⟩ Aᴴ` (with `Aᴴ = Āᵀ`). -/
noncomputable def coverAction (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ := A * bracket x * Aᴴ

/-- **[Greaves–Thomas] The cover preserves the Minkowski norm** `det(A⟨x⟩Aᴴ) = det⟨x⟩` when `det A = 1` —
so `π(A) ∈ L↑₊` is a Lorentz transformation. -/
theorem det_coverAction (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) (hA : A.det = 1) :
    (coverAction A x).det = (bracket x).det := by
  simp only [coverAction, Matrix.det_mul, Matrix.det_conjTranspose, hA]
  simp

/-- **[Greaves–Thomas] `π` is two-to-one** `π(−A) = π(A)` — `SL(2,ℂ) → L↑₊` is a double cover. -/
theorem coverAction_neg (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    coverAction (-A) x = coverAction A x := by
  simp [coverAction, Matrix.conjTranspose_neg]

/-! ## §C — the four-fold cover `L̃₊(ℂ)` (Eq. 18) -/

/-- **[Greaves–Thomas Eq. 18] The four-fold cover action** `⟨π(A,B)x⟩ = A ⟨x⟩ Bᵀ` of
`L̃₊(ℂ) ≅ {(A,B) : det A = det B}` over the complex proper Lorentz group `L₊(ℂ)`. The `SL(2,ℂ)` action of
§B is the restriction to the real form `(A, Ā)` (`Bᵀ = Āᵀ = Aᴴ`). -/
noncomputable def coverAction2 (A B : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ := A * bracket x * Bᵀ

/-- **[Greaves–Thomas, four-to-one] `π(−A,−B) = π(A,B)`.** -/
theorem coverAction2_neg (A B : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    coverAction2 (-A) (-B) x = coverAction2 A B x := by
  simp [coverAction2, Matrix.transpose_neg]

/-- **[Greaves–Thomas, four-to-one] `π(iA,−iB) = π(A,B)`.** The remaining sheet of the four-fold cover —
the `i`-scalings `I` (with `I² = τ`) act trivially on `L₊(ℂ)`. -/
theorem coverAction2_iScale (A B : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    coverAction2 (I • A) ((-I) • B) x = coverAction2 A B x := by
  simp only [coverAction2, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [neg_mul, Complex.I_mul_I, neg_neg, one_smul]

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.SL2CCover

end
