/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState

/-!
# The Sorkin–Johnston decomposition is the real/imaginary split of a Hermitian kernel

The Sorkin–Johnston two-point function is `W = A + (i/2)Δ` with `A` a symmetric (Hadamard) kernel and `Δ` an
antisymmetric (Pauli–Jordan) kernel (`SorkinJohnstonRegionState.wightmanTwoPoint`). This module makes precise the
statement that **this decomposition is literally the `Re + i·Im` split of a complex number**: for *any*
complex-valued kernel `W`, taking `A = Re W` and `Δ = 2·Im W` reconstructs `W` exactly as `wightmanTwoPoint A Δ`,
and the kernel is **Hermitian** (`W(x,y) = conj W(y,x)`) precisely when that `A` is symmetric and that `Δ` is
Pauli–Jordan. Hence a Hermitian complex kernel with non-negative diagonal *is* a Sorkin–Johnston state — no real
symmetric/antisymmetric data need be supplied separately.

* **`hadamardPart W = Re W`, `pauliJordanPart W = 2·Im W`** — the real and (doubled) imaginary parts.
* **`wightmanTwoPoint_hadamardPart_pauliJordanPart`** — `wightmanTwoPoint (Re W) (2·Im W) = W`: the SJ form *is*
 the `Re + i·Im` split.
* **`hadamardPart_symmetric` / `pauliJordanPart_isPauliJordan`** — Hermiticity `W(x,y) = conj W(y,x)` gives exactly
 the two SJ structural conditions (`Re` symmetric, `Im` antisymmetric).
* **`hermitian_isSJState`** — a Hermitian kernel with `Re W(x,x) ≥ 0` is a Sorkin–Johnston state.

Exact `Complex`-part identities (`Complex.re_add_im`, `Complex.conj_re/​conj_im`). This is the
general principle behind `TimeOperator.NagaoNielsenSorkinJohnston`, where the Nagao–Nielsen Hermitian pairing
`q̄_j q_k` is the instance realizing the SJ Wightman.

## References

* Johnston, arXiv:0909.0944; Sorkin, *Mod. Phys. Lett. A* **9** (1994) 3119. Refines
 `SorkinJohnstonRegionState.wightmanTwoPoint` to the complex-kernel level.

No new axioms.
-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition

open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState

variable {α : Type*}

/-- **A Hermitian kernel** `W(x,y) = conj W(y,x)` — the reality/reflection condition of a genuine two-point
function. -/
def IsHermitianKernel (W : α → α → ℂ) : Prop := ∀ x y, W x y = (starRingEnd ℂ) (W y x)

/-- The **Hadamard (symmetric) part** of a complex kernel, `Re W`. -/
noncomputable def hadamardPart (W : α → α → ℂ) (x y : α) : ℝ := (W x y).re

/-- The **Pauli–Jordan (antisymmetric) part** of a complex kernel, `2·Im W` (doubled so that `(i/2)Δ = i·Im W`). -/
noncomputable def pauliJordanPart (W : α → α → ℂ) (x y : α) : ℝ := 2 * (W x y).im

/-- **The Sorkin–Johnston form is the `Re + i·Im` split** `wightmanTwoPoint (Re W) (2·Im W) = W` — for *any*
complex kernel `W`, its own real and imaginary parts reconstruct it as an SJ two-point function. This is the exact
sense in which `W = A + (i/2)Δ` is the complex-number decomposition `z = Re z + i·Im z`. -/
theorem wightmanTwoPoint_hadamardPart_pauliJordanPart (W : α → α → ℂ) :
    wightmanTwoPoint (hadamardPart W) (pauliJordanPart W) = W := by
  funext x y
  simp only [wightmanTwoPoint, hadamardPart, pauliJordanPart]
  rw [show ((2 * (W x y).im / 2 : ℝ)) = (W x y).im from by ring, mul_comm Complex.I]
  exact Complex.re_add_im _

/-- **Hermiticity ⟹ the Hadamard part is symmetric** `Re W(x,y) = Re W(y,x)` (since `Re(conj z) = Re z`). -/
theorem hadamardPart_symmetric {W : α → α → ℂ} (hW : IsHermitianKernel W) :
    IsSymmetricKernel (hadamardPart W) := by
  intro x y
  simp only [hadamardPart]
  rw [hW x y, Complex.conj_re]

/-- **Hermiticity ⟹ the Pauli–Jordan part is antisymmetric** `2 Im W(x,y) = −2 Im W(y,x)` (since
`Im(conj z) = −Im z`). -/
theorem pauliJordanPart_isPauliJordan {W : α → α → ℂ} (hW : IsHermitianKernel W) :
    IsPauliJordan (pauliJordanPart W) := by
  intro x y
  simp only [pauliJordanPart]
  rw [hW x y, Complex.conj_im]
  ring

/-- **A Hermitian kernel with non-negative diagonal is a Sorkin–Johnston state** `IsSJState W (2·Im W)` — combining
the reconstruction `W = wightmanTwoPoint (Re W) (2·Im W)` with the SJ structural conditions from Hermiticity and
diagonal positivity `Re W(x,x) ≥ 0`. The complex two-point datum alone determines the SJ vacuum. -/
theorem hermitian_isSJState {W : α → α → ℂ} (hW : IsHermitianKernel W)
    (hpos : ∀ x, 0 ≤ (W x x).re) :
    IsSJState W (pauliJordanPart W) := by
  have h := wightman_isSJState (hadamardPart W) (pauliJordanPart W)
    (hadamardPart_symmetric hW) (pauliJordanPart_isPauliJordan hW) hpos
  rwa [wightmanTwoPoint_hadamardPart_pauliJordanPart W] at h

end Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition
