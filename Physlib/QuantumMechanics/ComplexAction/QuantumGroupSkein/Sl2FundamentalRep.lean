/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.QuantumGroupSl2Casimir
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The fundamental representation `V₂` of `sl₂`, and the Casimir acting as a scalar (Sawin §3, Eq. 13)

The two-dimensional fundamental representation `V₂` of `sl₂` (Sawin, *Links, Quantum Groups and TQFT's*,
q-alg/9506002, Eq. 13 with `n = 2`) is the concrete model of the abstract relations of the companion file
`QuantumGroupSkein.QuantumGroupSl2Casimir`. On the basis `{v₁, v₂}` Sawin's formulas `h v_i = (n−2i+1)v_i`,
`x v_i = (i−1)v_{i−1}`, `y v_i = (n−i)v_{i+1}` give the standard `sl₂` triple

* `fundH = diag(1, −1)`, `fundX = e` (the raising matrix), `fundY = f` (the lowering matrix).

This file makes the abstract development **non-vacuous** by exhibiting explicit matrices that satisfy the
presentation, and proves the representation-theoretic payoff of Casimir centrality:

* **The `sl₂` relations hold on `V₂`** (`fund_relation_hx/hy/xy`): `[h,x] = 2x`, `[h,y] = −2y`, `[x,y] = h`.
* **The Casimir is a scalar on `V₂`** (`casimir_fundamental`): `C = (h+1)² + 4yx = 4·𝟙`. By Schur's lemma
  the central Casimir must act as a scalar on the irreducible `V₂`; here that scalar is `4`.
* **Centrality, concretely** (`casimir_central_fundamental`): `[C, M] = 0` for every `2×2` matrix `M` — the
  matrix-level shadow of `casimir_central_{h,x,y}`, immediate once `C = 4·𝟙`.

## References

* S. Sawin, *Links, Quantum Groups and TQFT's*, q-alg/9506002, §3, Eq. 13 (the `n`-dimensional
  representation `V_n`; here `n = 2`, the self-dual fundamental representation).

No additional assumptions.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.QuantumGroupSl2Casimir

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.Sl2FundamentalRep

/-- **The Cartan generator `h` on `V₂`**: `h v_i = (3 − 2i)v_i`, i.e. `diag(1, −1)`. -/
def fundH : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- **The raising generator `x = e` on `V₂`**: `x v₂ = v₁`, `x v₁ = 0`. -/
def fundX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- **The lowering generator `y = f` on `V₂`**: `y v₁ = v₂`, `y v₂ = 0`. -/
def fundY : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- **[`[h, x] = 2x` on `V₂`]** the raising matrix is the `+2` eigenvector of `ad h`. -/
theorem fund_relation_hx : fundH * fundX - fundX * fundH = 2 * fundX := by
  unfold fundH fundX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.ofNat_apply] <;> norm_num

/-- **[`[h, y] = −2y` on `V₂`]** the lowering matrix is the `−2` eigenvector of `ad h`. -/
theorem fund_relation_hy : fundH * fundY - fundY * fundH = -(2 * fundY) := by
  unfold fundH fundY
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.ofNat_apply] <;> norm_num

/-- **[`[x, y] = h` on `V₂`]** the commutator of raising and lowering is the Cartan generator. -/
theorem fund_relation_xy : fundX * fundY - fundY * fundX = fundH := by
  unfold fundH fundX fundY
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **[The Casimir is the scalar `4` on `V₂`]** `C = (h+1)² + 4yx = 4·𝟙`. The central Casimir acts as a
scalar on the irreducible fundamental representation (Schur); the eigenvalue is `4`. -/
theorem casimir_fundamental :
    casimirElt fundX fundY fundH = (4 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold casimirElt fundH fundX fundY
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.one_apply,
      Matrix.smul_apply, Matrix.ofNat_apply] <;> norm_num

/-- **[The Casimir is central on `V₂`, concretely]** `[C, M] = 0` for every `2×2` matrix `M` — immediate
from `C = 4·𝟙`, and the matrix realization of the abstract `casimir_central_{h,x,y}`. -/
theorem casimir_central_fundamental (M : Matrix (Fin 2) (Fin 2) ℂ) :
    commR (casimirElt fundX fundY fundH) M = 0 := by
  rw [commR, casimir_fundamental, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, sub_self]

end Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.Sl2FundamentalRep

end
