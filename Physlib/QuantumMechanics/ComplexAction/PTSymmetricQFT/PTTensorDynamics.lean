/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics

/-!
# Greaves–Thomas: the tensor / `PT` side — Lorentz-covariant tensor dynamics is `PT`-invariant

The companion files did the *spinor* side of *H. Greaves, T. Thomas, "The CPT Theorem"*
(arXiv:1204.4674): fields valued in *projective* (spinor) representations, where total inversion is the
double-valued `−iγ⁵` and Lorentz covariance entails **`CPT`** invariance. The paper develops the *tensor*
case first (their §5–6): fields valued in **true** representations of the Lorentz group, where Lorentz
covariance entails plain **`PT`** invariance — no charge conjugation, no double cover.

The structural difference is exactly the representation of total inversion `−I`:

* on a **true** rank-`r` representation (a tensor), `ρ(−I) = (−1)^r` — a **single-valued real scalar**
  (`totalInversion_tensor`). No `i`, no complex conjugation, no `±` sign ambiguity. Hence **`PT`**.
* on the **spinor** (projective) representation, `ρ(−I) = ±(−iγ⁵)` — double-valued, requiring the complex
  double cover. Hence **`CPT`** (`PTSymmetricQFT.CPTComplexification`). The spinor `−iγ⁵` *projects onto* the
  vector total inversion: its adjoint sends `γ^μ ↦ −γ^μ` (`cpt_total_inversion`), i.e. acts as `−I` on the
  rank-1 vector index — the spinor cover sitting over the tensor base.

The motivating example is Maxwell `F^{αβ},_β − J^α = 0` (Greaves–Thomas Example 1).

* **§A — total inversion on a true representation is `(−1)^r`** (`totalInversion_tensor`,
  `totalInversionVec`). On a rank-`r` covariant tensor (a `MultilinearMap`) total inversion negates every
  argument and so multiplies the value by `(−1)^r`; on a vector (`r = 1`) it is `v ↦ −v`. Scalars (`r = 0`)
  are invariant, the field strength (`r = 2`) is invariant.
* **§B — the field strength and the Maxwell operator** (`fieldStrength_pt_invariant`, `maxwellOp`,
  `maxwellOp_pt`). `F` is a rank-2 tensor, invariant under total inversion `(−I)F(−I) = F`; the rank-1
  momentum-space operator `(F k)^α = ∑_β F^{αβ} k_β` (`= F^{αβ},_β`) flips by `(−1)` because the derivative
  covector `k` flips, `maxwellOp F (−k) = −maxwellOp F k`.
* **§C — `PT` invariance of the Maxwell dynamics** (`pt_maxwell_invariant`, `pt_maxwell_equation`). If
  `(F, J)` solves Maxwell at momentum `k` (`F^{αβ}k_β = J^α`), the `PT` image solves it at `−k` with the
  rank-1 current flipped `J ↦ −J`: `maxwellOp F (−k) = −J`. Lorentz-covariant tensor dynamics ⟹
  `PT`-invariant dynamics — the tensor analogue of the Dirac `CPT` result
  (`PTSymmetricQFT.CPTDiracDynamics.cpt_maps_dirac_solution`).

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674 — §5–6 the classical/quantum `PT` theorem for
  true (tensor) representations; Example 1, the Maxwell equation.
* Repo dependencies: `PTSymmetricQFT.CPTComplexification` (the spinor `−iγ⁵` side, `cpt_total_inversion`);
  `PTSymmetricQFT.CPTDiracDynamics` (the Dirac `CPT` dynamics this parallels).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.PTTensorDynamics

open scoped BigOperators

/-! ## §A — total inversion on a true (tensor) representation acts as the scalar `(−1)^r` -/

/-- **[Greaves–Thomas tensor case] Total inversion on a rank-`r` true representation is `(−1)^r`.** For a
rank-`r` covariant tensor `T` (a multilinear map of `r` vector arguments), total spacetime inversion negates
every argument, multiplying the value by the **single-valued real scalar** `(−1)^r`:
`T(−v₁,…,−v_r) = (−1)^r · T(v₁,…,v_r)`. The single-valuedness (no `i`, no `±`) is precisely why a true rep
gives `PT`, not `CPT`. -/
theorem totalInversion_tensor {r : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin r => Fin 4 → ℝ) ℝ) (v : Fin r → (Fin 4 → ℝ)) :
    T (fun i => -(v i)) = (-1) ^ r * T v := by
  have hneg : (fun i => -(v i)) = (fun i => ((-1 : ℝ)) • v i) := by
    funext i; rw [neg_one_smul]
  rw [hneg, MultilinearMap.map_smul_univ]
  simp [Finset.prod_const]

/-- **Total inversion on a vector (rank 1)** `v ↦ −v` — the `ρ(−I) = (−1)^1` action on the contravariant
vector representation (the current `J^α` transforms this way). -/
def totalInversionVec (v : Fin 4 → ℝ) : Fin 4 → ℝ := -v

/-- A scalar (rank 0) is `PT`-invariant: `(−1)^0 = 1`. -/
theorem totalInversion_scalar (T : MultilinearMap ℝ (fun _ : Fin 0 => Fin 4 → ℝ) ℝ)
    (v : Fin 0 → (Fin 4 → ℝ)) : T (fun i => -(v i)) = T v := by
  rw [totalInversion_tensor]; simp

/-! ## §B — the field strength (rank 2) and the Maxwell operator -/

/-- **The field strength `F^{αβ}` is `PT`-invariant** `(−I) F (−I) = F` — a rank-2 tensor picks up
`(−1)^2 = 1` from total inversion on its two indices. -/
theorem fieldStrength_pt_invariant (F : Matrix (Fin 4) (Fin 4) ℝ) :
    (-1 : Matrix (Fin 4) (Fin 4) ℝ) * F * (-1) = F := by
  rw [neg_one_mul, mul_neg_one, neg_neg]

/-- **The momentum-space Maxwell operator** `(F k)^α = ∑_β F^{αβ} k_β` — the principal symbol of
`F^{αβ},_β` (Greaves–Thomas Example 1), a rank-1 (contravariant) object. -/
def maxwellOp (F : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun α => ∑ β, F α β * k β

/-- **Total inversion flips the rank-1 Maxwell operator** `maxwellOp F (−k) = −maxwellOp F k`. The field
strength `F` is invariant (rank 2); the derivative covector `k` flips, so the rank-1 result picks up `(−1)`
— exactly the transformation of `F^{αβ},_β` as a contravariant vector. -/
theorem maxwellOp_pt (F : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) :
    maxwellOp F (-k) = -(maxwellOp F k) := by
  funext α; simp only [maxwellOp, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-! ## §C — `PT` invariance of the Maxwell dynamics -/

/-- **[Greaves–Thomas] `PT` maps Maxwell solutions to Maxwell solutions.** If `(F, J)` solves Maxwell at
momentum `k` (`F^{αβ}k_β = J^α`), then the `PT` image — `F` unchanged (rank 2), momentum reversed `k ↦ −k`,
current flipped `J ↦ −J` (rank 1) — solves it: `maxwellOp F (−k) = −J`. Lorentz-covariant tensor dynamics
is `PT`-invariant, with **no charge conjugation** — the tensor analogue of the Dirac `CPT` theorem. -/
theorem pt_maxwell_invariant (F : Matrix (Fin 4) (Fin 4) ℝ) (k J : Fin 4 → ℝ)
    (h : maxwellOp F k = J) : maxwellOp F (-k) = totalInversionVec J := by
  rw [maxwellOp_pt, h, totalInversionVec]

/-- **[Greaves–Thomas] The Maxwell field equation is `PT`-invariant.** Both sides of `F^{αβ}k_β − J^α = 0`
are rank-1 tensors flipping by `(−1)` under total inversion, so the equation `= 0` is preserved:
`maxwellOp F (−k) − (−J) = 0`. -/
theorem pt_maxwell_equation (F : Matrix (Fin 4) (Fin 4) ℝ) (k J : Fin 4 → ℝ)
    (h : maxwellOp F k - J = 0) : maxwellOp F (-k) - (-J) = 0 := by
  rw [maxwellOp_pt, neg_sub_neg, ← neg_sub, h, neg_zero]

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.PTTensorDynamics

end
