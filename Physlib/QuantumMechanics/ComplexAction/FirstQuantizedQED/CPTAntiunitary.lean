/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ChiralityHelicityProjectors

/-!
# Bennett's antiunitary `C, P, T` acting on the four-spinor `ψ` (Eqs. 7–10)

The companion file `FirstQuantizedQED.ChiralityHelicityProjectors` establishes the *matrix* facts `P² = γ⁰² = 1`,
`(−iγ⁵)² = −1`. This file completes Bennett's discrete symmetries (*A. F. Bennett, "First Quantized
Electrodynamics", arXiv:1406.0750v3*, Eqs. 7–10) by realizing them as **operators on the spinor field**
`ψ : Fin 4 → ℂ`, including the **antiunitary** charge conjugation and time reversal that have a
component-wise complex conjugation `ψ ↦ ψ*` (here `star ψ`):

  `P ψ = γ⁰ ψ`   (unitary),   `C ψ = i γ² ψ*`,   `T ψ = i γ¹γ³ ψ*`   (antiunitary).

The antiunitary structure is exactly the sign encoded in squaring each operator:

  `P² = +1`,   `C² = +1`,   `T² = −1`,

the last being the half-integer-spin (`spin-½`) signature `T² = −1`. The mechanism is uniform: an
antilinear operator `A ψ = M ψ*` squares to `A² ψ = M M* ψ` (the conjugate matrix `M*` appears because
the second conjugation hits `M`), so the sign is set by whether the Dirac-rep matrix is **real**
(`γ¹, γ³` ⇒ `M* = M`) or **imaginary** (`γ²` ⇒ `M* = −M`).

* **§A — conjugation algebra** (`star_mulVec_map`, the entrywise-`star` images of `iγ²`, `iγ¹γ³`,
  `γ⁰·iγ¹γ³`, and the matrix squares). `star (M ⬝ᵥ v) = M* ⬝ᵥ v*`; `iγ²` is real, `iγ¹γ³` and
  `γ⁰·iγ¹γ³` are imaginary.
* **§B — the operators and their squares** (`parityOp`, `chargeConj`, `timeReversal`,
  `parity_involutive`, `chargeConj_involutive`, `timeReversal_sq`). `P² = +1`, `C² = +1`, `T² = −1`.
* **§C — the combined `CPT` is linear and equals `−iγ⁵`** (`cpt`, `cpt_eq_tpcMatrix`, `cpt_sq`). The two
  conjugations of `C` and `T` cancel, so `CPT ψ = (C∘P∘T) ψ = (−iγ⁵) ψ` is a **unitary** (linear)
  operator — the TPC matrix of `FirstQuantizedQED.ChiralityHelicityProjectors.tpc_matrix_sq` — and hence
  `CPT² = (−iγ⁵)² ψ = −ψ`, the fermionic TPC sign.

These are the spinor-component (Dirac-matrix) parts of Bennett's discrete symmetries; the coordinate
flips `x ↦ −x` (parity, TPC) and `t ↦ −t` (time reversal) act on `ψ`'s *arguments* and are orthogonal to
the matrix/conjugation algebra formalized here.

## References

* A. F. Bennett, *First Quantized Electrodynamics*, arXiv:1406.0750v3 (2020), Eqs. 7–10.
* Repo dependencies: `Relativity.CliffordAlgebra` (`γ0`–`γ5`, Dirac representation; `γⁱ_mul_γʲ` relations);
  `FirstQuantizedQED.ChiralityHelicityProjectors` (`parity_sq`, `tpc_matrix_sq`, `gamma1gamma3`-type relations).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary

open Matrix Complex
open spaceTime
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.ChiralityHelicityProjectors

/-! ## §A — the conjugation algebra -/

/-- **Entrywise conjugation through `mulVec`.** `star (M ⬝ᵥ v) = M* ⬝ᵥ v*`, where `M*` is the
entrywise-conjugate matrix `M.map star`. This is what lets an antilinear `ψ ↦ M ψ*` be squared. -/
theorem star_mulVec_map {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    star (A *ᵥ v) = A.map star *ᵥ star v := by
  ext i
  simp only [Pi.star_apply, Matrix.mulVec, dotProduct, star_sum, Matrix.map_apply]
  exact Finset.sum_congr rfl (fun j _ => by rw [star_mul'])

/-- `iγ²` is a **real** matrix: its entrywise conjugate is itself. (`γ²` is purely imaginary in the Dirac
representation, so `i·γ²` is real — the source of `C² = +1`.) -/
theorem Iγ2_map_star : (I • γ2).map star = I • γ2 := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [γ2, Matrix.map_apply, Matrix.smul_apply] <;> ring_nf <;> simp [Complex.ext_iff]

/-- `iγ¹γ³` is an **imaginary** matrix: its entrywise conjugate negates it. (`γ¹, γ³` are real, so `iγ¹γ³`
is imaginary — the source of `T² = −1`.) -/
theorem Iγ1γ3_map_star : (I • (γ1 * γ3)).map star = -(I • (γ1 * γ3)) := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [γ1, γ3, Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply, Matrix.smul_apply,
      Matrix.neg_apply] <;> ring_nf <;> simp [Complex.ext_iff]

/-- `γ⁰·iγ¹γ³` is imaginary: its entrywise conjugate negates it (used in the `CPT` reduction). -/
theorem Iγ0γ1γ3_map_star : (γ0 * (I • (γ1 * γ3))).map star = -(γ0 * (I • (γ1 * γ3))) := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [γ0, γ1, γ3, Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply, Matrix.smul_apply,
      Matrix.neg_apply] <;> ring_nf <;> simp [Complex.ext_iff]

/-- `(iγ²)² = 1` (the `C`-matrix squares to `+1`): `(iγ²)² = i²(γ²)² = (−1)(−1) = 1`. -/
theorem IgammaC_sq : (I • γ2) * (I • γ2) = 1 := by
  rw [smul_mul_smul_comm, γ2_mul_γ2, Complex.I_mul_I, neg_one_smul, neg_neg]

/-- `(γ¹γ³)² = −1`: `γ¹γ³γ¹γ³ = −(γ¹)²(γ³)² = −(−1)(−1) = −1`. -/
theorem gamma1gamma3_sq : (γ1 * γ3) * (γ1 * γ3) = -1 := by
  rw [show (γ1 * γ3) * (γ1 * γ3) = γ1 * (γ3 * γ1) * γ3 by noncomm_ring, γ3_mul_γ1,
    show γ1 * -(γ1 * γ3) * γ3 = -((γ1 * γ1) * (γ3 * γ3)) by noncomm_ring, γ1_mul_γ1, γ3_mul_γ3]
  simp

/-- `(iγ¹γ³)² = 1` (the `T`-matrix squares to `+1`; the `−1` of `T²` comes from the conjugation, not the
matrix): `(iγ¹γ³)² = i²(γ¹γ³)² = (−1)(−1) = 1`. -/
theorem IgammaT_sq : (I • (γ1 * γ3)) * (I • (γ1 * γ3)) = 1 := by
  rw [smul_mul_smul_comm, gamma1gamma3_sq, Complex.I_mul_I, neg_one_smul, neg_neg]

/-! ## §B — the discrete-symmetry operators on `ψ` -/

/-- **[Bennett Eq. 8] Parity** `P ψ = γ⁰ ψ` (the spinor-component action; the coordinate flip `x ↦ −x`
acts on `ψ`'s argument). Unitary. -/
noncomputable def parityOp (ψ : Fin 4 → ℂ) : Fin 4 → ℂ := γ0 *ᵥ ψ

/-- **[Bennett Eq. 7] Charge conjugation** `C ψ = i γ² ψ*` — antilinear (note the `star ψ`). -/
noncomputable def chargeConj (ψ : Fin 4 → ℂ) : Fin 4 → ℂ := (I • γ2) *ᵥ star ψ

/-- **[Bennett Eq. 9] Time reversal** `T ψ = i γ¹γ³ ψ*` — antilinear (the coordinate flip `t ↦ −t` acts
on `ψ`'s argument). -/
noncomputable def timeReversal (ψ : Fin 4 → ℂ) : Fin 4 → ℂ := (I • (γ1 * γ3)) *ᵥ star ψ

/-- **[Bennett Eq. 8] `P² = +1`.** Parity is an involution (`γ⁰² = 1`). -/
theorem parity_involutive (ψ : Fin 4 → ℂ) : parityOp (parityOp ψ) = ψ := by
  unfold parityOp; rw [Matrix.mulVec_mulVec, γ0_mul_γ0, Matrix.one_mulVec]

/-- **[Bennett Eq. 7] `C² = +1`.** Charge conjugation is an involution: the second conjugation hits the
**real** matrix `iγ²` (`(iγ²)* = iγ²`), and `(iγ²)² = 1`. -/
theorem chargeConj_involutive (ψ : Fin 4 → ℂ) : chargeConj (chargeConj ψ) = ψ := by
  unfold chargeConj
  rw [star_mulVec_map, Iγ2_map_star, star_star, Matrix.mulVec_mulVec, IgammaC_sq, Matrix.one_mulVec]

/-- **[Bennett Eq. 9] `T² = −1`.** Time reversal squares to `−1`: the second conjugation hits the
**imaginary** matrix `iγ¹γ³` (`(iγ¹γ³)* = −iγ¹γ³`), giving `−(iγ¹γ³)² = −1`. This is the half-integer-spin
signature `T² = −1` (the `spin-½` double cover). -/
theorem timeReversal_sq (ψ : Fin 4 → ℂ) : timeReversal (timeReversal ψ) = -ψ := by
  unfold timeReversal
  rw [star_mulVec_map, Iγ1γ3_map_star, star_star, Matrix.neg_mulVec, mulVec_neg,
    Matrix.mulVec_mulVec, IgammaT_sq, Matrix.one_mulVec]

/-! ## §C — the combined `CPT` is linear and equals `−iγ⁵` -/

/-- **[Bennett Eq. 10] The combined `CPT` operator** `CPT ψ = (C∘P∘T) ψ`. -/
noncomputable def cpt (ψ : Fin 4 → ℂ) : Fin 4 → ℂ := chargeConj (parityOp (timeReversal ψ))

/-- The matrix collapse `−(iγ²)(γ⁰·iγ¹γ³) = −iγ⁵` behind `CPT = −iγ⁵`: `(iγ²)(γ⁰)(iγ¹γ³) = i²·γ²γ⁰γ¹γ³`,
and reordering `γ²γ⁰γ¹γ³ = γ⁰γ¹γ²γ³` gives `−iγ⁵` after the overall sign. -/
theorem cpt_matrix : -((I • γ2) * (γ0 * (I • (γ1 * γ3)))) = (-I) • γ5 := by
  simp only [γ0, γ1, γ2, γ3, γ5]
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.smul_apply, Matrix.neg_apply] <;> ring

/-- **[Bennett Eq. 10] `CPT` is unitary and equals `−iγ⁵`.** The two complex conjugations encoded in `C`
and `T` cancel, so `CPT ψ = (−iγ⁵) ψ` is **linear** — it is precisely the TPC matrix `−iγ⁵` of
`FirstQuantizedQED.ChiralityHelicityProjectors.tpc_matrix_sq` realized on the spinor. -/
theorem cpt_eq_tpcMatrix (ψ : Fin 4 → ℂ) : cpt ψ = ((-I) • γ5) *ᵥ ψ := by
  unfold cpt chargeConj parityOp timeReversal
  rw [Matrix.mulVec_mulVec, star_mulVec_map, Iγ0γ1γ3_map_star, star_star, Matrix.neg_mulVec,
    mulVec_neg, Matrix.mulVec_mulVec,
    show -(((I • γ2) * (γ0 * (I • (γ1 * γ3)))) *ᵥ ψ)
      = (-((I • γ2) * (γ0 * (I • (γ1 * γ3))))) *ᵥ ψ from (Matrix.neg_mulVec _ _).symm, cpt_matrix]

/-- **[Bennett Eq. 10] `CPT² = −1`.** Via `CPT = −iγ⁵` and `(−iγ⁵)² = −1`
(`FirstQuantizedQED.ChiralityHelicityProjectors.tpc_matrix_sq`), `CPT² ψ = (−iγ⁵)² ψ = −ψ` — the fermionic TPC sign,
the linear counterpart of `T² = −1`. -/
theorem cpt_sq (ψ : Fin 4 → ℂ) : cpt (cpt ψ) = -ψ := by
  rw [cpt_eq_tpcMatrix, cpt_eq_tpcMatrix, Matrix.mulVec_mulVec, tpc_matrix_sq,
    Matrix.neg_mulVec, Matrix.one_mulVec]

end Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary

end
