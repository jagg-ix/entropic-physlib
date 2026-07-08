/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit

/-!
# Bennett's spinor orthonormality `ūu = I₂`, `v̄v = −I₂`, `ūv = v̄u = 0` (Eqs. 14–17)

Formalizes the explicit forward/backward spinors and their Dirac-conjugate orthonormality of
*A. F. Bennett, "First Quantized Electrodynamics", arXiv:1406.0750v3*, Eqs. 14–17. In the Dirac
representation `γ⁰ = diag(I₂, −I₂)`, the on-shell spinors are the `4×2` block matrices (Eq. 15)

  `u(p) = K [ (m+E) I₂ ; φ (p·σ) ]`,   `v(p) = K [ φ (p·σ) ; (m+E) I₂ ]`,   `K = [2m(m+E)]^(−1/2)`,

and the Dirac conjugate is `ū = u† γ⁰`. Bennett's Eq. 17 orthonormality `ūu = I₂`, `v̄v = −I₂`,
`ūv = v̄u = 0` follows from three ingredients already in the repo:

* `(p·σ)² = |p|² I₂` (`Dirac.PauliEquationSpinOrbit.sigmaDot_sq`),
* `(p·σ)† = p·σ` Hermitian (`Dirac.PauliEquationSpinOrbit.sigmaDot_isSelfAdjoint`),
* the **mass shell** `|p|² = E² − m²` and the **normalization** `K² · 2m(m+E) = 1`.

Because `γ⁰ = diag(I₂, −I₂)`, the bilinear `ū·v = u† γ⁰ v` reduces to `Tᵘ† Tᵛ − Bᵘ† Bᵛ` of the top/bottom
`2×2` blocks (`diracConj_reduce`), so the whole computation stays at the `2×2` level — no `4×4` entry
expansion. The sign `φ = ±1` (the `dt/dτ` direction of `FirstQuantizedQED.ParametrizedDirac`) enters only as
`φ² = 1`, so it drops out of every norm.

* **§A — the block spinor and the `γ⁰` reduction** (`blockSpinor`, `gamma0Block`, `diracConj_reduce`).
  `ū·v = u† γ⁰ v = Tᵘ† Tᵛ − Bᵘ† Bᵛ`.
* **§B — the normalization identity** (`blockNorm_massShell`). `Tᵘ† Tᵘ − Bᵘ† Bᵘ = K²[(m+E)² − |p|²] I₂ = I₂`
  on the mass shell with `K² · 2m(m+E) = 1`.
* **§C — the spinors and Eq. 17** (`uSpinor`, `vSpinor`, `ubar_u`, `vbar_v`, `ubar_v`, `vbar_u`).
  `ūu = I₂`, `v̄v = −I₂`, `ūv = 0`, `v̄u = 0`.

These are exactly the orthonormality relations whose projector form `Λ_u = uū`, `Λ_v = −v̄v` is the
involution → projector algebra of `FirstQuantizedQED.DiracProjectors` (`bennett_proj_complete`, `…_idem`,
`…_orthogonal`): `ūu = I₂` and `v̄v = −I₂` make `Λ_u + Λ_v = I₄` and `Λ_u Λ_v = 0`.

## References

* A. F. Bennett, *First Quantized Electrodynamics*, arXiv:1406.0750v3 (2020), Eqs. 14–17.
* Repo dependencies: `Dirac.PauliEquationSpinOrbit` (`sigmaDot`, `sigmaDot_sq`, `sigmaDot_isSelfAdjoint`, `dotR`);
  the Bennett mass-shell / `K` agreement is in `FirstQuantizedQED.ParametrizedDirac`, the projectors in
  `FirstQuantizedQED.DiracProjectors`.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.SpinorNormalization

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit

/-- 2×2 complex matrices (a Weyl block of the Dirac four-spinor). -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-! ## §A — the block spinor and the `γ⁰` reduction -/

/-- **A `4×2` block spinor** with top block `T` (rows `inl`) and bottom block `Bo` (rows `inr`). -/
def blockSpinor (T Bo : M2) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2) ℂ :=
  Matrix.of (Sum.elim (fun a => T a) (fun a => Bo a))

/-- **The Dirac time matrix** `γ⁰ = diag(I₂, −I₂)` in `2×2` block form. -/
def gamma0Block : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := Matrix.fromBlocks 1 0 0 (-1)

/-- **[Bennett — the `γ⁰` reduction] The Dirac-conjugate bilinear reduces to the blocks.** With
`γ⁰ = diag(I₂, −I₂)`, the Dirac conjugate `ū = u† γ⁰` gives `ū·v = u† γ⁰ v = Tᵘ† Tᵛ − Bᵘ† Bᵛ` — the
upper block contributes `+`, the lower block `−`. This is what turns the `4×2` orthonormality into the
`2×2` block algebra below. -/
theorem diracConj_reduce (T Bo S Bot : M2) :
    (blockSpinor T Bo)ᴴ * gamma0Block * (blockSpinor S Bot) = Tᴴ * S - Boᴴ * Bot := by
  ext j k
  simp only [Matrix.mul_apply, gamma0Block, blockSpinor, Matrix.fromBlocks, Matrix.of_apply,
    Fintype.sum_sum_type, Matrix.conjTranspose_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, Matrix.neg_apply]
  simp only [mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_const_zero, add_zero, zero_add,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-! ## §B — the normalization identity from the mass shell -/

/-- **[Bennett Eq. 17 — the normalization] `K²[(m+E)² − |p|²] I₂ = I₂` on the mass shell.** The forward
block norm `Tᵘ† Tᵘ − Bᵘ† Bᵘ = (K(m+E))² I₂ − K²(p·σ)² = K²[(m+E)² − |p|²] I₂`. On the mass shell
`|p|² = E² − m²` this is `K² · 2m(m+E) · I₂ = I₂` by the normalization `K² · 2m(m+E) = 1`. -/
theorem blockNorm_massShell (m E K : ℝ) (p : Fin 3 → ℝ)
    (hMass : dotR p p = E ^ 2 - m ^ 2) (hK : K ^ 2 * (2 * m * (m + E)) = 1) :
    ((K * (m + E) : ℂ) • (1 : M2))ᴴ * ((K * (m + E) : ℂ) • 1)
      - ((K : ℂ) • sigmaDot p)ᴴ * ((K : ℂ) • sigmaDot p) = 1 := by
  rw [conjTranspose_smul, conjTranspose_smul, conjTranspose_one, sigmaDot_isSelfAdjoint,
    smul_mul_smul_comm, smul_mul_smul_comm, one_mul, sigmaDot_sq, hMass]
  simp only [RCLike.star_def, map_mul, map_add, Complex.conj_ofReal, smul_smul]
  rw [← sub_smul]
  rw [show (K : ℂ) * ((m : ℂ) + E) * ((K : ℂ) * ((m : ℂ) + E))
        - (K : ℂ) * K * ((E ^ 2 - m ^ 2 : ℝ) : ℂ) = 1 from ?_, one_smul]
  have hKc : (K : ℂ) ^ 2 * (2 * m * (m + E)) = 1 := by exact_mod_cast hK
  push_cast at hKc ⊢
  linear_combination hKc

/-! ## §C — the on-shell spinors and Bennett's Eq. 17 orthonormality -/

/-- **[Bennett Eq. 15] The forward spinor** `u(p) = K [ (m+E) I₂ ; (p·σ) ]` (`φ = +1`). -/
noncomputable def uSpinor (m E K : ℝ) (p : Fin 3 → ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2) ℂ :=
  blockSpinor ((K * (m + E) : ℂ) • 1) ((K : ℂ) • sigmaDot p)

/-- **[Bennett Eq. 15] The backward spinor** `v(p) = K [ (p·σ) ; (m+E) I₂ ]` (`φ = +1`). -/
noncomputable def vSpinor (m E K : ℝ) (p : Fin 3 → ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2) ℂ :=
  blockSpinor ((K : ℂ) • sigmaDot p) ((K * (m + E) : ℂ) • 1)

/-- **[Bennett Eq. 17] `ūu = I₂`.** The forward spinor is unit-normalized on the mass shell. -/
theorem ubar_u (m E K : ℝ) (p : Fin 3 → ℝ)
    (hMass : dotR p p = E ^ 2 - m ^ 2) (hK : K ^ 2 * (2 * m * (m + E)) = 1) :
    (uSpinor m E K p)ᴴ * gamma0Block * (uSpinor m E K p) = 1 := by
  rw [uSpinor, diracConj_reduce]
  exact blockNorm_massShell m E K p hMass hK

/-- **[Bennett Eq. 17] `v̄v = −I₂`.** The backward spinor has the opposite-sign Dirac norm — the negative
norm of the antiparticle (`Λ_v = −v̄v`). -/
theorem vbar_v (m E K : ℝ) (p : Fin 3 → ℝ)
    (hMass : dotR p p = E ^ 2 - m ^ 2) (hK : K ^ 2 * (2 * m * (m + E)) = 1) :
    (vSpinor m E K p)ᴴ * gamma0Block * (vSpinor m E K p) = -1 := by
  rw [vSpinor, diracConj_reduce]
  rw [show ((K : ℂ) • sigmaDot p)ᴴ * ((K : ℂ) • sigmaDot p)
        - ((K * (m + E) : ℂ) • (1 : M2))ᴴ * ((K * (m + E) : ℂ) • 1)
      = -(((K * (m + E) : ℂ) • (1 : M2))ᴴ * ((K * (m + E) : ℂ) • 1)
        - ((K : ℂ) • sigmaDot p)ᴴ * ((K : ℂ) • sigmaDot p)) from (neg_sub _ _).symm]
  rw [blockNorm_massShell m E K p hMass hK]

/-- **[Bennett Eq. 17] `ūv = 0`.** The forward and backward spinors are Dirac-orthogonal — and this holds
off the mass shell too, since it is pure block commutativity `(m+E)(p·σ) = (p·σ)(m+E)`. -/
theorem ubar_v (m E K : ℝ) (p : Fin 3 → ℝ) :
    (uSpinor m E K p)ᴴ * gamma0Block * (vSpinor m E K p) = 0 := by
  rw [uSpinor, vSpinor, diracConj_reduce, conjTranspose_smul, conjTranspose_smul,
    conjTranspose_one, sigmaDot_isSelfAdjoint]
  simp only [RCLike.star_def, map_mul, map_add, Complex.conj_ofReal]
  rw [smul_mul_smul_comm, smul_mul_smul_comm, one_mul, mul_one, sub_eq_zero]
  congr 1
  ring

/-- **[Bennett Eq. 17] `v̄u = 0`.** The other off-diagonal Dirac overlap vanishes (again pure block
commutativity). -/
theorem vbar_u (m E K : ℝ) (p : Fin 3 → ℝ) :
    (vSpinor m E K p)ᴴ * gamma0Block * (uSpinor m E K p) = 0 := by
  rw [uSpinor, vSpinor, diracConj_reduce, conjTranspose_smul, conjTranspose_smul,
    conjTranspose_one, sigmaDot_isSelfAdjoint]
  simp only [RCLike.star_def, map_mul, map_add, Complex.conj_ofReal]
  rw [smul_mul_smul_comm, smul_mul_smul_comm, one_mul, mul_one, sub_eq_zero]
  congr 1
  ring

end Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.SpinorNormalization

end
