/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorPurification
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The `μ_s` interpolation family, polar decomposition `R = U|R|`, and three-lines (Verch §2.1, Prop 2.1)

Formalizes the **functional-analytic layer** of *R. Verch, arXiv:funct-an/9609004*, §2.1 — the one-parameter
family `μ_s(φ,ψ) = μ(φ,|R_μ|^s ψ)` (Eq 2.11), the polar decomposition `R_μ = U_μ|R_μ|` (Eq 2.8), and the
interpolation (Prop 2.1 / the three-lines bound) — on the 2-dim Cauchy-data model where it becomes elementary
and exact, completing `AlgebraicQFTQuasifree.PolarizatorPurification` (§2.1 polarizator) and `AlgebraicQFTQuasifree.SymplecticAdjointContinuity`
(§2.2 continuity).

The key structural fact: on `ℝ²` **every polarizator is `R = r·J`** with `|r| ≤ 1` (a `2×2` real skew matrix is
a multiple of `J = sympForm`, `skew_eq_smul_sympForm`). Hence everything is scalar:

* `|R_μ| = |r|·1` (`absPol`), with the polar decomposition `R = ((r/|r|)·J)·|R|` (`polar_decomposition`,
  `U_orthogonal`) — `U = (r/|r|)J` orthogonal, `|R| = |r|·1` symmetric positive;
* the family `μ_s = |R_μ|^s·μ = |r|^s·μ` (`muInterp_eq`), constant (`= μ`) exactly when `μ` is **pure**
  (`|r| = 1`, `muInterp_pure`), with `μ₀ = μ` (`muInterp_zero`) and the purification `μ̃ = μ₁ = |r|·μ`
  (`muInterp_one`);
* the **Hadamard three-lines interpolation** collapses to the `rpow` log-convexity
  `|r|^{(1−t)s₀+ts₁} = (|r|^{s₀})^{1−t}(|r|^{s₁})^t` (`interp_rpow`), giving the log-linear interpolation of the
  `μ_s`-weights (`muInterp_interpolation`) — the scalar shadow of the three-lines theorem (Appendix A).

* **§A — the general polarizator `r·J` and its square** (`skew_eq_smul_sympForm`, `polOf`, `polOf_skew`,
  `polOf_sq`, `polOf_pure_of_abs_one`).
* **§B — polar decomposition `R = U|R|`** (`absPol`, `absPol_sq`, `U_orthogonal`, `polar_decomposition`).
* **§C — the `μ_s` family** (`muInterp`, `muInterp_eq`, `muInterp_zero`, `muInterp_pure`, `muInterp_one`).
* **§D — the three-lines interpolation** (`interp_rpow`, `muInterp_interpolation`).

The genuinely infinite-dimensional content — the spectral functional calculus `f(|R_μ|)`, the operator
interpolation for unbounded `R`, the abstract Hadamard three-lines argument (Appendix A) — is the part that the
`2×2` model makes scalar; the operator-analytic generality is the remaining layer.

## References

* R. Verch, arXiv:funct-an/9609004, §2.1 (Prop 2.1 the `μ_s` family, Eq 2.8 polar decomposition, Eq 2.11),
  Appendix A (the complex/Hadamard three-lines interpolation).
* Repo dependencies: `AlgebraicQFT.SymplecticAdjointHadamard` (`sympForm`, `sympForm_sq`, `sympForm_antisymm`),
  `AlgebraicQFTQuasifree.PolarizatorPurification` (`muProd`, the polarizator and pure/primary characterization).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorInterpolation

open Matrix
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorPurification

/-! ## §A — the general polarizator `R = r·J` -/

/-- **[Every `2×2` skew matrix is `r·J`] `R = (R₀₁)·sympForm`** when `Rᵀ = −R` — the only real antisymmetric
`2×2` matrices are multiples of `J`, so every polarizator on the 2-dim Cauchy space is `r·J`. -/
theorem skew_eq_smul_sympForm (R : Matrix (Fin 2) (Fin 2) ℝ) (h : Rᵀ = -R) :
    R = (R 0 1) • sympForm := by
  have d00 : R 0 0 = -R 0 0 := by have := congrFun (congrFun h 0) 0; simpa using this
  have d11 : R 1 1 = -R 1 1 := by have := congrFun (congrFun h 1) 1; simpa using this
  have d10 : R 1 0 = -R 0 1 := by have := congrFun (congrFun h 0) 1; simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sympForm, Matrix.smul_apply] <;> linarith

/-- **The polarizator `R = r·J`** parametrized by `r ∈ [−1,1]` (`‖R‖ ≤ 1`). -/
def polOf (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := r • sympForm

/-- **`R` is `μ`-skew** `Rᵀ = −R`. -/
theorem polOf_skew (r : ℝ) : (polOf r)ᵀ = -(polOf r) := by
  rw [polOf, transpose_smul, sympForm_antisymm, smul_neg]

/-- **`R² = −r²·1`** — the polarizator squares to a negative scalar (from `J² = −1`). -/
theorem polOf_sq (r : ℝ) : polOf r * polOf r = -(r ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [polOf, smul_mul_smul_comm, sympForm_sq]; module

/-- **[Pure ⟺ `|r| = 1`] `R² = −1` when `|r| = 1`** — the pure polarizator is the complex structure; `μ` is
pure exactly when `‖R_μ‖ = 1` saturates. -/
theorem polOf_pure_of_abs_one (r : ℝ) (h : |r| = 1) :
    polOf r * polOf r = -1 := by
  rw [polOf_sq]
  have : r ^ 2 = 1 := by rw [← sq_abs, h, one_pow]
  rw [this]; module

/-! ## §B — the polar decomposition `R = U|R|` (Eq 2.8) -/

/-- **The modulus `|R_μ| = |r|·1`** — symmetric, positive semidefinite, with norm `|r| ≤ 1`. -/
noncomputable def absPol (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := |r| • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- **`|R|² = Rᵀ R`** — `absPol` is the modulus `√(RᵀR)` of the polarizator. -/
theorem absPol_sq (r : ℝ) : absPol r * absPol r = (polOf r)ᵀ * polOf r := by
  rw [polOf_skew, neg_mul, polOf_sq, absPol, smul_mul_smul_comm, one_mul, abs_mul_abs_self]
  module

/-- **The phase `U = (r/|r|)·J` is orthogonal** `UᵀU = 1` — the unitary part of the polar decomposition. -/
theorem U_orthogonal (r : ℝ) (hr : r ≠ 0) :
    ((r / |r|) • sympForm)ᵀ * ((r / |r|) • sympForm) = 1 := by
  rw [transpose_smul, sympForm_antisymm, smul_neg, neg_mul, smul_mul_smul_comm, sympForm_sq]
  have : r / |r| * (r / |r|) = 1 := by
    rw [div_mul_div_comm, abs_mul_abs_self, div_self (by positivity : r * r ≠ 0)]
  rw [this]; module

/-- **[Eq 2.8] The polar decomposition `R_μ = U|R_μ|`** — `R = ((r/|r|)·J)·(|r|·1)` with `U` orthogonal
(`U_orthogonal`) and `|R|` symmetric positive (`absPol`). -/
theorem polar_decomposition (r : ℝ) (hr : r ≠ 0) :
    polOf r = ((r / |r|) • sympForm) * absPol r := by
  rw [polOf, absPol, smul_mul_assoc, mul_smul_comm, mul_one, smul_smul,
    div_mul_cancel₀ r (abs_ne_zero.mpr hr)]

/-! ## §C — the `μ_s` interpolation family (Eq 2.11) -/

/-- **[Eq 2.11] The interpolating form `μ_s(φ,ψ) = μ(φ, |R_μ|^s ψ)`** — with `|R_μ|^s = |r|^s·1` (the
functional calculus of the scalar modulus). -/
noncomputable def muInterp (M : Matrix (Fin 2) (Fin 2) ℝ) (r s : ℝ) (φ ψ : Fin 2 → ℝ) : ℝ :=
  muProd M φ ((|r| ^ s • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ ψ)

/-- **`μ_s = |r|^s·μ`** — the interpolation family is a scalar rescaling of `μ` by `|R_μ|^s = |r|^s`. -/
theorem muInterp_eq (M : Matrix (Fin 2) (Fin 2) ℝ) (r s : ℝ) (φ ψ : Fin 2 → ℝ) :
    muInterp M r s φ ψ = |r| ^ s * muProd M φ ψ := by
  rw [muInterp, muProd, muProd, Matrix.smul_mulVec, one_mulVec, mulVec_smul, dotProduct_smul,
    smul_eq_mul]

/-- **[`μ₀ = μ`] `s = 0` is the original scalar product** (`|r|^0 = 1`). -/
theorem muInterp_zero (M : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) (φ ψ : Fin 2 → ℝ) :
    muInterp M r 0 φ ψ = muProd M φ ψ := by
  rw [muInterp_eq, Real.rpow_zero, one_mul]

/-- **[Pure ⟹ `μ_s = μ`] the family is constant when `|r| = 1`** — Prop 2.1(c): for a *pure* scalar product
(`|R_μ| = 1`) all the `μ_s` coincide with `μ` (`= μ̃`), the interpolation is trivial. -/
theorem muInterp_pure (M : Matrix (Fin 2) (Fin 2) ℝ) (r s : ℝ) (h : |r| = 1) (φ ψ : Fin 2 → ℝ) :
    muInterp M r s φ ψ = muProd M φ ψ := by
  rw [muInterp_eq, h, Real.one_rpow, one_mul]

/-- **[The purification `μ̃ = μ₁`] `s = 1` gives `μ̃ = |r|·μ`** (Eq 2.10) — whose polarizator is the pure phase
`(r/|r|)·J` with square `−1`, so `μ̃ ∈ pu`. -/
theorem muInterp_one (M : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) (φ ψ : Fin 2 → ℝ) :
    muInterp M r 1 φ ψ = |r| * muProd M φ ψ := by
  rw [muInterp_eq, Real.rpow_one]

/-! ## §D — the three-lines interpolation (Appendix A, scalar shadow) -/

/-- **[Hadamard three-lines, scalar form] log-convexity of `|r|^s`** —
`|r|^{(1−t)s₀+ts₁} = (|r|^{s₀})^{1−t}(|r|^{s₁})^{t}`. The interpolation constant is log-linear in `s`: this is
the conclusion of the three-lines theorem on the 1-dim (scalar) spectrum of `|R_μ|`. -/
theorem interp_rpow (r s0 s1 t : ℝ) (hr : 0 < |r|) :
    |r| ^ ((1 - t) * s0 + t * s1) = (|r| ^ s0) ^ (1 - t) * (|r| ^ s1) ^ t := by
  rw [Real.rpow_add hr, mul_comm (1 - t) s0, mul_comm t s1, Real.rpow_mul hr.le,
    Real.rpow_mul hr.le]

/-- **[Interpolation of the `μ_s`-weights] `μ_{(1−t)s₀+ts₁} = (|r|^{s₀})^{1−t}(|r|^{s₁})^{t}·μ`** — the `μ_s`
family interpolates log-linearly between `μ_{s₀}` and `μ_{s₁}`, the form-level three-lines bound. -/
theorem muInterp_interpolation (M : Matrix (Fin 2) (Fin 2) ℝ) (r s0 s1 t : ℝ) (hr : 0 < |r|)
    (φ ψ : Fin 2 → ℝ) :
    muInterp M r ((1 - t) * s0 + t * s1) φ ψ
      = (|r| ^ s0) ^ (1 - t) * (|r| ^ s1) ^ t * muProd M φ ψ := by
  rw [muInterp_eq, interp_rpow r s0 s1 t hr]

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorInterpolation

end
