/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime

/-!
# The polarizator `R_μ`, purification and the pure/primary characterization (Verch 1996, §2.1)

Continues the Hadamard-representation arc (`AlgebraicQFT.SymplecticAdjointHadamard`, `OperatorAlgebra.WeylCCRSpacetime`,
`AlgebraicQFT.GNSVonNeumannHadamard`) with the analytic heart of *R. Verch, arXiv:funct-an/9609004*, §2.1: the
**polarizator** `R_μ` of a `σ`-dominating scalar product `μ`, and the characterization of *pure* and *primary*
quasifree states by properties of `R_μ`. This closes the loop the `AlgebraicQFT.GNSVonNeumannHadamard` docstring promised —
"primary ⟺ `R_μ` injective, pure ⟺ `R_μ² = −1`" — concretely on the 2-dim Cauchy-data space.

For a scalar product `μ` dominating the symplectic form `σ` (Eq 2.1, `|σ(φ,ψ)|² ≤ 4μ(φ,φ)μ(ψ,ψ)`), the
**polarizator** `R_μ` is the `μ`-bounded operator with `σ(x,y) = 2μ(x, R_μ y)` (Eq 2.2); it is `μ`-skew
`R_μ* = −R_μ` (Eq 2.3) with `‖R_μ‖ ≤ 1`. Verch's dichotomy:

* `μ` is **primary** `⟺ R_μ` injective (`σ_μ` non-degenerate) `⟺ ω_μ` primary (trivial centre);
* `μ` is **pure** `⟺ R_μ` is a *complex structure* `R_μ² = −1`, `R_μ⁻¹ = R_μ*` (Eq 2.4) `⟺ ω_μ` pure
  (irreducible); and `pu ⊂ pr`.

On the 2-dim Cauchy-data space `σ = sympForm = J`, a scalar product is a symmetric positive matrix `M` with
`μ(φ,ψ) = φ·Mψ`, and the polarizator equation `σ(φ,ψ) = 2μ(φ,R_μψ)` reads `2 M R_μ = J`. The *canonical pure*
choice `μ = ½‖·‖²` (`M = ½·1`) gives `R_μ = J`, whose `J² = −1` (`AlgebraicQFT.SymplecticAdjointHadamard.sympForm_sq`) is
exactly the complex structure — the quantum-mechanical `i` of the one-particle space.

* **§A — the dominating bound** (`sympForm_cauchySchwarz`). Eq 2.1 for `μ = ½‖·‖²`: `|σ(φ,ψ)|² ≤ ‖φ‖²‖ψ‖²`
  (the Lagrange/Cauchy-Schwarz identity), so `μ` dominates `σ` and the polarizator exists.
* **§B — the polarizator** (`muProd`, `IsPolarizator`, `polarizator_pairing`, `polarizator_skew`,
  `isPolarizator_pure`). The relation `σ = 2μ(·,R·)` (Eq 2.2), its `μ`-skewness `(MR)ᵀ = −(MR)` (Eq 2.3), and
  the canonical pure polarizator `R = J`.
* **§C — pure ⟺ complex structure, `pu ⊂ pr`** (`pure_polarizator_complexStructure`,
  `sympForm_mulVec_injective`). The pure polarizator is a complex structure `R² = −1` with inverse `−R`
  (`R⁻¹ = R*`, Eq 2.4), and is injective — pure states are primary.
* **§D — the purification** (`sympForm_orthogonal`). For the pure case `|R_μ| = 1` (`R_μ` is `μ`-orthogonal,
  `JᵀJ = 1`), so the purification `μ̃(φ,ψ) = μ(φ,|R_μ|ψ)` (Eq 2.10) equals `μ`: a pure scalar product is its
  own purification (`μ = μ̃ = μ₁`, Prop 2.1 for `μ ∈ pu`).

The functional-analytic generality (the family `μ_s = μ(·,|R_μ|^s·)`, Prop 2.1(b–e), the polar decomposition
`R_μ = U_μ|R_μ|`, the `μ₀–μ₁` continuity of symplectically adjoint maps, Chapter 3's local
definiteness/primarity/Haag-duality/type III₁) is the operator-analytic layer; the 2-dim algebraic kernel is
formalized here.

## References

* R. Verch, arXiv:funct-an/9609004, §2.1 (the polarizator `R_μ` Eq 2.2–2.4, purification Eq 2.10–2.11,
  Prop 2.1; pure/primary quasifree states I/II).
* P. Chmielowski, *States of scalar field on spacetimes with two isometries...* (the purification `μ̃`).
* Repo dependencies: `AlgebraicQFT.SymplecticAdjointHadamard` (`sympForm`, `sympForm_sq`, `sympForm_antisymm`),
  `OperatorAlgebra.WeylCCRSpacetime` (`symplecticPairing`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorPurification

open Matrix
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime

/-! ## §A — the dominating bound (Eq 2.1) -/

/-- **[Eq 2.1, `μ = ½‖·‖²` dominates `σ`] `|σ(φ,ψ)|² ≤ ‖φ‖²‖ψ‖²`.** The Lagrange/Cauchy-Schwarz identity on
`ℝ²`: `(σ(φ,ψ))² + (φ·ψ)² = ‖φ‖²‖ψ‖²`. With `μ(φ,φ) = ½‖φ‖²` this is `|σ(φ,ψ)|² ≤ 4μ(φ,φ)μ(ψ,ψ)`, so the
energy-type scalar product dominates the symplectic form and the polarizator `R_μ` exists. -/
theorem sympForm_cauchySchwarz (φ ψ : Fin 2 → ℝ) :
    (symplecticPairing φ ψ) ^ 2 ≤ (φ ⬝ᵥ φ) * (ψ ⬝ᵥ ψ) := by
  simp only [symplecticPairing, sympForm, mulVec, dotProduct, Fin.sum_univ_two,
    cons_val_zero, cons_val_one, of_apply]
  nlinarith [sq_nonneg (φ 0 * ψ 0 + φ 1 * ψ 1)]

/-! ## §B — the polarizator `R_μ` (Eq 2.2–2.3) -/

/-- **The dominating scalar product** `μ_M(φ,ψ) = φ·Mψ` given by a symmetric positive matrix `M`. -/
def muProd (M : Matrix (Fin 2) (Fin 2) ℝ) (φ ψ : Fin 2 → ℝ) : ℝ := φ ⬝ᵥ (M *ᵥ ψ)

/-- **[Eq 2.2] The polarizator relation** `σ = 2μ_M(·, R·)`, i.e. the matrix equation `2 M R = J` (with `M`
symmetric). `R` is the `μ`-bounded operator `R_μ` realizing the symplectic form inside the scalar product. -/
def IsPolarizator (M R : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Mᵀ = M ∧ (2 : ℝ) • (M * R) = sympForm

/-- **[Eq 2.2 in bilinear form] `σ(φ,ψ) = 2μ_M(φ, R_μ ψ)`** — the defining property of the polarizator. -/
theorem polarizator_pairing (M R : Matrix (Fin 2) (Fin 2) ℝ) (h : IsPolarizator M R)
    (φ ψ : Fin 2 → ℝ) : symplecticPairing φ ψ = 2 * muProd M φ (R *ᵥ ψ) := by
  rw [symplecticPairing, muProd, mulVec_mulVec, ← h.2, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]

/-- **[Eq 2.3, `R_μ* = −R_μ`] The polarizator is `μ`-skew** — `MR` is antisymmetric (`= ½J`), the matrix form
of `R_μ`'s `μ`-skew-adjointness, inherited from the antisymmetry of `σ`. -/
theorem polarizator_skew (M R : Matrix (Fin 2) (Fin 2) ℝ) (h : IsPolarizator M R) :
    (M * R)ᵀ = -(M * R) := by
  have h2 := h.2
  have ht : ((2 : ℝ) • (M * R))ᵀ = sympFormᵀ := by rw [h2]
  rw [transpose_smul, sympForm_antisymm, ← h2, ← smul_neg] at ht
  exact smul_right_injective (Matrix (Fin 2) (Fin 2) ℝ) (by norm_num : (2 : ℝ) ≠ 0) ht

/-- **[Canonical pure scalar product] `R_μ = J` for `μ = ½‖·‖²`** (`M = ½·1`) — the energy/purification scalar
product on the one-particle space has the symplectic form itself as its polarizator. -/
theorem isPolarizator_pure :
    IsPolarizator ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) sympForm := by
  refine ⟨?_, ?_⟩
  · rw [transpose_smul, transpose_one]
  · rw [smul_mul_assoc, one_mul, smul_smul]; norm_num

/-! ## §C — pure ⟺ complex structure, and `pu ⊂ pr` -/

/-- **[Eq 2.4, `μ ∈ pu ⟺ R_μ² = −1`] The pure polarizator is a complex structure with `R_μ⁻¹ = R_μ*`.** The
canonical pure scalar product has polarizator `J` satisfying `J² = −1` and `J·(−J) = 1` — a unitary
anti-involution (`R_μ⁻¹ = −R_μ = R_μ*`), the defining property of a *pure* quasifree state (Verch Eq 2.4); it
is the complex structure (the `i`) of the one-particle Hilbert space. -/
theorem pure_polarizator_complexStructure :
    IsPolarizator ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) sympForm
      ∧ sympForm * sympForm = -1 ∧ sympForm * (-sympForm) = 1 :=
  ⟨isPolarizator_pure, sympForm_sq, by rw [mul_neg, sympForm_sq, neg_neg]⟩

/-- **[`pu ⊂ pr`] A complex-structure polarizator is injective ⟹ pure states are primary.** Since `R_μ² = −1`
gives `R_μ` the left inverse `−R_μ`, the map `φ ↦ R_μ φ` is injective — `σ_μ` is non-degenerate, so the pure
quasifree state is primary (Verch: `pu ⊂ pr`). -/
theorem sympForm_mulVec_injective :
    Function.Injective (fun x : Fin 2 → ℝ => sympForm *ᵥ x) := by
  intro x y hxy
  have h : (-sympForm) *ᵥ (sympForm *ᵥ x) = (-sympForm) *ᵥ (sympForm *ᵥ y) := by
    simp only at hxy ⊢; rw [hxy]
  rwa [mulVec_mulVec, mulVec_mulVec, neg_mul, sympForm_sq, neg_neg, one_mulVec, one_mulVec] at h

/-! ## §D — the purification (Eq 2.10) -/

/-- **[`|R_μ| = 1` in the pure case] `JᵀJ = 1`** — the pure polarizator is `μ`-orthogonal, so `|R_μ| = 1` and
the purification `μ̃(φ,ψ) = μ(φ,|R_μ|ψ)` (Eq 2.10) equals `μ`: a *pure* scalar product is its own purification
(`μ = μ̃ = μ₁`, Prop 2.1 for `μ ∈ pu`). -/
theorem sympForm_orthogonal : sympFormᵀ * sympForm = 1 := by
  rw [sympForm_antisymm, neg_mul, sympForm_sq, neg_neg]

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorPurification

end
