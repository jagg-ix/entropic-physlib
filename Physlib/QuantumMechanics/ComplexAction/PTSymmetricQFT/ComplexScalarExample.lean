/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ChargeConjugation

/-!
# Greaves–Thomas §3, Example 4: the complex scalar field and the PT/CPT table

Formalizes the remaining §3 material of *H. Greaves, T. Thomas, "The CPT Theorem"* (arXiv:1204.4674)
after Eq. 14 and Definitions 4–5: the **charge-sector decomposition** `W = W⁺ ⊕ W⁰ ⊕ W⁻`, the two
charge conjugations (`ℂ`-linear `C_#`, anti-linear `C_∗`), and the worked **Example 4** — a complex scalar
field and its four-way PT/CPT transformation table.

For a complex scalar field the target is `V = ℝ²` and the field-value covector space is
`W = Hom(ℝ², ℂ)`. Greaves–Thomas pick `λ(x,y) = x + iy` and decompose `W = W⁺ ⊕ W⁰ ⊕ W⁻` with
`W⁺ = ℂλ`, `W⁻ = ℂλ*`, `W⁰ = 0`. Here we model the relevant `2`-(complex-)dimensional charge space
directly as `Wcs = Fin 2 → ℂ` with `λ = (1,0)`, `λ* = (0,1)`. The internal charge conjugation
`#(x,y) = (x,−y)` induces on covectors the **coordinate swap** `swapLE` (`λ ↦ λ*`), and `$ = ∗`
induces the **conjugate swap** `conjSwapSL` (anti-linear, `λ ↦ λ*`).

* **§A — the complex-scalar data** (`swapLE`, `conjSwapSL`, `swapLE_lam`/`_lamStar`,
  `conjSwapSL_lam`/`_lamStar`, `swapLE_involutive`, `cHash_kform_involutive`). `C_# = swapLE` is the
  `ℂ`-linear internal charge conjugation `C_#(Φ^λ) = Φ^{λ*}`; `C_∗ = conjSwapSL` is the anti-linear one.
  Both are involutions, so `C_#` on `K^form` is the `ℤ₂` action (`chargeConjugation_involutive`).
* **§B — the charge-sector decomposition** (`swapLE_chargeConjugating`, `conjSwapSL_chargeConjugating`,
  `conjSwapSL_chargeConjugating'`). `W⁺ = ℂλ`, `W⁻ = ℂλ*`; both `C_#` and `C_∗` are **charge-conjugating**
  (they encode `W⁺` onto / into `W⁻` and back) — the formal sense of Definition 4 and of "`C_∗` is always
  charge-conjugating."
* **§C — Example 4: the PT/CPT table** (`cs_classicalPT`, `cs_classicalCPT`, `cs_quantumCPT`,
  `cs_quantumPT`). For `F = iΦ^λ = Φ^{iλ}` and `g ∈ L↓₊` with `[ρω](g)` charge-preserving (so a classical
  PT, fixing `Φ^λ`), the four actions give

  | transformation        | `F = iΦ^λ ↦` |
  |------------------------|--------------|
  | classical PT `[ρω]`    | `iΦ^λ`       |
  | quantum CPT `[ρω]_q = C_∗∘[ρω]` | `−iΦ^{λ*}` |
  | classical CPT `C_#∘[ρω]`        | `iΦ^{λ*}`  |
  | quantum PT `C_#∘[ρω]_q`         | `−iΦ^λ`    |

  The `ℂ`-linear rows use the genuine `chargeConjugation` of `PTSymmetricQFT.ChargeConjugation`; the
  anti-linear rows realize `C_∗` by its Eq.-14 action on the field symbol (the conjugate-semilinear label
  map `conjSwapSL`, which is all the single-symbol element `F` requires). The sign flips track exactly the
  `ℂ`-linearity of `C_#` vs. the anti-linearity of `C_∗`.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §3 (Example 4, the `W⁺/W⁰/W⁻` decomposition,
  `C_#` vs `C_∗`).
* Repo dependencies: `PTSymmetricQFT.ChargeConjugation` (`chargeConjugation`, `chargeConjugation_ι`,
  `chargeConjugation_involutive`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ComplexScalarExample

open Complex
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ChargeConjugation

/-! ## §A — the complex-scalar data -/

/-- The charge space `W = Hom(ℝ², ℂ) = ℂλ ⊕ ℂλ*` of a complex scalar field, modelled as `Fin 2 → ℂ`. -/
abbrev Wcs := Fin 2 → ℂ

/-- The particle covector `λ(x,y) = x + iy`, here the first coordinate `(1,0)`. -/
def lam : Wcs := ![1, 0]

/-- The anti-particle covector `λ*(x,y) = x − iy`, here the second coordinate `(0,1)`. -/
def lamStar : Wcs := ![0, 1]

/-- **`C_#` on covectors**: the `ℂ`-linear coordinate swap induced by the internal charge conjugation
`#(x,y) = (x,−y)` — `λ ↦ λ*`. This is the symbol map of the standard QFT charge conjugation. -/
def swapLE : Wcs ≃ₗ[ℂ] Wcs where
  toFun w := ![w 1, w 0]
  invFun w := ![w 1, w 0]
  map_add' a b := by funext i; fin_cases i <;> simp
  map_smul' c a := by funext i; fin_cases i <;> simp
  left_inv w := by funext i; fin_cases i <;> simp
  right_inv w := by funext i; fin_cases i <;> simp

/-- **`C_∗` on covectors**: the anti-linear (conjugate-semilinear) conjugate swap induced by `$ = ∗`
(`λ ↦ λ∗`, `λ(v) ↦ λ(v)∗`) — again `λ ↦ λ*`, but conjugating scalars. -/
def conjSwapSL : Wcs →ₛₗ[starRingEnd ℂ] Wcs where
  toFun w := ![star (w 1), star (w 0)]
  map_add' a b := by funext i; fin_cases i <;> simp
  map_smul' c a := by funext i; fin_cases i <;> simp

@[simp] theorem swapLE_lam : swapLE lam = lamStar := by
  apply funext; intro i; fin_cases i <;>
    simp only [swapLE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, lam, lamStar,
      Matrix.cons_val_zero, Matrix.cons_val_one]

@[simp] theorem swapLE_lamStar : swapLE lamStar = lam := by
  apply funext; intro i; fin_cases i <;>
    simp only [swapLE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, lam, lamStar,
      Matrix.cons_val_zero, Matrix.cons_val_one]

@[simp] theorem conjSwapSL_lam : conjSwapSL lam = lamStar := by
  apply funext; intro i; fin_cases i <;>
    simp only [conjSwapSL, LinearMap.coe_mk, AddHom.coe_mk, lam, lamStar,
      Matrix.cons_val_zero, Matrix.cons_val_one, star_zero, star_one]

@[simp] theorem conjSwapSL_lamStar : conjSwapSL lamStar = lam := by
  apply funext; intro i; fin_cases i <;>
    simp only [conjSwapSL, LinearMap.coe_mk, AddHom.coe_mk, lam, lamStar,
      Matrix.cons_val_zero, Matrix.cons_val_one, star_zero, star_one]

/-- **`#` is an involution** `# ∘ # = id` — the order-2 internal charge conjugation. -/
theorem swapLE_involutive (w : Wcs) : swapLE (swapLE w) = w := by
  funext i; fin_cases i <;> simp [swapLE]

/-- **[`C_#` is the `ℤ₂` action] `C_#` is an involution of `K^form`** — the complex-scalar internal charge
conjugation generates the `ℤ₂ = {±1}` action of `PTSymmetricQFT.ChargeConjugation` (`chargeConjugation` of an
involution). -/
theorem cHash_kform_involutive (F : KForm Wcs) :
    chargeConjugation swapLE (chargeConjugation swapLE F) = F :=
  chargeConjugation_involutive swapLE swapLE_involutive F

/-! ## §B — the charge-sector decomposition `W⁺ = ℂλ`, `W⁻ = ℂλ*` -/

/-- **[Def. 4] `C_#` is charge-conjugating**: it includes the particle sector `W⁺ = ℂλ` *onto* the
anti-particle sector `W⁻ = ℂλ*`. -/
theorem swapLE_chargeConjugating :
    Submodule.map (swapLE : Wcs →ₗ[ℂ] Wcs) (Submodule.span ℂ {lam}) = Submodule.span ℂ {lamStar} := by
  rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, swapLE_lam]

/-- **[`C_∗` always charge-conjugating] `C_∗` includes the particle generator `λ` into `W⁻ = ℂλ*`.** -/
theorem conjSwapSL_chargeConjugating :
    conjSwapSL lam ∈ Submodule.span ℂ ({lamStar} : Set Wcs) := by
  rw [conjSwapSL_lam]; exact Submodule.mem_span_singleton_self _

/-- **[`C_∗` always charge-conjugating] `C_∗` includes the anti-particle generator `λ*` into `W⁺ = ℂλ`.**
Together with the previous lemma, `C_∗` exchanges the particle and anti-particle sectors. -/
theorem conjSwapSL_chargeConjugating' :
    conjSwapSL lamStar ∈ Submodule.span ℂ ({lam} : Set Wcs) := by
  rw [conjSwapSL_lamStar]; exact Submodule.mem_span_singleton_self _

/-! ## §C — Example 4: the PT/CPT transformation table for `F = iΦ^λ` -/

/-- **[Example 4 — classical PT] `[ρω](g)(iΦ^λ) = iΦ^λ`.** A charge-preserving classical PT transformation
`T` (here fixing the field symbol `Φ^λ`) sends `iΦ^λ ↦ iΦ^λ`, by `ℂ`-linearity. -/
theorem cs_classicalPT (T : KForm Wcs ≃ₐ[ℂ] KForm Wcs)
    (hT : T (TensorAlgebra.ι ℂ lam) = TensorAlgebra.ι ℂ lam) :
    T (I • TensorAlgebra.ι ℂ lam) = I • TensorAlgebra.ι ℂ lam := by
  rw [map_smul, hT]

/-- **[Example 4 — classical CPT] `C_# ∘ [ρω](g)(iΦ^λ) = iΦ^{λ*}`.** Applying the `ℂ`-linear charge
conjugation `C_#` to `iΦ^λ` keeps the `i` and swaps `λ ↦ λ*`. -/
theorem cs_classicalCPT :
    chargeConjugation swapLE (TensorAlgebra.ι ℂ (I • lam)) = I • TensorAlgebra.ι ℂ lamStar := by
  rw [chargeConjugation_ι, swapLE.map_smul, swapLE_lam, (TensorAlgebra.ι ℂ).map_smul]

/-- **[Example 4 — quantum CPT] `[ρω]_q(g)(iΦ^λ) = −iΦ^{λ*}`.** For time-reversing `g`,
`[ρω]_q(g) = C_∗ ∘ [ρω](g)`; the anti-linear `C_∗` conjugates the `i` to `−i` while swapping `λ ↦ λ*`. -/
theorem cs_quantumCPT :
    TensorAlgebra.ι ℂ (conjSwapSL (I • lam)) = -(I • TensorAlgebra.ι ℂ lamStar) := by
  rw [map_smulₛₗ, conjSwapSL_lam, (TensorAlgebra.ι ℂ).map_smul]
  simp

/-- **[Example 4 — quantum PT] `C_# ∘ [ρω]_q(g)(iΦ^λ) = −iΦ^λ`.** Following the anti-linear `C_∗`
(giving `−iΦ^{λ*}`) by the `ℂ`-linear `C_#` swaps `λ* ↦ λ`, returning `−iΦ^λ`. -/
theorem cs_quantumPT :
    chargeConjugation swapLE (TensorAlgebra.ι ℂ (conjSwapSL (I • lam)))
      = -(I • TensorAlgebra.ι ℂ lam) := by
  rw [map_smulₛₗ, conjSwapSL_lam, Complex.conj_I, chargeConjugation_ι, swapLE.map_smul,
    swapLE_lamStar, (TensorAlgebra.ι ℂ).map_smul]
  simp

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ComplexScalarExample

end
