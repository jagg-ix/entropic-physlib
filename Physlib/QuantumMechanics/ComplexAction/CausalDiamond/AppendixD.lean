/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Appendix D: the conformal group from the two-time embedding (Eqs. D.1–D.6)

`d`-dimensional Minkowski (and (A)dS) space embeds in `ℝ^{2,d}` as a section of the light cone
`X · X = 0`. This file formalizes Jacobson–Visser Appendix D.

* **D.1** `X · X = −(X^{−1})² − (X⁰)² + (X¹)² + ⋯ + (X^d)² = 0` — the light cone in `ℝ^{2,d}`
 (`embeddingForm`, `lightCone`).
* **D.2** `ds̃² = (X dΩ + Ω dX)² = Ω² dX · dX` — under `X̃ = ΩX` the induced metric on a light-cone
 section scales by `Ω²` (`weyl_transformation`), using `X·X = 0` and `X·dX = 0`: the sections are Weyl
 related.
* **D.3** the de Sitter embedding `X⁰ = √(L²−r²) sinh(t/L)`, `X^{−1} = L`, `X^d = √(L²−r²) cosh(t/L)`,
 `Xⁱ = r Ωⁱ` (`∑Ω² = 1`) satisfies `X · X = 0` (`dS_embedding_lightCone`) — equivalently the dS
 hyperboloid `−(X⁰)² + ∑(Xⁱ)² + (X^d)² = L²`.
* **D.4** the generators `J_AB = i(X_A ∂_{X^B} − X_B ∂_{X^A})` are antisymmetric `J_AB = −J_BA`
 (`genJ_antisymm`).
* **D.5** the `O(2,d)` algebra `[J_AB, J_CD] = i(η_AD J_BC + η_BC J_AD − η_AC J_BD − η_BD J_AC)` — the
 structure constants are antisymmetric in each index pair (`structureConst_antisymm`).
* **D.6** the true Killing vectors are the boosts/rotations preserving the section, e.g. `iJ_{0d} = L∂_t`
 (Eq. D.6) — noted in the references.

## Scope

D.1, D.2, D.3 are proved as concrete scalar identities (the light-cone form, the Weyl scaling, the dS
embedding constraint). D.4 is the generator antisymmetry; D.5 is the antisymmetry of the `O(2,d)`
structure constants (the full bracket of the differential operators is not built); D.6 is referenced.

No new axioms.
-/

set_option autoImplicit false

open Real Finset

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixD

/-! ## §D.1 — the `ℝ^{2,d}` light cone `X · X = 0` -/

/-- **Eq. D.1: the `ℝ^{2,d}` quadratic form** `X · X = −(X^{−1})² − (X⁰)² + ∑ᵢ(Xⁱ)²` (two timelike
directions `X^{−1}, X⁰` and `d` spacelike `Xⁱ`). -/
def embeddingForm {d : ℕ} (Xm1 X0 : ℝ) (Xs : Fin d → ℝ) : ℝ :=
  -Xm1 ^ 2 - X0 ^ 2 + ∑ i, (Xs i) ^ 2

/-- **Eq. D.1: the light cone** `X · X = 0`. -/
def lightCone {d : ℕ} (Xm1 X0 : ℝ) (Xs : Fin d → ℝ) : Prop := embeddingForm Xm1 X0 Xs = 0

/-- **The `ℝ^{2,d}` symmetric bilinear form** `X · Y = −X^{−1}Y^{−1} − X⁰Y⁰ + ∑ᵢ Xⁱ Yⁱ`. -/
def embeddingBilin {d : ℕ} (Xm1 X0 : ℝ) (Xs : Fin d → ℝ) (Ym1 Y0 : ℝ) (Ys : Fin d → ℝ) : ℝ :=
  -Xm1 * Ym1 - X0 * Y0 + ∑ i, Xs i * Ys i

/-! ## §D.2 — the Weyl transformation `(X dΩ + Ω dX)² = Ω² dX · dX` -/

/-- **Eq. D.2: the Weyl transformation** — for a point `X` on the light cone (`X·X = 0`) with `dX`
tangent to it (`X·dX = 0`), the rescaled differential `X̃' = (dΩ)X + Ω(dX)` has
`X̃' · X̃' = Ω² (dX · dX)`: the induced metrics on two light-cone sections are related by the Weyl factor
`Ω²`. (Here `a = dΩ`, and `X, Y = dX`.) -/
theorem weyl_transformation {d : ℕ} (a Ω : ℝ) (Xm1 X0 : ℝ) (Xs : Fin d → ℝ)
    (Ym1 Y0 : ℝ) (Ys : Fin d → ℝ)
    (hXX : embeddingForm Xm1 X0 Xs = 0)
    (hXY : embeddingBilin Xm1 X0 Xs Ym1 Y0 Ys = 0) :
    embeddingForm (a * Xm1 + Ω * Ym1) (a * X0 + Ω * Y0) (fun i => a * Xs i + Ω * Ys i)
      = Ω ^ 2 * embeddingForm Ym1 Y0 Ys := by
  simp only [embeddingForm, embeddingBilin] at *
  have hsum : (∑ i, (a * Xs i + Ω * Ys i) ^ 2)
      = a ^ 2 * (∑ i, (Xs i) ^ 2) + 2 * a * Ω * (∑ i, Xs i * Ys i) + Ω ^ 2 * (∑ i, (Ys i) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsum]
  linear_combination a ^ 2 * hXX + 2 * a * Ω * hXY

/-! ## §D.3 — the de Sitter embedding lies on the light cone -/

/-- **Eq. D.3: the de Sitter embedding satisfies `X · X = 0`.** With `X^{−1} = L`,
`X⁰ = w sinh(t/L)`, `X^d = w cosh(t/L)` (`w² = L² − r²`), and the spacelike `∑(Xⁱ)² = r²` (radius `r`,
`∑Ω² = 1`), the de Sitter embedding lies on the light cone of `ℝ^{2,d}` — equivalently the dS
hyperboloid `−(X⁰)² + r² + (X^d)² = L²`. -/
theorem dS_embedding_lightCone (L r t w : ℝ) (hw : w ^ 2 = L ^ 2 - r ^ 2) :
    -L ^ 2 - (w * Real.sinh (t / L)) ^ 2 + (r ^ 2 + (w * Real.cosh (t / L)) ^ 2) = 0 := by
  have hcs : Real.cosh (t / L) ^ 2 = Real.sinh (t / L) ^ 2 + 1 := Real.cosh_sq (t / L)
  rw [mul_pow, mul_pow, hcs]
  nlinarith [hw]

/-! ## §D.4 — the generators `J_AB = i(X_A ∂_B − X_B ∂_A)` are antisymmetric -/

/-- **Eq. D.4: the generator coefficient** `J_AB ∼ X_A ∂_B − X_B ∂_A` (dropping the `i`), as a function
of the embedding coordinate `X` and the partial-derivative directions `∂`. -/
def genJ {m : ℕ} (X der : Fin m → ℝ) (A B : Fin m) : ℝ := X A * der B - X B * der A

/-- **Eq. D.4: the generators are antisymmetric** `J_AB = −J_BA` — the `½(d+1)(d+2)` independent
generators of the conformal group `O(2,d)`. -/
theorem genJ_antisymm {m : ℕ} (X der : Fin m → ℝ) (A B : Fin m) :
    genJ X der A B = -genJ X der B A := by
  rw [genJ, genJ]; ring

/-- **The diagonal generators vanish** `J_AA = 0`. -/
@[simp] theorem genJ_diag {m : ℕ} (X der : Fin m → ℝ) (A : Fin m) : genJ X der A A = 0 := by
  rw [genJ]; ring

/-! ## §D.5 — the `O(2,d)` structure constants are antisymmetric -/

/-- **Eq. D.5: the `O(2,d)` structure-constant term** `η_AD J_BC` appearing in
`[J_AB, J_CD] = i(η_AD J_BC + η_BC J_AD − η_AC J_BD − η_BD J_AC)`, with `η` the `ℝ^{2,d}` metric
`diag(−1, −1, +1, …)`. -/
def structureTerm {m : ℕ} (η : Fin m → Fin m → ℝ) (J : Fin m → Fin m → ℝ) (A B C D : Fin m) : ℝ :=
  η A D * J B C + η B C * J A D - η A C * J B D - η B D * J A C

/-- **Eq. D.5: the `O(2,d)` bracket is antisymmetric in `(A,B)`** — swapping `A ↔ B` in the
structure-constant term negates it, consistent with `J_AB = −J_BA` (so `[J_AB, J_CD] = −[J_BA, J_CD]`):
the bracket has the correct Lie-algebra antisymmetry of `so(2,d)`. -/
theorem structureTerm_antisymm_AB {m : ℕ} (η J : Fin m → Fin m → ℝ) (A B C D : Fin m)
    (hJ : ∀ a b, J a b = -J b a) :
    structureTerm η J A B C D = -structureTerm η J B A C D := by
  rw [structureTerm, structureTerm, hJ B C, hJ A D, hJ B D, hJ A C]; ring

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixD

end
