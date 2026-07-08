/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Data.Real.Basic

/-!
# Dissipative Nambu mechanics on `R³`: the algebraic core (Axenides–Floratos 2010)

Nambu–Hamiltonian mechanics on `R³` with two generalized Hamiltonians `H₁, H₂` (Axenides, Floratos,
*Strange attractors in dissipative Nambu mechanics*, JHEP 04 (2010) 036, §2). The Nambu 3-bracket
`{f,g,h} = ε^{ijk} ∂ᵢf ∂ⱼg ∂ₖh` (Eq. 2.2) is the **scalar triple product of the gradients**
`∇f · (∇g × ∇h)`, the flow is `ẋ = ∇H₁ × ∇H₂` (Eqs. 2.11, 2.24), and `H₁, H₂` are constants of motion — the
orbit lies on the intersection of the two surfaces `H₁ = const`, `H₂ = const` (Eqs. 2.8–2.9). Dissipation
adds the irrotational gradient `∇D`, `ẋ = ∇H₁ × ∇H₂ + ∇D` (Eq. 2.23), which deforms the surfaces in time:
`Ḣⱼ = ∇D · ∇Hⱼ` (Eq. 2.28) — and produces the strange attractors (Lorenz, Rössler).

This file formalizes the pointwise vector-algebra heart (gradients as given vectors in `R³`), with Mathlib's
`crossProduct`. The differential layer (`∂ᵢvⁱ = ∇²D`, the specific Lorenz/Rössler potentials) is not
included.

* **§A — the Nambu bracket = triple product** (Eq. 2.2). `nambuBracket`; `nambuBracket_eq_det` (`= det`,
  the `ε^{ijk}`), `nambuBracket_cyclic`, and the antisymmetry/`repeated-argument` vanishing
  (`nambuBracket_self_left/right`).
* **§B — the Nambu flow conserves `H₁, H₂`** (Eqs. 2.8, 2.24). `nambuFlow = ∇H₁ × ∇H₂`;
  `nambuFlow_conserves_H₁/H₂`: `∇Hⱼ · (∇H₁×∇H₂) = {Hⱼ,H₁,H₂} = 0`.
* **§C — dissipative deformation** (Eqs. 2.23, 2.28). `dissipativeFlow = ∇H₁×∇H₂ + ∇D`;
  `dissipativeFlow_H₁/H₂_rate`: `Ḣⱼ = ∇D · ∇Hⱼ` — the generalized Hamiltonians evolve *only* through the
  dissipative gradient; `dissipativeFlow_reversible`: at `∇D = 0` both are conserved.

The conservative (rotational) Nambu flow ↔ the dissipative (irrotational `∇D`) part is the same split as the
real vs imaginary action of the complex-action arc.

## References

* M. Axenides, E. Floratos, *Strange attractors in dissipative Nambu mechanics: classical and quantum
  aspects*, JHEP 04 (2010) 036, §2 (Eqs. 2.1–2.2, 2.8–2.9, 2.11, 2.23–2.24, 2.28). Y. Nambu (1973).

No new axioms.
-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeNambu

/-! ## §A — the Nambu 3-bracket as the scalar triple product (Eq. 2.2) -/

/-- **The Nambu 3-bracket** `{f,g,h} = ε^{ijk} ∂ᵢf ∂ⱼg ∂ₖh = ∇f · (∇g × ∇h)`, written on the gradient
vectors `gf = ∇f`, `gg = ∇g`, `gh = ∇h ∈ R³` (Eq. 2.2). -/
def nambuBracket (gf gg gh : Fin 3 → ℝ) : ℝ := gf ⬝ᵥ (gg ⨯₃ gh)

/-- **[Nambu bracket = determinant]** `{f,g,h} = det[∇f, ∇g, ∇h]` — the `ε^{ijk}` of Eq. 2.2 is the
Levi-Civita determinant; total antisymmetry follows. -/
theorem nambuBracket_eq_det (gf gg gh : Fin 3 → ℝ) :
    nambuBracket gf gg gh = Matrix.det ![gf, gg, gh] := by
  rw [nambuBracket, triple_product_eq_det]

/-- **[Cyclic symmetry]** `{f,g,h} = {g,h,f}` — the triple product is cyclically invariant. -/
theorem nambuBracket_cyclic (gf gg gh : Fin 3 → ℝ) :
    nambuBracket gf gg gh = nambuBracket gg gh gf := by
  rw [nambuBracket, nambuBracket, triple_product_permutation]

/-- **[Vanishing on a repeated first argument]** `{f,f,h} = 0`. -/
@[simp] theorem nambuBracket_self_left (gf gh : Fin 3 → ℝ) :
    nambuBracket gf gf gh = 0 := by
  rw [nambuBracket, dot_self_cross]

/-- **[Vanishing on a repeated last argument]** `{f,g,g} = 0`. -/
@[simp] theorem nambuBracket_self_right (gf gg : Fin 3 → ℝ) :
    nambuBracket gf gg gg = 0 := by
  rw [nambuBracket, cross_self, dotProduct_zero]

/-! ## §B — the non-dissipative Nambu flow conserves `H₁, H₂` (Eqs. 2.8, 2.24) -/

/-- **The (non-dissipative) Nambu flow** `v_ND = ∇H₁ × ∇H₂` (Eqs. 2.11, 2.24). -/
def nambuFlow (gH₁ gH₂ : Fin 3 → ℝ) : Fin 3 → ℝ := gH₁ ⨯₃ gH₂

/-- **[`H₁` is a constant of motion]** `Ḣ₁ = ∇H₁ · v = {H₁,H₁,H₂} = 0` — the flow is tangent to the surface
`H₁ = const` (Eq. 2.8). -/
@[simp] theorem nambuFlow_conserves_H₁ (gH₁ gH₂ : Fin 3 → ℝ) :
    gH₁ ⬝ᵥ nambuFlow gH₁ gH₂ = 0 := dot_self_cross gH₁ gH₂

/-- **[`H₂` is a constant of motion]** `Ḣ₂ = ∇H₂ · v = {H₂,H₁,H₂} = 0` — the orbit lies on the intersection
`H₁ = const, H₂ = const` (Eqs. 2.8–2.9). -/
@[simp] theorem nambuFlow_conserves_H₂ (gH₁ gH₂ : Fin 3 → ℝ) :
    gH₂ ⬝ᵥ nambuFlow gH₁ gH₂ = 0 := dot_cross_self gH₁ gH₂

/-! ## §C — dissipative deformation `ẋ = ∇H₁ × ∇H₂ + ∇D` (Eqs. 2.23, 2.28) -/

/-- **The dissipative flow** `ẋ = ∇H₁ × ∇H₂ + ∇D` (Eq. 2.23): the rotational Nambu flow plus the irrotational
dissipative gradient `gD = ∇D`. -/
def dissipativeFlow (gH₁ gH₂ gD : Fin 3 → ℝ) : Fin 3 → ℝ := nambuFlow gH₁ gH₂ + gD

/-- **[`Ḣ₁ = ∇D · ∇H₁`]** under dissipation the first generalized Hamiltonian evolves *only* through the
dissipative gradient (Eq. 2.28): the conservative cross-product term drops by `nambuFlow_conserves_H₁`. -/
theorem dissipativeFlow_H₁_rate (gH₁ gH₂ gD : Fin 3 → ℝ) :
    gH₁ ⬝ᵥ dissipativeFlow gH₁ gH₂ gD = gH₁ ⬝ᵥ gD := by
  rw [dissipativeFlow, dotProduct_add, nambuFlow_conserves_H₁, zero_add]

/-- **[`Ḣ₂ = ∇D · ∇H₂`]** likewise the second generalized Hamiltonian evolves only through dissipation
(Eq. 2.28). -/
theorem dissipativeFlow_H₂_rate (gH₁ gH₂ gD : Fin 3 → ℝ) :
    gH₂ ⬝ᵥ dissipativeFlow gH₁ gH₂ gD = gH₂ ⬝ᵥ gD := by
  rw [dissipativeFlow, dotProduct_add, nambuFlow_conserves_H₂, zero_add]

/-- **[Reversible limit]** with no dissipation (`∇D = 0`) both generalized Hamiltonians are conserved —
the conservative Nambu flow, the orbit confined to the surface intersection. -/
theorem dissipativeFlow_reversible (gH₁ gH₂ : Fin 3 → ℝ) :
    gH₁ ⬝ᵥ dissipativeFlow gH₁ gH₂ 0 = 0 ∧ gH₂ ⬝ᵥ dissipativeFlow gH₁ gH₂ 0 = 0 := by
  rw [dissipativeFlow, add_zero]
  exact ⟨nambuFlow_conserves_H₁ gH₁ gH₂, nambuFlow_conserves_H₂ gH₁ gH₂⟩

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeNambu

end
