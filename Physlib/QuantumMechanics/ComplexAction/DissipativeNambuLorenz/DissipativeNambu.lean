/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Data.Real.Basic
public import Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence

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


-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeNambu


/-- **The Nambu 3-bracket** `{f,g,h} = ε^{ijk} ∂ᵢf ∂ⱼg ∂ₖh = ∇f · (∇g × ∇h)`, written on the gradient
vectors `gf = ∇f`, `gg = ∇g`, `gh = ∇h ∈ R³` (Eq. 2.2). -/
def nambuBracket (gf gg gh : Fin 3 → ℝ) : ℝ := gf ⬝ᵥ (gg ⨯₃ gh)

/-- **[Nambu bracket = determinant]** `{f,g,h} = det[∇f, ∇g, ∇h]` — the `ε^{ijk}` of Eq. 2.2 is the
Levi-Civita determinant; total antisymmetry follows. -/
lemma nambuBracket_eq_det (gf gg gh : Fin 3 → ℝ) :
    nambuBracket gf gg gh = Matrix.det ![gf, gg, gh] := by
  rw [nambuBracket, triple_product_eq_det]

/-- **[Cyclic symmetry]** `{f,g,h} = {g,h,f}` — the triple product is cyclically invariant. -/
lemma nambuBracket_cyclic (gf gg gh : Fin 3 → ℝ) :
    nambuBracket gf gg gh = nambuBracket gg gh gf := by
  rw [nambuBracket, nambuBracket, triple_product_permutation]

/-- **[Vanishing on a repeated first argument]** `{f,f,h} = 0`. -/
@[simp] lemma nambuBracket_self_left (gf gh : Fin 3 → ℝ) :
    nambuBracket gf gf gh = 0 := by
  rw [nambuBracket, dot_self_cross]

/-- **[Vanishing on a repeated last argument]** `{f,g,g} = 0`. -/
@[simp] lemma nambuBracket_self_right (gf gg : Fin 3 → ℝ) :
    nambuBracket gf gg gg = 0 := by
  rw [nambuBracket, cross_self, dotProduct_zero]


/-- **The (non-dissipative) Nambu flow** `v_ND = ∇H₁ × ∇H₂` (Eqs. 2.11, 2.24). -/
def nambuFlow (gH₁ gH₂ : Fin 3 → ℝ) : Fin 3 → ℝ := gH₁ ⨯₃ gH₂

/-- **[`H₁` is a constant of motion]** `Ḣ₁ = ∇H₁ · v = {H₁,H₁,H₂} = 0` — the flow is tangent to the surface
`H₁ = const` (Eq. 2.8). -/
@[simp] lemma nambuFlow_conserves_H₁ (gH₁ gH₂ : Fin 3 → ℝ) :
    gH₁ ⬝ᵥ nambuFlow gH₁ gH₂ = 0 := dot_self_cross gH₁ gH₂

/-- **[`H₂` is a constant of motion]** `Ḣ₂ = ∇H₂ · v = {H₂,H₁,H₂} = 0` — the orbit lies on the intersection
`H₁ = const, H₂ = const` (Eqs. 2.8–2.9). -/
@[simp] lemma nambuFlow_conserves_H₂ (gH₁ gH₂ : Fin 3 → ℝ) :
    gH₂ ⬝ᵥ nambuFlow gH₁ gH₂ = 0 := dot_cross_self gH₁ gH₂


/-- **The dissipative flow** `ẋ = ∇H₁ × ∇H₂ + ∇D` (Eq. 2.23): the rotational Nambu flow plus the irrotational
dissipative gradient `gD = ∇D`. -/
def dissipativeFlow (gH₁ gH₂ gD : Fin 3 → ℝ) : Fin 3 → ℝ := nambuFlow gH₁ gH₂ + gD

/-- **[`Ḣ₁ = ∇D · ∇H₁`]** under dissipation the first generalized Hamiltonian evolves *only* through the
dissipative gradient (Eq. 2.28): the conservative cross-product term drops by `nambuFlow_conserves_H₁`. -/
lemma dissipativeFlow_H₁_rate (gH₁ gH₂ gD : Fin 3 → ℝ) :
    gH₁ ⬝ᵥ dissipativeFlow gH₁ gH₂ gD = gH₁ ⬝ᵥ gD := by
  rw [dissipativeFlow, dotProduct_add, nambuFlow_conserves_H₁, zero_add]

/-- **[`Ḣ₂ = ∇D · ∇H₂`]** likewise the second generalized Hamiltonian evolves only through dissipation
(Eq. 2.28). -/
lemma dissipativeFlow_H₂_rate (gH₁ gH₂ gD : Fin 3 → ℝ) :
    gH₂ ⬝ᵥ dissipativeFlow gH₁ gH₂ gD = gH₂ ⬝ᵥ gD := by
  rw [dissipativeFlow, dotProduct_add, nambuFlow_conserves_H₂, zero_add]

/-- **[Reversible limit]** with no dissipation (`∇D = 0`) both generalized Hamiltonians are conserved —
the conservative Nambu flow, the orbit confined to the surface intersection. -/
lemma dissipativeFlow_reversible (gH₁ gH₂ : Fin 3 → ℝ) :
    gH₁ ⬝ᵥ dissipativeFlow gH₁ gH₂ 0 = 0 ∧ gH₂ ⬝ᵥ dissipativeFlow gH₁ gH₂ 0 = 0 := by
  rw [dissipativeFlow, add_zero]
  exact ⟨nambuFlow_conserves_H₁ gH₁ gH₂, nambuFlow_conserves_H₂ gH₁ gH₂⟩

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeNambu

/-! ## Entropic Nambu contour weight -/

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.NambuEntropicContour

open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence

/-- **The local entropy-production rate** `|∇D|² = ∇D · ∇D` of the dissipative Nambu flow:
the positive term by which the dissipative gradient injects imaginary action. -/
def nambuEntropyProductionRate (gD : Fin 3 → ℝ) : ℝ := gD ⬝ᵥ gD

/-- **Entropy production is nonnegative**: `|∇D|² ≥ 0`. -/
lemma nambuEntropyProductionRate_nonneg (gD : Fin 3 → ℝ) :
    0 ≤ nambuEntropyProductionRate gD := by
  simpa [nambuEntropyProductionRate] using dotProduct_star_self_nonneg gD

/-- **Reversible iff no dissipation**: `|∇D|² = 0 ↔ ∇D = 0`. -/
lemma nambuEntropyProductionRate_eq_zero_iff (gD : Fin 3 → ℝ) :
    nambuEntropyProductionRate gD = 0 ↔ gD = 0 :=
  dotProduct_self_eq_zero

/-- **Dissipation gives positive entropy production**: `∇D ≠ 0 ⟹ |∇D|² > 0`. -/
lemma nambuEntropyProductionRate_pos {gD : Fin 3 → ℝ} (h : gD ≠ 0) :
    0 < nambuEntropyProductionRate gD := by
  refine lt_of_le_of_ne (nambuEntropyProductionRate_nonneg gD) ?_
  intro heq
  exact h ((nambuEntropyProductionRate_eq_zero_iff gD).mp heq.symm)

/-- **The accumulated imaginary action** `S_I = |∇D|²·t` along the trajectory over time `t`. -/
def nambuImaginaryAction (gD : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  nambuEntropyProductionRate gD * t

/-- **Contour weight along the dissipative Nambu trajectory**:
`‖nnPathWeight S_R S_I ℏ‖ = e^{−|∇D|² t/ℏ}`. -/
lemma nambuPathWeight_norm (S_R : ℝ) (gD : Fin 3 → ℝ) (ℏ t : ℝ) :
    ‖nnPathWeight S_R (nambuImaginaryAction gD t) ℏ‖
      = Real.exp (-(nambuEntropyProductionRate gD * t) / ℏ) := by
  rw [norm_nnPathWeight, nambuImaginaryAction]
  congr 1
  ring

/-- **Conservative flow gives an undeformed contour**: at `∇D = 0`, the contour weight is `1`. -/
lemma conservative_contour_undeformed (S_R ℏ t : ℝ) :
    ‖nnPathWeight S_R (nambuImaginaryAction 0 t) ℏ‖ = 1 := by
  rw [nambuPathWeight_norm]
  simp [nambuEntropyProductionRate]

/-- **Dissipation gives contour decay**: at `∇D ≠ 0` and positive time/Planck scale, the contour
weight is strictly less than `1`. -/
lemma dissipative_contour_decays (S_R : ℝ) {gD : Fin 3 → ℝ} {t ℏ : ℝ}
    (hgD : gD ≠ 0) (ht : 0 < t) (hℏ : 0 < ℏ) :
    ‖nnPathWeight S_R (nambuImaginaryAction gD t) ℏ‖ < 1 := by
  rw [nambuPathWeight_norm]
  have hpos : 0 < nambuEntropyProductionRate gD * t / ℏ :=
    div_pos (mul_pos (nambuEntropyProductionRate_pos hgD) ht) hℏ
  rw [neg_div]
  exact Real.exp_lt_one_iff.mpr (by linarith)

/-- The dissipative Nambu entropy-production rate is a valid nonnegative Lyapunov decay rate. -/
lemma nambuEntropyProduction_is_decayRate_nonneg (gD : Fin 3 -> ℝ) :
    0 ≤ nambuEntropyProductionRate gD :=
  nambuEntropyProductionRate_nonneg gD

/-- Nonzero dissipative Nambu gradient gives a strictly positive decay rate. -/
lemma nambuEntropyProduction_is_decayRate_pos {gD : Fin 3 -> ℝ} (hgD : gD ≠ 0) :
    0 < nambuEntropyProductionRate gD :=
  nambuEntropyProductionRate_pos hgD

/-- The Nambu contour theorem is a strict Lyapunov/attractor decay statement for the
Nagao-Nielsen complex-action weight. -/
lemma nambu_dissipation_gives_strict_weight_decay
    (S_R : ℝ) {gD : Fin 3 -> ℝ} {t hbar : ℝ}
    (hgD : gD ≠ 0) (ht : 0 < t) (hhbar : 0 < hbar) :
    ‖nnPathWeight S_R (nambuImaginaryAction gD t) hbar‖ < 1 :=
  dissipative_contour_decays S_R hgD ht hhbar

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.NambuEntropicContour

end
