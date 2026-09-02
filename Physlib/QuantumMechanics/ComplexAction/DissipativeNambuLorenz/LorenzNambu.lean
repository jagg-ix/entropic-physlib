/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeNambu

/-!
# The Lorenz system as dissipative Nambu mechanics (Axenides–Floratos 2010, §3.1)

The abstract dissipative Nambu split `ẋ = ∇H₁ × ∇H₂ + ∇D` (`DissipativeNambuLorenz.DissipativeNambu`) reproduces
the **Lorenz system** exactly (Axenides, Floratos, JHEP 04 (2010) 036, §3.1, Eqs. 3.1, 3.15–3.22):

  `ẋ = σ(y−x)`,  `ẏ = x(r−z) − y`,  `ż = xy − bz`.

The two generalized Hamiltonians and the dissipation potential are (Eqs. 3.19, 3.20, 3.16)

  `H₁ = ½[y² + (z−r)²]`,  `H₂ = σz − x²/2`,  `D = −½(σx² + y² + bz²)`,

with gradients (Eqs. 3.17, 3.15)

  `∇H₁ = (0, y, z−r)`,  `∇H₂ = (−x, 0, σ)`,  `∇D = (−σx, −y, −bz)`.

This file works at the **vector-algebra layer** of `DissipativeNambuLorenz.DissipativeNambu`: the gradients above are
given as the concrete vectors in `R³` (their identification as gradients of the stated scalar `H₁, H₂, D` is
by hand — the differential layer is not formalized). The genuine content proved here is that the Nambu
cross-product structure **reconstructs the Lorenz vector field**:

* **§A — reconstruction.** `lorenz_nambuFlow_eq`: the non-dissipative flow `∇H₁ × ∇H₂` equals the
  Lorenz non-dissipative field `(σy, x(r−z), xy)` (Eq. 3.17/3.22). `lorenz_dissipativeFlow_eq`: adding `∇D`
  gives the **full Lorenz field** `(σ(y−x), x(r−z)−y, xy−bz)` (Eqs. 3.1/3.21).
* **§B — conservation and dissipation rates.** `lorenz_conserves_H₁/H₂`: the non-dissipative orbit lies on the
  surface intersection `H₁ = const, H₂ = const`. `lorenz_H₁/H₂_dissipation_rate`: under the full flow the
  generalized Hamiltonians evolve only through `∇D` (Eq. 3.28 mechanism), `Ḣ₁ = −y² − bz(z−r)`,
  `Ḣ₂ = σ(x² − bz)`.
* **§C — the induced Poisson algebra on `Σ₂`** (Eq. 3.25). `lorenz_poisson_xy/yz/zx`:
  `{x,y}_{H₂} = ∂_z H₂ = σ`, `{y,z}_{H₂} = ∂_x H₂ = −x`, `{z,x}_{H₂} = ∂_y H₂ = 0` — the `SO(3)`-type
  structure constants read off as Nambu brackets of the coordinate gradients with `∇H₂`.

## References

* M. Axenides, E. Floratos, *Strange attractors in dissipative Nambu mechanics*, JHEP 04 (2010) 036, §3.1
  (Eqs. 3.1, 3.15–3.22, 3.25). `Physlib` (`DissipativeNambuLorenz.DissipativeNambu`).


-/

set_option autoImplicit false

open Matrix
open Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeNambu

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzNambu

variable (σ r b : ℝ) (p : Fin 3 → ℝ)

/-! ## The Lorenz gradients and vector field (Eqs. 3.15–3.20) -/

/-- **`∇H₁ = (0, y, z−r)`** — gradient of `H₁ = ½[y² + (z−r)²]` (Eq. 3.19). -/
def lorenzGradH₁ : Fin 3 → ℝ := ![0, p 1, p 2 - r]

/-- **`∇H₂ = (−x, 0, σ)`** — gradient of `H₂ = σz − x²/2` (Eq. 3.20). -/
def lorenzGradH₂ : Fin 3 → ℝ := ![-(p 0), 0, σ]

/-- **`∇D = (−σx, −y, −bz)`** — gradient of the dissipation `D = −½(σx² + y² + bz²)` (Eqs. 3.15–3.16). -/
def lorenzGradD : Fin 3 → ℝ := ![-(σ * p 0), -(p 1), -(b * p 2)]

/-- **The non-dissipative Lorenz field** `v_ND = (σy, x(r−z), xy)` (Eq. 3.17). -/
def lorenzNonDissField : Fin 3 → ℝ := ![σ * p 1, p 0 * (r - p 2), p 0 * p 1]

/-- **The full Lorenz vector field** `(σ(y−x), x(r−z)−y, xy−bz)` (Eq. 3.1). -/
def lorenzField : Fin 3 → ℝ := ![σ * (p 1 - p 0), p 0 * (r - p 2) - p 1, p 0 * p 1 - b * p 2]


/-- **[Non-dissipative reconstruction]** `∇H₁ × ∇H₂ = (σy, x(r−z), xy)` — the Nambu flow equals the Lorenz
non-dissipative field (Eqs. 3.17, 3.18, 3.22). -/
lemma lorenz_nambuFlow_eq :
    nambuFlow (lorenzGradH₁ r p) (lorenzGradH₂ σ p) = lorenzNonDissField σ r p := by
  rw [nambuFlow, cross_apply]
  funext i
  fin_cases i <;> simp [lorenzGradH₁, lorenzGradH₂, lorenzNonDissField] <;> ring

/-- **[Full Lorenz reconstruction]** `∇H₁ × ∇H₂ + ∇D = (σ(y−x), x(r−z)−y, xy−bz)` — the dissipative Nambu
flow *is* the Lorenz system (Eqs. 3.1, 3.21). -/
lemma lorenz_dissipativeFlow_eq :
    dissipativeFlow (lorenzGradH₁ r p) (lorenzGradH₂ σ p) (lorenzGradD σ b p)
      = lorenzField σ r b p := by
  rw [dissipativeFlow, lorenz_nambuFlow_eq]
  funext i
  fin_cases i <;> simp [lorenzNonDissField, lorenzGradD, lorenzField] <;> ring


/-- **[`H₁` conserved by the ND orbit]** `∇H₁ · (∇H₁ × ∇H₂) = 0` — the Lorenz non-dissipative orbit lies on
`H₁ = const` (Eq. 3.22 + 2.8), instantiating `nambuFlow_conserves_H₁`. -/
lemma lorenz_conserves_H₁ :
    lorenzGradH₁ r p ⬝ᵥ nambuFlow (lorenzGradH₁ r p) (lorenzGradH₂ σ p) = 0 :=
  nambuFlow_conserves_H₁ _ _

/-- **[`H₂` conserved by the ND orbit]** `∇H₂ · (∇H₁ × ∇H₂) = 0` — the orbit lies on the intersection
`H₁ = const, H₂ = const` (Eqs. 3.22, 3.23). -/
lemma lorenz_conserves_H₂ :
    lorenzGradH₂ σ p ⬝ᵥ nambuFlow (lorenzGradH₁ r p) (lorenzGradH₂ σ p) = 0 :=
  nambuFlow_conserves_H₂ _ _

/-- **[`Ḣ₁ = ∇D · ∇H₁ = −y² − bz(z−r)`]** under the full Lorenz flow `H₁` evolves only through the dissipation
(Eq. 3.28 mechanism): the conservative cross-product term drops. -/
lemma lorenz_H₁_dissipation_rate :
    lorenzGradH₁ r p ⬝ᵥ dissipativeFlow (lorenzGradH₁ r p) (lorenzGradH₂ σ p) (lorenzGradD σ b p)
      = -(p 1) ^ 2 - b * p 2 * (p 2 - r) := by
  rw [dissipativeFlow_H₁_rate]
  simp only [lorenzGradH₁, lorenzGradD, vec3_dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **[`Ḣ₂ = ∇D · ∇H₂ = σ(x² − bz)`]** likewise `H₂` evolves only through the dissipation (Eq. 3.28). -/
lemma lorenz_H₂_dissipation_rate :
    lorenzGradH₂ σ p ⬝ᵥ dissipativeFlow (lorenzGradH₁ r p) (lorenzGradH₂ σ p) (lorenzGradD σ b p)
      = σ * ((p 0) ^ 2 - b * p 2) := by
  rw [dissipativeFlow_H₂_rate]
  simp only [lorenzGradH₂, lorenzGradD, vec3_dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring


/-- **[`{x,y}_{H₂} = ∂_z H₂ = σ`]** the Nambu bracket of the coordinate gradients `∇x = e₀`, `∇y = e₁` with
`∇H₂` gives the induced Poisson structure constant (Eq. 3.25). -/
lemma lorenz_poisson_xy :
    nambuBracket ![1, 0, 0] ![0, 1, 0] (lorenzGradH₂ σ p) = σ := by
  simp [nambuBracket, cross_apply, lorenzGradH₂]

/-- **[`{y,z}_{H₂} = ∂_x H₂ = −x`]** (Eq. 3.25). -/
lemma lorenz_poisson_yz :
    nambuBracket ![0, 1, 0] ![0, 0, 1] (lorenzGradH₂ σ p) = -(p 0) := by
  simp [nambuBracket, cross_apply, lorenzGradH₂]

/-- **[`{z,x}_{H₂} = ∂_y H₂ = 0`]** (Eq. 3.25). -/
lemma lorenz_poisson_zx :
    nambuBracket ![0, 0, 1] ![1, 0, 0] (lorenzGradH₂ σ p) = 0 := by
  simp [nambuBracket, cross_apply, lorenzGradH₂]

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzNambu

end
