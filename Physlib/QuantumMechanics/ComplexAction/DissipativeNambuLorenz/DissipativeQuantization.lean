/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.WeylHeisenberg

/-!
# Dissipative quantization: the open-system Heisenberg equation (Axenides–Floratos §5, Eqs. 5.16–5.19)

For a *quadratic* dissipation function `D = ½ Xⁱ Sᵢⱼ Xʲ` (`S` symmetric — the case of the Lorenz system,
Axenides, Floratos, JHEP 04 (2010) 036, Eq. 5.16) the dissipative Nambu flow is quantized by appending a
**linear dissipative drift** to the Heisenberg equation (Eq. 5.17):

  `iℏ Ẋⁱ = [Xⁱ, H₁] + iℏ Sᵢₖ Xᵏ`.

With the Weyl-ordered quadratic energy `H₁ = ½ Xⁱ Mᵢⱼ Xʲ` (Eq. 5.18) the commutator is the Weyl-symmetrized
Euler term (`DissipativeNambuLorenz.WeylHeisenberg.heisenberg_eom`), so dividing by `iℏ` gives the operator evolution
(Eq. 5.19)

  `Ẋⁱ = Aⁱⱼₖ ½(XʲXᵏ + XᵏXʲ) + Sⁱᵏ Xᵏ`,

a Weyl-symmetrized conservative part plus the dissipative drift `S·X` — the operator image of the classical
`ẋ = ∇H₁×∇H₂ + ∇D`.

This file works over any base ring (`κ = iℏ`, the `½` of `H₁` absorbed into the `aᵢ` as in
`DissipativeNambuLorenz.WeylHeisenberg`):

* `dissipativeDrift`: the quantized `∇D`, the drift `(S·X)ⁱ = Σⱼ Sᵢⱼ Xʲ` (Eq. 5.16).
* `quantumEvolution`: the right-hand side of Eq. 5.17, `iℏẊⁱ = [Xⁱ, H₁] + iℏ(S·X)ⁱ`.
* `dissipative_quantum_eom0/1/2`: `iℏẊⁱ = iℏ·(Aⁱⱼₖ·symmetrized + (S·X)ⁱ)` (Eq. 5.19) — the `iℏ` factors
  out, leaving the Weyl-symmetrized conservative term plus the dissipative drift.

## References

* M. Axenides, E. Floratos, JHEP 04 (2010) 036, §5, Eqs. 5.16–5.19. `Physlib`
  (`DissipativeNambuLorenz.WeylHeisenberg`).

No additional assumptions.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.WeylHeisenberg

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeQuantization

variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A]

/-- **The dissipative drift** `(S·X)ⁱ = Σⱼ Sᵢⱼ Xʲ` — the quantized gradient `∇D` of the quadratic dissipation
`D = ½ Xⁱ Sᵢⱼ Xʲ` (Eqs. 5.16–5.17). -/
def dissipativeDrift (S : Fin 3 → Fin 3 → R) (X : Fin 3 → A) (i : Fin 3) : A :=
  S i 0 • X 0 + S i 1 • X 1 + S i 2 • X 2

/-- **The dissipative quantum evolution** `iℏẊⁱ = [Xⁱ, H₁] + iℏ(S·X)ⁱ` (Eq. 5.17): the Heisenberg commutator
plus the linear dissipative drift. -/
def quantumEvolution (X : Fin 3 → A) (a : Fin 3 → R) (κ : R) (S : Fin 3 → Fin 3 → R) (i : Fin 3) : A :=
  (X i * eulerH1 X a - eulerH1 X a * X i) + κ • dissipativeDrift S X i

/-- **[Dissipative operator EOM for `X₀`]** `iℏẊ₀ = iℏ((a₁−a₂)(X₁X₂+X₂X₁) + (S·X)₀)` (Eq. 5.19): the `iℏ`
factors out of the Weyl-symmetrized conservative term and the dissipative drift, recovering
`Ẋ₀ = (a₁−a₂)(X₁X₂+X₂X₁) + (S·X)₀`. -/
theorem dissipative_quantum_eom0 (X : Fin 3 → A) (a : Fin 3 → R) (κ : R) (S : Fin 3 → Fin 3 → R)
    (h01 : X 0 * X 1 - X 1 * X 0 = κ • X 2) (h20 : X 2 * X 0 - X 0 * X 2 = κ • X 1) :
    quantumEvolution X a κ S 0
      = κ • ((a 1 - a 2) • (X 1 * X 2 + X 2 * X 1) + dissipativeDrift S X 0) := by
  simp only [quantumEvolution]
  rw [heisenberg_eom0 X a κ h01 h20, mul_smul, ← smul_add]

/-- **[Dissipative operator EOM for `X₁`]** `iℏẊ₁ = iℏ((a₂−a₀)(X₂X₀+X₀X₂) + (S·X)₁)` (Eq. 5.19, cyclic). -/
theorem dissipative_quantum_eom1 (X : Fin 3 → A) (a : Fin 3 → R) (κ : R) (S : Fin 3 → Fin 3 → R)
    (h12 : X 1 * X 2 - X 2 * X 1 = κ • X 0) (h01 : X 0 * X 1 - X 1 * X 0 = κ • X 2) :
    quantumEvolution X a κ S 1
      = κ • ((a 2 - a 0) • (X 2 * X 0 + X 0 * X 2) + dissipativeDrift S X 1) := by
  simp only [quantumEvolution]
  rw [heisenberg_eom1 X a κ h12 h01, mul_smul, ← smul_add]

/-- **[Dissipative operator EOM for `X₂`]** `iℏẊ₂ = iℏ((a₀−a₁)(X₀X₁+X₁X₀) + (S·X)₂)` (Eq. 5.19, cyclic). -/
theorem dissipative_quantum_eom2 (X : Fin 3 → A) (a : Fin 3 → R) (κ : R) (S : Fin 3 → Fin 3 → R)
    (h20 : X 2 * X 0 - X 0 * X 2 = κ • X 1) (h12 : X 1 * X 2 - X 2 * X 1 = κ • X 0) :
    quantumEvolution X a κ S 2
      = κ • ((a 0 - a 1) • (X 0 * X 1 + X 1 * X 0) + dissipativeDrift S X 2) := by
  simp only [quantumEvolution]
  rw [heisenberg_eom2 X a κ h20 h12, mul_smul, ← smul_add]

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.DissipativeQuantization

end
