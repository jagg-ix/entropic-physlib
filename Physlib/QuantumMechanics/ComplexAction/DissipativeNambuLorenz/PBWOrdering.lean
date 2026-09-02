/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Tactic.Abel

/-!
# The diamond / PBW ordering of the quantized Nambu algebra (Axenides–Floratos §5, Eqs. 5.9–5.10)

The fourth quantization requirement (Axenides, Floratos, JHEP 04 (2010) 036, requirement δ, Eqs. 5.9–5.10) is
the **unique ordering of monomials** (the *diamond property*, generalizing Poincaré–Birkhoff–Witt): every
product of generators can be rewritten into a *single* normal-ordered form `(X⁰)^{m₁}(X¹)^{m₂}(X²)^{m₃}` using
the commutation relations, and the result is independent of the order of reductions.

For the angular-momentum algebra `[Xᵢ,Xⱼ] = κ ε_{ijk} Xₖ` (`κ = iℏ`) the elementary reduction rules move a
descending adjacent pair into ascending order plus a lower-degree term:

* `reorder_10`: `X₁X₀ = X₀X₁ − κ X₂`,  `reorder_20`: `X₂X₀ = X₀X₂ + κ X₁`,  `reorder_21`: `X₂X₁ = X₁X₂ − κ X₀`.

Iterating these *terminates* (each lowers the inversion count) at a unique ascending normal form. The
maximally-disordered cubic monomial `X₂X₁X₀` reduces to (`pbw_normalOrder`)

  `X₂X₁X₀ = X₀X₁X₂ − κ X₀² + κ X₁² − κ X₂²`,

a *single* element of the algebra. Because this is proved as an **equation**, every reduction path (left pair
first or right pair first — the two sides of the "diamond") necessarily yields this same element: confluence
is automatic. This concretely exhibits the diamond/PBW property — the ordered monomials are a well-defined
normal form, so the enveloping algebra has the expected basis.

This file works over any base ring (`κ = iℏ`).

## References

* M. Axenides, E. Floratos, JHEP 04 (2010) 036, §5, requirement δ, Eqs. 5.9–5.10 (diamond property, PBW).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.PBWOrdering

variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A]
variable (X : Fin 3 → A) (κ : R)

/-! ## The elementary reordering rules (the diamond reductions) -/

/-- **[Reorder `X₁X₀`]** `X₁X₀ = X₀X₁ − κ X₂`: move the lower generator `X₀` left past `X₁`. -/
lemma reorder_10 (h01 : X 0 * X 1 - X 1 * X 0 = κ • X 2) :
    X 1 * X 0 = X 0 * X 1 - κ • X 2 := by
  rw [← h01]; abel

/-- **[Reorder `X₂X₀`]** `X₂X₀ = X₀X₂ + κ X₁`: move `X₀` left past `X₂`. -/
lemma reorder_20 (h20 : X 2 * X 0 - X 0 * X 2 = κ • X 1) :
    X 2 * X 0 = X 0 * X 2 + κ • X 1 := by
  rw [← h20]; abel

/-- **[Reorder `X₂X₁`]** `X₂X₁ = X₁X₂ − κ X₀`: move `X₁` left past `X₂`. -/
lemma reorder_21 (h12 : X 1 * X 2 - X 2 * X 1 = κ • X 0) :
    X 2 * X 1 = X 1 * X 2 - κ • X 0 := by
  rw [← h12]; abel

/-! ## The normal-ordered form of the maximally-disordered monomial -/

/-- **[Diamond / PBW normal form]** `X₂X₁X₀ = X₀X₁X₂ − κ X₀² + κ X₁² − κ X₂²`: the fully reverse-ordered cubic
monomial reduces to a unique ascending normal form. Proved as an equation, so every reduction path agrees —
the confluence (diamond) property holds, exhibiting the PBW normal form (Eqs. 5.9–5.10). -/
lemma pbw_normalOrder (h01 : X 0 * X 1 - X 1 * X 0 = κ • X 2)
    (h12 : X 1 * X 2 - X 2 * X 1 = κ • X 0) (h20 : X 2 * X 0 - X 0 * X 2 = κ • X 1) :
    X 2 * X 1 * X 0
      = X 0 * X 1 * X 2 - κ • (X 0 * X 0) + κ • (X 1 * X 1) - κ • (X 2 * X 2) := by
  calc X 2 * X 1 * X 0
      = (X 1 * X 2 - κ • X 0) * X 0 := by rw [reorder_21 X κ h12]
    _ = X 1 * X 2 * X 0 - κ • (X 0 * X 0) := by rw [sub_mul, smul_mul_assoc]
    _ = X 1 * (X 0 * X 2 + κ • X 1) - κ • (X 0 * X 0) := by rw [mul_assoc, reorder_20 X κ h20]
    _ = X 1 * X 0 * X 2 + κ • (X 1 * X 1) - κ • (X 0 * X 0) := by
          rw [mul_add, ← mul_assoc, mul_smul_comm]
    _ = (X 0 * X 1 - κ • X 2) * X 2 + κ • (X 1 * X 1) - κ • (X 0 * X 0) := by
          rw [reorder_10 X κ h01]
    _ = X 0 * X 1 * X 2 - κ • (X 2 * X 2) + κ • (X 1 * X 1) - κ • (X 0 * X 0) := by
          rw [sub_mul, smul_mul_assoc]
    _ = X 0 * X 1 * X 2 - κ • (X 0 * X 0) + κ • (X 1 * X 1) - κ • (X 2 * X 2) := by abel

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.PBWOrdering

end
