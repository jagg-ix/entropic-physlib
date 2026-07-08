/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.WeylHeisenberg

/-!
# The polynomial Lie algebra of Nambu quantization (Axenides–Floratos §5, Eqs. 5.5–5.10)

Quantizing the induced Poisson structure `{xⁱ,xʲ}_{H₂} = ε^{ijk}∂ₖH₂` (Axenides, Floratos, JHEP 04 (2010) 036,
Eq. 5.4) promotes the coordinates to operators satisfying (Eq. 5.5)

  `[Xⁱ, Xʲ] = iℏ ε^{ijk} Pᵏ(X)`,

where `Pᵏ` are **polynomials** in `X` (linear only when `H₂` is quadratic, Eq. 5.12). A consistent
quantization must satisfy four requirements (Eqs. 5.6–5.10); this file formalizes the two that are
operator identities:

* **(α) the Jacobi identity** (Eq. 5.6). `jacobi_identity`: in any ring, `[x,[y,z]] + [y,[z,x]] + [z,[x,y]] = 0`.
  `polynomial_consistency`: with `Pᵏ` defined by `[Xⁱ,Xʲ] = κ Pᵏ`, the closure condition
  `κ([X⁰,P⁰] + [X¹,P¹] + [X²,P²]) = 0` (Eq. 5.6) is exactly the Jacobi identity (so for `κ = iℏ ≠ 0` the
  bracketed sum vanishes).
* **(γ) the Casimir** (Eq. 5.8). `casimir_commutes`: for the quadratic Euler-top `H₂ = Σ Xᵢ²` and the
  angular-momentum algebra `[Xᵢ,Xⱼ] = κ ε_{ijk} Xₖ`, every `Xⁱ` commutes with `H₂`, `[Xⁱ, H₂] = 0` — `H₂` is a
  Casimir (the conserved second Hamiltonian survives quantization).

The remaining requirements are not operator identities and are not formalized: **(β)** the classical limit
`limₕ→₀ Pᵏ = ∂ᵏH₂` (Eq. 5.7, an `ℏ→0` statement on the deformation family) and **(δ)** the unique-ordering /
diamond / PBW property (Eqs. 5.9–5.10, a statement about a monomial basis of the enveloping algebra).

## References

* M. Axenides, E. Floratos, JHEP 04 (2010) 036, §5, Eqs. 5.4–5.10. `Physlib`
  (`DissipativeNambuLorenz.WeylHeisenberg`).

No additional assumptions.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.WeylHeisenberg

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.PolynomialLieAlgebra

variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A]

/-! ## (α) The Jacobi identity and the closure of the polynomial Lie algebra (Eq. 5.6) -/

/-- **[Jacobi identity]** `[x,[y,z]] + [y,[z,x]] + [z,[x,y]] = 0` in any ring (with `[a,b] = ab − ba`) — the
fundamental consistency of the commutator bracket. -/
theorem jacobi_identity (x y z : A) :
    (x * (y * z - z * y) - (y * z - z * y) * x)
      + (y * (z * x - x * z) - (z * x - x * z) * y)
      + (z * (x * y - y * x) - (x * y - y * x) * z) = 0 := by
  noncomm_ring

/-- **[Polynomial-algebra closure]** (Eq. 5.6) with the polynomials `Pᵏ` defined by `[Xⁱ,Xʲ] = κ Pᵏ`, the
closure condition `κ([X⁰,P⁰] + [X¹,P¹] + [X²,P²]) = 0` holds — it is precisely the Jacobi identity. For
`κ = iℏ ≠ 0` this is the requirement `[X⁰,P⁰] + [X¹,P¹] + [X²,P²] = 0`. -/
theorem polynomial_consistency (X P : Fin 3 → A) (κ : R)
    (hP0 : X 1 * X 2 - X 2 * X 1 = κ • P 0)
    (hP1 : X 2 * X 0 - X 0 * X 2 = κ • P 1)
    (hP2 : X 0 * X 1 - X 1 * X 0 = κ • P 2) :
    κ • ((X 0 * P 0 - P 0 * X 0) + (X 1 * P 1 - P 1 * X 1) + (X 2 * P 2 - P 2 * X 2)) = 0 := by
  have key : κ • ((X 0 * P 0 - P 0 * X 0) + (X 1 * P 1 - P 1 * X 1) + (X 2 * P 2 - P 2 * X 2))
      = (X 0 * (κ • P 0) - (κ • P 0) * X 0)
        + (X 1 * (κ • P 1) - (κ • P 1) * X 1)
        + (X 2 * (κ • P 2) - (κ • P 2) * X 2) := by
    simp only [smul_add, smul_sub, mul_smul_comm, smul_mul_assoc]
  rw [key, ← hP0, ← hP1, ← hP2]
  noncomm_ring

/-! ## (γ) The Casimir of the quadratic Euler top (Eq. 5.8) -/

/-- **[`H₂` is a Casimir]** for the quadratic Euler-top `H₂ = Σ Xᵢ²` and the angular-momentum algebra
`[Xᵢ,Xⱼ] = κ ε_{ijk} Xₖ`, every generator commutes with `H₂`: `[X₀, H₂] = 0` (Eq. 5.8). The conserved second
Hamiltonian survives quantization. -/
theorem casimir_commutes (X : Fin 3 → A) (κ : R)
    (h01 : X 0 * X 1 - X 1 * X 0 = κ • X 2) (h20 : X 2 * X 0 - X 0 * X 2 = κ • X 1) :
    X 0 * eulerH1 X (fun _ => (1 : R)) - eulerH1 X (fun _ => (1 : R)) * X 0 = 0 := by
  rw [heisenberg_eom0 X (fun _ => (1 : R)) κ h01 h20]
  simp

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.PolynomialLieAlgebra

end
