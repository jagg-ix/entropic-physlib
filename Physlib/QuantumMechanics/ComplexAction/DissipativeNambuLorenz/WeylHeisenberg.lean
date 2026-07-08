/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# Weyl-ordered Heisenberg evolution of the quantized Euler top (Axenides–Floratos §5)

The quantization of dissipative Nambu mechanics (Axenides, Floratos, JHEP 04 (2010) 036, §5) promotes the
phase-space coordinates `xⁱ` to operators `Xⁱ`. For a *quadratic* second Hamiltonian `H₂ = ½XⁱNᵢⱼXʲ` the
induced Poisson structure (Eq. 5.4) becomes a **linear Lie algebra** (Eq. 5.12); for the Euler top
(`H₂ = ½Σlᵢ²`) this is the angular-momentum algebra

  `[Xᵢ, Xⱼ] = κ ε_{ijk} Xₖ`,   `κ = iℏ`   (Eqs. 5.12, 5.14).

The Heisenberg equation `iℏẊᵢ = [Xᵢ, H₁]` for the Weyl-ordered energy `H₁ = ½Σ aᵢ Xᵢ²` (`aᵢ = 1/Iᵢ`) then
gives the operator Euler equations (Eq. 5.15), in which the *classical* product `lⱼlₖ` is replaced by the
**Weyl-symmetrized** product `½(XⱼXₖ + XₖXⱼ)`:

  `iℏ Ẋ₁ = [X₁, H₁] = κ(a₂ − a₃)·½(X₂X₃ + X₃X₂)`,  and cyclically.

This file proves that algebraically over any base ring (`κ` a scalar; the global `½` is absorbed into the
`aᵢ`, so `H₁ = Σ aᵢ Xᵢ²`):

* `comm_sq_leibniz`: the derivation/Leibniz rule `[x, y²] = y[x,y] + [x,y]y` — the source of the
  symmetrization (a `[x,y]` flanked symmetrically by `y`).
* `heisenberg_eom0/1/2`: `[Xᵢ, H₁] = κ(a_{i+1} − a_{i+2})·(X_{i+1}X_{i+2} + X_{i+2}X_{i+1})` — the three
  Weyl-ordered Heisenberg–Euler equations, the symmetric product `XⱼXₖ + XₖXⱼ` being the Weyl ordering.

`κ = iℏ` recovers the physical `iℏẊᵢ`; dividing by `κ` gives the operator velocities `Ẋᵢ`.

## References

* M. Axenides, E. Floratos, JHEP 04 (2010) 036, §5, Eqs. 5.4, 5.12, 5.14–5.15. Weyl ordering;
  angular-momentum Lie algebra.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.WeylHeisenberg

variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A]

/-- **The Weyl-ordered quadratic Hamiltonian** `H₁ = Σ aᵢ Xᵢ²` (Eq. 5.18, the conventional `½` absorbed into
`aᵢ`). -/
def eulerH1 (X : Fin 3 → A) (a : Fin 3 → R) : A :=
  a 0 • (X 0 * X 0) + a 1 • (X 1 * X 1) + a 2 • (X 2 * X 2)

/-- **[Leibniz/derivation rule]** `[x, y²] = y[x,y] + [x,y]y` — the commutator with a square is the
commutator flanked *symmetrically* by `y`; this is the algebraic origin of the Weyl-symmetrized product. -/
theorem comm_sq_leibniz (x y : A) :
    x * (y * y) - (y * y) * x = y * (x * y - y * x) + (x * y - y * x) * y := by
  noncomm_ring

/-- **[Heisenberg–Euler equation for `X₀`]** `[X₀, H₁] = κ(a₁ − a₂)(X₁X₂ + X₂X₁)` (Eq. 5.15): the operator
Euler equation, with the classical product replaced by the Weyl-symmetrized `X₁X₂ + X₂X₁`. -/
theorem heisenberg_eom0 (X : Fin 3 → A) (a : Fin 3 → R) (κ : R)
    (h01 : X 0 * X 1 - X 1 * X 0 = κ • X 2)
    (h20 : X 2 * X 0 - X 0 * X 2 = κ • X 1) :
    X 0 * eulerH1 X a - eulerH1 X a * X 0
      = (κ * (a 1 - a 2)) • (X 1 * X 2 + X 2 * X 1) := by
  have key1 : X 0 * (X 1 * X 1) - (X 1 * X 1) * X 0 = κ • (X 1 * X 2 + X 2 * X 1) := by
    rw [comm_sq_leibniz, h01, mul_smul_comm, smul_mul_assoc, ← smul_add]
  have key2 : X 0 * (X 2 * X 2) - (X 2 * X 2) * X 0 = (-κ) • (X 1 * X 2 + X 2 * X 1) := by
    have hx : X 0 * X 2 - X 2 * X 0 = (-κ) • X 1 := by
      rw [show X 0 * X 2 - X 2 * X 0 = -(X 2 * X 0 - X 0 * X 2) from by abel, h20, neg_smul]
    rw [comm_sq_leibniz, hx, mul_smul_comm, smul_mul_assoc, ← smul_add, add_comm (X 2 * X 1)]
  have hsq0 : X 0 * (X 0 * X 0) - (X 0 * X 0) * X 0 = 0 := by noncomm_ring
  have expand : X 0 * eulerH1 X a - eulerH1 X a * X 0
      = a 0 • (X 0 * (X 0 * X 0) - (X 0 * X 0) * X 0)
      + a 1 • (X 0 * (X 1 * X 1) - (X 1 * X 1) * X 0)
      + a 2 • (X 0 * (X 2 * X 2) - (X 2 * X 2) * X 0) := by
    simp only [eulerH1, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub]; abel
  rw [expand, hsq0, key1, key2, smul_zero, zero_add, smul_smul, smul_smul, ← add_smul]
  congr 1; ring

/-- **[Heisenberg–Euler equation for `X₁`]** `[X₁, H₁] = κ(a₂ − a₀)(X₂X₀ + X₀X₂)` (Eq. 5.15, cyclic). -/
theorem heisenberg_eom1 (X : Fin 3 → A) (a : Fin 3 → R) (κ : R)
    (h12 : X 1 * X 2 - X 2 * X 1 = κ • X 0)
    (h01 : X 0 * X 1 - X 1 * X 0 = κ • X 2) :
    X 1 * eulerH1 X a - eulerH1 X a * X 1
      = (κ * (a 2 - a 0)) • (X 2 * X 0 + X 0 * X 2) := by
  have key2 : X 1 * (X 2 * X 2) - (X 2 * X 2) * X 1 = κ • (X 2 * X 0 + X 0 * X 2) := by
    rw [comm_sq_leibniz, h12, mul_smul_comm, smul_mul_assoc, ← smul_add]
  have key0 : X 1 * (X 0 * X 0) - (X 0 * X 0) * X 1 = (-κ) • (X 2 * X 0 + X 0 * X 2) := by
    have hx : X 1 * X 0 - X 0 * X 1 = (-κ) • X 2 := by
      rw [show X 1 * X 0 - X 0 * X 1 = -(X 0 * X 1 - X 1 * X 0) from by abel, h01, neg_smul]
    rw [comm_sq_leibniz, hx, mul_smul_comm, smul_mul_assoc, ← smul_add, add_comm (X 0 * X 2)]
  have hsq1 : X 1 * (X 1 * X 1) - (X 1 * X 1) * X 1 = 0 := by noncomm_ring
  have expand : X 1 * eulerH1 X a - eulerH1 X a * X 1
      = a 0 • (X 1 * (X 0 * X 0) - (X 0 * X 0) * X 1)
      + a 1 • (X 1 * (X 1 * X 1) - (X 1 * X 1) * X 1)
      + a 2 • (X 1 * (X 2 * X 2) - (X 2 * X 2) * X 1) := by
    simp only [eulerH1, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub]; abel
  rw [expand, key0, hsq1, key2, smul_zero, add_zero, smul_smul, smul_smul, ← add_smul]
  congr 1; ring

/-- **[Heisenberg–Euler equation for `X₂`]** `[X₂, H₁] = κ(a₀ − a₁)(X₀X₁ + X₁X₀)` (Eq. 5.15, cyclic). -/
theorem heisenberg_eom2 (X : Fin 3 → A) (a : Fin 3 → R) (κ : R)
    (h20 : X 2 * X 0 - X 0 * X 2 = κ • X 1)
    (h12 : X 1 * X 2 - X 2 * X 1 = κ • X 0) :
    X 2 * eulerH1 X a - eulerH1 X a * X 2
      = (κ * (a 0 - a 1)) • (X 0 * X 1 + X 1 * X 0) := by
  have key0 : X 2 * (X 0 * X 0) - (X 0 * X 0) * X 2 = κ • (X 0 * X 1 + X 1 * X 0) := by
    rw [comm_sq_leibniz, h20, mul_smul_comm, smul_mul_assoc, ← smul_add]
  have key1 : X 2 * (X 1 * X 1) - (X 1 * X 1) * X 2 = (-κ) • (X 0 * X 1 + X 1 * X 0) := by
    have hx : X 2 * X 1 - X 1 * X 2 = (-κ) • X 0 := by
      rw [show X 2 * X 1 - X 1 * X 2 = -(X 1 * X 2 - X 2 * X 1) from by abel, h12, neg_smul]
    rw [comm_sq_leibniz, hx, mul_smul_comm, smul_mul_assoc, ← smul_add, add_comm (X 1 * X 0)]
  have hsq2 : X 2 * (X 2 * X 2) - (X 2 * X 2) * X 2 = 0 := by noncomm_ring
  have expand : X 2 * eulerH1 X a - eulerH1 X a * X 2
      = a 0 • (X 2 * (X 0 * X 0) - (X 0 * X 0) * X 2)
      + a 1 • (X 2 * (X 1 * X 1) - (X 1 * X 1) * X 2)
      + a 2 • (X 2 * (X 2 * X 2) - (X 2 * X 2) * X 2) := by
    simp only [eulerH1, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub]; abel
  rw [expand, key0, key1, hsq2, smul_zero, add_zero, smul_smul, smul_smul, ← add_smul]
  congr 1; ring

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.WeylHeisenberg

end
