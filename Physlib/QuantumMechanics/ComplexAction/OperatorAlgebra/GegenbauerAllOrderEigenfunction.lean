/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence
meta import Zil

/-!
# The all-order general-`α` Gegenbauer eigenfunction theorem

Turns the explicit `n ≤ 2` Gegenbauer ODE proofs (`GegenbauerODESolution`) into the all-`n`
eigenfunction theorem for general `α`, via the coupled derivative-of-recurrence induction on the
polynomial family `gegenbauerP` (`GegenbauerGeneralRecurrence`).

The two Gegenbauer derivative relations, proven together by induction from the three-term
recurrence (`gegenbauer_derivativeRelations`):

* **D1**  `(1−X²) C_{n+1}' = (n+2α) C_n − (n+1) X C_{n+1}`,
* **D2**  `X C_{n+1}' − C_n' = (n+1) C_{n+1}`,

give, by differentiating D1 and substituting D2, the Gegenbauer ODE as a polynomial identity
(`gegenbauerP_ode`), and hence the analytic eigenfunction statement for every `n`
(`gegenbauerP_solves`): `IsGegenbauerSolution α n (eval C_n) (eval C_n')` with eigenvalue
`λ_n = n(n+2α)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Polynomial

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution
open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.CutkoskyBetheSalpeterSolution

/-- **The differentiated three-term recurrence**:
`(n+2) C_{n+2}' = 2(α+n+1)(C_{n+1} + X C_{n+1}') − (2α+n) C_n'`. -/
@[zil_level physical_theorem]
theorem gegenbauerP_deriv_recurrence (α : ℝ) (n : ℕ) :
    C ((↑n : ℝ) + 2) * derivative (gegenbauerP α (n + 2))
      = C (2 * (α + (↑n + 1))) * gegenbauerP α (n + 1)
        + C (2 * (α + (↑n + 1))) * X * derivative (gegenbauerP α (n + 1))
        - C (2 * α + ↑n) * derivative (gegenbauerP α n) := by
  have h := congrArg derivative (gegenbauerP_recurrence α n)
  simp only [derivative_mul, derivative_sub, derivative_C, derivative_X, zero_mul, add_zero,
    zero_add, mul_one] at h
  linear_combination h

/-- **The two Gegenbauer derivative relations, proven together by induction** on the polynomial
family:
* **D1** `(1−X²) C_{n+1}' = (2α+n) C_n − (n+1) X C_{n+1}`,
* **D2** `X C_{n+1}' − C_n' = (n+1) C_{n+1}`. -/
@[zil_level bridge_theorem]
theorem gegenbauer_derivativeRelations (α : ℝ) : ∀ n : ℕ,
    (1 - X ^ 2) * derivative (gegenbauerP α (n + 1))
        = C (2 * α + ↑n) * gegenbauerP α n - C ((↑n : ℝ) + 1) * X * gegenbauerP α (n + 1)
      ∧ X * derivative (gegenbauerP α (n + 1)) - derivative (gegenbauerP α n)
        = C ((↑n : ℝ) + 1) * gegenbauerP α (n + 1) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩ <;>
    · simp only [gegenbauerP_zero, gegenbauerP_one, Nat.cast_zero, zero_add, add_zero,
        derivative_mul, derivative_C, derivative_X, derivative_one, zero_mul, mul_one, mul_zero,
        C_1, sub_zero]
      ring
  | succ n ih =>
    obtain ⟨ihA, ihB⟩ := ih
    have hc : (C ((↑n : ℝ) + 2) : ℝ[X]) ≠ 0 := by
      simp only [ne_eq, C_eq_zero]; positivity
    have hDR := gegenbauerP_deriv_recurrence α n
    have hR := gegenbauerP_recurrence α n
    simp only [map_add, map_mul, map_ofNat, C_1] at hDR hR ihA ihB
    refine ⟨?_, ?_⟩
    · apply mul_left_cancel₀ hc
      push_cast
      simp only [map_add, map_mul, map_ofNat, C_1]
      linear_combination (1 - X ^ 2) * hDR + (C (↑n : ℝ) + 2) * X * hR
        + (2 * C α + C (↑n : ℝ)) * (1 - X ^ 2) * ihB + (C (↑n : ℝ) + 2) * X * ihA
    · apply mul_left_cancel₀ hc
      push_cast
      simp only [map_add, map_mul, map_ofNat, C_1]
      linear_combination X * hDR - (C (↑n : ℝ) + 2) * hR
        + (2 * C α + C (↑n : ℝ)) * X * ihB - (C (↑n : ℝ) + 2) * ihA

/-- **The Gegenbauer ODE as a polynomial identity, for every `n`** — from differentiating D1 and
substituting D2: `(1−X²) C_{n+1}'' − (2α+1) X C_{n+1}' + λ_{n+1} C_{n+1} = 0`, `λ_{n+1} =
(n+1)(n+1+2α)`. -/
@[zil_level physical_theorem]
theorem gegenbauerP_ode (α : ℝ) (n : ℕ) :
    (1 - X ^ 2) * derivative (derivative (gegenbauerP α (n + 1)))
        - C (2 * α + 1) * X * derivative (gegenbauerP α (n + 1))
        + C (gegenbauerEigenvalue α (n + 1)) * gegenbauerP α (n + 1) = 0 := by
  obtain ⟨hD1, hD2⟩ := gegenbauer_derivativeRelations α n
  have hD1' := congrArg derivative hD1
  simp only [derivative_mul, derivative_sub, derivative_C, derivative_X, derivative_pow,
    derivative_one, pow_one, mul_one, zero_mul, sub_zero, zero_sub, zero_add] at hD1'
  simp only [gegenbauerEigenvalue, map_add, map_mul, map_ofNat, C_1, Nat.cast_ofNat,
    Nat.cast_add, Nat.cast_one] at hD1' hD2 ⊢
  linear_combination hD1' - (2 * C α + C (↑n : ℝ)) * hD2

/-- **[The all-`n` general-`α` Gegenbauer eigenfunction]** `C_{n+1}^{(α)}` solves the Gegenbauer ODE
for every `n`, with eigenvalue `λ_{n+1} = (n+1)(n+1+2α)` — the induction promoting the explicit
`n ≤ 2` proofs to all orders. -/
@[zil_level bridge_theorem]
theorem gegenbauerP_solves (α : ℝ) (n : ℕ) :
    IsGegenbauerSolution α (n + 1) (fun x => (gegenbauerP α (n + 1)).eval x)
      (fun x => (derivative (gegenbauerP α (n + 1))).eval x) := by
  intro x
  refine ⟨(gegenbauerP α (n + 1)).hasDerivAt x,
    (derivative (derivative (gegenbauerP α (n + 1)))).eval x,
    (derivative (gegenbauerP α (n + 1))).hasDerivAt x, ?_⟩
  have key := congr_arg (eval x) (gegenbauerP_ode α n)
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_one, eval_C, eval_zero] at key
  linear_combination key

/-- **[The all-`n` Gegenbauer eigenfunction, every order]** for every `n` (including `n = 0`),
`C_n^{(α)}` solves the Gegenbauer ODE with eigenvalue `λ_n = n(n+2α)`. -/
@[zil_level bridge_theorem]
theorem gegenbauerP_solves_all (α : ℝ) (n : ℕ) :
    IsGegenbauerSolution α n (fun x => (gegenbauerP α n).eval x)
      (fun x => (derivative (gegenbauerP α n)).eval x) := by
  cases n with
  | zero =>
    intro x
    refine ⟨(gegenbauerP α 0).hasDerivAt x,
      (derivative (derivative (gegenbauerP α 0))).eval x,
      (derivative (gegenbauerP α 0)).hasDerivAt x, ?_⟩
    simp only [gegenbauerP_zero, derivative_one, derivative_zero, eval_zero, eval_one,
      gegenbauerEigenvalue, Nat.cast_zero]
    ring
  | succ m => exact gegenbauerP_solves α m

/-- **[Legendre / hydrogen `O(4)` — all `n`]** At `α = 1/2` the Gegenbauer polynomials are the
Legendre polynomials, solving the Legendre ODE with the hydrogen bound-state eigenvalue
`gegenbauerEigenvalue (1/2) n = n(n+1) = cutkoskyEigenvalue n`. -/
@[zil_level bridge_theorem]
theorem gegenbauerP_legendre_solves_all (n : ℕ) :
    IsGegenbauerSolution (1 / 2) n (fun x => (gegenbauerP (1 / 2) n).eval x)
        (fun x => (derivative (gegenbauerP (1 / 2) n)).eval x)
      ∧ gegenbauerEigenvalue (1 / 2) n = cutkoskyEigenvalue n :=
  ⟨gegenbauerP_solves_all (1 / 2) n, gegenbauerEigenvalue_half_eq_cutkosky n⟩

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction

zil attach gegenbauer_derivativeRelations where
  supported_by @ "lean:gegenbauerP_recurrence",
  formalizes @ "claim:the-two-gegenbauer-derivative-relations-d1-and-d2-hold-for-all-n-proven-together-by-the-coupled-derivative-of-recurrence-induction-from-the-three-term-recurrence"

zil attach gegenbauerP_ode where
  supported_by @ "lean:gegenbauer_derivativeRelations",
  formalizes @ "claim:the-general-alpha-gegenbauer-polynomial-satisfies-the-gegenbauer-ode-as-a-polynomial-identity-for-every-n-from-differentiating-d1-and-substituting-d2"

zil attach gegenbauerP_solves_all where
  formalizes @ "claim:the-general-alpha-gegenbauer-polynomial-c-n-solves-the-gegenbauer-ode-for-every-n-with-eigenvalue-n-times-n-plus-two-alpha-the-all-order-eigenfunction-theorem-promoting-the-explicit-n-at-most-two-proofs-to-all-orders",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction.gegenbauer_derivativeRelations"

zil attach gegenbauerP_legendre_solves_all where
  formalizes @ "claim:at-alpha-one-half-the-gegenbauer-polynomials-solve-the-legendre-ode-for-all-n-with-the-hydrogen-bound-state-o-four-casimir-eigenvalue-n-times-n-plus-one-equal-to-the-cutkosky-bethe-salpeter-eigenvalue",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution.gegenbauerEigenvalue_half_eq_cutkosky"

zil_file_contract physlib.gegenbauerAllOrderEigenfunction where
  promises "The all-order general-alpha Gegenbauer eigenfunction theorem, promoting the explicit n at most two Gegenbauer ODE proofs to all orders by the coupled derivative-of-recurrence induction. From the three-term recurrence of the general-alpha polynomial family, the two Gegenbauer derivative relations are proven together by induction: D1 that one minus X squared times the derivative equals two alpha plus n times C n minus n plus one times X times C n plus one, and D2 that X times the derivative minus the derivative of C n equals n plus one times C n plus one. Differentiating D1 and substituting D2 gives the Gegenbauer ODE as a polynomial identity for every n, and hence the analytic eigenfunction statement for every n, that the general-alpha Gegenbauer polynomial solves the Gegenbauer ODE with eigenvalue n times n plus two alpha. At alpha one half these are the Legendre polynomials solving the Legendre ODE with the hydrogen bound-state O four Casimir eigenvalue equal to the Cutkosky Bethe-Salpeter eigenvalue for all n."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence.gegenbauerP",
    "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution.IsGegenbauerSolution",
    "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence.gegenbauerP_recurrence"
  ]
  forbids_substitutes [
    "claiming the ODE is proven by the three-term recurrence alone without the coupled derivative relations D1 and D2"
  ]
  witnessed_by [
    gegenbauerP_deriv_recurrence,
    gegenbauer_derivativeRelations,
    gegenbauerP_ode,
    gegenbauerP_solves,
    gegenbauerP_solves_all,
    gegenbauerP_legendre_solves_all
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.gegenbauerAllOrderEigenfunction
