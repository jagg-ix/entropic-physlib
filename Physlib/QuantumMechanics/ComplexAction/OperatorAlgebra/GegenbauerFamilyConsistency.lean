/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction
meta import Zil

/-!
# Consistency of the recurrence family with the pre-existing Gegenbauer solutions

`GegenbauerODESolution` (pre-existing) proved the Gegenbauer ODE for the *explicit* low-order
functions `C₀ = 1`, `C₁ = 2αx`, `C₂ = 2α(α+1)x² − α` (`gegenbauer0/1/2_solves`) and, at `α = 1`,
for all `n` via Mathlib's Chebyshev `U` (`gegenbauerOne`).  `GegenbauerGeneralRecurrence`/
`GegenbauerAllOrderEigenfunction` (recent) built the general-`α` family `gegenbauerP` from the
recurrence and proved the all-`n` ODE.

This module links the two: the recurrence family reproduces the pre-existing explicit low-order
solutions, and at `α = 1` it *is* Mathlib's Chebyshev polynomial of the second kind — so the recent
recurrence-based all-`n` proof and the pre-existing Chebyshev-based `α = 1` proof are the same family.

* `gegenbauerP_eval_zero/one/two` — `(gegenbauerP α n).eval` reproduces the explicit
  `gegenbauer0/1/2_solves` functions.
* `gegenbauerP_one_eq_chebyshevU` — `gegenbauerP 1 n = U_n` (Mathlib's `Polynomial.Chebyshev.U`),
  the family underlying the pre-existing `gegenbauerOne`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Polynomial

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerFamilyConsistency

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerAllOrderEigenfunction

/-- `C₀^{(α)}` evaluates to the `gegenbauer0_solves` function `1`. -/
@[zil_level physical_theorem]
theorem gegenbauerP_eval_zero (α x : ℝ) : (gegenbauerP α 0).eval x = 1 := by
  rw [gegenbauerP_zero, eval_one]

/-- `C₁^{(α)}` evaluates to the `gegenbauer1_solves` function `2αx`. -/
@[zil_level physical_theorem]
theorem gegenbauerP_eval_one (α x : ℝ) : (gegenbauerP α 1).eval x = 2 * α * x := by
  rw [gegenbauerP_one, eval_mul, eval_C, eval_X]

/-- `C₂^{(α)}` evaluates to the `gegenbauer2_solves` function `2α(α+1)x² − α`. -/
@[zil_level physical_theorem]
theorem gegenbauerP_eval_two (α x : ℝ) :
    (gegenbauerP α 2).eval x = 2 * α * (α + 1) * x ^ 2 - α := by
  rw [gegenbauerP_two, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_C]

/-- **At `α = 1` the recurrence family is Mathlib's Chebyshev polynomial of the second kind**
`gegenbauerP 1 n = U_n` — the pre-existing `gegenbauerOne`/`gegenbauerOne_solves` `α = 1` all-`n`
proof and the recent recurrence-based all-`n` proof are the same family. -/
@[zil_level bridge_theorem]
theorem gegenbauerP_one_eq_chebyshevU (n : ℕ) :
    gegenbauerP 1 n = Chebyshev.U ℝ (n : ℤ) := by
  suffices h : ∀ m : ℕ, gegenbauerP 1 m = Chebyshev.U ℝ (m : ℤ)
      ∧ gegenbauerP 1 (m + 1) = Chebyshev.U ℝ ((m : ℤ) + 1) from (h n).1
  intro m
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [gegenbauerP_zero, Nat.cast_zero, Chebyshev.U_zero]
    · rw [gegenbauerP_one, Nat.cast_zero, zero_add, Chebyshev.U_one,
        show (2 * (1 : ℝ)) = 2 from by ring, map_ofNat]
  | succ m ih =>
    obtain ⟨ih0, ih1⟩ := ih
    have hm : ((m : ℝ) + 2) ≠ 0 := by positivity
    have e : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    refine ⟨e ▸ ih1, ?_⟩
    have hdef : gegenbauerP (1 : ℝ) (m + 1 + 1)
        = C (2 * (1 + ((m : ℝ) + 1)) / ((m : ℝ) + 2)) * X * gegenbauerP 1 (m + 1)
          - C ((2 * 1 + (m : ℝ)) / ((m : ℝ) + 2)) * gegenbauerP 1 m := rfl
    rw [hdef, ih0, ih1,
      show (2 * (1 + ((m : ℝ) + 1)) / ((m : ℝ) + 2)) = 2 from by field_simp; ring,
      show ((2 * 1 + (m : ℝ)) / ((m : ℝ) + 2)) = 1 from by field_simp; ring,
      map_ofNat, C_1, one_mul,
      show (((m + 1 : ℕ) : ℤ) + 1) = (m : ℤ) + 2 from by push_cast; ring,
      Chebyshev.U_add_two]

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerFamilyConsistency

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerFamilyConsistency

zil attach gegenbauerP_eval_two where
  supported_by @ "lean:gegenbauerP_two",
  formalizes @ "claim:the-recurrence-gegenbauer-family-evaluated-reproduces-the-pre-existing-explicit-second-order-solution-two-alpha-alpha-plus-one-x-squared-minus-alpha"

zil attach gegenbauerP_one_eq_chebyshevU where
  formalizes @ "claim:at-alpha-one-the-general-alpha-recurrence-gegenbauer-family-equals-mathlibs-chebyshev-polynomial-of-the-second-kind-so-the-pre-existing-chebyshev-based-all-n-proof-and-the-recent-recurrence-based-all-n-proof-are-the-same-family",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence.gegenbauerP"

zil_file_contract physlib.gegenbauerFamilyConsistency where
  promises "Linking the recent general-alpha recurrence Gegenbauer family to the pre-existing GegenbauerODESolution explicit solutions. The recurrence family evaluated reproduces the pre-existing explicit low-order solutions: C zero is one, C one is two alpha x, and C two is two alpha alpha plus one x squared minus alpha. At alpha one the general-alpha recurrence family equals Mathlib's Chebyshev polynomial of the second kind U n, the polynomial underlying the pre-existing gegenbauerOne, so the pre-existing Chebyshev-based alpha one all-n proof and the recent recurrence-based all-n proof are the same family."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence.gegenbauerP",
    "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence.gegenbauerP_two"
  ]
  forbids_substitutes [
    "reading the consistency link as re-proving the ODE rather than identifying the recurrence family with the pre-existing solutions"
  ]
  witnessed_by [
    gegenbauerP_eval_zero,
    gegenbauerP_eval_one,
    gegenbauerP_eval_two,
    gegenbauerP_one_eq_chebyshevU
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.gegenbauerFamilyConsistency
