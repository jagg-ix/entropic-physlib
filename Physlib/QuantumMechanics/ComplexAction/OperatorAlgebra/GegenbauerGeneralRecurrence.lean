/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution
meta import Zil

/-!
# The general-`α` Gegenbauer family via the three-term recurrence

`GegenbauerODESolution` proves the Gegenbauer ODE for the explicit low orders `n ≤ 2` (general `α`)
and for all `n` at `α = 1` (via Mathlib's Chebyshev `U`).  This module builds the **fully
general-`α` Gegenbauer polynomial family** `gegenbauerP α n` from the three-term recurrence

`(n+2) C_{n+2}^{(α)} = 2(α+n+1) x C_{n+1}^{(α)} − (2α+n) C_n^{(α)}`,  `C_0 = 1`, `C_1 = 2αx`,

(`gegenbauerP_recurrence`), and checks it reproduces the explicit low-order polynomials
(`gegenbauerP_zero/one/two`) — the family that the `n ≤ 2` proofs are the base cases of.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Polynomial

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerODESolution

/-- **The general-`α` Gegenbauer polynomial family** defined by the three-term recurrence:
`C_0 = 1`, `C_1 = 2αX`, and
`C_{n+2} = (2(α+n+1)/(n+2)) X C_{n+1} − ((2α+n)/(n+2)) C_n`. -/
noncomputable def gegenbauerP (α : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C (2 * α) * X
  | (n + 2) => C (2 * (α + (↑n + 1)) / (↑n + 2)) * X * gegenbauerP α (n + 1)
                - C ((2 * α + ↑n) / (↑n + 2)) * gegenbauerP α n

@[simp] lemma gegenbauerP_zero (α : ℝ) : gegenbauerP α 0 = 1 := rfl

@[simp] lemma gegenbauerP_one (α : ℝ) : gegenbauerP α 1 = C (2 * α) * X := rfl

/-- **The three-term recurrence** in cleared form:
`(n+2) C_{n+2} = 2(α+n+1) X C_{n+1} − (2α+n) C_n`. -/
@[zil_level physical_theorem]
theorem gegenbauerP_recurrence (α : ℝ) (n : ℕ) :
    C ((↑n : ℝ) + 2) * gegenbauerP α (n + 2)
      = C (2 * (α + (↑n + 1))) * X * gegenbauerP α (n + 1)
        - C (2 * α + ↑n) * gegenbauerP α n := by
  have hn : ((↑n : ℝ) + 2) ≠ 0 := by positivity
  have hA : ((↑n : ℝ) + 2) * (2 * (α + (↑n + 1)) / (↑n + 2)) = 2 * (α + (↑n + 1)) := by
    field_simp
  have hB : ((↑n : ℝ) + 2) * ((2 * α + ↑n) / (↑n + 2)) = 2 * α + ↑n := by
    field_simp
  simp only [gegenbauerP]
  rw [mul_sub,
    show C ((↑n : ℝ) + 2) * (C (2 * (α + (↑n + 1)) / (↑n + 2)) * X * gegenbauerP α (n + 1))
        = C (((↑n : ℝ) + 2) * (2 * (α + (↑n + 1)) / (↑n + 2))) * X * gegenbauerP α (n + 1) from by
      rw [C_mul]; ring,
    show C ((↑n : ℝ) + 2) * (C ((2 * α + ↑n) / (↑n + 2)) * gegenbauerP α n)
        = C (((↑n : ℝ) + 2) * ((2 * α + ↑n) / (↑n + 2))) * gegenbauerP α n from by
      rw [C_mul]; ring,
    hA, hB]

/-- **`C_2^{(α)} = 2α(α+1)X² − α`** — the recurrence reproduces the explicit second-order polynomial. -/
@[zil_level physical_theorem]
theorem gegenbauerP_two (α : ℝ) :
    gegenbauerP α 2 = C (2 * α * (α + 1)) * X ^ 2 - C α := by
  simp only [gegenbauerP, gegenbauerP_zero, gegenbauerP_one, Nat.cast_zero, mul_one]
  rw [show (2 * (α + ((0 : ℝ) + 1)) / (0 + 2)) = α + 1 from by ring,
    show ((2 * α + (0 : ℝ)) / (0 + 2)) = α from by ring,
    show C (α + 1) * X * (C (2 * α) * X) = C (2 * α * (α + 1)) * X ^ 2 from by
      rw [show C (α + 1) * X * (C (2 * α) * X) = C (α + 1) * C (2 * α) * X ^ 2 from by ring,
        ← C_mul, show ((α + 1) * (2 * α) : ℝ) = 2 * α * (α + 1) from by ring]]

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence

zil attach gegenbauerP_recurrence where
  formalizes @ "claim:the-general-alpha-gegenbauer-polynomial-family-satisfies-the-three-term-recurrence-n-plus-two-times-c-n-plus-two-equals-two-alpha-plus-n-plus-one-times-x-c-n-plus-one-minus-two-alpha-plus-n-times-c-n"

zil attach gegenbauerP_two where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence.gegenbauerP_one",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence.gegenbauerP_zero",
  formalizes @ "claim:the-general-alpha-gegenbauer-recurrence-reproduces-the-explicit-second-order-polynomial-two-alpha-alpha-plus-one-x-squared-minus-alpha"

zil_file_contract physlib.gegenbauerGeneralRecurrence where
  promises "The fully general-alpha Gegenbauer polynomial family built from the three-term recurrence. The family is defined by C zero equals one, C one equals two alpha X, and C n plus two equals two alpha plus n plus one over n plus two times X times C n plus one minus two alpha plus n over n plus two times C n. The recurrence in cleared form states n plus two times C n plus two equals two alpha plus n plus one times X times C n plus one minus two alpha plus n times C n. The recurrence reproduces the explicit low-order polynomials, in particular C two equals two alpha alpha plus one X squared minus alpha, so the general-alpha family has the explicit n at most two Gegenbauer solutions as its base cases."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.GegenbauerGeneralRecurrence.gegenbauerP"
  ]
  forbids_substitutes [
    "reading the recurrence family as already carrying the all-n ODE proof, which needs the derivative-of-recurrence induction"
  ]
  witnessed_by [
    gegenbauerP_recurrence,
    gegenbauerP_two
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.gegenbauerGeneralRecurrence
