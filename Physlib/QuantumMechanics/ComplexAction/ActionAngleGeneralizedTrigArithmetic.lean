/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GeneralizedTrigArithmetic

/-!
# Takeuchi's arithmetic applied to the action-angle half-period

This links `GeneralizedTrigArithmetic` (Takeuchi's conjugate exponent and the `π` Beta-duplication) to the
action-angle formalizations that use `genPi2` — the purely nonlinear oscillator's generalized half-period
`genPi2 α = π_{2,α+1}` (`PurelyNonlinearActionAngle`, appearing in `T·Ω = 2π_{2,α+1}` via
`periodU_mul_frequency`).

The physical exponent of the oscillator is `n = α+1`; its Hölder conjugate is `(α+1)* = (α+1)/α`. Takeuchi's
duplication `π_{p*,p} = 2^{1−2/p}·π_{2,p}` at `p = α+1` gives the conjugate partner of the action-angle
half-period, and — via `periodU_mul_frequency` (`T·Ω = 2·genPi2`) — ties it to the amplitude-dependent period and
frequency.

* **`physical_holder_conjugate`** (`1/(α+1) + 1/(α+1)* = 1`).
* **`genPi2_conjugate_duplication`** (`π_{(α+1)*,α+1} = 2^{1−2/(α+1)}·π_{2,α+1}`).
* **`periodU_frequency_conjugate_duplication`** (the conjugate half-period in terms of `T·Ω`).

**Honest layering.** Exact identities reusing `genPi_conjugate_eq_duplication`, `holder_conjugate`,
`genPi2_eq_genPi` and `periodU_mul_frequency`. ## References

* Links `GeneralizedTrigArithmetic` (Takeuchi 2017) to `PurelyNonlinearActionAngle` (Ghosh–Bhamidipati 1905.08062).


-/

set_option autoImplicit false

open scoped Real
open Physlib.QuantumMechanics.ComplexAction.GeneralizedIsotonicOscillator
open Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngle
open Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngleRemarks
open Physlib.QuantumMechanics.ComplexAction.GeneralizedTrigArithmetic

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ActionAngleGeneralizedTrigArithmetic

/-- **The oscillator exponent and its Hölder conjugate** `1/(α+1) + 1/(α+1)* = 1` — the purely nonlinear
oscillator's exponent `n = α+1` (from `sgn(q)|q|^α`, potential `|q|^{α+1}/(α+1)`) pairs with the conjugate
`(α+1)* = (α+1)/α`. -/
lemma physical_holder_conjugate (α : ℝ) (hα : 0 < α) :
    1 / (α + 1) + 1 / conjugateExponent (α + 1) = 1 :=
  holder_conjugate (α + 1) (by positivity) (by intro h; nlinarith)

/-- **Takeuchi's duplication for the action-angle half-period** `π_{(α+1)*,α+1} = 2^{1−2/(α+1)}·π_{2,α+1}` — the
generalized `π` at the conjugate exponent equals the Legendre factor times the oscillator's half-period
`genPi2 α = π_{2,α+1}`. -/
lemma genPi2_conjugate_duplication (α : ℝ) (hα : 0 < α) :
    genPi (conjugateExponent (α + 1)) (α + 1) = (2 : ℝ) ^ (1 - 2 / (α + 1)) * genPi2 α := by
  rw [genPi_conjugate_eq_duplication (α + 1) (by linarith), ← genPi2_eq_genPi]

/-- **The conjugate half-period via the period and frequency** `π_{(α+1)*,α+1} = 2^{1−2/(α+1)}·(T·Ω)/2` — using
`periodU_mul_frequency` (`T·Ω = 2·π_{2,α+1}`), the Takeuchi conjugate half-period is expressed through the
amplitude-dependent period `T = periodU 1 α q₀` and frequency `Ω = pnlFrequency α q₀`. -/
lemma periodU_frequency_conjugate_duplication (α q₀ : ℝ) (hα : 0 < α) (hq₀ : q₀ ≠ 0) :
    genPi (conjugateExponent (α + 1)) (α + 1)
      = (2 : ℝ) ^ (1 - 2 / (α + 1)) * (periodU 1 α q₀ * pnlFrequency α q₀) / 2 := by
  rw [genPi2_conjugate_duplication α hα,
    show genPi2 α = periodU 1 α q₀ * pnlFrequency α q₀ / 2 from by
      rw [periodU_mul_frequency α q₀ (by linarith) hq₀]; ring]
  ring

end Physlib.QuantumMechanics.ComplexAction.ActionAngleGeneralizedTrigArithmetic
