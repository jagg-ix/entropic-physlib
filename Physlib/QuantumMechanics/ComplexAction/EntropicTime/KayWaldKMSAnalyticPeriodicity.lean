/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The KMS condition: the thermal two-point function is analytic and `β`-periodic, `G(t − iβ) = G(−t)` (Kay–Wald)

Formalizes the analytic **Kubo–Martin–Schwinger (KMS) condition** — the defining property that makes the Kay–Wald
horizon state *thermal*. For a single Killing-horizon mode of frequency `ω`, the stationary two-point (Wightman)
function in the Hawking–KMS state is

`G_β(t) = (n+1) e^{−iωt} + n e^{+iωt}`, `n = 1/(e^{βω} − 1)` (the Bose occupation),

and it satisfies the KMS periodicity in imaginary time

`G_β(t − iβ) = G_β(−t)`.

This is the algebraic content behind the thermality of the Kay–Wald state: the correlator, analytically continued
by one period `β = 2π/κ` of imaginary Killing time, reproduces the time-reversed correlator. The proof is *exactly*
the detailed-balance relations of the Bose occupation (`KayWaldHawkingRadiationBoseEinstein`),
`(n+1) e^{−βω} = n` and `n e^{βω} = n+1`, lifted to the complexified time argument.

* the **detailed-balance identities** `(n+1) e^{−βω} = n` and `n e^{βω} = n+1` (`occupation_add_one_mul_exp_neg`,
 `occupation_mul_exp`) — the emission/absorption ratios of the Hawking occupation `n`;
* the **thermal Wightman function** `G_β(t) = (n+1) e^{−iωt} + n e^{+iωt}` (`thermalWightman`) — the stationary
 two-point function of a horizon mode in the Hawking–KMS state, on complexified time;
* the **KMS condition** `G_β(t − iβ) = G_β(−t)` (`thermalWightman_kms`) — the imaginary-time periodicity that *is*
 the thermal (KMS) equilibrium condition; the whole statement collapses onto the two detailed-balance identities;
* the **Hawking specialization** `β = 2π/κ` (`hawking_kms_period`) — at the Hawking inverse temperature
 `β = hawkingBeta 1 κ 1 1 = 2π/κ` the horizon correlator's KMS imaginary period is the geometric Killing-horizon
 period (`imaginary_period_is_hawking_beta`), closing the loop geometry → occupation → KMS.

So the Kay–Wald thermality is this one identity: the horizon two-point function is periodic in imaginary Killing
time with period the Hawking inverse temperature `β = 2π/κ`, and that periodicity is nothing but the
detailed-balance ratios of the Bose–Einstein occupation.

* **§A — the detailed-balance identities** (`occupation_add_one_mul_exp_neg`, `occupation_mul_exp`).
* **§B — the thermal Wightman function and the KMS condition** (`thermalWightman`, `thermalWightman_kms`).
* **§C — the Hawking specialization `β = 2π/κ`** (`hawking_kms_period`).

The single-mode thermal two-point function, its KMS `β`-periodicity, and the detailed-balance
identities are exact `Real.exp`/`Complex.exp` algebra. The full mode decomposition of the horizon field, the
Hadamard/positivity structure, and the operator-algebraic KMS characterization (analyticity in the strip
`0 < Im t < β`) are the referenced Kay–Wald content, not re-derived. No new axioms.

## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49; R. Kubo; P.C. Martin, J. Schwinger (KMS condition). Repo dependencies:
 `EntropicTime.KayWaldHawkingRadiationBoseEinstein` (`hawkingOccupation`, detailed balance),
 `EntropicTime.KayWaldBifurcateHorizonSurfaceGravity` (`imaginary_period_is_hawking_beta`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity

/-! ## §A — the detailed-balance identities -/

/-- **[Detailed balance: `(n+1) e^{−βω} = n`].** The total-emission occupation `n+1` times the Boltzmann factor
`e^{−βω}` returns the absorption occupation `n = 1/(e^{βω}−1)` — one of the two KMS detailed-balance ratios of the
Hawking–Bose occupation. -/
theorem occupation_add_one_mul_exp_neg (β ω : ℝ) (h : Real.exp (β * ω) - 1 ≠ 0) :
    (hawkingOccupation β ω + 1) * Real.exp (-(β * ω)) = hawkingOccupation β ω := by
  unfold hawkingOccupation
  rw [Real.exp_neg]
  have hE : Real.exp (β * ω) ≠ 0 := Real.exp_ne_zero _
  field_simp
  ring

/-- **[Detailed balance: `n e^{βω} = n+1`].** The absorption occupation `n` times the Boltzmann factor `e^{βω}`
returns the total-emission occupation `n+1` — the second KMS detailed-balance ratio. -/
theorem occupation_mul_exp (β ω : ℝ) (h : Real.exp (β * ω) - 1 ≠ 0) :
    hawkingOccupation β ω * Real.exp (β * ω) = hawkingOccupation β ω + 1 := by
  unfold hawkingOccupation
  field_simp
  ring

/-! ## §B — the thermal Wightman function and the KMS condition -/

/-- **The thermal (Wightman) two-point function of a horizon mode** `G_β(t) = (n+1) e^{−iωt} + n e^{+iωt}` with
`n = hawkingOccupation β ω` the Bose occupation — the stationary two-point function of a Killing-horizon mode of
frequency `ω` in the Hawking–KMS state, on complexified time `t ∈ ℂ`. -/
noncomputable def thermalWightman (β ω : ℝ) (t : ℂ) : ℂ :=
  ((hawkingOccupation β ω + 1 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ω : ℂ) * t))
    + ((hawkingOccupation β ω : ℝ) : ℂ) * Complex.exp (Complex.I * (ω : ℂ) * t)

/-- **[The KMS condition] `G_β(t − iβ) = G_β(−t)`.** The thermal two-point function is periodic under a shift of the
time argument by one imaginary period `−iβ`, reproducing the time-reversed correlator. Expanding the shift,
`e^{−iω(t−iβ)} = e^{−iωt} e^{−βω}` and `e^{+iω(t−iβ)} = e^{+iωt} e^{+βω}`, the two Boltzmann factors turn the
occupation coefficients into one another by detailed balance — `(n+1) e^{−βω} = n` and `n e^{βω} = n+1` — which is
exactly the swap producing `G_β(−t)`. This imaginary-time periodicity is the defining KMS (thermal-equilibrium)
condition of the Kay–Wald state. -/
theorem thermalWightman_kms (β ω : ℝ) (t : ℂ) (h : Real.exp (β * ω) - 1 ≠ 0) :
    thermalWightman β ω (t - Complex.I * (β : ℂ)) = thermalWightman β ω (-t) := by
  unfold thermalWightman
  have db1C : ((hawkingOccupation β ω + 1 : ℝ) : ℂ) * ((Real.exp (-(β * ω)) : ℝ) : ℂ)
      = ((hawkingOccupation β ω : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, occupation_add_one_mul_exp_neg β ω h]
  have db2C : ((hawkingOccupation β ω : ℝ) : ℂ) * ((Real.exp (β * ω) : ℝ) : ℂ)
      = ((hawkingOccupation β ω + 1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, occupation_mul_exp β ω h]
  have arg1 : -(Complex.I * (ω : ℂ) * (t - Complex.I * (β : ℂ)))
      = -(Complex.I * (ω : ℂ) * t) + ((-(β * ω) : ℝ) : ℂ) := by
    push_cast
    linear_combination ((β : ℂ) * (ω : ℂ)) * Complex.I_sq
  have arg2 : Complex.I * (ω : ℂ) * (t - Complex.I * (β : ℂ))
      = Complex.I * (ω : ℂ) * t + ((β * ω : ℝ) : ℂ) := by
    push_cast
    linear_combination (-((β : ℂ) * (ω : ℂ))) * Complex.I_sq
  have arg3 : -(Complex.I * (ω : ℂ) * -t) = Complex.I * (ω : ℂ) * t := by ring
  have arg4 : Complex.I * (ω : ℂ) * -t = -(Complex.I * (ω : ℂ) * t) := by ring
  rw [arg1, arg2, arg3, arg4, Complex.exp_add, Complex.exp_add,
    ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  set A := Complex.exp (-(Complex.I * (ω : ℂ) * t))
  set B := Complex.exp (Complex.I * (ω : ℂ) * t)
  linear_combination A * db1C + B * db2C

/-! ## §C — the Hawking specialization `β = 2π/κ` -/

/-- **[The horizon correlator is KMS at the Hawking inverse temperature] `β = 2π/κ`.** Specializing the KMS
condition to the Hawking inverse temperature `β = hawkingBeta 1 κ 1 1 = 2π/κ`: the stationary two-point function of
a bifurcate-Killing-horizon mode is periodic in imaginary Killing time with period the Hawking `β`, whose value is
the geometric horizon period `2π/κ` (`imaginary_period_is_hawking_beta`). Geometry (`U = e^{κv}`), the Bose
occupation, and the KMS thermal condition close into one. -/
theorem hawking_kms_period (κ ω : ℝ) (t : ℂ)
    (h : Real.exp (hawkingBeta 1 κ 1 1 * ω) - 1 ≠ 0) :
    thermalWightman (hawkingBeta 1 κ 1 1) ω (t - Complex.I * ((hawkingBeta 1 κ 1 1 : ℝ) : ℂ))
      = thermalWightman (hawkingBeta 1 κ 1 1) ω (-t) :=
  thermalWightman_kms (hawkingBeta 1 κ 1 1) ω t h

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldKMSAnalyticPeriodicity

end
