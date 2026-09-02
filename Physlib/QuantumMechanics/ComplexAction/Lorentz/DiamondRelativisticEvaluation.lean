/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondRelativisticEquations

/-!
# Evaluating the special-relativity equations: the (3,4,5) observer

A worked numerical instance of the diamond special-relativity equations at the rapidity `θ = log 2`, where
the **(3,4,5) Pythagorean triple** makes every quantity an exact rational:

`cosh(log 2) = 5/4`, `sinh(log 2) = 3/4`, `tanh(log 2) = 3/5`, `e^{−log 2} = 1/2`.

So the observer moves at `β = 3/5`, with Lorentz factor `γ = 5/4`.  Each SR equation evaluates exactly:

| Equation | Value at `θ = log 2` |
|---|---|
| Lorentz factor `γ = cosh θ` | `5/4` |
| velocity `β = tanh θ` | `3/5` |
| mass shell `cosh²θ − sinh²θ` | `1` |
| time dilation / clock rate² `γ²` | `25/16` |
| length contraction `1/γ` | `4/5` |
| longitudinal Doppler `e^{−θ}` | `1/2` |
| velocity addition `β ⊕ β` (`tanh 2θ`) | `15/17` |

The BCJ dual here is `lorentzForceDual = β² = 9/25`, and `γ² = 25/16 = 1/(1 − 9/25)`.

* `cosh_log_two`, `sinh_log_two`, `tanh_log_two`, `exp_neg_log_two` — the (3,4,5) rapidity values.
* `massShell_eval`, `lengthContraction_eval`, `clockRateSq_eval`, `longitudinalDoppler_eval`,
  `velocityAddition_eval` — the SR equations evaluated.

Honest scope: exact rational evaluation of the diamond SR identities at one rapidity; no new physics.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondRelativisticEvaluation

open Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondRelativisticEquations

/-- **[Lorentz factor `γ = 5/4`] `cosh(log 2) = 5/4`.**  The time-dilation factor of the (3,4,5) observer. -/
theorem cosh_log_two : Real.cosh (Real.log 2) = 5 / 4 := by
  rw [Real.cosh_eq, Real.exp_log (by norm_num : (0:ℝ) < 2), Real.exp_neg,
    Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

/-- **[Proper momentum `p/m = 3/4`] `sinh(log 2) = 3/4`.** -/
theorem sinh_log_two : Real.sinh (Real.log 2) = 3 / 4 := by
  rw [Real.sinh_eq, Real.exp_log (by norm_num : (0:ℝ) < 2), Real.exp_neg,
    Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

/-- **[Velocity `β = 3/5`] `tanh(log 2) = 3/5`.** -/
theorem tanh_log_two : Real.tanh (Real.log 2) = 3 / 5 := by
  rw [Real.tanh_eq_sinh_div_cosh, sinh_log_two, cosh_log_two]
  norm_num

/-- **[Doppler value `e^{−log 2} = 1/2`].**  The redshift factor and the null-boost eigenvalue. -/
theorem exp_neg_log_two : Real.exp (-Real.log 2) = 1 / 2 := by
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

/-- **[Mass shell `= 1`] `cosh²(log 2) − sinh²(log 2) = 25/16 − 9/16 = 1`.**  The energy-momentum invariant
`E² − p² = m²` evaluated. -/
theorem massShell_eval : Real.cosh (Real.log 2) ^ 2 - Real.sinh (Real.log 2) ^ 2 = 1 := by
  rw [cosh_log_two, sinh_log_two]; norm_num

/-- **[Length contraction `1/γ = 4/5`] `1/cosh(log 2) = 4/5`.**  The Compton wavelength contracts to `4/5`. -/
theorem lengthContraction_eval : 1 / Real.cosh (Real.log 2) = 4 / 5 := by
  rw [cosh_log_two]; norm_num

/-- **[Clock rate² / time dilation `γ² = 25/16`] `cosh²(log 2) = 25/16`.**  The entropic clock's squared
time-dilation, equal to `1/(1 − BCJ dual) = 1/(1 − 9/25)`. -/
theorem clockRateSq_eval : Real.cosh (Real.log 2) ^ 2 = 25 / 16 := by
  rw [cosh_log_two]; norm_num

/-- **[Longitudinal Doppler `= 1/2`] `dopplerLongitudinal (tanh(log 2)) = 1/2`.**  The relativistic redshift
of the (3,4,5) observer. -/
theorem longitudinalDoppler_eval : dopplerLongitudinal (Real.tanh (Real.log 2)) = 1 / 2 := by
  rw [diamond_longitudinal_doppler]; exact exp_neg_log_two

/-- **[Velocity addition `3/5 ⊕ 3/5 = 15/17`] `tanh(log 2 + log 2) = 15/17`.**  Composing two `β = 3/5`
boosts by the relativistic velocity-addition law gives `15/17` — not `6/5` (which would exceed `c`). -/
theorem velocityAddition_eval : Real.tanh (Real.log 2 + Real.log 2) = 15 / 17 := by
  rw [rapidity_velocity_addition, tanh_log_two]; norm_num

end Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondRelativisticEvaluation

end
