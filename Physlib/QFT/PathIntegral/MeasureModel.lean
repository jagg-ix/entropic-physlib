/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.PathIntegral.Coercivity
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Measurable path-integral model

A **measurable** representative for the path integral: a measurable
state space `α`, a measure `μ`, and measurable real/imaginary action
functionals `actionRe, actionIm : α → ℝ` with `actionIm ≥ 0` and
`ℏ > 0`.  From these we build the **complex weight**

  `w(x) = exp(i·S_R(x)/ℏ − S_I(x)/ℏ) ∈ ℂ`,

which factorises into a phase (unit modulus) and the entropic damping
`exp(−S_I/ℏ) ∈ (0, 1]`.

## Main results

* `weight_factorizes` — `w(x) = exp(i·S_R/ℏ) · exp(−S_I/ℏ)`.
* `phase_norm_one` — the phase has unit modulus.
* `weight_norm_is_damping` — `‖w(x)‖ = exp(−S_I/ℏ)`.
* `damping_pos`, `damping_le_one` — damping ∈ (0, 1].
* `weight_bochner_bounded` — uniform `‖w(x)‖ ≤ 1`.
* `weight_eq_damping_of_actionRe_zero` — the Euclidean sector
  (`S_R = 0`) is purely-real damping.
* Measurability of `weight`, `damping`, and `actionImScaled`.


## References

- **Fujiwara 1979** — *A construction of the fundamental solution for the Schrödinger equation*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.PathIntegral

open MeasureTheory Complex Real

/-- **Measurable path-integral model** on state space `α`. -/
structure MeasurePathIntegralModel (α : Type*) [MeasurableSpace α] where
  /-- Reference measure on the path space. -/
  μ : Measure α
  /-- Planck constant `ℏ > 0`. -/
  hbar : ℝ
  /-- `ℏ` is strictly positive. -/
  hbar_pos : 0 < hbar
  /-- Real-action functional `S_R : α → ℝ`. -/
  actionRe : α → ℝ
  /-- Imaginary-action functional `S_I : α → ℝ` (`≥ 0`). -/
  actionIm : α → ℝ
  /-- Measurability of `S_R`. -/
  measurable_actionRe : Measurable actionRe
  /-- Measurability of `S_I`. -/
  measurable_actionIm : Measurable actionIm
  /-- Non-negativity of the imaginary action `S_I ≥ 0`. -/
  actionIm_nonneg : ∀ x, 0 ≤ actionIm x

namespace MeasurePathIntegralModel

variable {α : Type*} [MeasurableSpace α] (m : MeasurePathIntegralModel α)

/-- Scaled real action `S_R / ℏ`. -/
def actionReScaled (x : α) : ℝ := m.actionRe x / m.hbar

/-- Scaled imaginary action `S_I / ℏ`. -/
def actionImScaled (x : α) : ℝ := m.actionIm x / m.hbar

/-- Oscillatory **phase** factor `exp(i · S_R/ℏ)`. -/
def phase (x : α) : ℂ :=
  Complex.exp ((m.actionReScaled x : ℂ) * Complex.I)

/-- Entropic **damping** factor `exp(−S_I/ℏ)`. -/
def damping (x : α) : ℝ :=
  Real.exp (- m.actionImScaled x)

/-- The full **complex weight** `w = exp(i·S_R/ℏ − S_I/ℏ)`. -/
def weight (x : α) : ℂ :=
  Complex.exp
    ((-(m.actionImScaled x) : ℂ) +
      ((m.actionReScaled x : ℂ) * Complex.I))

/-- The weight factorises into phase times damping. -/
theorem weight_factorizes (x : α) :
    m.weight x =
      Complex.exp ((m.actionReScaled x : ℂ) * Complex.I) *
        (Real.exp (-(m.actionImScaled x)) : ℂ) := by
  unfold weight
  rw [show (Real.exp (-(m.actionImScaled x)) : ℂ) =
        Complex.exp (-(m.actionImScaled x : ℂ)) from by
    simp [Complex.ofReal_exp, Complex.ofReal_neg]]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The oscillatory phase has unit modulus. -/
theorem phase_norm_one (x : α) : ‖m.phase x‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp_ofReal_mul_I]

/-- The **norm of the complex weight is the entropic damping**:
`‖w(x)‖ = exp(−S_I/ℏ)`. -/
theorem weight_norm_is_damping (x : α) :
    ‖m.weight x‖ = Real.exp (-(m.actionImScaled x)) := by
  rw [m.weight_factorizes]
  rw [norm_mul]
  have hphase :
      ‖Complex.exp ((m.actionReScaled x : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  rw [hphase, one_mul]
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

/-- Damping is strictly positive. -/
theorem damping_pos (x : α) : 0 < m.damping x := by
  unfold damping
  exact Real.exp_pos _

/-- Damping is at most one. -/
theorem damping_le_one (x : α) : m.damping x ≤ 1 := by
  unfold damping actionImScaled
  rw [Real.exp_le_one_iff]
  linarith [div_nonneg (m.actionIm_nonneg x) m.hbar_pos.le]

/-- **Global modulus bound**: `‖w(x)‖ ≤ 1` everywhere. -/
theorem weight_bochner_bounded (x : α) : ‖m.weight x‖ ≤ 1 := by
  rw [m.weight_norm_is_damping]
  exact m.damping_le_one x

/-- The complex weight is measurable. -/
theorem measurable_weight : Measurable m.weight := by
  unfold weight
  apply Complex.measurable_exp.comp
  apply Measurable.add
  · exact (Complex.measurable_ofReal.comp
      (m.measurable_actionIm.div_const m.hbar)).neg
  · exact (Complex.measurable_ofReal.comp
      (m.measurable_actionRe.div_const m.hbar)).mul_const Complex.I

/-- The scaled imaginary action is measurable. -/
theorem measurable_actionImScaled : Measurable m.actionImScaled :=
  m.measurable_actionIm.div_const m.hbar

/-- The damping profile is measurable. -/
theorem measurable_damping : Measurable m.damping :=
  Real.measurable_exp.comp m.measurable_actionImScaled.neg

/-- **Euclidean sector**: when `S_R ≡ 0` the weight is purely real and
equals the damping. -/
theorem weight_eq_damping_of_actionRe_zero
    (hRe : ∀ x, m.actionRe x = 0) (x : α) :
    m.weight x = (m.damping x : ℂ) := by
  rw [m.weight_factorizes]
  have hscaled : m.actionReScaled x = 0 := by
    unfold actionReScaled
    simp [hRe x]
  simp [hscaled, damping]

/-- The path-integral damping (scalar form `path_integral_damping`) applied
to `S_I(x)` is exactly `damping x`. -/
theorem damping_eq_path_integral_damping (x : α) :
    m.damping x = path_integral_damping m.hbar (m.actionIm x) := by
  unfold damping actionImScaled path_integral_damping
  congr 1; ring

end MeasurePathIntegralModel

end Physlib.QFT.PathIntegral

end
