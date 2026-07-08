/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.Special.UnruhEntropicRate
public import Physlib.Relativity.Special.HyperbolicBoost
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Entropic time as a function of rapidity / velocity along a Rindler worldline

For a Rindler observer with possibly **time-varying** proper acceleration
`a : ℝ → ℝ` (`a ≥ 0`), the rapidity grows along proper time as
`η̇ = a / c`, so the **total rapidity sweep** over a proper-time interval
`[0, T]` is

  `Δη  =  (1/c) · ∫₀^T a(τ) dτ`.

The corresponding **accumulated entropic time** is

  `Δτ_ent  =  ∫₀^T λ_U(τ) dτ  =  (1/(2πc)) · ∫₀^T a(τ) dτ`,

so the load-bearing identity is

  **`Δτ_ent  =  Δη / (2π)`**

— entropic time is linear in the total rapidity sweep, independent of the
shape of `a(τ)` (only the integral matters).  This is the variable-acceleration
generalisation of the uniform Rindler case `Δτ_ent = η / (2π)`.

In velocity form (starting at rest), the final velocity is
`β_final = tanh(Δη)`, so

  `Δτ_ent  =  artanh(β_final) / (2π)`.

## Contents

* `RindlerWorldline` — structure holding `a : ℝ → ℝ`, `c > 0`, `T ≥ 0`,
  non-negativity of `a`, and `IntervalIntegrable a` on `[0, T]`.
* `rapiditySweep W = (1/c) · ∫₀^T a(τ) dτ` — total rapidity sweep.
* `entropicTime W = (1/(2πc)) · ∫₀^T a(τ) dτ` — accumulated entropic time.
* `rapiditySweep_nonneg`, `entropicTime_nonneg`.
* `entropicTime_eq_rapiditySweep_over_two_pi` — load-bearing identity
  `Δτ_ent = Δη / (2π)`.
* `finalVelocity W = tanh (rapiditySweep W)` (starting from rest) +
  `entropicTime_eq_artanh_finalVelocity_over_two_pi`
  (`Δτ_ent = artanh(β_final) / (2π)`).
* `entropicTime_zero_of_T_zero`, `entropicTime_of_zero_acceleration`
  — endpoint behaviour.
* `constant`, `rapiditySweep_constant`, `entropicTime_constant` — the
  uniform-acceleration specialisation `Δτ_ent = a₀·T / (2πc)`.
* `bridge to UnruhEntropicRate`: constant case agrees with the existing
  `UnruhEntropicRate.Δτ_ent`.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special

open Real MeasureTheory

/-! ## §1 — Variable-acceleration Rindler worldline -/

/-- **Variable-acceleration Rindler worldline.**

A `(1+1)`-D Rindler observer parameterised by their proper time `τ ∈ [0, T]`,
with proper acceleration `a : ℝ → ℝ` non-negative and `IntervalIntegrable`
on `[0, T]`. -/
structure RindlerWorldline where
  /-- Proper acceleration as a function of proper time. -/
  a : ℝ → ℝ
  /-- Speed of light. -/
  c : ℝ
  /-- Proper-time endpoint. -/
  T : ℝ
  /-- `c > 0`. -/
  c_pos : 0 < c
  /-- `T ≥ 0`. -/
  T_nonneg : 0 ≤ T
  /-- `a(τ) ≥ 0` (unsigned proper acceleration). -/
  a_nonneg : ∀ τ, 0 ≤ a τ
  /-- `a` is interval-integrable on `[0, T]`. -/
  a_intervalIntegrable : IntervalIntegrable a volume 0 T

namespace RindlerWorldline

variable (W : RindlerWorldline)

/-! ## §2 — Rapidity sweep and entropic-time accumulation -/

/-- **Total rapidity sweep** `Δη = (1/c) · ∫₀^T a(τ) dτ` over the
proper-time interval `[0, T]`. -/
def rapiditySweep : ℝ := (1 / W.c) * ∫ τ in (0 : ℝ)..W.T, W.a τ

/-- **Accumulated entropic time**
`Δτ_ent = (1/(2πc)) · ∫₀^T a(τ) dτ` over `[0, T]`. -/
def entropicTime : ℝ :=
  (1 / (2 * Real.pi * W.c)) * ∫ τ in (0 : ℝ)..W.T, W.a τ

/-- Helper: the integral `∫₀^T a(τ) dτ` is non-negative. -/
theorem integral_a_nonneg :
    0 ≤ ∫ τ in (0 : ℝ)..W.T, W.a τ :=
  intervalIntegral.integral_nonneg W.T_nonneg
    (fun τ _ => W.a_nonneg τ)

/-- Rapidity sweep is non-negative. -/
theorem rapiditySweep_nonneg : 0 ≤ W.rapiditySweep := by
  unfold rapiditySweep
  exact mul_nonneg (le_of_lt (one_div_pos.mpr W.c_pos)) W.integral_a_nonneg

/-- Accumulated entropic time is non-negative. -/
theorem entropicTime_nonneg : 0 ≤ W.entropicTime := by
  unfold entropicTime
  refine mul_nonneg ?_ W.integral_a_nonneg
  have h2πc : 0 < 2 * Real.pi * W.c :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) W.c_pos
  exact le_of_lt (one_div_pos.mpr h2πc)

/-! ## §3 — Load-bearing identity `Δτ_ent = Δη / (2π)` -/

/-- **Variable-acceleration identity** `Δτ_ent = Δη / (2π)`. The entropic
time is linear in the *total rapidity sweep*; the shape of `a(τ)` enters
only through the integral. -/
theorem entropicTime_eq_rapiditySweep_over_two_pi :
    W.entropicTime = W.rapiditySweep / (2 * Real.pi) := by
  unfold entropicTime rapiditySweep
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hc : W.c ≠ 0 := ne_of_gt W.c_pos
  field_simp

/-! ## §4 — Endpoint behaviour -/

/-- At `T = 0` the entropic time vanishes. -/
theorem entropicTime_zero_of_T_zero (h : W.T = 0) : W.entropicTime = 0 := by
  unfold entropicTime
  rw [h]
  simp

/-- At `T = 0` the rapidity sweep vanishes. -/
theorem rapiditySweep_zero_of_T_zero (h : W.T = 0) : W.rapiditySweep = 0 := by
  unfold rapiditySweep
  rw [h]
  simp

/-- Under identically-zero proper acceleration (inertial), the entropic
time vanishes. -/
theorem entropicTime_of_zero_acceleration (h : ∀ τ, W.a τ = 0) :
    W.entropicTime = 0 := by
  unfold entropicTime
  rw [intervalIntegral.integral_congr (g := fun _ => 0)
    (fun τ _ => h τ), intervalIntegral.integral_zero, mul_zero]

/-- Under identically-zero proper acceleration the rapidity sweep
vanishes. -/
theorem rapiditySweep_of_zero_acceleration (h : ∀ τ, W.a τ = 0) :
    W.rapiditySweep = 0 := by
  unfold rapiditySweep
  rw [intervalIntegral.integral_congr (g := fun _ => 0)
    (fun τ _ => h τ), intervalIntegral.integral_zero, mul_zero]

end RindlerWorldline

/-! ## §5 — Velocity form: `Δτ_ent = artanh(β_final) / (2π)` -/

namespace RindlerWorldline

variable (W : RindlerWorldline)

/-- **Final velocity** (starting from rest): `β_final = tanh(Δη)`. -/
def finalVelocity : ℝ := Real.tanh W.rapiditySweep

/-- Final velocity lies in `(−1, 1)`. -/
theorem finalVelocity_lt_one : W.finalVelocity < 1 := by
  unfold finalVelocity
  exact Real.tanh_lt_one _

theorem neg_one_lt_finalVelocity : -1 < W.finalVelocity := by
  unfold finalVelocity
  exact Real.neg_one_lt_tanh _

/-- **Entropic time in velocity form** (starting from rest):
`Δτ_ent = artanh(β_final) / (2π)`. -/
theorem entropicTime_eq_artanh_finalVelocity_over_two_pi :
    W.entropicTime = Real.artanh W.finalVelocity / (2 * Real.pi) := by
  unfold finalVelocity
  rw [Real.artanh_tanh]
  exact W.entropicTime_eq_rapiditySweep_over_two_pi

/-- Bridge to the existing rapidity-form identity: at `β_final = tanh η`,
`artanh(β_final) = Δη`. -/
theorem artanh_finalVelocity_eq_rapiditySweep :
    Real.artanh W.finalVelocity = W.rapiditySweep := by
  unfold finalVelocity
  exact Real.artanh_tanh _

end RindlerWorldline

/-! ## §6 — Constant-acceleration specialisation -/

/-- **Constant-acceleration Rindler worldline** with `a(τ) ≡ a₀`. -/
def RindlerWorldline.constant (a₀ c T : ℝ)
    (hc : 0 < c) (hT : 0 ≤ T) (ha₀ : 0 ≤ a₀) :
    RindlerWorldline where
  a := fun _ => a₀
  c := c
  T := T
  c_pos := hc
  T_nonneg := hT
  a_nonneg := fun _ => ha₀
  a_intervalIntegrable := intervalIntegrable_const

/-- Constant-acceleration rapidity sweep: `Δη = a₀ · T / c`. -/
theorem RindlerWorldline.rapiditySweep_constant (a₀ c T : ℝ)
    (hc : 0 < c) (hT : 0 ≤ T) (ha₀ : 0 ≤ a₀) :
    (RindlerWorldline.constant a₀ c T hc hT ha₀).rapiditySweep =
      a₀ * T / c := by
  unfold RindlerWorldline.rapiditySweep RindlerWorldline.constant
  simp [intervalIntegral.integral_const]
  ring

/-- Constant-acceleration entropic time: `Δτ_ent = a₀ · T / (2π c)`. -/
theorem RindlerWorldline.entropicTime_constant (a₀ c T : ℝ)
    (hc : 0 < c) (hT : 0 ≤ T) (ha₀ : 0 ≤ a₀) :
    (RindlerWorldline.constant a₀ c T hc hT ha₀).entropicTime =
      a₀ * T / (2 * Real.pi * c) := by
  unfold RindlerWorldline.entropicTime RindlerWorldline.constant
  simp [intervalIntegral.integral_const]
  ring

/-! ## §7 — Bridge to `UnruhEntropicRate` -/

/-- **Bridge to `UnruhEntropicRate`.** The constant-acceleration
`RindlerWorldline` reproduces the `UnruhEntropicRate.Δτ_ent` formula. -/
theorem RindlerWorldline.entropicTime_constant_eq_unruh
    (U : UnruhEntropicRate) :
    (RindlerWorldline.constant U.a U.c U.Δτ_geom U.c_pos U.Δτ_geom_nonneg
      U.a_nonneg).entropicTime = U.Δτ_ent := by
  rw [RindlerWorldline.entropicTime_constant U.a U.c U.Δτ_geom
    U.c_pos U.Δτ_geom_nonneg U.a_nonneg]
  unfold UnruhEntropicRate.Δτ_ent UnruhEntropicRate.lambdaU
  ring

end Physlib.Relativity.Special

end
