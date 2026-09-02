/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Order.Filter.AtTopBot.Field

/-!
# The thermal Rindler-wedge geometric modular flow (Caminiti–Capeccia–Ciambelli–Myers)

The spacetime modular arc of this repository — `KazamaTomitaTakesakiModular`,
`EntropicClockImaginaryModularTime`, `HolographicGravityFromModularFlow` — carries the *vacuum* Rindler
modular flow, which by Bisognano–Wichmann is the boost `ξ = x ∂_t + t ∂_x`
(`AlgebraicQFT.SummersRelativisticVacuum.modularBoost`). Caminiti, Capeccia, Ciambelli and Myers,
*Geometric modular flows in 2d CFT and beyond* (JHEP 08 (2025) 166, arXiv:2502.02633), study the whole
family of geometric modular flows. Their eq. (1.7) is the geometric modular flow of the **thermal** state
of a 2d CFT reduced to the right Rindler wedge, at inverse temperature `β`:

  `ξ = (β/2π) [ (1 − e^{−2πx/β} cosh(2πt/β)) ∂_t  +  e^{−2πx/β} sinh(2πt/β) ∂_x ]`.

This module formalizes that vector field and the two limits that make it the interpolation between the
Unruh boost and thermality.

* `thermalModularTime`, `thermalModularSpace` — the two components of eq. (1.7).
* `thermalModular_fixed_at_bifurcation` — both components vanish at the bifurcation point `t = x = 0`
  (the Rindler horizon edge is a fixed point of the flow), exactly.
* `thermalModular_thermal_limit_time`, `thermalModular_thermal_limit_space` — the **thermal end**: as
  `x → ∞` the flow approaches the constant time translation `ξ → (β/2π) ∂_t`, the signature of the
  underlying thermal state (`ξ_x → 0`, `ξ_t → β/2π`).
* `thermalModular_vacuum_boost_limit_time`, `thermalModular_vacuum_boost_limit_space` — the **boost end**:
  as `β → ∞` (zero temperature) the flow reduces to the vacuum Rindler boost `ξ → x ∂_t + t ∂_x` of
  eq. (1.6), recovering the Bisognano–Wichmann modular flow of the arc.

So the single number `β` interpolates: the vacuum boost (Unruh, our Bisognano–Wichmann sector,
`β → ∞`) and the constant thermal translation (`x → ∞`), the two ends observers on the flow can
experience. The KMS periodicity `s ~ s + i` ⟺ imaginary time `t ~ t + iβ` that both share is the
`EntropicClockImaginaryModularTime` identity. Only the classical vector field and its two limits are
formalized here, not the full CFT construction (conformal unitaries, the entanglement-entropy formula).
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ThermalGeometricModularFlow

open Filter Topology

/-- **Time component of the thermal geometric modular flow** (Caminiti–Ciambelli–Myers eq. 1.7):
`ξ^t = (β/2π)(1 − e^{−2πx/β} cosh(2πt/β))`. -/
noncomputable def thermalModularTime (β t x : ℝ) : ℝ :=
  β / (2 * Real.pi) *
    (1 - Real.exp (-(2 * Real.pi * x) / β) * Real.cosh (2 * Real.pi * t / β))

/-- **Space component of the thermal geometric modular flow** (eq. 1.7):
`ξ^x = (β/2π) e^{−2πx/β} sinh(2πt/β)`. -/
noncomputable def thermalModularSpace (β t x : ℝ) : ℝ :=
  β / (2 * Real.pi) *
    (Real.exp (-(2 * Real.pi * x) / β) * Real.sinh (2 * Real.pi * t / β))

/-- **The bifurcation point is a fixed point.**  At the Rindler horizon edge `t = x = 0` both components
of the thermal modular flow vanish — exactly, at any temperature. -/
theorem thermalModular_fixed_at_bifurcation (β : ℝ) :
    thermalModularTime β 0 0 = 0 ∧ thermalModularSpace β 0 0 = 0 := by
  constructor <;> simp [thermalModularTime, thermalModularSpace]

/-- The exponential redshift factor `e^{−2πx/β} → 0` as `x → ∞` (for `β > 0`). -/
private theorem tendsto_redshift_atTop (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun x : ℝ => Real.exp (-(2 * Real.pi * x) / β)) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have hrw : (fun x : ℝ => -(2 * Real.pi * x) / β) = (fun x => (-(2 * Real.pi) / β) * x) := by
    funext x; ring
  rw [hrw]
  have hr : (-(2 * Real.pi) / β) < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr (by positivity)) hβ
  exact (tendsto_const_mul_atBot_of_neg hr).mpr tendsto_id

/-- **The thermal end of the flow, time component.**  As `x → ∞` the flow approaches the constant time
translation: `ξ^t → β/2π`, the signature of the underlying thermal state. -/
theorem thermalModular_thermal_limit_time (β t : ℝ) (hβ : 0 < β) :
    Tendsto (fun x => thermalModularTime β t x) atTop (𝓝 (β / (2 * Real.pi))) := by
  have h2 : Tendsto (fun x => Real.exp (-(2 * Real.pi * x) / β) * Real.cosh (2 * Real.pi * t / β))
      atTop (𝓝 0) := by
    simpa using (tendsto_redshift_atTop β hβ).mul_const (Real.cosh (2 * Real.pi * t / β))
  have h3 : Tendsto
      (fun x => 1 - Real.exp (-(2 * Real.pi * x) / β) * Real.cosh (2 * Real.pi * t / β))
      atTop (𝓝 1) := by
    simpa using h2.const_sub 1
  simpa [thermalModularTime] using h3.const_mul (β / (2 * Real.pi))

/-- **The thermal end of the flow, space component.**  As `x → ∞` the space component vanishes:
`ξ^x → 0`. -/
theorem thermalModular_thermal_limit_space (β t : ℝ) (hβ : 0 < β) :
    Tendsto (fun x => thermalModularSpace β t x) atTop (𝓝 0) := by
  have h2 : Tendsto (fun x => Real.exp (-(2 * Real.pi * x) / β) * Real.sinh (2 * Real.pi * t / β))
      atTop (𝓝 0) := by
    simpa using (tendsto_redshift_atTop β hβ).mul_const (Real.sinh (2 * Real.pi * t / β))
  simpa [thermalModularSpace] using h2.const_mul (β / (2 * Real.pi))

/-- Reparametrization `u = 2π/β → 0` (through nonzero values) as `β → ∞`. -/
private theorem tendsto_reparam :
    Tendsto (fun β : ℝ => 2 * Real.pi / β) atTop (𝓝[≠] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (2 * Real.pi)
  · filter_upwards [eventually_gt_atTop 0] with β hβ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (by positivity : (0 : ℝ) < 2 * Real.pi / β).ne'

/-- **The boost end of the flow, space component.**  As `β → ∞` (zero temperature) the space component
reduces to the vacuum Rindler boost `ξ^x → t` of eq. (1.6) — the Bisognano–Wichmann modular flow. -/
theorem thermalModular_vacuum_boost_limit_space (t x : ℝ) :
    Tendsto (fun β => thermalModularSpace β t x) atTop (𝓝 t) := by
  have h1 : HasDerivAt (fun u : ℝ => t * u) t 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul t
  have hsinh : HasDerivAt (fun u : ℝ => Real.sinh (t * u)) t 0 := by
    simpa [Real.cosh_zero] using h1.sinh
  have hslope : Tendsto (fun u : ℝ => Real.sinh (t * u) / u) (𝓝[≠] 0) (𝓝 t) := by
    have h := hasDerivAt_iff_tendsto_slope.mp hsinh
    rw [slope_fun_def_field] at h
    simpa [Real.sinh_zero, mul_zero, sub_zero] using h
  have hexp1 : Tendsto (fun β : ℝ => Real.exp (-(2 * Real.pi * x) / β)) atTop (𝓝 1) := by
    have harg : Tendsto (fun β : ℝ => -(2 * Real.pi * x) / β) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (-(2 * Real.pi * x))
    have h := (Real.continuous_exp.tendsto 0).comp harg
    rwa [Real.exp_zero] at h
  have hmul := (hslope.comp tendsto_reparam).mul hexp1
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with β hβ
  have hβ0 : β ≠ 0 := hβ.ne'
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  simp only [thermalModularSpace, Function.comp_apply]
  rw [show t * (2 * Real.pi / β) = 2 * Real.pi * t / β by ring]
  field_simp

/-- **The boost end of the flow, time component.**  As `β → ∞` (zero temperature) the time component
reduces to the vacuum Rindler boost `ξ^t → x` of eq. (1.6) — the Bisognano–Wichmann modular flow. -/
theorem thermalModular_vacuum_boost_limit_time (t x : ℝ) :
    Tendsto (fun β => thermalModularTime β t x) atTop (𝓝 x) := by
  have h1x : HasDerivAt (fun u : ℝ => -x * u) (-x) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-x)
  have h1t : HasDerivAt (fun u : ℝ => t * u) t 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul t
  have he : HasDerivAt (fun u : ℝ => Real.exp (-x * u)) (-x) 0 := by
    simpa using h1x.exp
  have hc : HasDerivAt (fun u : ℝ => Real.cosh (t * u)) 0 0 := by
    simpa [Real.sinh_zero] using h1t.cosh
  have hG : HasDerivAt (fun u : ℝ => 1 - Real.exp (-x * u) * Real.cosh (t * u)) x 0 := by
    have hp := he.mul hc
    simp only [Real.cosh_zero, mul_zero, Real.exp_zero, mul_one, add_zero] at hp
    simpa using hp.const_sub 1
  have hslope : Tendsto (fun u : ℝ => (1 - Real.exp (-x * u) * Real.cosh (t * u)) / u)
      (𝓝[≠] 0) (𝓝 x) := by
    have h := hasDerivAt_iff_tendsto_slope.mp hG
    rw [slope_fun_def_field] at h
    simpa [Real.exp_zero, Real.cosh_zero, mul_zero, mul_one, sub_self, sub_zero] using h
  refine (hslope.comp tendsto_reparam).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with β hβ
  have hβ0 : β ≠ 0 := hβ.ne'
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  simp only [thermalModularTime, Function.comp_apply]
  rw [show -x * (2 * Real.pi / β) = -(2 * Real.pi * x) / β by ring,
      show t * (2 * Real.pi / β) = 2 * Real.pi * t / β by ring]
  field_simp

end Physlib.QuantumMechanics.ComplexAction.ThermalGeometricModularFlow

end
