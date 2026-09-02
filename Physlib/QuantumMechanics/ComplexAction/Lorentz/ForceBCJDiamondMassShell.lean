/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamond

/-!
# The Lorentz-BCJ diamond dual encodes the mass shell and is subluminal

Building on `Lorentz.ForceBCJDiamond`, where the Lorentz-force gravitational dual at the diamond mode is the
squared diamond velocity `lorentzForceDual = tanh²θ` (with propagator the diamond horizon energy squared
`cosh²θ`).  Two consequences of that identification:

* **Mass-shell completeness.**  `tanh²θ + sech²θ = 1`, i.e.
  `lorentzForceDual + 1/cosh²θ = 1` — the gravitational dual plus the reciprocal mass-shell propagator is
  unity.  This is exactly the diamond mass shell `cosh²θ − sinh²θ = 1` (the Nagao–Nielsen cone
  `lorentzianForm = p² − q²` the temporal-orientation `T` preserves), rewritten on the gravity side.  The
  same completeness holds for the diamond BCJ double-copy diagonal.

* **Subluminality.**  `0 ≤ lorentzForceDual < 1` — the squared diamond velocity is a genuine (subluminal)
  velocity², bounded strictly below the light cone `1`.

* **Lorentz factor.**  Since the dual is the squared velocity `v² = tanh²θ`, the reciprocal Lorentz factor
  is `1 − v² = sech²θ` and the mass-shell propagator is the Lorentz factor `γ² = cosh²θ = 1/(1 − v²)` — the
  BCJ double copy reconstructs the full relativistic kinematics of the diamond mode.

* `diamond_dual_massShell` — `lorentzForceDual + 1/cosh²θ = 1`.
* `diamondBCJ_diagonal_massShell` — the same for the BCJ double-copy diagonal.
* `diamond_dual_mem_Ico` — `0 ≤ lorentzForceDual < 1`.
* `diamond_dual_one_sub` — `1 − lorentzForceDual = 1/cosh²θ` (the reciprocal Lorentz factor `1 − v²`).
* `diamond_lorentzFactor` — `cosh²θ = 1/(1 − lorentzForceDual)` (the Lorentz factor `γ²` from the dual).

The Lorentz-force numerator is the diamond **momentum** `p = sinh θ` and the propagator the **energy²**
`E² = cosh²θ`, so the mass shell is the on-shell relation `E² − p² = 1` and the velocity is `v = p/E`:

* `diamond_energyMomentum_massShell` — `E² − p² = 1` (the on-shell condition with unit rest mass).
* `diamond_velocity_eq_momentum_over_energy` — `p/E = tanh θ` (velocity = momentum/energy).
* `diamond_dual_eq_momentum_over_energy_sq` — `lorentzForceDual = (p/E)²`.
* `diamond_velocity_magnitude` — `√lorentzForceDual = |tanh θ|` (the unsigned diamond velocity).

Honest scope: algebraic hyperbolic identities at the diamond mode built on `ForceBCJDiamond`; no new
dynamical content beyond the mass shell, the velocity bound, the Lorentz factor and the energy-momentum
on-shell relation.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamondMassShell

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DiamondTimeReversal
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamond

/-- **[Mass-shell completeness] `lorentzForceDual + 1/cosh²θ = 1`.**  The Lorentz-force gravitational dual at
the diamond mode (`tanh²θ`) plus the reciprocal mass-shell propagator (`sech²θ`) is unity — the diamond mass
shell `cosh²θ − sinh²θ = 1` rewritten on the gravity side. -/
theorem diamond_dual_massShell (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4) (θ : ℝ)
    (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2)
      + 1 / (bogoliubovEnergy (Real.sinh θ) 1 ^ 2) = 1 := by
  have hc : Real.cosh θ ≠ 0 := (Real.cosh_pos θ).ne'
  rw [lorentzForceDual_eq_diamond_velocity_sq F V μ θ hnum, diamond_horizon_energy,
    Real.tanh_eq_sinh_div_cosh, div_pow]
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq θ]

/-- **[BCJ diagonal mass shell] The diamond BCJ double-copy diagonal satisfies the same completeness** —
`(diamondBCJTriple θ).numerator²/(diamondBCJTriple θ).propagator + 1/cosh²θ = 1`.  The gravity-side amplitude
of the double copy encodes the diamond mass shell. -/
theorem diamondBCJ_diagonal_massShell (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4) (θ : ℝ)
    (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    (diamondBCJTriple θ).numerator ^ 2 / (diamondBCJTriple θ).propagator
      + 1 / (bogoliubovEnergy (Real.sinh θ) 1 ^ 2) = 1 := by
  rw [← lorentzForceDual_eq_diamondBCJ F V μ θ hnum]
  exact diamond_dual_massShell F V μ θ hnum

/-- **[Subluminal] `0 ≤ lorentzForceDual < 1`.**  The squared diamond velocity `tanh²θ` is a genuine
velocity², non-negative and strictly below the light cone `1`. -/
theorem diamond_dual_mem_Ico (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4) (θ : ℝ)
    (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    0 ≤ lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2)
      ∧ lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2) < 1 := by
  rw [lorentzForceDual_eq_diamond_velocity_sq F V μ θ hnum]
  exact ⟨sq_nonneg _, by nlinarith [Real.tanh_lt_one θ, Real.neg_one_lt_tanh θ]⟩

/-- **[Reciprocal Lorentz factor] `1 − lorentzForceDual = 1/cosh²θ`.**  One minus the squared diamond
velocity `1 − v²` is the reciprocal Lorentz factor `sech²θ` — a rearrangement of the mass-shell
completeness. -/
theorem diamond_dual_one_sub (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4) (θ : ℝ)
    (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    1 - lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2)
      = 1 / (bogoliubovEnergy (Real.sinh θ) 1 ^ 2) := by
  have h := diamond_dual_massShell F V μ θ hnum
  linarith

/-- **[Lorentz factor] `cosh²θ = 1/(1 − lorentzForceDual)`.**  The mass-shell propagator (diamond horizon
energy squared) is the Lorentz factor `γ² = 1/(1 − v²)` reconstructed from the gravitational dual — the BCJ
double copy recovers the full relativistic kinematics of the diamond mode. -/
theorem diamond_lorentzFactor (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4) (θ : ℝ)
    (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    bogoliubovEnergy (Real.sinh θ) 1 ^ 2
      = 1 / (1 - lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2)) := by
  rw [diamond_dual_one_sub F V μ θ hnum, one_div_one_div]

/-- **[On-shell `E² − p² = 1`] The diamond mass shell in energy-momentum form.**  The Lorentz-force numerator
is the diamond momentum `p = sinh θ` and the propagator is the energy squared `E² = cosh²θ`, so
`E² − p² = 1` — the relativistic mass shell `E² − p² = m²` at unit rest mass. -/
theorem diamond_energyMomentum_massShell (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4) (θ : ℝ)
    (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    bogoliubovEnergy (Real.sinh θ) 1 ^ 2 - lorentzForceNum F V μ ^ 2 = 1 := by
  unfold lorentzForceNum
  rw [hnum, diamond_horizon_energy]
  exact Real.cosh_sq_sub_sinh_sq θ

/-- **[Velocity = momentum/energy] `p/E = tanh θ`.**  The diamond velocity is the Lorentz-force numerator
over the horizon energy — momentum over energy. -/
theorem diamond_velocity_eq_momentum_over_energy (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4)
    (θ : ℝ) (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    lorentzForceNum F V μ / bogoliubovEnergy (Real.sinh θ) 1 = Real.tanh θ := by
  unfold lorentzForceNum
  rw [hnum, diamond_horizon_energy, Real.tanh_eq_sinh_div_cosh]

/-- **[Dual = (p/E)²] The gravitational dual is the squared momentum-to-energy ratio** `v² = (p/E)²`. -/
theorem diamond_dual_eq_momentum_over_energy_sq (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4)
    (θ : ℝ) (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2)
      = (lorentzForceNum F V μ / bogoliubovEnergy (Real.sinh θ) 1) ^ 2 := by
  rw [lorentzForceDual_eq_diamond_velocity_sq F V μ θ hnum,
    diamond_velocity_eq_momentum_over_energy F V μ θ hnum]

/-- **[Velocity magnitude] `√lorentzForceDual = |tanh θ|`.**  The unsigned diamond velocity is the square
root of the gravitational dual. -/
theorem diamond_velocity_magnitude (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4) (θ : ℝ)
    (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    Real.sqrt (lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2)) = |Real.tanh θ| := by
  rw [lorentzForceDual_eq_diamond_velocity_sq F V μ θ hnum, Real.sqrt_sq_eq_abs]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamondMassShell

end
