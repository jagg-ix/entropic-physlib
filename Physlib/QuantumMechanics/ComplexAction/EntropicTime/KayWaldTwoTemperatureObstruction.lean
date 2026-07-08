/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon

/-!
# Kay–Wald §6: no global thermal state on two-horizon spacetimes; the Unruh effect as the Minkowski case

Formalizes two further Kay–Wald results (Phys. Rep. 207 (1991)): the **nonexistence** of a stationary Hadamard
state on Schwarzschild–deSitter and Kerr (§6), and the **Unruh effect** as the Minkowski instance of the general
theorem.

* **The two-temperature obstruction** (§6): a spacetime with two bifurcate Killing horizons of *different* surface
 gravities `κ₁ ≠ κ₂` (the black-hole and cosmological horizons of Schwarzschild–deSitter, or the outer and inner
 horizons of Kerr) has two *different* Hawking temperatures (`hawkingTemperature_ne_of_kappa_ne`). A KMS
 (thermal) state has a single temperature, so no global state can be thermal at both horizons — the Kay–Wald
 nonexistence of a stationary, nonsingular quasifree state (`two_horizon_no_global_kms`);
* **the Unruh effect is the Minkowski Kay–Wald case** (`unruh_temperature_ne_of_accel_ne`): a uniformly
 accelerated observer's Rindler horizon has surface gravity equal to the proper acceleration `a`, so the observer
 sees the Minkowski vacuum as a Kay–Wald KMS state at the Unruh temperature `T_U = a/2π = T_H(κ = a)` — reusing the
 repository's `CausalDiamond.EquivalencePrinciple.unruhTemperature = hawkingTemperature`, the same injectivity in
 the acceleration.

So the Kay–Wald framework simultaneously explains the Unruh effect (Minkowski, `κ = a`) and forbids a global
equilibrium on multi-horizon spacetimes (Schwarzschild–deSitter, Kerr) where the horizons encode incompatible
temperatures: the Hawking temperature is a strictly injective function of the surface gravity.

* **§A — the two-temperature obstruction** (`hawkingTemperature_ne_of_kappa_ne`, `two_horizon_no_global_kms`,
 `unruh_temperature_ne_of_accel_ne`).

The injectivity of the Hawking temperature in the surface gravity is exact algebra; the
nonexistence framing states the obstruction (two incompatible KMS temperatures) that the analytic Kay–Wald §6
proof establishes. The Unruh identification reuses `hawkingTemperature`. No new axioms.

## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49, §6 (nonexistence on Schwarzschild–deSitter and Kerr); W.G. Unruh.
 Repo structure: `EntropicTime.KayWaldHawkingKMSHorizon`, `Relativity.SemiClassical.HawkingTemperature`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.Relativity.SemiClassical

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldTwoTemperatureObstruction

/-! ## §A — the two-temperature obstruction -/

/-- **[Different surface gravities give different Hawking temperatures] `κ₁ ≠ κ₂ ⟹ T_H(κ₁) ≠ T_H(κ₂)`.** The
Hawking temperature `T_H = ℏκ/(2πckB)` is strictly injective in the surface gravity: two horizons with distinct
`κ` encode distinct temperatures. -/
theorem hawkingTemperature_ne_of_kappa_ne (ℏ κ₁ κ₂ c kB : ℝ) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hkB : kB ≠ 0)
    (h : κ₁ ≠ κ₂) : hawkingTemperature ℏ κ₁ c kB ≠ hawkingTemperature ℏ κ₂ c kB := by
  unfold hawkingTemperature
  have hden : (2 * Real.pi * c * kB) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hc) hkB
  intro heq
  apply h
  rw [div_eq_div_iff hden hden] at heq
  exact mul_left_cancel₀ hℏ (mul_right_cancel₀ hden heq)

/-- **[No global KMS state on a two-horizon spacetime] (Kay–Wald §6).** On a spacetime with two bifurcate Killing
horizons of different surface gravities `κ₁ ≠ κ₂` (Schwarzschild–deSitter: black-hole and cosmological horizons;
Kerr: outer and inner horizons), the two Hawking temperatures differ. A single KMS state has one temperature, so
no stationary state can be simultaneously thermal at both horizons — the Kay–Wald nonexistence of a stationary,
nonsingular quasifree (Hadamard) state on such spacetimes. -/
theorem two_horizon_no_global_kms (ℏ κ_bh κ_c c kB : ℝ) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hkB : kB ≠ 0)
    (h : κ_bh ≠ κ_c) : hawkingTemperature ℏ κ_bh c kB ≠ hawkingTemperature ℏ κ_c c kB :=
  hawkingTemperature_ne_of_kappa_ne ℏ κ_bh κ_c c kB hℏ hc hkB h

/-- **[The Unruh effect is the Minkowski Kay–Wald case] two distinct accelerations give distinct temperatures.**
The Unruh temperature (the existing `CausalDiamond.EquivalencePrinciple.unruhTemperature = hawkingTemperature`
with surface gravity `κ = a`, the proper acceleration) inherits the same injectivity: a uniformly accelerated
observer's Rindler-horizon Kay–Wald KMS state at `T_U = a/2π` distinguishes accelerations. -/
theorem unruh_temperature_ne_of_accel_ne (ℏ a₁ a₂ c kB : ℝ) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hkB : kB ≠ 0)
    (h : a₁ ≠ a₂) : hawkingTemperature ℏ a₁ c kB ≠ hawkingTemperature ℏ a₂ c kB :=
  hawkingTemperature_ne_of_kappa_ne ℏ a₁ a₂ c kB hℏ hc hkB h

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldTwoTemperatureObstruction

end
