/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.VerlindeEntropicForce
public import Physlib.Relativity.SemiClassical.EinsteinEquationAsThermodynamicIdentity
public import Physlib.QuantumMechanics.ComplexAction.VanDerWaalsPolarizabilityScaling
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence

/-!
# The force-scale welds

Pairwise welds among four force carriers from four sectors — `newtonForce` (`GMm/r²`),
`verlindeEntropicForce` (`T·ΔS/Δx`), `horizonEnergyRate` (`c⁴/2G` — the maximum-force
scale of general relativity, `dE/da` of the Einstein-equation-as-thermodynamic-identity
derivation), and the van der Waals `dispersionForce` (`−(9/2)A/R⁷`).
`#zil_groupoid_report` found all six edges dimensionally homogeneous (the multiplicative
unifier normalizes the dispersion force's sign) with only the Newton–entropic edge proven.
The five welds below close the rest; the headline is the maximum-force saturation
`2G²Mm = c⁴r²` — Newton's inverse-square force *reaches* the relativistic force bound
`c⁴/2G` exactly at the gravitational-radius geometric mean `r² = 2·(GM/c²)(Gm/c²)`.
Guarded by `Physlib.Meta.ForceQuadGate`.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ForceScaleWelds

open Physlib.Thermodynamics
open Physlib.Relativity.SemiClassical.EinsteinEquationAsThermodynamicIdentity
open Physlib.QuantumMechanics.ComplexAction.VanDerWaalsPolarizabilityScaling
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence

/-- **Newton saturates the maximum force exactly at `2G²Mm = c⁴r²`** — the separation is the
geometric mean of the two gravitational radii (`r² = 2·λ_g(M)·λ_g(m)` in the
`ZeroPointLength` vocabulary): inside it, the inverse-square force exceeds `c⁴/2G`. -/
theorem newtonForce_eq_horizonEnergyRate_iff {G M m r c : ℝ}
    (hG : 0 < G) (hr : 0 < r) :
    newtonForce G M m r = horizonEnergyRate c G ↔ 2 * G ^ 2 * M * m = c ^ 4 * r ^ 2 := by
  unfold newtonForce horizonEnergyRate
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    exact mul_right_cancel₀ (show (1 : ℝ) ≠ 0 by norm_num)
      (show 2 * G ^ 2 * M * m * 1 = c ^ 4 * r ^ 2 * 1 by linear_combination h)
  · intro h
    linear_combination h

/-- **The entropic force reaches the maximum force exactly at `2G·TΔS = c⁴·Δx`** — the
displacement across which an entropy drop `ΔS` at temperature `T` can exert the
relativistic bound. -/
theorem verlindeEntropicForce_eq_horizonEnergyRate_iff {T ΔS Δx c G : ℝ}
    (hΔx : 0 < Δx) (hG : 0 < G) :
    verlindeEntropicForce T ΔS Δx = horizonEnergyRate c G
      ↔ 2 * G * (T * ΔS) = c ^ 4 * Δx := by
  unfold verlindeEntropicForce horizonEnergyRate
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor <;> intro h <;> linear_combination h

/-- **The gravity–dispersion crossover: `2GMm·R⁷ = −9A·r²`** — where the inverse-square
attraction matches the van der Waals `R⁻⁷` force (attractive for `A < 0` in this
convention), the colloid/AFM crossover scale as a rest-point weld. -/
theorem newtonForce_eq_dispersionForce_iff {G M m r A R : ℝ}
    (hr : 0 < r) (hR : 0 < R) :
    newtonForce G M m r = dispersionForce A R
      ↔ 2 * (G * M * m) * R ^ 7 = -(9 * A) * r ^ 2 := by
  unfold newtonForce dispersionForce
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h; linear_combination 2 * h
  · intro h; linear_combination h / 2

/-- **The entropic–dispersion crossover: `2TΔS·R⁷ = −9A·Δx`.** -/
theorem verlindeEntropicForce_eq_dispersionForce_iff {T ΔS Δx A R : ℝ}
    (hΔx : 0 < Δx) (hR : 0 < R) :
    verlindeEntropicForce T ΔS Δx = dispersionForce A R
      ↔ 2 * (T * ΔS) * R ^ 7 = -(9 * A) * Δx := by
  unfold verlindeEntropicForce dispersionForce
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h; linear_combination 2 * h
  · intro h; linear_combination h / 2

/-- **The dispersion force at the maximum force: `c⁴·R⁷ = −9GA`** — the (sub-ångström for
laboratory Hamaker constants) separation at which van der Waals attraction would reach the
relativistic bound. -/
theorem dispersionForce_eq_horizonEnergyRate_iff {A R c G : ℝ}
    (hR : 0 < R) (hG : 0 < G) :
    dispersionForce A R = horizonEnergyRate c G ↔ c ^ 4 * R ^ 7 = -(9 * G * A) := by
  unfold dispersionForce horizonEnergyRate
  rw [div_eq_div_iff (by positivity) (by positivity)]
  constructor <;> intro h <;> linear_combination -h

end Physlib.QuantumMechanics.ComplexAction.ForceScaleWelds
