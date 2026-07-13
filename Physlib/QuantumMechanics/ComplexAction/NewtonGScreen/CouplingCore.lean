/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.VerlindeNewtonGravityCore
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Coupling core for the entropic screen: BCJ duality, the Einstein bit-coupling, the Poisson
reduction

The light coupling/gravity pieces the Newton-`G` screen derivation uses:

* `BCJDoubleCopy.ColorKinematicsDoubleCopy` — the `BCJColorKinematicsDuality` record;
* `Thermodynamics.GravitationalCouplingSystem` — the Einstein coupling in area-per-bit form
  `κ = 8πG/c⁴ = 8π(A/N)/(ℏc)`;
* `ComptonClock.NewtonianAndGRLimit` — the linearised Ricci `∂²Φ/c²` and the reduction of the
  trace-reversed Einstein equation to Newton's Poisson equation `∇²Φ = 4πGρ`.

Depends only on `VerlindeNewtonGravityCore` (`sphereArea`, `holographicBits`) and `Real.pi`.

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson, *New Relations for Gauge-Theory Amplitudes*, Phys. Rev.
  D **78** (2008) 085011, arXiv:0805.3993 — color–kinematics duality and the double copy.
* T. Jacobson, *Thermodynamics of Spacetime: The Einstein Equation of State*, Phys. Rev. Lett.
  **75** (1995) 1260, arXiv:gr-qc/9504004 — the Einstein equation in area-per-bit form.
* E. Verlinde, *On the Origin of Gravity and the Laws of Newton*, JHEP **04** (2011) 029 — the
  holographic screen and bit count.
* Newtonian limit of the Einstein equation: standard, e.g. R. M. Wald, *General Relativity*, Univ.
  Chicago Press (1984), §4.4a.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy

/-- **BCJ color–kinematics duality** for a three-channel `(s, t, u)` amplitude: the kinematic
numerators satisfy the *same* Jacobi identity `n_s + n_t + n_u = 0` as the color factors
`c_s + c_t + c_u = 0`. -/
structure BCJColorKinematicsDuality where
  /-- Color factor, `s`-channel. -/
  c_s : ℝ
  /-- Color factor, `t`-channel. -/
  c_t : ℝ
  /-- Color factor, `u`-channel. -/
  c_u : ℝ
  /-- Kinematic numerator, `s`-channel. -/
  n_s : ℝ
  /-- Kinematic numerator, `t`-channel. -/
  n_t : ℝ
  /-- Kinematic numerator, `u`-channel. -/
  n_u : ℝ
  /-- Jacobi identity for the color factors. -/
  color_jacobi : c_s + c_t + c_u = 0
  /-- Kinematic Jacobi identity — the BCJ duality condition. -/
  kinematic_jacobi : n_s + n_t + n_u = 0

end Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy

namespace Physlib.Thermodynamics.GravitationalCouplingSystem

open Physlib.Thermodynamics

/-- **The Einstein coupling at the isolated `G` is `8π` times the area-per-bit over `ℏc`**:
`κ = 8πG/c⁴ = 8π·(sphereArea R/N)/(ℏc)` when `N = holographicBits (sphereArea R) G ℏ c`. -/
lemma einsteinCoupling_bitForm (G ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hN : N = holographicBits (sphereArea R) G ℏ c) :
    8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  unfold holographicBits sphereArea at hN
  rw [hN]
  unfold sphereArea
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end Physlib.Thermodynamics.GravitationalCouplingSystem

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit

/-- **The linearised time-time Ricci component** `R₀₀ = ∂²_x Φ / c²` in the weak static field. -/
noncomputable def weakFieldRicci00 (d2Φ c : ℝ) : ℝ := d2Φ / c ^ 2

/-- **[Einstein ⇒ Newton] the field equation in the weak static limit is the Poisson equation**
`∇²Φ = 4πGρ`. -/
lemma weakField_einstein_poisson (d2Φ c G ρ : ℝ) (hc : c ≠ 0)
    (hEin : weakFieldRicci00 d2Φ c = 4 * Real.pi * G * ρ / c ^ 2) :
    d2Φ = 4 * Real.pi * G * ρ := by
  unfold weakFieldRicci00 at hEin
  rw [div_eq_div_iff (pow_ne_zero 2 hc) (pow_ne_zero 2 hc)] at hEin
  exact mul_right_cancel₀ (pow_ne_zero 2 hc) hEin

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit

end
