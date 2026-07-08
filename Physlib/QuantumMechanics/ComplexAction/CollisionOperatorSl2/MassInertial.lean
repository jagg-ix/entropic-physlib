/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannThermalOscillator

/-!
# Mass dependence of the Boltzmann collision operator and the Nagao–Nielsen inertial mass

This file formalizes the **mass dependence of Saveliev's linear Boltzmann collision operator**
(Saveliev 1996, §III, Eqs. 21–28) and proves it **links to the inertial (effective) mass of the
Nagao–Nielsen path integral and complex oscillator** (`PathIntegral.MomentumPathIntegral.effectiveMass`,
`ComplexOscillator.ComplexHarmonicOscillatorBoson`).

## Saveliev's mass dependence (§III)

The mass enters the collision operator through the parameter `ξ = log(1 + m)` (Eq. 21,
`m = m₁/m₂` the mass ratio), via the velocity star map `∇v∗` (another adjoint action), as a
one-parameter semigroup `exp(ξ ∇v∗)` (Eq. 25). On a `∇v∗`-eigenmode `μ` the mass semigroup is
`massMode μ ξ = e^{μ ξ}`, and at `ξ = log(1+m)` it is a **power of `1+m`**: `(1+m)^μ`
(`massMode_massLogParam`). The temperature enters the *same* operator through the diffusivity
`D = k/(2m₂)` (Eq. 15, `thermalDiffusivity`), and the temperature/mass generators commute
(Eq. 27).

## The link to the Nagao–Nielsen inertial mass

The diffusivity `D = k/(2m)` is the place the **mass** governs the collision operator. Feeding
the **Nagao–Nielsen inertial (effective) mass** `m_eff = m_R + m_I²/m_R`
(`PathIntegral.MomentumPathIntegral.effectiveMass`, Eq. 5.10) into it gives the collision operator's inertial
diffusivity, and the dissipative imaginary mass `m_I` has a definite effect:

* `collisionInertialDiffusivity_le_bare` — `D(m_eff) ≤ D(m_R)`: the imaginary mass **slows**
  thermal diffusion (more inertia).
* `collisionInertialDiffusivity_lt_bare` — `m_I ≠ 0 ⟹ D(m_eff) < D(m_R)`: *strictly* slower
  whenever there is a nonzero imaginary mass.
* `collisionInertialDiffusivity_reversible` — `D(m_eff)|_{m_I=0} = D(m_R)`: at the reversible /
  no-information point (`m_I = 0`, `m_eff = m_R`, `effectiveMass_eq_self_iff`) the inertial
  correction vanishes and the collision operator's mass dependence is the bare one.

So Saveliev's collision-operator diffusivity, evaluated on the Nagao–Nielsen inertial mass,
sees the imaginary mass `m_I` as added inertia — the same `m_I` whose vanishing is the
reversible / `S_I = 0` / `Im λ = 0` point of the whole arc. (For a *massless* boson `m_R = 0`,
`m_eff` is singular, `effectiveMass_eq_normSq_div`; the inertial scale is then the Wick-rotated
`m_I` / thermal mass of `MassOrigin.BosonicInertialMass`.)

## References

* V. Saveliev, J. Math. Phys. 37 (1996) 6139, §III, Eqs. 21–28 (mass dependence, `ξ = log(1+m)`).
* K. Nagao, H. B. Nielsen, arXiv:1304.4017, Eq. 5.10 (`m_eff`); arXiv:1902.01424 (oscillator).
* `PathIntegral.MomentumPathIntegral`, `StatisticalMechanics.BoltzmannThermalOscillator`, `ComplexOscillator.ComplexHarmonicOscillatorBoson`,
  `MassOrigin.BosonicInertialMass` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannThermalOscillator

namespace Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.MassInertial

/-! ## §A — the mass-dependence semigroup `exp(ξ ∇v∗)` (Saveliev §III) -/

/-- **The mass-transformation semigroup on a `∇v∗`-eigenmode** `μ`: `massMode μ ξ = e^{μ ξ}`,
the eigenvalue of Saveliev's `exp(ξ ∇v∗)` (Eq. 25). -/
def massMode (μ ξ : ℝ) : ℝ := Real.exp (μ * ξ)

/-- **Identity at `ξ = 0`** (mass ratio `m = 0`, infinitely heavy scattering centers). -/
theorem massMode_zero (μ : ℝ) : massMode μ 0 = 1 := by
  unfold massMode; simp

/-- **Additive one-parameter semigroup** `massMode μ (ξ₁+ξ₂) = massMode μ ξ₁ · massMode μ ξ₂`. -/
theorem massMode_add (μ ξ₁ ξ₂ : ℝ) :
    massMode μ (ξ₁ + ξ₂) = massMode μ ξ₁ * massMode μ ξ₂ := by
  unfold massMode
  rw [← Real.exp_add]; congr 1; ring

/-- **The mass dependence is a power of `1+m`**: `massMode μ (log(1+m)) = (1+m)^μ` (Saveliev
`ξ = log(1+m)`, Eq. 21). -/
theorem massMode_massLogParam (μ m : ℝ) (hm : -1 < m) :
    massMode μ (massLogParam m) = (1 + m) ^ μ := by
  unfold massMode massLogParam
  rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < 1 + m), mul_comm]

/-! ## §B — the collision operator's diffusivity on the Nagao–Nielsen inertial mass -/

/-- **The collision operator's inertial diffusivity** `D(m_eff) = k/(2 m_eff)` — Saveliev's
temperature diffusivity (Eq. 15) evaluated on the Nagao–Nielsen inertial (effective) mass
`m_eff = m_R + m_I²/m_R`. -/
def collisionInertialDiffusivity (kB m_R m_I : ℝ) : ℝ :=
  thermalDiffusivity kB (effectiveMass m_R m_I)

/-- **The imaginary mass slows thermal diffusion** (more inertia): `D(m_eff) ≤ D(m_R)`. -/
theorem collisionInertialDiffusivity_le_bare (kB m_R m_I : ℝ) (hkB : 0 < kB) (hm_R : 0 < m_R) :
    collisionInertialDiffusivity kB m_R m_I ≤ thermalDiffusivity kB m_R := by
  unfold collisionInertialDiffusivity thermalDiffusivity
  have hge : m_R ≤ effectiveMass m_R m_I := effectiveMass_ge m_R m_I hm_R
  gcongr

/-- **A nonzero imaginary mass strictly slows diffusion**: `m_I ≠ 0 ⟹ D(m_eff) < D(m_R)`. -/
theorem collisionInertialDiffusivity_lt_bare (kB m_R m_I : ℝ) (hkB : 0 < kB) (hm_R : 0 < m_R)
    (hm_I : m_I ≠ 0) :
    collisionInertialDiffusivity kB m_R m_I < thermalDiffusivity kB m_R := by
  unfold collisionInertialDiffusivity thermalDiffusivity
  have hgt : m_R < effectiveMass m_R m_I := by
    unfold effectiveMass
    have : (0 : ℝ) < m_I ^ 2 / m_R := by positivity
    linarith
  gcongr

/-- **Reversible limit**: at `m_I = 0` (`m_eff = m_R`, the no-information point) the inertial
diffusivity is the bare diffusivity — no inertial correction. -/
theorem collisionInertialDiffusivity_reversible (kB m_R : ℝ) :
    collisionInertialDiffusivity kB m_R 0 = thermalDiffusivity kB m_R := by
  unfold collisionInertialDiffusivity thermalDiffusivity effectiveMass
  norm_num

/-- **The inertial correction vanishes iff `m_I = 0`**: `m_eff = m_R ⟺ m_I = 0`
(`PathIntegral.MomentumPathIntegral.effectiveMass_eq_self_iff`) — the collision operator's mass dependence
reduces to the bare one exactly at the reversible / no-information point. -/
theorem inertialCorrection_eq_zero_iff (m_R m_I : ℝ) (hm_R : m_R ≠ 0) :
    effectiveMass m_R m_I = m_R ↔ m_I = 0 :=
  effectiveMass_eq_self_iff m_R m_I hm_R

end Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.MassInertial

end
