/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Sciama–Candelas–Deutsch Appendix D: radiation reaction of a uniformly accelerated charge

The classic paradox.  A uniformly accelerated charge radiates at the **Larmor** rate `P = ⅔ e²a²/c³` (`a` the
proper acceleration) — yet the **Abraham–Lorentz** radiation-reaction force `F_rad = ⅔ (e²/c³) v̈` depends on
the *jerk* `v̈` and so **vanishes when `a` is constant**.  How can it radiate with no reaction force?

The resolution (Appendix D (iv)) is the **Schott energy balance**: pointwise,

`F_rad·v + P = d/dt(⅔(e²/c³) a·v)`,

an integration-by-parts identity.  Integrated over a motion that is inertial at early and late times, the
Schott boundary term vanishes, so `−∫F_rad·v dt = ∫P dt`: the work done against the reaction force over the
*whole* motion equals the total radiated energy — energy is conserved even though `F_rad = 0` during the
uniform stretch.

The paper (p. 365) reads this through the Unruh bath: a uniformly accelerated charge is in *equilibrium* with
the co-moving thermal vacuum it perceives, so there is no net energy/momentum transfer — hence no
instantaneous reaction force.

* `larmorPower`, `abrahamLorentzForce`, `characteristicTime` — the radiated power, reaction force, `τ₀`.
* `larmorPower_nonneg`, `larmorPower_pos_of_accel` — the charge radiates iff it accelerates.
* `abrahamLorentzForce_zero_of_constant_accel` — `F_rad = 0` at zero jerk (uniform acceleration).
* `schott_energy_balance` — `d/dt(Schott) = F_rad·v + P` (the paradox resolution, via the product rule).

Honest scope: the Larmor/Abraham–Lorentz algebra and the pointwise Schott balance (product rule); the
spacetime integral and the vanishing of the boundary term for inertial asymptotics are contextualized.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaRadiationReaction

/-- **The radiation coefficient** `⅔ e²/c³`. -/
def radiationCoeff (e c : ℝ) : ℝ := (2 / 3) * (e ^ 2 / c ^ 3)

/-- **The Larmor radiated power** `P = ⅔ e²a²/c³` (`a` the proper acceleration). -/
def larmorPower (e a c : ℝ) : ℝ := radiationCoeff e c * a ^ 2

/-- **The Abraham–Lorentz radiation-reaction force** `F_rad = ⅔ (e²/c³) j` (`j = v̈` the jerk). -/
def abrahamLorentzForce (e c j : ℝ) : ℝ := radiationCoeff e c * j

/-- **The characteristic time** `τ₀ = ⅔ e²/(mc³)` — light-crossing time of the classical electron radius. -/
def characteristicTime (e m c : ℝ) : ℝ := (2 / 3) * (e ^ 2 / (m * c ^ 3))

/-- **The radiated power is non-negative.** -/
theorem larmorPower_nonneg (e a c : ℝ) (hc : 0 < c) : 0 ≤ larmorPower e a c := by
  unfold larmorPower radiationCoeff; positivity

/-- **[Radiates iff accelerating] `P > 0` for `a ≠ 0`.**  A charge radiates exactly when it accelerates. -/
theorem larmorPower_pos_of_accel (e a c : ℝ) (he : e ≠ 0) (ha : a ≠ 0) (hc : 0 < c) :
    0 < larmorPower e a c := by
  unfold larmorPower radiationCoeff
  have h1 : 0 < e ^ 2 := by positivity
  have h2 : 0 < a ^ 2 := by positivity
  positivity

/-- **[Reaction force vanishes at constant acceleration] `F_rad = 0` when the jerk is zero.**  The heart of
the paradox: during uniform acceleration `v̈ = 0`, so the instantaneous radiation-reaction force vanishes. -/
theorem abrahamLorentzForce_zero_of_constant_accel (e c : ℝ) : abrahamLorentzForce e c 0 = 0 := by
  unfold abrahamLorentzForce; ring

/-- **[Schott energy balance] `d/dt(⅔(e²/c³) a·v) = F_rad·v + P`.**  The rate of change of the Schott energy
equals the power delivered by the reaction force plus the radiated power — the integration-by-parts identity
that reconciles Larmor radiation with the vanishing reaction force.  With `a = v̇` and `j = v̈` (the
`HasDerivAt` hypotheses), it is the product rule `(a·v)' = j·v + a²`. -/
theorem schott_energy_balance (e c : ℝ) (v a j : ℝ → ℝ) (t : ℝ)
    (hv : HasDerivAt v (a t) t) (ha : HasDerivAt a (j t) t) :
    HasDerivAt (fun s => radiationCoeff e c * (a s * v s))
      (abrahamLorentzForce e c (j t) * v t + larmorPower e (a t) c) t := by
  have h := (ha.mul hv).const_mul (radiationCoeff e c)
  have heq : abrahamLorentzForce e c (j t) * v t + larmorPower e (a t) c
      = radiationCoeff e c * (j t * v t + a t * a t) := by
    unfold abrahamLorentzForce larmorPower; ring
  rw [heq]
  exact h

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaRadiationReaction

end
