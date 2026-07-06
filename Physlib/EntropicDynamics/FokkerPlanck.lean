/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The entropic-dynamics probability flow: current, osmotic, and drift velocities

The dynamical layer. In entropic dynamics the probability `ρ` flows by a Fokker–Planck equation whose drift is the
sum of two velocities: the **current velocity** `v = ∇φ/m` (from the phase `φ`) and the **osmotic velocity**
`u = −D ∇log ρ` (the entropic, diffusive drift). The osmotic velocity is exactly `−D` times the gradient of the
log-density,

`u = −D ∇log ρ = −D (∇ρ)/ρ`,

the identity that ties the diffusion to information (the score `∇log ρ`). The total drift `b = v + u` transports
`ρ` while diffusion spreads it — the balance whose stationary point is the Gibbs equilibrium.

References: E. Nelson (stochastic mechanics); A. Caticha (entropic dynamics). No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.EntropicDynamics.FokkerPlanck

/-- **The current velocity** `v = ∇φ/m` — the transport velocity carried by the phase `φ`. -/
noncomputable def currentVelocity (dφ m : ℝ) : ℝ := dφ / m

/-- **The osmotic velocity** `u = −D (∇ρ)/ρ` — the entropic/diffusive drift, `−D` times the log-density gradient. -/
noncomputable def osmoticVelocity (D ρ dρ : ℝ) : ℝ := -D * (dρ / ρ)

/-- **The drift velocity** `b = v + u` — the total Fokker–Planck drift, current plus osmotic. -/
noncomputable def driftVelocity (D ρ dρ dφ m : ℝ) : ℝ := currentVelocity dφ m + osmoticVelocity D ρ dρ

/-- **The osmotic velocity is minus `D` times the log-density gradient** `u = −D ∇log ρ`. For a differentiable
positive density, the osmotic (diffusive) velocity `−D (∇ρ)/ρ` equals `−D` times the gradient of `log ρ` (the
score) — the identity linking diffusion to information. -/
theorem osmoticVelocity_eq_log_gradient (ρ : ℝ → ℝ) (D x dρ : ℝ)
    (hρ : HasDerivAt ρ dρ x) (hpos : ρ x ≠ 0) :
    osmoticVelocity D (ρ x) dρ = -D * deriv (fun y => Real.log (ρ y)) x := by
  unfold osmoticVelocity
  rw [(hρ.log hpos).deriv]

/-- **The drift is the current velocity plus the osmotic (log-gradient) velocity** — the Fokker–Planck drift
decomposition `b = ∇φ/m − D ∇log ρ`, transport plus diffusion. -/
theorem driftVelocity_decomposition (ρ : ℝ → ℝ) (D x dρ dφ m : ℝ)
    (hρ : HasDerivAt ρ dρ x) (hpos : ρ x ≠ 0) :
    driftVelocity D (ρ x) dρ dφ m = currentVelocity dφ m - D * deriv (fun y => Real.log (ρ y)) x := by
  unfold driftVelocity
  rw [osmoticVelocity_eq_log_gradient ρ D x dρ hρ hpos]
  ring

end Physlib.EntropicDynamics.FokkerPlanck

end
