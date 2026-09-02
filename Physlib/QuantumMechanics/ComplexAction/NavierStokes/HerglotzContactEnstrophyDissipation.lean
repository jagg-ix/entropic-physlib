/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect
public import Physlib.ClassicalMechanics.ActionPrinciple
public import Physlib.FluidDynamics.NavierStokes.Momentum

/-!
# Navier–Stokes as a Herglotz contact system: the enstrophy dissipation and the entropic action

Navier–Stokes is **dissipative**, so it has no standard (conservative) Lagrangian.  Its variational home is the
**Herglotz / contact** principle, where the action `S` obeys `dS/dt = L(q, q̇, S, t)` and the dependence on `S`
supplies the friction — precisely the viscous term.  `Lindblad.HerglotzContactCalibration` calibrates the
contact-friction coefficient to a dissipation rate with factor `2/ℏ`, and `ClassicalMechanics.ActionPrinciple`
carries the entropic action `S_I = ℏ·τ_ent` with the Herglotz equality *classical Euler–Lagrange ⟺ dissipative
force vanishes* (`stationary_total_at_frozen_iff_classical_EL`).  This file reads the Navier–Stokes enstrophy
dynamics through that structure.

* **§A — the Herglotz split of the enstrophy rate.** `dΩ/dt = 2(VS − νP)` decomposes as a **conservative**
  vortex-stretching part `2·VS` (the Euler coadjoint term) minus a **contact-friction** part `2ν·P`
  (`enstrophyRate_herglotz_split`).  At `ν = 0` the friction vanishes and the rate is pure conservation
  (`enstrophyRate_euler_frictionless`); the dynamics is conservative *iff* the friction `νP` vanishes
  (`enstrophyRate_conservative_iff_frictionless`) — the fluid analogue of the Herglotz equality.  With
  Constantin–Iyer `ℏ = 2ν` the friction coefficient *is* `ℏ` (`friction_coefficient_constantinIyer`).

* **§B — the entropic action.** The dissipation accumulates into the entropic action `S_I = ℏ·τ_ent`; the total
  action exceeds the classical (Euler) action by exactly this non-negative amount
  (`navierStokes_total_action_ge_classical`), reducing to the classical action *iff* the entropic time vanishes
  (`navierStokes_action_classical_iff_euler`) — the reversible Euler limit.

* **§C — velocity terms carry time.** The material acceleration `Du/Dt = ∂ₜu + (u·∇)u` (`materialAcceleration`)
  splits into an explicit-time part and a **velocity-carried** convective part; at steady flow (`∂ₜu = 0`) the
  acceleration is *purely* convective (`materialAcceleration_eq_convective_of_steady`).  The velocity field is
  its own clock: the convective term feeds the vortex stretching `VS`, so the conservative half of §A is
  driven by the time-evolving velocity, not by the friction.

## Honest scope

This is the correct *variational structure* of dissipative Navier–Stokes, not a regularity result.  It sharpens
the earlier fiber picture: the friction (`2νP`, dissipative, `∝ ℏ`) is the part the entropic clock damps, while
the vortex stretching (`2VS`, conservative, velocity-carried) is the part it does not — the same term that
vanishes in 2D and obstructs 3D.  Nothing here closes the 3D problem.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.HerglotzContactEnstrophyDissipation

open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect
open Physlib.ClassicalMechanics.ActionPrinciple
open FluidDynamics
open FluidDynamics.NavierStokes

/-! ### §A — The Herglotz split of the enstrophy rate -/

/-- **The Herglotz contact split.**  The enstrophy rate `dΩ/dt = 2(VS − νP)` is the conservative
vortex-stretching part `2·VS` minus the contact-friction part `2ν·P`: the standard form of a Herglotz /
contact system, conservative Lagrangian minus friction on the momentum. -/
theorem enstrophyRate_herglotz_split (VS ν P : ℝ) :
    enstrophyRate VS ν P = 2 * VS - 2 * ν * P := by
  unfold enstrophyRate; ring

/-- **The conservative (Euler) limit is frictionless.**  At `ν = 0` the contact friction vanishes and the
enstrophy rate is pure conservative vortex stretching `2·VS` — the enstrophy Casimir on the Euler coadjoint
orbit, matching the Herglotz conservative limit (`Lindblad.HerglotzContactCalibration`'s `L = 0 ⇒ ρ = 0`). -/
theorem enstrophyRate_euler_frictionless (VS P : ℝ) : enstrophyRate VS 0 P = 2 * VS := by
  unfold enstrophyRate; ring

/-- **Conservative dynamics ⟺ no friction.**  The enstrophy dynamics is conservative (pure vortex stretching,
`dΩ/dt = 2·VS`) *iff* the contact friction `νP` vanishes — the fluid analogue of the Herglotz equality
`stationary classical action ⟺ dissipative force = 0`. -/
theorem enstrophyRate_conservative_iff_frictionless (VS ν P : ℝ) :
    enstrophyRate VS ν P = 2 * VS ↔ ν * P = 0 := by
  unfold enstrophyRate
  constructor <;> intro h <;> linarith

/-- **The friction coefficient is `ℏ` (Constantin–Iyer `ℏ = 2ν`).**  The contact-friction term `2ν·P` is
`ℏ·P`: the enstrophy dissipation's friction coefficient is exactly the quantum `ℏ` that the Herglotz
calibration `2/ℏ` and the entropic action `S_I = ℏ·τ_ent` carry. -/
theorem friction_coefficient_constantinIyer (ν ℏ P : ℝ) (hℏ : ℏ = 2 * ν) :
    2 * ν * P = ℏ * P := by
  rw [hℏ]

/-! ### §B — The entropic action `S_I = ℏ·τ_ent` -/

/-- **The Navier–Stokes entropic action.**  The dissipation accumulates into the entropic action
`S_I = ℏ·τ_ent` (`ℏ·τ ≥ 0`), carried on the `EntropicAction` structure alongside the classical (Euler)
action. -/
noncomputable def navierStokesEntropicAction (Sclassical ℏ τ : ℝ) (hτ : 0 ≤ ℏ * τ) : EntropicAction :=
  ⟨Sclassical, ℏ * τ, hτ⟩

/-- **The total action exceeds the classical action by the entropic dissipation.**  `S_classical ≤ S_total`:
the viscous dissipation adds the non-negative entropic action `ℏ·τ_ent` to the reversible Euler action — the
operational second law for the fluid. -/
theorem navierStokes_total_action_ge_classical (Sclassical ℏ τ : ℝ) (hτ : 0 ≤ ℏ * τ) :
    Sclassical ≤ (navierStokesEntropicAction Sclassical ℏ τ hτ).total :=
  (navierStokesEntropicAction Sclassical ℏ τ hτ).total_ge_classical

/-- **The action reduces to the Euler action iff the entropic time vanishes.**  The total Navier–Stokes action
equals the classical (Euler) action *iff* the entropic contribution `ℏ·τ_ent` vanishes — the reversible,
zero-dissipation limit. -/
theorem navierStokes_action_classical_iff_euler (Sclassical ℏ τ : ℝ) (hτ : 0 ≤ ℏ * τ) :
    (navierStokesEntropicAction Sclassical ℏ τ hτ).total = Sclassical ↔ ℏ * τ = 0 :=
  (navierStokesEntropicAction Sclassical ℏ τ hτ).total_eq_classical_iff_zero_entropic

/-! ### §C — Velocity terms carry time: the material acceleration -/

/-- **The velocity field is its own clock.**  The material acceleration `Du/Dt = ∂ₜu + (u·∇)u` is purely the
velocity-carried convective term at steady flow — when the explicit-time part `∂ₜu` (here
`materialAcceleration − convectiveTerm`) vanishes, the acceleration is entirely `(u·∇)u`.  The velocity
transports its own evolution: this convective term is what feeds the conservative vortex stretching `VS` of
§A, driven by the time-evolving velocity rather than by the friction. -/
theorem materialAcceleration_eq_convective_of_steady (d : ℕ) (fluid : FluidState d)
    (hsteady : ∀ t x, materialAcceleration d fluid t x - convectiveTerm d fluid t x = 0) :
    materialAcceleration d fluid = convectiveTerm d fluid := by
  funext t x
  exact sub_eq_zero.mp (hsteady t x)

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.HerglotzContactEnstrophyDissipation

end
