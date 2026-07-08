/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.ClassicalMechanics.Herglotz.Balance

/-!
# Concrete Herglotz–Noether instances

The abstract `HerglotzNoetherBalance` underlying space of `Balance.lean` is inhabited
here by **constant-rate** dissipation — the simplest non-trivial Herglotz
dynamics, which already covers the paper's Rayleigh example (Simoes–Colombo
2025, Example 4.2) under the renaming `α := −γ`.

* `ofConstantRate α J₀` — `J(t) = J₀·exp(α·t)`, `A(t) = α·t`; the structure's
  balance law `J̇ = α·J` is satisfied by direct calculus.
* `constant_rate_rescaled_invariant_eq` — for any constant-rate balance the
  rescaled invariant takes the explicit value `J₀`: `J(t)·exp(−A(t)) = J₀` for
  all `t`.
* `ofRayleigh γ J₀` — the Rayleigh damping specialisation (`α := −γ`, with
  `γ > 0`), making `α ≤ 0` a theorem and giving the energy-decay form
  `J(t) = J₀·exp(−γt)` definitionally.

These are real witnesses of `HerglotzNoetherBalance`: the abstract framework is
not vacuous; the rescaled invariant is conserved at the *explicit value* `J₀`.


## References

- **Bartosiewicz & Torres 2008** — *Noether's theorem on time scales*
- **Herglotz 1930** — *Berührungstransformationen (lectures)*
- **Lazo et al. 2018** — *Action principle for action-dependent Lagrangians*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section


open Physlib.ClassicalMechanics.Herglotz.Balance
namespace Physlib.ClassicalMechanics.Herglotz.Instances

/-- **Constant-rate Herglotz–Noether balance.** From a constant dissipation
coefficient `α` and an initial value `J₀`, build the balance with
`J(t) = J₀·exp(α·t)` and `A(t) = α·t`. -/
def ofConstantRate (alpha J0 : ℝ) : HerglotzNoetherBalance where
  J := fun t => J0 * Real.exp (alpha * t)
  alpha := fun _ => alpha
  A := fun t => alpha * t
  hasDerivAt_J := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => alpha * s) alpha t := by
      exact ((hasDerivAt_id t).const_mul alpha).congr_deriv (by ring)
    have h3 := (h1.exp).const_mul J0
    exact h3.congr_deriv (by ring)
  hasDerivAt_A := fun t => by
    exact ((hasDerivAt_id t).const_mul alpha).congr_deriv (by ring)

/-- **The constant-rate rescaled invariant is exactly `J₀`.** `J(t)·exp(−A(t))`
collapses to `J₀ · exp(α·t) · exp(−α·t) = J₀` for all `t` — a fully explicit
conservation law (a concrete witness that the abstract structure is not vacuous). -/
theorem constant_rate_rescaled_invariant_eq (alpha J0 t : ℝ) :
    (ofConstantRate alpha J0).J t * Real.exp (- (ofConstantRate alpha J0).A t) = J0 := by
  unfold ofConstantRate
  rw [mul_assoc, ← Real.exp_add,
    show alpha * t + -(alpha * t) = 0 from by ring,
    Real.exp_zero, mul_one]

/-! ## Rayleigh damping as a constant-rate Herglotz balance -/

/-- **Rayleigh dissipation as a constant-rate Herglotz balance.** With damping
`γ ≥ 0`, the constant `α := −γ` defines the Herglotz–Noether balance of
*Simoes–Colombo 2025, Example 4.2*: `J(t) = J₀·exp(−γt)` (exponential decay)
and `exp(γt)·J(t) = J₀` is the conserved rescaled invariant. -/
def ofRayleigh (gamma J0 : ℝ) : HerglotzNoetherBalance := ofConstantRate (- gamma) J0

/-- The Rayleigh balance has dissipation sign `α ≤ 0` (when `γ ≥ 0`). -/
theorem ofRayleigh_alpha_nonpos (gamma : ℝ) (hγ : 0 ≤ gamma) (J0 : ℝ) :
    ∀ t, (ofRayleigh gamma J0).alpha t ≤ 0 := by
  intro _; unfold ofRayleigh ofConstantRate; linarith

/-- The Rayleigh charge decays exponentially: `J(t) = J₀·exp(−γt)`. -/
theorem ofRayleigh_J_eq (gamma J0 t : ℝ) :
    (ofRayleigh gamma J0).J t = J0 * Real.exp (- gamma * t) := rfl

/-! ## Navier–Stokes viscous dissipation as a constant-rate Herglotz balance

For a fluid satisfying the incompressible Navier–Stokes equations, the kinetic
energy `E(t) = ½ ∫ ρ |u|² dx` decays through the **viscous-dissipation rate**
`ε = ν · ∫ ρ |∇u|² dx ≥ 0` (kinematic viscosity `ν > 0`).  In the simplest
*regular-decay* regime — where the energy-dissipation ratio `ε/E` is roughly
constant `γ ≥ 0` — the energy balance `Ė = −ε = −γ·E` is exactly a Rayleigh /
constant-rate Herglotz balance with `α = −γ`.

This instance specialises `ofRayleigh` to that NS energy-dissipation reading:
the **viscous decay constant** `γ_visc` plays the role of Rayleigh damping,
`E₀` is the initial kinetic energy.  No new axioms; the construction inherits
its dissipation sign `α ≤ 0` from `ofRayleigh_alpha_nonpos`.

In entropic-time terms the accumulated entropic time is
`τ_ent(t) = γ_visc · t = −A(t)`, identifying NS viscous dissipation with the
classical-mechanics entropic-time arrow.
-/

/-- **NS viscous dissipation as a constant-rate Herglotz balance.**  With
viscous decay constant `γ_visc ≥ 0` and initial kinetic energy `E₀`, the
kinetic-energy balance `E(t) = E₀·exp(−γ_visc·t)` is a Rayleigh / Herglotz
balance with `α = −γ_visc`. -/
def ofNSViscousDissipation (gamma_visc E0 : ℝ) : HerglotzNoetherBalance :=
  ofRayleigh gamma_visc E0

/-- The NS viscous-dissipation balance has dissipation sign `α ≤ 0` when
`γ_visc ≥ 0`. -/
theorem ofNSViscousDissipation_alpha_nonpos
    (gamma_visc : ℝ) (hγ : 0 ≤ gamma_visc) (E0 : ℝ) :
    ∀ t, (ofNSViscousDissipation gamma_visc E0).alpha t ≤ 0 :=
  ofRayleigh_alpha_nonpos gamma_visc hγ E0

/-- The NS kinetic energy decays exponentially:
`E(t) = E₀·exp(−γ_visc·t)`.  This is the simplest Herglotz reading of the
viscous-dissipation energy balance. -/
theorem ofNSViscousDissipation_E_eq (gamma_visc E0 t : ℝ) :
    (ofNSViscousDissipation gamma_visc E0).J t =
      E0 * Real.exp (- gamma_visc * t) :=
  ofRayleigh_J_eq gamma_visc E0 t

/-- The NS viscous-dissipation rescaled invariant collapses to `E₀`:
`E(t) · exp(γ_visc · t) = E₀` for all `t`. -/
theorem ofNSViscousDissipation_rescaled_invariant_eq
    (gamma_visc E0 t : ℝ) :
    (ofNSViscousDissipation gamma_visc E0).J t *
        Real.exp (- (ofNSViscousDissipation gamma_visc E0).A t) = E0 := by
  unfold ofNSViscousDissipation ofRayleigh
  exact constant_rate_rescaled_invariant_eq _ _ _

end Physlib.ClassicalMechanics.Herglotz.Instances

end
