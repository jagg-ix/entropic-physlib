/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.ClassicalMechanics.Herglotz.Balance

/-!
# TDSE ⇒ Herglotz: density-matrix magnitude decay bridge

Stage 4-B: the **general** TDSE → Herglotz bridge, via the Heisenberg-picture
density-matrix magnitude surrogate.

Following the reduced-dynamics convention (`SatisfiesTemporalOrderReducedDynamics`):
the reduced non-unitary dynamics
`ρ̇ = −(i/ℏ)[H_R, ρ] − (1/ℏ){H_I, ρ}` admits a non-negative **magnitude**
`rhoMag : ρ → ℝ` and a non-negative time-dependent **dissipation rate** `γ(t)`
with

  `(d/dt) rhoMag(ρ(t)) = −γ(t) · rhoMag(ρ(t))`.

The unitary `[H_R, ρ]` part contributes zero to the magnitude derivative;
the magnitude equation is closed under the dissipative `{H_I, ρ}` content alone.

This is exactly the balance law `J̇ = α·J` of `HerglotzNoetherBalance` with
`J := rhoMag(ρ(·))` and `α := −γ ≤ 0`. The constructor
`HerglotzNoetherBalance.ofTDSEMagnitudeDecay` realises the bridge with
**time-varying α** (the TDSE general case — not just constant rate / TiSE).

The Herglotz dissipation sign `α ≤ 0` is now a **theorem** from
`γ ≥ 0` (`ofTDSEMagnitudeDecay_alpha_nonpos`), unifying the TDSE side with the
Lindblad operator-positivity bridge (`LindbladHerglotz.lean`) and the Rayleigh
classical-mechanics route (`Instances.lean`): all three are concrete inhabitants
of `HerglotzNoetherBalance` whose `α ≤ 0` is structurally certified.


## References

- **Herglotz 1930** — *Berührungstransformationen (lectures)*
- **Lazo et al. 2018** — *Action principle for action-dependent Lagrangians*
- **Bartosiewicz & Torres 2008** — *Noether's theorem on time scales*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section


open Physlib.ClassicalMechanics.Herglotz.Balance
namespace Physlib.QuantumMechanics.Schrodinger.HerglotzMagnitudeDecay

/-- **TDSE density-matrix magnitude decay** (Heisenberg-picture surrogate).
A `ρ`-typed trajectory `rho : ℝ → ρ` with a non-negative magnitude `rhoMag` and a
non-negative dissipation rate `γ(t)` satisfying `d/dt rhoMag(ρ(t)) = −γ·rhoMag`.
-/
structure TDSEMagnitudeDecay (ρ : Type*) where
  /-- The density-matrix trajectory. -/
  rho : ℝ → ρ
  /-- The non-negative magnitude functional on density matrices. -/
  rhoMag : ρ → ℝ
  /-- The (time-dependent) dissipation rate. -/
  gamma : ℝ → ℝ
  /-- `γ(t) ≥ 0` along the trajectory. -/
  gamma_nonneg : ∀ t, 0 ≤ gamma t
  /-- `rhoMag` is non-negative on the codomain. -/
  rhoMag_nonneg : ∀ x, 0 ≤ rhoMag x
  /-- **The TDSE magnitude balance law** `d/dt rhoMag(ρ(t)) = −γ(t)·rhoMag(ρ(t))`. -/
  balance : ∀ t, HasDerivAt (fun s => rhoMag (rho s))
                            (- gamma t * rhoMag (rho t)) t

/-- **TDSE ⇒ Herglotz bridge.** A density-matrix magnitude decay instantiates a
`HerglotzNoetherBalance` with `J := rhoMag(ρ(·))` and `α := −γ`. The accumulator
`A` (with `A' = α = −γ`) is supplied by the caller; for constant `γ` the
canonical choice is `A(t) = −γ·t`, for time-varying `γ` an antiderivative via
the fundamental theorem of calculus. -/
def HerglotzNoetherBalance.ofTDSEMagnitudeDecay
    {ρ : Type*} (D : TDSEMagnitudeDecay ρ)
    (A : ℝ → ℝ) (hA : ∀ t, HasDerivAt A (- D.gamma t) t) :
    HerglotzNoetherBalance where
  J := fun s => D.rhoMag (D.rho s)
  alpha := fun t => - D.gamma t
  A := A
  hasDerivAt_J := fun t => by
    have h := D.balance t
    convert h using 1
  hasDerivAt_A := hA

/-- **Structural TDSE → Herglotz dissipation sign.** The Heisenberg-picture
density-matrix balance has Herglotz `α ≤ 0` automatically — derived from
`γ ≥ 0`, with no Rayleigh-style hypothesis. -/
theorem ofTDSEMagnitudeDecay_alpha_nonpos
    {ρ : Type*} (D : TDSEMagnitudeDecay ρ)
    (A : ℝ → ℝ) (hA : ∀ t, HasDerivAt A (- D.gamma t) t) :
    ∀ t, (HerglotzNoetherBalance.ofTDSEMagnitudeDecay D A hA).alpha t ≤ 0 := by
  intro t
  show - D.gamma t ≤ 0
  linarith [D.gamma_nonneg t]

end Physlib.QuantumMechanics.Schrodinger.HerglotzMagnitudeDecay

end
