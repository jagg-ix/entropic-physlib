/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.ClassicalMechanics.EulerLagrange
public import Physlib.ClassicalMechanics.HamiltonsEquations
public import Physlib.Thermodynamics.SecondLaw

/-!
# Dissipative mechanics — Newton, Euler-Lagrange, Hamilton at frozen LRF

Phase 3 of the counterpart program (A1 + A4 + A5).  This module
introduces three *dissipative structures* and proves that each reduces to
its standard non-dissipative form when the dissipative perturbation
vanishes.  Together these are the classical-mechanics counterpart of
the entropic-time-from-dissipation forward direction: at zero
dissipation (the frozen LRF in the entropic-time picture), the standard
mechanics laws emerge as the residue.

## structures and recovery theorems

* **`DissipativeNewtonSystem`** — Newton's second law with an additive
  dissipative force: `m·a = F_rev + F_diss`.  At `F_diss = 0`, the
  standard law `m·a = F_rev` is recovered (`newtonsSecondLaw_at_zero_dissipation`).

* **`DissipativeEulerLagrangeSystem`** — the Euler-Lagrange operator is
  shifted by a dissipative-force term: `_root_.ClassicalMechanics.eulerLagrangeOp L q = F_diss`.
  At `F_diss = 0`, `_root_.ClassicalMechanics.eulerLagrangeOp L q = 0` — the standard EL
  equations (`eulerLagrange_at_zero_dissipation`).

* **`DissipativeHamiltonSystem`** — the Hamilton-equations operator is
  shifted by a dissipative perturbation: `hamiltonEqOp H p q = D`.  At
  `D = 0`, `hamiltonEqOp H p q = 0` — the standard Hamilton's equations
  (`hamiltons_at_zero_dissipation`).

## References

- **Gough, Ratiu, Smolyanov 2015** — *Noether's theorem for dissipative quantum semigroups* [bib: `Gough2015`]
- **Lazo et al. 2018** — *Action principle for action-dependent Lagrangians* [bib key needed: `Lazo2018`]
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.ClassicalMechanics.DissipativeMechanics

open ClassicalMechanics Time

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-! ## §1 — Newton's second law -/

/-- **Dissipative Newton system.** Has a mass `m`, a position
`position : Time → X`, an acceleration `acceleration : Time → X`, a
reversible force `forceReversible : Time → X`, a dissipative force
`forceDissipative : Time → X`, and the balance law
`m·a = F_rev + F_diss`. -/
structure DissipativeNewtonSystem (X : Type)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] where
  /-- Inertial mass. -/
  mass : ℝ
  /-- Mass is strictly positive. -/
  mass_pos : 0 < mass
  /-- Position along the trajectory. -/
  position : Time → X
  /-- Acceleration along the trajectory (here taken as data; matches
  `∂²ₜ position` for any twice-differentiable trajectory). -/
  acceleration : Time → X
  /-- Reversible (conservative) force. -/
  forceReversible : Time → X
  /-- Dissipative force.  At `0`, the system reduces to standard
  Newtonian mechanics. -/
  forceDissipative : Time → X
  /-- **Newton's second law with dissipation**: `m·a = F_rev + F_diss`. -/
  balance : ∀ t, mass • acceleration t = forceReversible t + forceDissipative t

namespace DissipativeNewtonSystem

variable (S : DissipativeNewtonSystem X)

/-- **A1 — Newton's second law at zero dissipation.** When the
dissipative force vanishes identically, the system satisfies the
standard form `m·a = F_rev`. -/
theorem newtonsSecondLaw_at_zero_dissipation
    (h : ∀ t, S.forceDissipative t = 0) :
    ∀ t, S.mass • S.acceleration t = S.forceReversible t := by
  intro t
  have hb := S.balance t
  rw [h t, add_zero] at hb
  exact hb

end DissipativeNewtonSystem

/-! ## §2 — Euler-Lagrange equations -/

/-- **Dissipative Euler-Lagrange system.** The Euler-Lagrange operator
applied to the trajectory equals a dissipative-force term; at zero
dissipative force the system satisfies the standard
Euler-Lagrange equations. -/
structure DissipativeEulerLagrangeSystem (X : Type)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] where
  /-- Lagrangian function. -/
  L : Time → X → X → ℝ
  /-- Trajectory. -/
  q : Time → X
  /-- Dissipative force (the operator's deficit from zero). -/
  dissipativeForce : Time → X
  /-- **EL with dissipation**: the EL operator equals the dissipative force. -/
  balance : _root_.ClassicalMechanics.eulerLagrangeOp L q = dissipativeForce

namespace DissipativeEulerLagrangeSystem

variable (S : DissipativeEulerLagrangeSystem X)

/-- **A4 — Euler-Lagrange equations at zero dissipation.** When the
dissipative force vanishes identically, the standard EL equations
`∂L/∂q − d/dt(∂L/∂q̇) = 0` are recovered. -/
theorem eulerLagrange_at_zero_dissipation
    (h : ∀ t, S.dissipativeForce t = 0) :
    _root_.ClassicalMechanics.eulerLagrangeOp S.L S.q = fun _ => 0 := by
  rw [S.balance]
  funext t
  exact h t

end DissipativeEulerLagrangeSystem

/-! ## §3 — Hamilton's equations -/

/-- **Dissipative Hamilton system.** The Hamilton-equations operator
applied to `(p, q)` equals a dissipative perturbation pair; at zero
perturbation the standard Hamilton's equations are recovered. -/
structure DissipativeHamiltonSystem (X : Type)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] where
  /-- Hamiltonian function. -/
  Hfun : Time → X → X → ℝ
  /-- Momentum trajectory. -/
  p : Time → X
  /-- Configuration trajectory. -/
  q : Time → X
  /-- Dissipative perturbation pair (`(δp, δq)`, the operator's deficit). -/
  dissipativePerturbation : Time → X × X
  /-- **Hamilton's eqns with dissipation**: the operator equals the
  dissipative perturbation pair. -/
  balance : _root_.ClassicalMechanics.hamiltonEqOp Hfun p q = dissipativePerturbation

namespace DissipativeHamiltonSystem

variable (S : DissipativeHamiltonSystem X)

/-- **A5 — Hamilton's equations at zero dissipation.** When the
dissipative perturbation vanishes identically, the standard Hamilton's
equations `dq/dt = ∂H/∂p, dp/dt = −∂H/∂q` are recovered (i.e.,
`hamiltonEqOp H p q = 0`). -/
theorem hamiltons_at_zero_dissipation
    (h : ∀ t, S.dissipativePerturbation t = 0) :
    _root_.ClassicalMechanics.hamiltonEqOp S.Hfun S.p S.q = fun _ => 0 := by
  rw [S.balance]
  funext t
  exact h t

end DissipativeHamiltonSystem

/-! ## §4 — Entropic-time wiring (dissipation ↔ second-law worldline)

Each "at zero dissipation" theorem above makes the physical claim:

  Zero dissipative force  ⟺  reversibility  ⟺  frozen entropic clock.

The first ⟺ is mechanical; the second ⟺ lives in
`Physlib.Thermodynamics.SecondLaw.EntropyArrowWorldline.IsReversible`
([SecondLaw.lean:186]).  This section provides the **bridge between
them** via a constitutive coupling — a Rayleigh-style identification
that ties the dissipative-force vanishing to the imaginary-action
worldline being constant.

The coupling records one structural field per system: an iff between
"zero dissipative perturbation at all times" and "the `S_I` worldline
is constant".  This is the textbook Rayleigh-dissipation identification
(dissipative power = `dS_I/dt · T`); we leave the precise functional
form to the consumer and only assume the iff at the level of vanishing.

Once that coupling is supplied, the three "at zero dissipation"
recovery theorems become **strengthened "at reversible worldline"**
theorems: standard mechanics is the residue at frozen entropic time.
-/

open Physlib.Thermodynamics.SecondLaw

/-! ### §4.1 — Newton ↔ entropic-time worldline -/

/-- **Coupling between a dissipative Newton system and an
`EntropyArrowWorldline`**.  The single structural field is the
Rayleigh-style iff: the dissipative force vanishes identically iff the
worldline's imaginary action is constant (frozen entropic clock).

Standard textbook content (Rayleigh dissipation function): power
dissipated `P = F_diss · v` is also equal to `T · dS_I/dt`, so
`F_diss = 0 ⟺ dS_I/dt = 0 ⟺ S_I = const`. -/
structure DissipativeNewtonEntropicCoupling
    (S : DissipativeNewtonSystem X) (W : EntropyArrowWorldline) : Prop where
  /-- Zero dissipative force at all times ⟺ constant `S_I` along the
  worldline (Rayleigh-style identification). -/
  zero_diss_iff_const_S_I :
    (∀ t : Time, S.forceDissipative t = 0) ↔
      (∀ t₁ t₂ : ℝ, W.S_I_along t₁ = W.S_I_along t₂)

namespace DissipativeNewtonSystem

variable (S : DissipativeNewtonSystem X)

/-- **Newton ⟺ reversible worldline.**  Given the coupling, the
dissipative force vanishes iff the worldline is reversible
(`IsReversible` in the second-law sense — constant `S_I`). -/
theorem zero_dissipation_iff_reversible
    (W : EntropyArrowWorldline)
    (C : DissipativeNewtonEntropicCoupling S W) :
    (∀ t : Time, S.forceDissipative t = 0) ↔ W.IsReversible :=
  C.zero_diss_iff_const_S_I

/-- **Strengthened recovery: Newton's law at a reversible worldline.**
Given a coupling and a reversible `EntropyArrowWorldline` (frozen
entropic clock), the dissipative Newton system reduces to standard
Newtonian mechanics `m·a = F_rev`.  No `forceDissipative = 0`
hypothesis at the call site — it is *discharged* from the second-law
worldline witness. -/
theorem newtonsSecondLaw_at_reversible_worldline
    (W : EntropyArrowWorldline)
    (C : DissipativeNewtonEntropicCoupling S W)
    (hRev : W.IsReversible) :
    ∀ t : Time, S.mass • S.acceleration t = S.forceReversible t :=
  S.newtonsSecondLaw_at_zero_dissipation
    (C.zero_diss_iff_const_S_I.mpr hRev)

end DissipativeNewtonSystem

/-! ### §4.2 — Euler–Lagrange ↔ entropic-time worldline -/

/-- **Coupling between a dissipative EL system and an
`EntropyArrowWorldline`** (Rayleigh-style iff on the dissipative
force). -/
structure DissipativeEulerLagrangeEntropicCoupling
    (S : DissipativeEulerLagrangeSystem X) (W : EntropyArrowWorldline) :
    Prop where
  zero_diss_iff_const_S_I :
    (∀ t : Time, S.dissipativeForce t = 0) ↔
      (∀ t₁ t₂ : ℝ, W.S_I_along t₁ = W.S_I_along t₂)

namespace DissipativeEulerLagrangeSystem

variable (S : DissipativeEulerLagrangeSystem X)

/-- **EL ⟺ reversible worldline.** -/
theorem zero_dissipation_iff_reversible
    (W : EntropyArrowWorldline)
    (C : DissipativeEulerLagrangeEntropicCoupling S W) :
    (∀ t : Time, S.dissipativeForce t = 0) ↔ W.IsReversible :=
  C.zero_diss_iff_const_S_I

/-- **Strengthened recovery: standard Euler–Lagrange at a reversible
worldline.**  Given a coupling and a reversible worldline, the standard
EL equations `eulerLagrangeOp L q = 0` are recovered. -/
theorem eulerLagrange_at_reversible_worldline
    (W : EntropyArrowWorldline)
    (C : DissipativeEulerLagrangeEntropicCoupling S W)
    (hRev : W.IsReversible) :
    _root_.ClassicalMechanics.eulerLagrangeOp S.L S.q = fun _ => 0 :=
  S.eulerLagrange_at_zero_dissipation
    (C.zero_diss_iff_const_S_I.mpr hRev)

end DissipativeEulerLagrangeSystem

/-! ### §4.3 — Hamilton ↔ entropic-time worldline -/

/-- **Coupling between a dissipative Hamilton system and an
`EntropyArrowWorldline`** (Rayleigh-style iff on the dissipative
perturbation). -/
structure DissipativeHamiltonEntropicCoupling
    (S : DissipativeHamiltonSystem X) (W : EntropyArrowWorldline) :
    Prop where
  zero_diss_iff_const_S_I :
    (∀ t : Time, S.dissipativePerturbation t = 0) ↔
      (∀ t₁ t₂ : ℝ, W.S_I_along t₁ = W.S_I_along t₂)

namespace DissipativeHamiltonSystem

variable (S : DissipativeHamiltonSystem X)

/-- **Hamilton ⟺ reversible worldline.** -/
theorem zero_dissipation_iff_reversible
    (W : EntropyArrowWorldline)
    (C : DissipativeHamiltonEntropicCoupling S W) :
    (∀ t : Time, S.dissipativePerturbation t = 0) ↔ W.IsReversible :=
  C.zero_diss_iff_const_S_I

/-- **Strengthened recovery: standard Hamilton's equations at a
reversible worldline.**  Given a coupling and a reversible worldline,
the standard Hamilton's equations `hamiltonEqOp H p q = 0` are
recovered. -/
theorem hamiltons_at_reversible_worldline
    (W : EntropyArrowWorldline)
    (C : DissipativeHamiltonEntropicCoupling S W)
    (hRev : W.IsReversible) :
    _root_.ClassicalMechanics.hamiltonEqOp S.Hfun S.p S.q = fun _ => 0 :=
  S.hamiltons_at_zero_dissipation
    (C.zero_diss_iff_const_S_I.mpr hRev)

end DissipativeHamiltonSystem

end Physlib.ClassicalMechanics.DissipativeMechanics

end
