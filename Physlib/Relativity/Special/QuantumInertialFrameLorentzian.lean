/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrame
public import Physlib.Relativity.Special.ProperTime

/-!
# Lorentzian Quantum Inertial Frame

Concrete instantiation of the operator-level
`QuantumMechanics.FiniteTarget.QuantumInertialFrame` structure on a
**Lorentzian** (Minkowski/`SpaceTime sd`) background.  The QIF data
`(H_R, H_I, ℏ)` is paired with:

* an `EntropyArrowWorldline` providing the second-law-protected
  `S_I_along` / `τ_ent_along` clock,
* a quantum-state assignment `state : ℝ → H` along the worldline,
* a constitutive identification (the **equilibrium-reversible
  bridge**) tying the QIF equilibrium condition (`λ(state t) = 0`)
  to the worldline's `IsReversible` predicate.

This is the operator-level companion of physlib's existing
`SRConstantVelocityEntropicCoupling` (`PhaseClock/Relativistic.lean`)
and follows the same `BridgeSRandEntropic`-style pattern: the
constitutive identification is supplied by the consumer per
physical model, and the QIF realisation theorems then follow as
unconditional Lean theorems.

## Main theorem

`totalProperTime_eq_properTime_at_allTimes_equilibrium` — when the
QIF state is at equilibrium at every parameter `t`, the
constitutive bridge forces the worldline to be reversible, and the
**total proper time reduces to the bare Minkowski proper time**
`SpaceTime.properTime q p = geometricInterval q p`.

This is the Lorentzian-frame realisation of the QIF equilibrium
condition: at every-time equilibrium QIF, the entropic contribution
to total proper time vanishes and one recovers special relativity.

## References

  Quantum Reference Frames".
* Connes & Rovelli 1994, "Von Neumann algebra automorphisms and
  time-thermodynamics relation in generally covariant quantum
  theories" — equilibrium-clock
  identification.
* Rovelli 1991, "Time in quantum gravity: An hypothesis"
 — partial-observable frame view.
* Bisognano & Wichmann 1975 — modular
  flow on a wedge algebra defines an operational equilibrium frame.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special.QuantumInertialFrameLorentzian

open QuantumMechanics.FiniteTarget SpaceTime QuantumInfo.Finite
open Physlib.Thermodynamics.SecondLaw

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]
variable {sd : ℕ} {d : Type*} [Fintype d] [DecidableEq d]

/-! ## §1 — Lorentzian QIF worldline (data) -/

/-- A **Lorentzian QIF worldline** packages a QIF with a quantum-state
assignment `state : ℝ → H` along an `EntropyArrowWorldline` `W` AND
a worldline embedding `worldline : ℝ → SpaceTime sd` in Minkowski
spacetime.

The four data pieces interlock:

* `Q` — operator-level QIF (`H_R, H_I, ℏ`).
* `W` — second-law-protected entropy clock (`S_I_along`, `τ_ent_along`).
* `state` — quantum state along the parameter (`ℝ → H`).
* `worldline` — Lorentzian-spacetime trajectory (`ℝ → SpaceTime sd`).

Equipped with the worldline, the structure supports the `IsInertial`
predicate (§2 below): an inertial QIF in the SR sense has both
*geometric inertiality* (affine / geodesic worldline) and
*quantum inertiality* (all-times equilibrium QIF). -/
structure LorentzianQIFWorldline
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] (sd : ℕ) where
  /-- Operator-level QIF data. -/
  Q         : QuantumInertialFrame H
  /-- Entropy-arrow worldline (second-law-protected `S_I` clock). -/
  W         : EntropyArrowWorldline
  /-- Quantum-state assignment along the worldline parameter. -/
  state     : ℝ → H
  /-- Lorentzian-spacetime worldline embedding. -/
  worldline : ℝ → SpaceTime sd

namespace LorentzianQIFWorldline

variable (LQW : LorentzianQIFWorldline H sd)

/-- The Lorentzian-QIF worldline is at **equilibrium QIF** at
parameter `t` iff its state at `t` is an equilibrium-QIF state. -/
def IsEquilibriumAt (t : ℝ) : Prop := LQW.Q.IsEquilibriumAt (LQW.state t)

/-- The worldline is at **all-times equilibrium QIF** iff the state
is at equilibrium QIF at every parameter `t`. -/
def IsAllTimesEquilibrium : Prop := ∀ t : ℝ, LQW.IsEquilibriumAt t

/-- At all-times equilibrium QIF, the QIF entropic rate vanishes at
every parameter. -/
theorem entropicRate_zero_of_allTimes_equilibrium
    (h_eq : LQW.IsAllTimesEquilibrium) (t : ℝ) :
    LQW.Q.entropicRate (LQW.state t) = 0 :=
  h_eq t

/-- At all-times equilibrium QIF, the QIF dissipation operator
annihilates the state at every parameter. -/
theorem H_I_apply_zero_of_allTimes_equilibrium
    (h_eq : LQW.IsAllTimesEquilibrium) (t : ℝ) :
    LQW.Q.H_I (LQW.state t) = 0 :=
  LQW.Q.H_I_apply_eq_zero_of_isEquilibrium (h_eq t)

end LorentzianQIFWorldline

/-! ## §1b — Geometric inertiality and the `IsInertial` predicate

A frame is *inertial* in the SR sense iff its worldline is a
**timelike geodesic** — equivalently in Minkowski space, an affine
map `t ↦ q + t • u` of `ℝ → SpaceTime sd`.  This is the geometric
half of inertiality.

Combined with the quantum half (the QIF is at all-times equilibrium,
so no fictitious openness is present in the reduced dynamics), the
two halves give the operational notion of an **inertial Quantum
Inertial Frame** — one in which both Newton's first law (geodesic
motion) and time-homogeneous quantum evolution (TISE recovery) hold
simultaneously.
-/

namespace LorentzianQIFWorldline

variable (LQW : LorentzianQIFWorldline H sd)

/-- **Geometric inertiality**: the worldline embedding is affine,
`worldline t = q + t • u` for some base point `q : SpaceTime sd`
and direction `u : SpaceTime sd`.  In Minkowski space this is
equivalent to *timelike geodesic motion* (no proper acceleration). -/
def IsGeodesicAffine : Prop :=
  ∃ q u : SpaceTime sd, ∀ t : ℝ, LQW.worldline t = q + t • u

/-- **Inertial QIF condition**: both the worldline is affine
(geometrically inertial / geodesic) *and* the QIF is at every-time
equilibrium (quantum-mechanically inertial / no fictitious openness).

This is the predicate that finally justifies the *Inertial* in
"Quantum Inertial Frame" — until this predicate, the name was only
naming convention. -/
def IsInertial : Prop :=
  LQW.IsGeodesicAffine ∧ LQW.IsAllTimesEquilibrium

/-- An inertial Lorentzian QIF has an affine worldline. -/
theorem isGeodesicAffine_of_isInertial (h : LQW.IsInertial) :
    LQW.IsGeodesicAffine := h.1

/-- An inertial Lorentzian QIF is at all-times equilibrium. -/
theorem isAllTimesEquilibrium_of_isInertial (h : LQW.IsInertial) :
    LQW.IsAllTimesEquilibrium := h.2

/-- **Inertial = geodesic ∧ equilibrium** — definitional unpacking. -/
theorem isInertial_iff :
    LQW.IsInertial ↔ LQW.IsGeodesicAffine ∧ LQW.IsAllTimesEquilibrium :=
  Iff.rfl

end LorentzianQIFWorldline

/-! ## §2 — Equilibrium-reversible bridge (constitutive identification)

The constitutive identification supplied by the consumer per physical
model: the QIF equilibrium condition (`λ = 0`) and the
`EntropyArrowWorldline.IsReversible` condition are operationally the
same statement viewed from two layers (quantum / thermodynamic). -/

/-- **Equilibrium-reversible bridge**: the worldline is reversible
(thermodynamic `S_I` constant) iff the QIF state is at equilibrium
at every parameter (operator-level `λ = 0`).

This is the operational bridge that ties the QIF structure to the
`EntropyArrowWorldline` structure.  It is a `Prop`-level Bridge in
the `BridgeSRandEntropic` sense: consumer supplies the
identification per physical model, then the main theorem follows. -/
structure LorentzianQIFEquilibriumBridge
    (LQW : LorentzianQIFWorldline H sd) : Prop where
  reversible_iff_equilibrium :
    LQW.W.IsReversible ↔ LQW.IsAllTimesEquilibrium

namespace LorentzianQIFEquilibriumBridge

/-- **Forward direction**: at all-times equilibrium QIF, the worldline
is reversible. -/
theorem isReversible_of_isAllTimesEquilibrium
    {LQW : LorentzianQIFWorldline H sd}
    (B : LorentzianQIFEquilibriumBridge LQW)
    (h_eq : LQW.IsAllTimesEquilibrium) : LQW.W.IsReversible :=
  B.1.mpr h_eq

/-- **Reverse direction**: at reversible worldline, the QIF state is
at all-times equilibrium. -/
theorem isAllTimesEquilibrium_of_isReversible
    {LQW : LorentzianQIFWorldline H sd}
    (B : LorentzianQIFEquilibriumBridge LQW)
    (h_rev : LQW.W.IsReversible) : LQW.IsAllTimesEquilibrium :=
  B.1.mp h_rev

end LorentzianQIFEquilibriumBridge

/-! ## §3 — Theorem: total proper time reduces to Minkowski at
equilibrium QIF -/

/-- **Lorentzian QIF equilibrium reduction.**

At all-times equilibrium QIF (with the consumer-supplied
equilibrium-reversible bridge `B`), the **total proper time**
between any two spacetime points along the worldline reduces to the
bare **Minkowski proper time** `SpaceTime.properTime q p`:

  `totalProperTimeMetric U q p (ρ t₁) (ρ t₂) = properTime q p`.

This is the QIF realisation of the Frozen-LRF condition of
`Physlib.Relativity.Special.ProperTime`: at every-time equilibrium
QIF, the entropic contribution to total proper time vanishes and
special-relativistic proper time is recovered as the residue.

The proof chains:

* `B.isReversible_of_isAllTimesEquilibrium h_eq` → `W.IsReversible`
* `SpaceTime.totalProperTime_eq_properTime_at_reversible_worldline`
  → `totalProperTimeMetric U q p (ρ t₁) (ρ t₂) = properTime q p`. -/
theorem totalProperTime_eq_properTime_at_allTimes_equilibrium
    (LQW : LorentzianQIFWorldline H sd)
    (B : LorentzianQIFEquilibriumBridge LQW)
    (h_eq : LQW.IsAllTimesEquilibrium)
    (U : EntropicTimeUnits) (q p : SpaceTime sd)
    (ρ : ℝ → MState d)
    (C : SpaceTime.EntropicProperTimeCoupling LQW.W ρ)
    (t₁ t₂ : ℝ) :
    totalProperTimeMetric U q p (ρ t₁) (ρ t₂) = SpaceTime.properTime q p :=
  SpaceTime.totalProperTime_eq_properTime_at_reversible_worldline
    LQW.W U ρ C
    (B.1.mpr h_eq)
    q p t₁ t₂

/-- **Corollary — `τ_ent` advance vanishes at all-times equilibrium QIF.**
The worldline's entropic-time advance over any interval vanishes
when the QIF state is at equilibrium at every parameter (no
dissipative leakage along the trajectory). -/
theorem tauEnt_advance_zero_at_allTimes_equilibrium
    (LQW : LorentzianQIFWorldline H sd)
    (B : LorentzianQIFEquilibriumBridge LQW)
    (h_eq : LQW.IsAllTimesEquilibrium) (t₁ t₂ : ℝ) :
    LQW.W.τ_ent_along t₂ - LQW.W.τ_ent_along t₁ = 0 :=
  LQW.W.clausius_equality_at_frozen (B.1.mpr h_eq)

/-! ## §4 — Inertial-frame theorem (geometric + quantum inertiality) -/

/-- **Inertial QIF reduces total proper time to Minkowski
along the worldline endpoints.**

Strengthens `totalProperTime_eq_properTime_at_allTimes_equilibrium`:
when the frame is *inertial* (both geometrically — the worldline is
affine — and quantum-mechanically — the QIF is at every-time
equilibrium), the total proper time between any two **worldline
endpoints** `LQW.worldline t₁`, `LQW.worldline t₂` reduces to the
bare Minkowski proper time between those endpoints.

This is the QIF-level realisation of the SR claim "inertial frames
realise the maximum proper time" along the worldline. -/
theorem totalProperTime_eq_properTime_at_inertial
    (LQW : LorentzianQIFWorldline H sd)
    (B : LorentzianQIFEquilibriumBridge LQW)
    (h_inertial : LQW.IsInertial)
    (U : EntropicTimeUnits)
    (ρ : ℝ → MState d)
    (C : SpaceTime.EntropicProperTimeCoupling LQW.W ρ)
    (t₁ t₂ : ℝ) :
    totalProperTimeMetric U (LQW.worldline t₁) (LQW.worldline t₂)
        (ρ t₁) (ρ t₂)
      = SpaceTime.properTime (LQW.worldline t₁) (LQW.worldline t₂) :=
  totalProperTime_eq_properTime_at_allTimes_equilibrium LQW B
    h_inertial.2 U _ _ ρ C t₁ t₂

/-- An inertial Lorentzian QIF has zero `τ_ent` advance over any
interval (the entropic clock is frozen along an inertial worldline). -/
theorem tauEnt_advance_zero_at_inertial
    (LQW : LorentzianQIFWorldline H sd)
    (B : LorentzianQIFEquilibriumBridge LQW)
    (h_inertial : LQW.IsInertial) (t₁ t₂ : ℝ) :
    LQW.W.τ_ent_along t₂ - LQW.W.τ_ent_along t₁ = 0 :=
  tauEnt_advance_zero_at_allTimes_equilibrium LQW B h_inertial.2 t₁ t₂

/-! ## §5 — Non-equilibrium dynamics (`λ > 0`): three-probe distinction

Operational classification near the Schwarzschild exterior:

* **Probe A (inertial, far away)**: `λ ≈ 0` (no detector clicks),
  `τ_ent ≈ const`. Modelled by `IsAllTimesEquilibrium` ↔ `IsInertial`
  with the §4 theorem.
* **Probe B (hovering at fixed radius)**: `λ ∝ κ > 0`, detector
  response grows linearly, `τ_ent` accumulates steadily.  Modelled
  by `IsAllTimesStrictlyNonEquilibrium` with the strict-dissipation
  bridge below.
* **Probe C (free-fall across horizon)**: bounded transients,
  `τ_ent` finite.  Modelled by transient non-equilibrium (not
  formalised here — requires `λ → 0` asymptotically; falls outside
  the always-on / always-off binary).

The strict-dissipation bridge ties the operator-level rate condition
`0 < entropicRate (state t)` to the thermodynamic `S_I` strict
monotonicity along the worldline, recovering strictly monotone
`τ_ent` via `EntropyArrowWorldline.tau_ent_strict_when_S_I_strict`.
-/

namespace LorentzianQIFWorldline

variable (LQW : LorentzianQIFWorldline H sd)

/-- **Strict non-equilibrium QIF at parameter `t`**: the local
entropic rate `λ(state t)` is strictly positive.  Operationally:
the dissipation operator `H_I` has a nonzero expectation on
`state t`. -/
def IsStrictlyNonEquilibriumAt (t : ℝ) : Prop :=
  0 < LQW.Q.entropicRate (LQW.state t)

/-- **All-times strictly non-equilibrium**: the QIF is strictly
non-equilibrium at every parameter.  Models the hovering-observer
regime: persistent dissipation throughout the worldline. -/
def IsAllTimesStrictlyNonEquilibrium : Prop :=
  ∀ t : ℝ, LQW.IsStrictlyNonEquilibriumAt t

/-- **Strict non-equilibrium contradicts equilibrium**: a state with
strictly positive entropic rate is not an equilibrium-QIF state. -/
theorem not_isEquilibriumAt_of_isStrictlyNonEquilibriumAt
    {t : ℝ} (h : LQW.IsStrictlyNonEquilibriumAt t) :
    ¬ LQW.IsEquilibriumAt t := by
  unfold IsEquilibriumAt QuantumInertialFrame.IsEquilibriumAt
    IsStrictlyNonEquilibriumAt at *
  linarith

/-- **Strict non-equilibrium forbids inertiality**: a strictly
non-equilibrium QIF cannot be inertial (because inertiality requires
all-times equilibrium). -/
theorem not_isInertial_of_isStrictlyNonEquilibriumAt
    {t : ℝ} (h : LQW.IsStrictlyNonEquilibriumAt t) :
    ¬ LQW.IsInertial := by
  intro h_inertial
  exact LQW.not_isEquilibriumAt_of_isStrictlyNonEquilibriumAt h
    (h_inertial.2 t)

end LorentzianQIFWorldline

/-- **Strict-dissipation bridge** (consumer-supplied constitutive
identification, dual to `LorentzianQIFEquilibriumBridge`): along any
positive-time interval where the QIF is strictly non-equilibrium at
*every* parameter, the worldline's `S_I_along` is strictly
increasing.

Operationally: persistent quantum-side dissipation drives strict
thermodynamic-side `S_I` growth.  This is the hovering-observer
regime of the three-probe thought experiment. -/
structure LorentzianQIFStrictDissipationBridge
    (LQW : LorentzianQIFWorldline H sd) : Prop where
  s_i_strict_mono_at_strictly_nonequilibrium :
    LQW.IsAllTimesStrictlyNonEquilibrium →
    ∀ {t₁ t₂ : ℝ}, t₁ < t₂ → LQW.W.S_I_along t₁ < LQW.W.S_I_along t₂

namespace LorentzianQIFStrictDissipationBridge

/-- **Strict-monotone `τ_ent` at all-times strict non-equilibrium**:
under the strict-dissipation bridge, the worldline's entropic-time
clock `τ_ent_along` is strictly increasing over any positive-time
interval — the hovering observer's clock accumulates monotonically.

This is the "non-equilibrium" companion of the `IsInertial` theorem:
the inertial frame freezes `τ_ent`; the hovering frame strictly
advances it. -/
theorem tauEnt_strict_mono_of_isAllTimesStrictlyNonEquilibrium
    {LQW : LorentzianQIFWorldline H sd}
    (B : LorentzianQIFStrictDissipationBridge LQW)
    (h_strict : LQW.IsAllTimesStrictlyNonEquilibrium)
    {t₁ t₂ : ℝ} (ht : t₁ < t₂) :
    LQW.W.τ_ent_along t₁ < LQW.W.τ_ent_along t₂ :=
  LQW.W.tau_ent_strict_when_S_I_strict (B.1 h_strict ht)

/-- **`τ_ent` advance is strictly positive** under all-times strict
non-equilibrium — the operational realisation of "detector
thermalisation grows linearly" (paper Eq. linear-growth, §4 of
`prl_entropic_qrf_body.tex`). -/
theorem tauEnt_advance_pos_of_isAllTimesStrictlyNonEquilibrium
    {LQW : LorentzianQIFWorldline H sd}
    (B : LorentzianQIFStrictDissipationBridge LQW)
    (h_strict : LQW.IsAllTimesStrictlyNonEquilibrium)
    {t₁ t₂ : ℝ} (ht : t₁ < t₂) :
    0 < LQW.W.τ_ent_along t₂ - LQW.W.τ_ent_along t₁ := by
  have h := tauEnt_strict_mono_of_isAllTimesStrictlyNonEquilibrium B h_strict ht
  linarith

end LorentzianQIFStrictDissipationBridge

end Physlib.Relativity.Special.QuantumInertialFrameLorentzian

end
