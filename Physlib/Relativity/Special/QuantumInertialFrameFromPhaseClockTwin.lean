/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameReversible
public import Physlib.Relativity.Special.QuantumInertialFrameLorentzian
public import Physlib.Relativity.Special.PhaseClock.Relativistic
public import Physlib.Relativity.Special.TwinParadox.Entropic

/-!
# Quantum Inertial Frame instances from `PhaseClock` and `InstantaneousTwinParadox`

Concrete consumers of `LorentzianQIFWorldline` and
`LorentzianQIFEquilibriumBridge` that wire a **reversible** QIF
(`H_I = 0`, from
`Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameReversible`)
to physlib's existing worldline carriers:

* `Physlib.QuantumMechanics.Clock.Phase.PhaseClock` and the SR /
  lapse-field couplings in
  `Physlib.Relativity.Special.PhaseClock.Relativistic`.
* `Physlib.Relativity.Special.TwinParadox.Basic.InstantaneousTwinParadox`
  and its entropic-time refinement in
  `Physlib.Relativity.Special.TwinParadox.Entropic` (which already
  defines `trivialReversibleArrow`, an `EntropyArrowWorldline` with
  `S_I_along ≡ 0`).

The pattern mirrors `fromLindbladJump` (commit `bef63391`): build a
specific `LorentzianQIFWorldline` from a physical model and **derive**
the equilibrium-reversible bridge as a theorem.  For the reversible
regime the derivation is *unconditional*: both sides of the bridge
(`W.IsReversible` and `IsAllTimesEquilibrium`) hold for any
`H_R`-eigenstate-or-any-state, since `H_I = 0`.


`fromReversible` packages:
* a reversible operator-level QIF (`reversibleQIF H_R ℏ ℏ_pos`),
* a `trivialReversibleArrow` entropy arrow (`S_I_along ≡ 0`),
* a frozen state assignment `state := fun _ => ψ`,
* a consumer-supplied worldline `γ : ℝ → SpaceTime sd`.


For SR constant-velocity (`SRConstantVelocityEntropicCoupling`) and
static-lapse (`LapseEntropicCoupling`) phase-clock couplings, the
reversible QIF's worldline is exactly the geometric trajectory; the
QIF's `λ ≡ 0` is consistent with the existing entropic coupling
identifying the worldline's `τ_ent` advance with the SR / lapse
proper-time formula at the **equilibrium / `Δτ_ent = 0`** limit.


Both twins in `InstantaneousTwinParadox` give reversible
Lorentzian-QIF worldlines (twin A on a single leg, twin B on each of
two legs).  At the operator level both are at every-time equilibrium
(`H_I = 0`), so the age gap `T.ageGap` is **purely geometric**: a
difference of Minkowski proper times, no entropic contribution.

This realises the standard SR twin paradox as the **inertial-QIF
limit** of the entropic-time twin paradox (companion to
`twin_paradox_at_frozen_LRF` in `TwinParadox/Entropic.lean`).

## References

  the inertial frame.
* Sergi & Giaquinta 2016 — reversible limit `H_I = 0`.
* Tooby-Smith et al. (physlib) — `PhaseClock`,
  `InstantaneousTwinParadox`, `trivialReversibleArrow`.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special.QuantumInertialFrameLorentzian

open QuantumMechanics.FiniteTarget
open Physlib.Thermodynamics.SecondLaw
open Physlib.Relativity.Special.TwinParadox.Entropic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]


/-- **Build a Lorentzian QIF worldline from a reversible
operator-level QIF**.

`fromReversible H_R ℏ ℏ_pos ψ γ` bundles:

* the reversible QIF `reversibleQIF H_R ℏ ℏ_pos` (with `H_I = 0`),
* the `trivialReversibleArrow ℏ ℏ_pos` entropy arrow
  (`S_I_along ≡ 0`),
* the frozen state `state := fun _ => ψ`,
* the consumer-supplied spacetime worldline `γ : ℝ → SpaceTime sd`.

Any quantum state ψ : H and any worldline γ are accepted; no
positivity / kernel / coupling hypotheses are needed because
`H_I = 0`. -/
def fromReversible (sd : ℕ)
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H)
    (γ : ℝ → SpaceTime sd) :
    LorentzianQIFWorldline H sd where
  Q         := reversibleQIF H_R hbar hbar_pos
  W         := trivialReversibleArrow hbar hbar_pos
  state     := fun _ => ψ
  worldline := γ

namespace fromReversible

variable {sd : ℕ}
  (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H)
  (γ : ℝ → SpaceTime sd)

/-- The reversible Lorentzian QIF is at all-times equilibrium —
*unconditionally*, since `H_I = 0`. -/
lemma isAllTimesEquilibrium :
    (fromReversible sd H_R hbar hbar_pos ψ γ).IsAllTimesEquilibrium := by
  intro _
  exact reversibleQIF_isEquilibriumAt H_R hbar hbar_pos ψ

/-- The reversible Lorentzian QIF's entropy arrow is reversible —
*unconditionally*, by `trivialReversibleArrow_isReversible`. -/
lemma isReversible :
    (fromReversible sd H_R hbar hbar_pos ψ γ).W.IsReversible :=
  trivialReversibleArrow_isReversible hbar hbar_pos

/-- **equilibrium-reversible bridge for the reversible
construction**.  The `LorentzianQIFEquilibriumBridge` is *derived as
a theorem* (no consumer-supplied `Prop`): both sides of the
biconditional hold unconditionally, so the iff is trivially true.

Pattern parallel to `fromLindbladJump.equilibriumBridge` (commit
`bef63391`): both sides reduce to the same operational anchor, here
the trivial anchor `True`. -/
lemma equilibriumBridge :
    LorentzianQIFEquilibriumBridge
      (fromReversible sd H_R hbar hbar_pos ψ γ) where
  reversible_iff_equilibrium :=
    ⟨fun _ => isAllTimesEquilibrium H_R hbar hbar_pos ψ γ,
     fun _ => isReversible H_R hbar hbar_pos ψ γ⟩

/-- **TISE recovery at `H_R`-eigenstates** along the reversible
Lorentzian QIF.  Specialisation of
`QuantumInertialFrame.tise_at_equilibrium` to the reversible
construction: any `H_R`-eigenstate ψ satisfies the TISE for the full
complex Hamiltonian `H_C = H_R - i·H_I = H_R` (since `H_I = 0`). -/
lemma tise_at_eigenstate
    {E : ℂ} (h_eig : H_R ψ = E • ψ) :
    (fromReversible sd H_R hbar hbar_pos ψ γ).Q.complexHamiltonian ψ
      = E • ψ :=
  reversibleQIF_tise H_R hbar hbar_pos h_eig

end fromReversible


/-- **The reversible QIF is inertial whenever the worldline is
affine** (geodesic in SR sense).

Since the all-times-equilibrium half of `IsInertial` holds
unconditionally for the reversible construction, the only
non-trivial input is the geometric-inertiality half: the worldline
`γ` is affine.

For SR constant-velocity (`SRConstantVelocityEntropicCoupling`)
trajectories `γ t = q + t • u`, this lifts the reversible QIF
worldline to the full `IsInertial` predicate, unlocking the §4
main theorem `totalProperTime_eq_properTime_at_inertial`. -/
lemma fromReversible_isInertial
    {sd : ℕ}
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H)
    (γ : ℝ → SpaceTime sd)
    (h_affine :
      (fromReversible sd H_R hbar hbar_pos ψ γ).IsGeodesicAffine) :
    (fromReversible sd H_R hbar hbar_pos ψ γ).IsInertial :=
  ⟨h_affine, fromReversible.isAllTimesEquilibrium H_R hbar hbar_pos ψ γ⟩

/-- **Linear-affine worldline lifts to inertial**: for any
constant-velocity worldline `γ t = q + t • u`, the reversible QIF is
inertial.  Convenience theorem packaging the `IsGeodesicAffine`
witness inline. -/
lemma fromReversible_isInertial_of_linearAffine
    {sd : ℕ}
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H)
    (q u : SpaceTime sd) :
    (fromReversible sd H_R hbar hbar_pos ψ (fun t => q + t • u)).IsInertial :=
  fromReversible_isInertial H_R hbar hbar_pos ψ (fun t => q + t • u)
    ⟨q, u, fun _ => rfl⟩


open SpecialRelativity

/-- **Twin A as a reversible Lorentzian-QIF worldline**.

In an `InstantaneousTwinParadox T`, twin A travels at constant
velocity from `T.startPoint` to `T.endPoint`.  Equipping twin A with
a reversible QIF `(H_R, ψ)` and the constant-velocity worldline
`t ↦ T.startPoint + t • (T.endPoint − T.startPoint)` realises twin A
as a reversible Lorentzian-QIF worldline; the affine form makes the
worldline geodesic-inertial. -/
def twinA (T : InstantaneousTwinParadox)
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    LorentzianQIFWorldline H 3 :=
  fromReversible 3 H_R hbar hbar_pos ψ
    (fun t => T.startPoint + t • (T.endPoint - T.startPoint))

/-- Twin A's reversible Lorentzian-QIF worldline is **inertial**:
the worldline is affine (constant-velocity), and the QIF is at
all-times equilibrium. -/
lemma twinA_isInertial (T : InstantaneousTwinParadox)
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (twinA T H_R hbar hbar_pos ψ).IsInertial :=
  fromReversible_isInertial_of_linearAffine H_R hbar hbar_pos ψ
    T.startPoint (T.endPoint - T.startPoint)

/-- **Twin B (first leg)**: constant velocity from `T.startPoint` to
`T.twinBMid`. -/
def twinB_leg1 (T : InstantaneousTwinParadox)
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    LorentzianQIFWorldline H 3 :=
  fromReversible 3 H_R hbar hbar_pos ψ
    (fun t => T.startPoint + t • (T.twinBMid - T.startPoint))

/-- Twin B's first leg is inertial. -/
lemma twinB_leg1_isInertial (T : InstantaneousTwinParadox)
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (twinB_leg1 T H_R hbar hbar_pos ψ).IsInertial :=
  fromReversible_isInertial_of_linearAffine H_R hbar hbar_pos ψ
    T.startPoint (T.twinBMid - T.startPoint)

/-- **Twin B (second leg)**: constant velocity from `T.twinBMid` to
`T.endPoint`. -/
def twinB_leg2 (T : InstantaneousTwinParadox)
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    LorentzianQIFWorldline H 3 :=
  fromReversible 3 H_R hbar hbar_pos ψ
    (fun t => T.twinBMid + t • (T.endPoint - T.twinBMid))

/-- Twin B's second leg is inertial. -/
lemma twinB_leg2_isInertial (T : InstantaneousTwinParadox)
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (twinB_leg2 T H_R hbar hbar_pos ψ).IsInertial :=
  fromReversible_isInertial_of_linearAffine H_R hbar hbar_pos ψ
    T.twinBMid (T.endPoint - T.twinBMid)

/-- **Twin paradox theorem — both twins are reversible inertial QIFs**.

For an `InstantaneousTwinParadox T` equipped with a reversible
operator-level QIF `(H_R, ℏ, ψ)`, both twins (and both of twin B's
legs) realise the `IsInertial` predicate as reversible Lorentzian-QIF
worldlines.

This identifies the standard SR twin paradox as the inertial-QIF
limit of the entropic twin paradox: the age gap
`T.ageGap = properTimeTwinA − properTimeTwinB` is *purely geometric*
because both twins are at equilibrium QIF (`H_I = 0`) throughout —
the entropic-time contribution vanishes (`τ_ent_along ≡ 0` via
`trivialReversibleArrow`).

The standard SR result `ageGap_nonneg_of` then applies unchanged —
the QIF lens does not change the result; it identifies the
operational reason both twins fall in the same (equilibrium-QIF /
inertial) class. -/
lemma twinParadox_both_inertial
    (T : InstantaneousTwinParadox)
    (H_R : H →L[ℂ] H) (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : H) :
    (twinA T H_R hbar hbar_pos ψ).IsInertial ∧
    (twinB_leg1 T H_R hbar hbar_pos ψ).IsInertial ∧
    (twinB_leg2 T H_R hbar hbar_pos ψ).IsInertial :=
  ⟨twinA_isInertial T H_R hbar hbar_pos ψ,
   twinB_leg1_isInertial T H_R hbar hbar_pos ψ,
   twinB_leg2_isInertial T H_R hbar hbar_pos ψ⟩

end Physlib.Relativity.Special.QuantumInertialFrameLorentzian

end
