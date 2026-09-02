/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameCPTP
public import QuantumInfo.States.Mixed.MState

/-!
# Mixed-state Quantum Inertial Frame (Schrödinger picture, density matrix)

Extends the QIF framework from **pure states** `ψ : H` to **mixed
states** `ρ : MState d` — the density-matrix carrier.

Until this file, every QIF consumer (Lindblad, free, Unruh, KMS,
etc.) bundled a *pure state* `ψ : H` (the `state : ℝ → H` field of
`LorentzianQIFWorldline`).  Thermal states, statistical ensembles,
and Kuramoto-network reduced states are intrinsically mixed —
they need a density-matrix carrier.

This file provides the natural extension: a `MixedStateQIF d` whose
worldline carries `ρ : ℝ → MState d` evolved by a CPTP semigroup
`Φ_t = QIFSemigroupCPTP.Φ t : MState d → MState d`.

Companion to `QIFHeisenbergPicture.lean`: that file provides the
Heisenberg picture (operators evolve, state is stationary); this
file provides the Schrödinger picture for mixed states (state
evolves, operator is fixed).

## Why mixed states matter for the QIF framework

* **Thermal states** (KMS / Gibbs) are mixed by construction
  (`ρ = exp(−βH)/Z`).  Pure-state QIF can describe only the
  expectation-value content; mixed-state QIF carries the full
  thermal density matrix.
* **Reduced states** of a multi-subsystem QIF (the Kuramoto network
  picture) are typically mixed even when the joint state is pure.
* **Classical limits** are most natural at the density-matrix
  level: classical probability distributions on phase space ↔
  diagonal density matrices.

## Carrier

`MixedStateQIF d` — a CPTP semigroup `Φ : ℝ → CPTPMap d d ℂ`
together with an initial density matrix `ρ₀ : MState d`.  The
worldline state is `ρ(t) := Φ_t(ρ₀)`.

## Main definitions and theorems

* `MixedStateQIF.stateTrajectory t := semigroup.Φ t initialState` —
  the time-evolved density matrix.
* `MixedStateQIF.stateTrajectory_zero` — `ρ(0) = ρ₀` (identity at
  zero).
* `MixedStateQIF.stateTrajectory_compose` — semigroup composition:
  `ρ(t₁ + t₂) = Φ_{t₁}(ρ(t₂))`.
* `MixedStateQIF.IsStationary` — predicate: `Φ_t(ρ₀) = ρ₀` for
  every `t`.  KMS / equilibrium states are stationary in this sense
  (the Schrödinger dual of `KMSStateFunctional.ω_invariant`).
* `MixedStateQIF.trivial d` — identity CPTP semigroup + uniform
  state; stationary by construction.

## Cross-references

* `QIFHeisenbergPicture.lean` — dual picture (operators evolve).
* `QIFSemigroupCPTP` — the CPTP-proper semigroup carrier.
* `kmsQIF_ofState` — constructs a *pure-state* (reversible) QIF
  from a density matrix via the modular Hamiltonian; this file
  carries the *density-matrix* itself as the QIF's evolving state.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open QuantumInfo.Finite

namespace QuantumMechanics.FiniteTarget


/-- **Mixed-state Quantum Inertial Frame** on a finite-dimensional
density-matrix space `MState d`.

Bundles a `QIFSemigroupCPTP d` (one-parameter CPTP family with
identity-at-zero and group-style composition law) with an initial
density matrix `ρ₀`.  The worldline state is `ρ(t) := Φ_t(ρ₀)`,
landing in `MState d` at every parameter (`MState`-valued
trajectory).

Physically: instead of carrying a pure state `ψ : ℝ → H`,
the carrier carries a density matrix `ρ : ℝ → MState d`.  This is
the natural mixed-state extension of the QIF carrier. -/
structure MixedStateQIF (d : Type*) [Fintype d] [DecidableEq d] where
  /-- CPTP semigroup driving the density-matrix evolution. -/
  semigroup    : QIFSemigroupCPTP d
  /-- Initial density matrix `ρ₀`. -/
  initialState : MState d

namespace MixedStateQIF

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The **state trajectory** of the mixed-state QIF:
`ρ(t) := Φ_t(ρ₀)`.  Schrödinger-picture evolution at the
density-matrix level. -/
def stateTrajectory (M : MixedStateQIF d) (t : ℝ) : MState d :=
  M.semigroup.Φ t M.initialState

/-- The state at `t = 0` is the initial density matrix `ρ₀`. -/
@[simp] lemma stateTrajectory_zero (M : MixedStateQIF d) :
    M.stateTrajectory 0 = M.initialState := by
  unfold stateTrajectory
  rw [M.semigroup.Φ_zero]
  exact CPTPMap.id_MState _

/-- **Semigroup composition** at the state-trajectory level:
`ρ(s + t) = Φ_s(ρ(t))`.  Pulls back the `QIFSemigroupCPTP.Φ_compose`
identity through application. -/
lemma stateTrajectory_compose (M : MixedStateQIF d) (s t : ℝ) :
    M.stateTrajectory (s + t) =
      M.semigroup.Φ s (M.stateTrajectory t) := by
  unfold stateTrajectory
  rw [M.semigroup.Φ_compose s t]
  exact CPTPMap.compose_eq _


/-- **Stationarity predicate**: the initial state is fixed by the
CPTP semigroup at every `t` (`Φ_t(ρ₀) = ρ₀`).

KMS / equilibrium states satisfy this — they are exactly the
density matrices invariant under the modular flow (the Schrödinger
dual of `KMSStateFunctional.ω_invariant`).  Stationary mixed-state
QIFs are the *equilibrium* mixed-state QIFs. -/
def IsStationary (M : MixedStateQIF d) : Prop :=
  ∀ t : ℝ, M.semigroup.Φ t M.initialState = M.initialState

/-- For a stationary mixed-state QIF, the trajectory is constant:
`ρ(t) = ρ₀` for every `t`. -/
lemma stateTrajectory_eq_initial_of_isStationary
    (M : MixedStateQIF d) (h : M.IsStationary) (t : ℝ) :
    M.stateTrajectory t = M.initialState := h t


/-- The **trivial mixed-state QIF** with identity CPTP semigroup
and consumer-supplied initial state.  Trivially stationary (the
state never evolves). -/
def trivial (d : Type*) [Fintype d] [DecidableEq d] (ρ₀ : MState d) :
    MixedStateQIF d where
  semigroup    := QIFSemigroupCPTP.trivial d
  initialState := ρ₀

/-- The trivial mixed-state QIF is stationary at every `t`. -/
lemma trivial_isStationary (d : Type*) [Fintype d] [DecidableEq d]
    (ρ₀ : MState d) :
    (trivial d ρ₀).IsStationary := by
  intro t
  unfold trivial
  rw [QIFSemigroupCPTP.trivial_Φ]
  exact CPTPMap.id_MState _

/-- The trivial mixed-state QIF's trajectory is the constant `ρ₀`. -/
@[simp] lemma trivial_stateTrajectory
    (d : Type*) [Fintype d] [DecidableEq d] (ρ₀ : MState d) (t : ℝ) :
    (trivial d ρ₀).stateTrajectory t = ρ₀ := by
  exact stateTrajectory_eq_initial_of_isStationary _
    (trivial_isStationary d ρ₀) t

end MixedStateQIF

end QuantumMechanics.FiniteTarget

end
