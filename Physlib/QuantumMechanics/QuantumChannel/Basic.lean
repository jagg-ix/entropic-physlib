/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Basic

/-!
# Abstract quantum channels — monoidal composition algebra

This module provides the bare algebraic skeleton of a category of quantum
channels, expressed at the level of types and equations rather than as
concrete CPTP maps on density operators.

The structure `QuantumChannelBackend` packages a `State` type, a `Channel`
type, channel application, channel composition, an identity channel, and
the three laws (`channelCompose_apply`, `channelId_apply`,
`channelCompose_assoc`) that make `(Channel, channelCompose, channelId)`
act monoidally on states.

`QuantumChannelPair` packages two channels — a *computation* lane and a
*communication* lane — and supports component-wise sequential composition
under `sequentialCompose`.  This is the abstract scaffold consumed by
downstream QTM modules to express the `Re S` / `Im S` duality of
the complex action; here it is presented purely as monoidal
algebra, with no quantum-information specialisation, no spacetime
attachment, and no entropic-time vocabulary.


## References

- **Bennett 1982** — *The thermodynamics of computation — a review*
- **Lindblad 1976** — *On the generators of quantum dynamical semigroups*
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.QuantumChannel

/-- An abstract quantum channel backend.

* `State` is the type of quantum states (density operators, vectors,
  Liouville kets — whatever the consumer chooses).
* `Channel` is the type of channels acting on states.
* `applyChannel`, `channelCompose`, `channelId` are channel application,
  binary composition, and the identity channel.
* The three laws make `Channel` act monoidally on `State` via
  `applyChannel`. -/
structure QuantumChannelBackend where
  /-- The type of states the backend acts on. -/
  State : Type
  /-- The type of channels acting on `State`. -/
  Channel : Type
  /-- Apply a channel to a state. -/
  applyChannel : Channel → State → State
  /-- Compose two channels. -/
  channelCompose : Channel → Channel → Channel
  /-- The identity channel. -/
  channelId : Channel
  /-- Composition acts on states by applying the right factor first. -/
  channelCompose_apply :
    ∀ (Φ Ψ : Channel) (ρ : State),
      applyChannel (channelCompose Φ Ψ) ρ =
        applyChannel Φ (applyChannel Ψ ρ)
  /-- The identity channel is neutral on states. -/
  channelId_apply :
    ∀ ρ : State, applyChannel channelId ρ = ρ
  /-- Associativity of composition (stated on states). -/
  channelCompose_assoc :
    ∀ (Φ₁ Φ₂ Φ₃ : Channel) (ρ : State),
      applyChannel (channelCompose Φ₁ (channelCompose Φ₂ Φ₃)) ρ =
        applyChannel (channelCompose (channelCompose Φ₁ Φ₂) Φ₃) ρ

/-- A pair of channels acting on the same backend — a *computation* lane
and a *communication* lane.

This is the algebraic structure consumed by the `Re S = computation`
and `Im S = communication` identification.  At this layer the two lanes
are interchangeable; the entropic-time layer breaks symmetry by naming which
lane records dissipation and which records phase. -/
structure QuantumChannelPair (backend : QuantumChannelBackend) where
  /-- The computation lane (Landauer / dissipative direction). -/
  computationChannel : backend.Channel
  /-- The communication lane (Shannon / unitary direction). -/
  communicationChannel : backend.Channel

namespace QuantumChannelPair

variable {backend : QuantumChannelBackend}

/-- `n`-fold application of the computation lane to a state. -/
def applyCompN (R : QuantumChannelPair backend) (n : ℕ) (ρ : backend.State) :
    backend.State :=
  Nat.rec ρ (fun _ acc => backend.applyChannel R.computationChannel acc) n

/-- `n`-fold application of the communication lane to a state. -/
def applyCommN (R : QuantumChannelPair backend) (n : ℕ) (ρ : backend.State) :
    backend.State :=
  Nat.rec ρ (fun _ acc => backend.applyChannel R.communicationChannel acc) n

@[simp] theorem applyCompN_zero (R : QuantumChannelPair backend) (ρ : backend.State) :
    R.applyCompN 0 ρ = ρ := rfl

@[simp] theorem applyCompN_succ
    (R : QuantumChannelPair backend) (n : ℕ) (ρ : backend.State) :
    R.applyCompN (Nat.succ n) ρ =
      backend.applyChannel R.computationChannel (R.applyCompN n ρ) := rfl

@[simp] theorem applyCommN_zero (R : QuantumChannelPair backend) (ρ : backend.State) :
    R.applyCommN 0 ρ = ρ := rfl

@[simp] theorem applyCommN_succ
    (R : QuantumChannelPair backend) (n : ℕ) (ρ : backend.State) :
    R.applyCommN (Nat.succ n) ρ =
      backend.applyChannel R.communicationChannel (R.applyCommN n ρ) := rfl

/-- The identity pair: both lanes are the backend identity channel. -/
def identityPair (backend : QuantumChannelBackend) : QuantumChannelPair backend where
  computationChannel := backend.channelId
  communicationChannel := backend.channelId

/-- Sequential composition of two channel pairs: `R1` is applied first,
then `R2`, lane by lane. -/
def sequentialCompose (R1 R2 : QuantumChannelPair backend) :
    QuantumChannelPair backend where
  computationChannel := backend.channelCompose R2.computationChannel R1.computationChannel
  communicationChannel := backend.channelCompose R2.communicationChannel R1.communicationChannel

/-- The computation lane of a composed pair acts as the composition of the
two computation channels on states. -/
theorem sequentialCompose_computation_apply
    (R1 R2 : QuantumChannelPair backend) (ρ : backend.State) :
    backend.applyChannel (sequentialCompose R1 R2).computationChannel ρ =
      backend.applyChannel R2.computationChannel
        (backend.applyChannel R1.computationChannel ρ) := by
  simpa [sequentialCompose] using
    backend.channelCompose_apply R2.computationChannel R1.computationChannel ρ

/-- The communication lane of a composed pair acts as the composition of
the two communication channels on states. -/
theorem sequentialCompose_communication_apply
    (R1 R2 : QuantumChannelPair backend) (ρ : backend.State) :
    backend.applyChannel (sequentialCompose R1 R2).communicationChannel ρ =
      backend.applyChannel R2.communicationChannel
        (backend.applyChannel R1.communicationChannel ρ) := by
  simpa [sequentialCompose] using
    backend.channelCompose_apply R2.communicationChannel R1.communicationChannel ρ

/-- Left identity of sequential composition on the computation lane: the
identity pair on the left is a left unit. -/
theorem sequentialCompose_left_identity_computation
    (R : QuantumChannelPair backend) (ρ : backend.State) :
    backend.applyChannel
        (sequentialCompose (identityPair backend) R).computationChannel ρ =
      backend.applyChannel R.computationChannel ρ := by
  have h := backend.channelCompose_apply R.computationChannel backend.channelId ρ
  simpa [identityPair, sequentialCompose, backend.channelId_apply ρ] using h

/-- Right identity of sequential composition on the computation lane: the
identity pair on the right is a right unit. -/
theorem sequentialCompose_right_identity_computation
    (R : QuantumChannelPair backend) (ρ : backend.State) :
    backend.applyChannel
        (sequentialCompose R (identityPair backend)).computationChannel ρ =
      backend.applyChannel R.computationChannel ρ := by
  have h := backend.channelCompose_apply backend.channelId R.computationChannel ρ
  simpa [identityPair, sequentialCompose,
    backend.channelId_apply (backend.applyChannel R.computationChannel ρ)] using h

/-- Left identity of sequential composition on the communication lane. -/
theorem sequentialCompose_left_identity_communication
    (R : QuantumChannelPair backend) (ρ : backend.State) :
    backend.applyChannel
        (sequentialCompose (identityPair backend) R).communicationChannel ρ =
      backend.applyChannel R.communicationChannel ρ := by
  have h := backend.channelCompose_apply R.communicationChannel backend.channelId ρ
  simpa [identityPair, sequentialCompose, backend.channelId_apply ρ] using h

/-- Right identity of sequential composition on the communication lane. -/
theorem sequentialCompose_right_identity_communication
    (R : QuantumChannelPair backend) (ρ : backend.State) :
    backend.applyChannel
        (sequentialCompose R (identityPair backend)).communicationChannel ρ =
      backend.applyChannel R.communicationChannel ρ := by
  have h := backend.channelCompose_apply backend.channelId R.communicationChannel ρ
  simpa [identityPair, sequentialCompose,
    backend.channelId_apply (backend.applyChannel R.communicationChannel ρ)] using h

end QuantumChannelPair

end Physlib.QuantumMechanics.QuantumChannel
