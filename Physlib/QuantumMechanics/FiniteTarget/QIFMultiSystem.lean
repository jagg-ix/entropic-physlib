/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameReversible

/-!
# Multi-subsystem Quantum Inertial Frame

Extends QIF from a single subsystem (`H_R, H_I, ℏ` on a single
Hilbert space `H`) to an **N-subsystem system** where each
subsystem `i : Fin N` carries its own QIF independently.

This is the operator-level scaffolding for the **density-as-locality
picture** (your insight): a system with N subsystems can be in any
of several regimes depending on how strongly they are coupled:

* **Sparse / low-density**: subsystems decouple, each is its own
  independent inertial QIF.  "Two drops in a glass" — each drop is
  inertial relative to the other.
* **Synchronized / high-density**: subsystems lock together via a
  shared collective phase (the Kuramoto-network limit) → single
  effective inertial QIF.

This file provides the **carrier + coupling parameter + independence
predicate**; the Kuramoto-network classical analog and the
density-locality bridge come in later files.

## Honest scope

The current `MultiQIF` carrier is **structural scaffolding** — it
bundles N independent QIFs with a `coupling : ℝ` metadata field.
The coupling does *not* yet enter the operational predicates
(`IsAllSubsystemsInertial`, `PairIsInertial`): those predicates
reduce to "every subsystem is at equilibrium QIF" regardless of
the coupling value.

For the coupling to acquire operational content (so that
"decoupled ⟹ mutually inertial" becomes a non-trivial theorem),
the carrier would need a *joint Hamiltonian* `H_joint = ⊕ H_R^{(i)}
+ g · V_inter` with `V_inter` coupling subsystems, plus a notion of
*reduced state* per subsystem that depends on the joint dynamics.
That extension is left for future work.

Contents: the carrier, the elementary predicates,
and the `allReversible` constructor showing that reversible
subsystems are at equilibrium on any state.  The "two drops in a
glass" intuition is **documented but not formally derived** —
proving it requires the coupling-aware joint-Hamiltonian extension
above.

## Main definitions

* `MultiQIF N H` — N independent `QuantumInertialFrame H` instances
  + a `coupling : ℝ` metadata field.
* `MultiQIF.IsDecoupled` — predicate `coupling = 0`.
* `MultiQIF.IsAllSubsystemsInertial` — every subsystem individually
  satisfies the QIF equilibrium condition.
* `MultiQIF.PairIsInertial` — conjunction of two equilibrium
  predicates (no bridge content beyond the conjunction).
* `MultiQIF.allReversible` — N reversible (`H_I = 0`) subsystems
  + zero coupling; carrier-level "N drops" instance.
* `MultiQIF.allReversible_isAllSubsystemsInertial` — every state
  is at equilibrium for the all-reversible MultiQIF (substantive
  content, follows from `reversibleQIF_isEquilibriumAt`).

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics.FiniteTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]


/-- **Multi-subsystem Quantum Inertial Frame**: `N` independent
`QuantumInertialFrame H` instances together with a **coupling
strength** `coupling : ℝ` representing the effective inter-subsystem
interaction strength.

* At `coupling = 0`: subsystems are operationally independent
  (each is its own inertial QIF in the limit).
* At `coupling > 0`: subsystems interact; the joint dynamics is
  not just the tensor product of single-subsystem dynamics.

The coupling parameter is the *density proxy*: in the consumer's
physical interpretation, it could be mass density, number density,
mean-field coupling strength, Kuramoto-network `K`, etc.  The QIF
carrier doesn't commit to any particular interpretation — it just
needs the scalar parameter. -/
structure MultiQIF (N : ℕ) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H] where
  /-- `N` independent QIF subsystems. -/
  subsystems     : Fin N → QuantumInertialFrame H
  /-- Effective coupling strength between subsystems (`0` = no
  interaction, `> 0` = interacting). -/
  coupling       : ℝ
  /-- Coupling is non-negative (interactions cannot reduce below
  zero in any sensible physical convention). -/
  coupling_nonneg : 0 ≤ coupling

namespace MultiQIF

variable {N : ℕ}


/-- **Decoupled regime**: the coupling strength vanishes.  At
this limit, the subsystems are operationally independent — each
evolves under its own QIF generator without mean-field interaction. -/
def IsDecoupled (M : MultiQIF N H) : Prop :=
  M.coupling = 0

/-- **All subsystems inertial at a state-pair-tuple**: every
subsystem `i` is at equilibrium QIF on its own quantum state `ψ i`.

`ψ : Fin N → H` is a tuple of pure states, one per subsystem.  This
is the operational definition of "all N subsystems are individually
inertial" at the operator level. -/
def IsAllSubsystemsInertial (M : MultiQIF N H) (ψ : Fin N → H) : Prop :=
  ∀ i : Fin N, (M.subsystems i).IsEquilibriumAt (ψ i)

/-- **Pair of subsystems is at equilibrium**: a weaker version of
`IsAllSubsystemsInertial` for just two subsystems. -/
def PairIsInertial (M : MultiQIF N H) (i j : Fin N) (ψ_i ψ_j : H) : Prop :=
  (M.subsystems i).IsEquilibriumAt ψ_i ∧
  (M.subsystems j).IsEquilibriumAt ψ_j

/-!

A previous draft (commit `5577533c`) of this file shipped theorems
named `subsystemsAreMutuallyInertial`,
`allMutuallyInertial_of_isAllSubsystemsInertial`, and `dropsInAGlass`
that took a `M.IsDecoupled` hypothesis but did **not use it** in
their proofs.  The current `MultiQIF` carrier has `coupling : ℝ` as
a **metadata field** only — it does not appear in the operational
predicates `IsAllSubsystemsInertial` or `PairIsInertial`.  So the
"decoupled ⟹ mutually inertial" framing was vacuous (the
conclusion held whether or not the coupling was zero).

Those over-claimed theorems have been removed.  The "drops in a
glass" content is left as the COMBINATION of two genuinely
independent facts, supplied by the consumer per situation:

* `allReversible_isAllSubsystemsInertial` (every state is at
  equilibrium for a reversible subsystem — substantive content).
* `PairIsInertial` predicate (just the conjunction of two
  equilibrium statements — no bridge content).

For a *substantive* "drops in a glass" theorem, future work would
need the coupling to actually appear in the dynamics: e.g., a
joint Hamiltonian `H_joint = ⊕ H_R^{(i)} + g · V_inter` where
`V_inter` couples subsystems, with the claim that single-subsystem
equilibrium predicates hold for the *reduced* states only at `g = 0`
(or under additional decoupling hypotheses).  The current carrier
does not encode `V_inter`; that's the gap.
-/


/-- The **all-reversible MultiQIF**: every subsystem is reversible
(`H_I = 0`), the coupling is zero (sparse limit).

This is the "N drops in an infinitely large glass" picture:
N free quantum subsystems with no interaction, all reversible. -/
def allReversible (N : ℕ) (H_R : Fin N → H →L[ℂ] H)
    (hbar : ℝ) (hbar_pos : 0 < hbar) :
    MultiQIF N H where
  subsystems      := fun i => reversibleQIF (H_R i) hbar hbar_pos
  coupling        := 0
  coupling_nonneg := le_refl 0

/-- The all-reversible MultiQIF is decoupled (by construction). -/
@[simp] lemma allReversible_isDecoupled
    (N : ℕ) (H_R : Fin N → H →L[ℂ] H)
    (hbar : ℝ) (hbar_pos : 0 < hbar) :
    (allReversible N H_R hbar hbar_pos).IsDecoupled := rfl

/-- **Every subsystem of the all-reversible MultiQIF is at
equilibrium QIF on any state**: trivially, since each subsystem is
reversible (`H_I = 0`). -/
lemma allReversible_isAllSubsystemsInertial
    (N : ℕ) (H_R : Fin N → H →L[ℂ] H)
    (hbar : ℝ) (hbar_pos : 0 < hbar) (ψ : Fin N → H) :
    (allReversible N H_R hbar hbar_pos).IsAllSubsystemsInertial ψ := by
  intro i
  exact reversibleQIF_isEquilibriumAt (H_R i) hbar hbar_pos (ψ i)

end MultiQIF

end QuantumMechanics.FiniteTarget

end
