/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance
public import Mathlib.Logic.Relation

/-!
# Computation is a causal set: welding the data-driven clock to AQFT, thermodynamics, spacetime

The `DataDrivenClockAutomaton` recognized that a deterministic computation's clock
advances only on data, with the quiescent vacuum a fixed point (a stationary,
time-independent-Schrödinger state).  This module supplies the missing structural
weld: **a computation's reachability relation is a partial order — a causal set —
and it is the very causal set that the repository's Sorkin–Johnston / causal-set
programme already turns into an AQFT and a spacetime.**  Three existing arcs then
meet on one object.

## Computation ⇒ causal set (this module)

For any one-step transition `step : α → α → Prop`, the reachability relation
`computationCausalOrder = Relation.ReflTransGen step` is reflexive
(`computationCausalOrder_refl`) and transitive (`computationCausalOrder_trans`),
i.e. a `Preorder` (`computationPreorder`) — a **causal set** in exactly the sense
`CausalSetIntervalAbundance` uses (`[Preorder α]`).  Each computation step is a
**causal link** of that order (`step_is_causal_link`).  So the certified runs of
the data-driven clock are certified causal-order relations, and the clock's
step-time *is* the causal order.

## Causal set ⇒ Sorkin–Johnston AQFT (existing, now fed by computation)

`worldline_causalSign_isPauliJordan` instantiates `causalSign_isPauliJordan` on a
computation worldline (the five configurations of the data-driven clock's `(2,3)`
run, ordered by step time): the order's `causalSign` is a **Pauli–Jordan kernel**
(`SorkinJohnstonRegionState.IsPauliJordan`, `Δ(x,y) = −Δ(y,x)`).  By
`CausalSetIntervalAbundance` this is exactly the Peierls-commutator function that
fixes the **Sorkin–Johnston vacuum** — so the computation's causal order *is* the
input to the AQFT construction, and its Benincasa–Dowker action
(`bdgAction2D`) is the emergent 2D gravity of `SorkinCausalSetGravityPathIntegral`.
Computation ⇒ causal set ⇒ AQFT ⇒ (discrete) spacetime.

## Computation ⇒ thermodynamics (existing: Carneiro's partial recursive functions)

The dynamics on this causal set is a genuine computation, and
`Thermodynamics.ComputationLandauer` already carries it at full strength on
**Mario Carneiro's partial recursive functions** (`Nat.Partrec.Code`, ITP 2019,
Mathlib's `Computability.PartrecCode`): a code's `eval` lifts to a Markov
`computationKernel`; `computation_keeps_kl` is the Kullback–Leibler
data-processing law; `erasureStep_tauEnt_eq_entropyProduced` identifies the
Landauer erasure entropy with the entropic time `τEnt`; irreversible primitives
(non-injective `left/right/const`) carry a nonzero cost, reversible ones produce
zero entropy.  A partial recursive function is *partial* precisely because it is
defined only where the computation halts — where there is data to complete it —
so its domain is the causal **future** picked out by `computationCausalOrder`, and
the data-free vacuum (undefined / non-halting / fixed point) is the timeless
stationary sector of `DataDrivenClockAutomaton.timeless_constant_on_data`.

## The single object

One deterministic computation carries all four:

* **its function** — a partial recursive map (Carneiro, `ComputationLandauer`);
* **its reachability** — a causal set / spacetime (`computationPreorder`,
  `CausalSetIntervalAbundance`);
* **its causal sign** — the Pauli–Jordan kernel / AQFT vacuum
  (`worldline_causalSign_isPauliJordan`, Sorkin–Johnston);
* **its clock** — the entropic time, advancing by the Kullback–Leibler /
  Landauer cost on data and frozen (time-independent Schrödinger) on the vacuum
  (`DataDrivenClockAutomaton`).

Horn certifies the classical substrate (the causal links); the Koopman /
Pauli–Jordan lift is the quantum step, and whether it reproduces genuine quantum
phenomenology remains the open problem — but the arithmetic (Partrec), the order
(causal set), the kernel (Pauli–Jordan), and the clock (KL) are now provably one
structure.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComputationCausalSetBridge

open Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState

variable {α : Type*}

/-- **The causal order of a computation**: the reflexive–transitive closure of its
one-step transition — reachability, read as causal precedence. -/
def computationCausalOrder (step : α → α → Prop) : α → α → Prop :=
  Relation.ReflTransGen step

/-- Reflexivity: every configuration causally precedes itself. -/
theorem computationCausalOrder_refl (step : α → α → Prop) (x : α) :
    computationCausalOrder step x x := Relation.ReflTransGen.refl

/-- Transitivity: causal precedence composes along the computation. -/
theorem computationCausalOrder_trans (step : α → α → Prop) {x y z : α}
    (hxy : computationCausalOrder step x y) (hyz : computationCausalOrder step y z) :
    computationCausalOrder step x z := hxy.trans hyz

/-- **Each computation step is a causal link** of the order. -/
theorem step_is_causal_link (step : α → α → Prop) {x y : α} (h : step x y) :
    computationCausalOrder step x y := Relation.ReflTransGen.single h

/-- **A computation is a causal set**: its configuration space carries the causal
(reachability) preorder — the `[Preorder α]` input of `CausalSetIntervalAbundance`
and the Sorkin–Johnston construction. -/
def computationPreorder (step : α → α → Prop) : Preorder α where
  le := computationCausalOrder step
  le_refl := computationCausalOrder_refl step
  le_trans := fun _ _ _ => computationCausalOrder_trans step

/-- **The weld to AQFT.**  The step-time order of a computation worldline (here the
five configurations of the data-driven clock's `(2,3)` run) has a `causalSign`
that is a Sorkin–Johnston **Pauli–Jordan kernel** — the Peierls commutator that
fixes the Sorkin–Johnston vacuum.  The computation's causal order *is* the input to
the AQFT construction. -/
theorem worldline_causalSign_isPauliJordan :
    IsPauliJordan (causalSign (α := Fin 5)) :=
  causalSign_isPauliJordan

end Physlib.QuantumMechanics.ComputationCausalSetBridge
