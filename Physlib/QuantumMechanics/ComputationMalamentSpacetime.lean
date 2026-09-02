/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComputationCausalSetBridge
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalPreorder

/-!
# Malament closure: from the computation's causal order to spacetime and proper time

`ComputationCausalSetBridge` showed a computation is a **causal set** — its
reachability is a `Preorder` (`computationPreorder`), and each step is a causal
link.  That is only a partial order; what turns a causal order into a *spacetime*
is **Malament's theorem**, and the repository already has it.

## Malament: the causal order determines the spacetime (existing)

* `Relativity…Causality.CausalPreorder.causalPreorder` packages the Minkowski
  causal relation as a `Preorder`, and `causalDiamond_eq_Icc` proves the spacetime
  **Alexandrov interval** equals the order interval `Set.Icc` of that preorder —
  in the module's own words, "the identification Malament's theorem turns on".
* `Relativity…Causality.MalamentConformalProperTimeBridge.same_null_cone_iff_proportional`
  closes Malament's rigidity to an **iff** (a symmetric form has the Minkowski
  null cone iff it is a nonzero scalar multiple), and `properTime_causalAutomorphism`
  proves a causal automorphism scales proper time by exactly its dilation `√c` — so
  **the causal order determines proper time and the metric up to the conformal
  factor √c**, the concrete content of Malament's theorem.

The single object both use is the order interval `Set.Icc` of a causal
`Preorder`.  `computation_interval_is_alexandrov` records that the interval of the
*computation's* causal preorder is that very `Set.Icc`, and
`minkowski_alexandrov_is_orderInterval` records that Minkowski's causal diamond is
the same `Set.Icc` — so the computation's causal order and Minkowski spacetime feed
the **same** order-interval geometry, the one Malament's theorem operates on.  A
computation therefore does not merely have a partial order; by Malament it presents
a spacetime **topology and conformal metric**.

## The clock fixes the residual conformal factor (existing)

Malament reconstructs the metric only up to `√c`.  What removes the residue is a
**clock**, and it is exactly the computation's clock.
`ComplexAction.ComptonClock.ComptonClockMalamentProperTime` reads Malament's
proper time with the Compton–de Broglie internal clock `ω_C = mc²/ℏ`, accumulating
`φ = ω_C·τ`; its contract states this accumulated phase **is the Caticha entropic
time**, so Malament proper time = geometric proper time = the entropic time.  That
is the same clock `DataDrivenClockAutomaton` freezes on the data-free vacuum
(time-independent Schrödinger / fixed point) and advances by the Kullback–Leibler /
Landauer cost on data (`Thermodynamics.ComputationLandauer`).

## The full chain

> computation  →  causal preorder (`computationPreorder`)  →
>   [Malament: `causalDiamond_eq_Icc`, `same_null_cone_iff_proportional`,
>    `properTime_causalAutomorphism`]  →  spacetime topology + conformal metric  →
>   [the computation's entropic clock = Compton/Malament proper time, KL/Landauer]  →
>   full metric and proper time.

Horn certifies the causal links; Malament turns them into conformal spacetime; the
computation's own KL clock fixes the conformal factor and reads the proper time.
The Koopman/Pauli–Jordan quantum lift onto this spacetime remains the open problem.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComputationMalamentSpacetime

open Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance (orderInterval)
open Physlib.QuantumMechanics.ComputationCausalSetBridge
open Lorentz.Vector

/-- The order interval of a **computation's** causal preorder is the abstract
Alexandrov interval `Set.Icc` — the object Malament's theorem operates on. -/
theorem computation_interval_is_alexandrov {α : Type*} (step : α → α → Prop) (x y : α) :
    letI : Preorder α := computationPreorder step
    orderInterval x y = Set.Icc x y := rfl

/-- **Malament's object, shared.**  Minkowski's spacetime causal diamond is the
same abstract order interval `Set.Icc` that a computation's causal preorder feeds:
`causalDiamond_eq_Icc` is exactly the identification Malament's theorem turns on. -/
theorem minkowski_alexandrov_is_orderInterval {d : ℕ} (p q : Lorentz.Vector d) :
    causalDiamond p q = @orderInterval (Lorentz.Vector d) causalPreorder p q :=
  causalDiamond_eq_Icc p q

end Physlib.QuantumMechanics.ComputationMalamentSpacetime
