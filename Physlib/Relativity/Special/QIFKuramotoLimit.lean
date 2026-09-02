/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QIFMultiSystem
public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameFree
public import Physlib.ClassicalMechanics.KuramotoNetwork

/-!
# QIF ↔ Kuramoto density-locality bridge (closure of the multi-subsystem chain)

Closure of the multi-subsystem + density-locality extension to the
QIF framework.  Combines:

* `MultiQIF N H` (`QIFMultiSystem.lean`) — N-subsystem QIF carrier
  with coupling parameter.
* `KuramotoNetwork N` (`Physlib/ClassicalMechanics/KuramotoNetwork.lean`)
  — classical Kuramoto oscillator network with the same coupling
  parameter.
* `freeQIF` (`QuantumInertialFrameFree.lean`) — single-frequency
  reversible QIF (the quantum analog of a single Kuramoto oscillator
  at the decoupled limit).

**The bridge**: at the decoupled regime (`coupling = 0` /
`K = 0`), the N-subsystem QIF and the N-oscillator Kuramoto
network describe the same physics from quantum and classical
perspectives respectively.

## Honest scope

This file provides the **structural bridge carrier** between
`MultiQIF N H` and `KuramotoNetwork N`, plus the
coupling-coherence law `quantum.coupling = classical.K`.  The
`decoupled_iff` theorem is the substantive structural content:
both layers' decoupling predicates are equivalent.

A previous draft (commit `5577533c`) shipped a theorem
`dropsInAGlass_classicalAnalog` that purported to formalise the
"two drops in a glass" intuition as a derived theorem of the
bridge.  On inspection that theorem just packaged two **independent**
statements (one per layer) without genuine bridge content — the
decoupling hypothesis was unused on the quantum side, and the
classical side was a one-line unfolding of the linear free
trajectory.  It has been removed.

For a substantive derivation of the "drops in a glass" picture,
future work would need:

* Coupling-aware joint Hamiltonian on the quantum side
  (`H_joint = ⊕ H_R^{(i)} + g·V_inter`), making `g = 0` the
  *operationally distinguished* regime.
* Synchronization order-parameter on the classical side
  (Strogatz-Mirollo continuum analysis); `K = 0` gives
  zero order parameter, `K > K_c` gives strict synchronization.

The current bridge provides only what's actually proved.

## Contents

* `QIFKuramotoBridge N H` — bundles a `MultiQIF N H` with a
  `KuramotoNetwork N` and the coupling-coherence law
  `quantum.coupling = classical.K`.
* `QIFKuramotoBridge.decoupled_iff` — substantive structural
  content: `MultiQIF.IsDecoupled ↔ KuramotoNetwork.IsDecoupled`.
* `QIFKuramotoBridge.trivialSparse` — non-vacuity witness (carrier-
  level only; no physical derivation claim).


## References

* Kuramoto 1975 — classical oscillator network.
* Strogatz 2000 — Kuramoto synchronization review.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Relativity.Special.QuantumInertialFrameLorentzian

open QuantumMechanics.FiniteTarget Physlib.ClassicalMechanics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]


/-- **QIF ↔ Kuramoto density-locality bridge**: bundles an
N-subsystem quantum QIF with an N-oscillator classical Kuramoto
network, related by the **coupling-coherence law**
`quantum.coupling = classical.K`.

This is the formal carrier of the "density-as-locality"
identification: the same density parameter governs both the
quantum-side inter-subsystem interaction (`MultiQIF.coupling`) and
the classical-side Kuramoto coupling (`KuramotoNetwork.K`).

* At `coupling = K = 0`: both layers decouple → N independent
  inertial frames in both quantum and classical layers.
* At `coupling = K > 0`: interacting / Kuramoto regime → potential
  synchronization (classical) / mean-field reduction (quantum). -/
structure QIFKuramotoBridge (N : ℕ) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H] where
  /-- Quantum-side N-subsystem QIF. -/
  quantum   : MultiQIF N H
  /-- Classical-side N-oscillator Kuramoto network. -/
  classical : KuramotoNetwork N
  /-- **Coupling-coherence law**: the shared density parameter
  governs both layers identically. -/
  coupling_coherent : quantum.coupling = classical.K

namespace QIFKuramotoBridge

variable {N : ℕ}


/-- **Decoupling predicates are equivalent across the bridge**: the
quantum layer is decoupled iff the classical layer is decoupled. -/
lemma decoupled_iff (B : QIFKuramotoBridge N H) :
    B.quantum.IsDecoupled ↔ B.classical.IsDecoupled := by
  unfold MultiQIF.IsDecoupled KuramotoNetwork.IsDecoupled
  rw [B.coupling_coherent]

/-- Forward direction: quantum-decoupled implies classical-decoupled. -/
lemma classical_isDecoupled_of_quantum_isDecoupled
    (B : QIFKuramotoBridge N H) (h : B.quantum.IsDecoupled) :
    B.classical.IsDecoupled :=
  (decoupled_iff B).mp h

/-- Reverse direction: classical-decoupled implies quantum-decoupled. -/
lemma quantum_isDecoupled_of_classical_isDecoupled
    (B : QIFKuramotoBridge N H) (h : B.classical.IsDecoupled) :
    B.quantum.IsDecoupled :=
  (decoupled_iff B).mpr h

/-!

A previous draft (commit `5577533c`) of this file shipped a
theorem `dropsInAGlass_classicalAnalog` that *appeared* to derive
the "two drops in a glass" picture from the bridge structure.
That theorem just packaged two **independent** statements (one per
layer) with no genuine bridge content — the decoupling hypothesis
was unused on the quantum side, and the classical side was just an
unfolding of the linear trajectory.

It has been removed.  Honest derivation of the "drops in a glass"
content would require:

* Coupling-aware joint dynamics on the quantum side (`H_joint =
  ⊕ H_R^{(i)} + g · V_inter`), with reduced subsystem states that
  *change* with `g`; equilibrium predicates would then depend on
  `g`, and "decoupled ⟹ mutually inertial" would become
  non-trivial.
* Synchronization-order parameter on the classical side
  (Strogatz-Mirollo continuum analysis); at `K = 0` the order
  parameter is `0` (no synchronization), at `K > K_c` it's nonzero.

The current bridge provides only the structural carrier + the
coupling-coherence law `quantum.coupling = classical.K`.  The
`decoupled_iff` theorem (§2) is the substantive content: both
layers' decoupling predicates are equivalent.

Constructors and existence witnesses (`trivialSparse`,
`trivialSparse_quantum_isDecoupled`) remain — they are structural
non-vacuity witnesses, not physical-derivation theorems.
-/


/-- **Trivial QIF-Kuramoto bridge at the sparse limit**: all-
reversible quantum subsystems + zero-coupling Kuramoto network.
Both layers are decoupled by construction.  Non-vacuity witness
for the bridge carrier; does NOT formalise the "drops in a glass"
physics (see §3 scope note). -/
def trivialSparse (N : ℕ) (H_R : Fin N → H →L[ℂ] H)
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (ω_classical : Fin N → ℝ) :
    QIFKuramotoBridge N H where
  quantum   := MultiQIF.allReversible N H_R hbar hbar_pos
  classical := { ω := ω_classical, K := 0, K_nonneg := le_refl 0 }
  coupling_coherent := rfl

/-- The trivial-sparse bridge has both layers decoupled. -/
@[simp] lemma trivialSparse_quantum_isDecoupled
    (N : ℕ) (H_R : Fin N → H →L[ℂ] H)
    (hbar : ℝ) (hbar_pos : 0 < hbar) (ω_classical : Fin N → ℝ) :
    (trivialSparse N H_R hbar hbar_pos ω_classical).quantum.IsDecoupled := rfl

end QIFKuramotoBridge

end Physlib.Relativity.Special.QuantumInertialFrameLorentzian

end
