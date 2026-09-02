/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameModularGroup
meta import Zil

/-!
# Heisenberg-picture Quantum Inertial Frame

Makes explicit that the **`ModularGroupData H`** carrier (commit
`7da26ac0`) is the **Heisenberg-picture** of the QIF framework:
operators evolve under `σ_t : (H →L[ℂ] H) → (H →L[ℂ] H)`, while
the state functional `ω` is stationary
(`ω(σ_t(A)) = ω(A)`).

The dual **Schrödinger-picture** (state evolves, operator is
fixed) lives at the density-matrix level in
`Physlib/QuantumMechanics/FiniteTarget/QIFMixedState.lean` via
`QIFSemigroupCPTP` acting on `MState d`.

The two pictures are *physically equivalent* — they give the same
expectation values — but operationally distinct: one uses
operator-time evolution (`σ_t`), the other state-time evolution
(`Φ_t`).

## Carriers

* `HeisenbergPictureQIF H` — bundles `ModularGroupData H` with a
  `KMSStateFunctional` (the stationary state).  This is "the
  Heisenberg picture of a KMS QIF": modular flow on operators +
  modular-invariant state.

## Main theorems

* `heisenberg_stationarity` — `ω(σ_t(A)) = ω(A)`: state is
  stationary, all dynamics is on the operator side.
* `kmsQIF_to_heisenbergPicture` — bridge from the Schrödinger-side
  `kmsQIF` (commit `f45b2b11`) to the Heisenberg picture: given a
  modular group + state functional, the kmsQIF is the
  Schrödinger-picture dual.

## References

* Heisenberg 1925 — Heisenberg picture (matrix mechanics).
* Tomita 1970, Takesaki 1970 — modular flow IS the Heisenberg
  picture for a KMS state at inverse temperature β (Tomita's
  fundamental theorem).
* Connes-Rovelli 1994 — thermal time as modular Heisenberg
  evolution.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics.FiniteTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]


/-- **Heisenberg-picture Quantum Inertial Frame**: bundles a modular
automorphism group `σ_t : (H →L[ℂ] H) → (H →L[ℂ] H)` (Heisenberg-
picture operator evolution) with a state functional
`ω : (H →L[ℂ] H) → ℂ` satisfying the modular-invariance hypothesis
`ω(σ_t(A)) = ω(A)`.

Physically: the state is **stationary** in the Schrödinger
picture (no state evolution), and *all* dynamics is carried by the
operator-time evolution `σ_t` — exactly the Heisenberg picture for
a KMS state at inverse temperature `β`. -/
structure HeisenbergPictureQIF (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H] where
  /-- Modular automorphism group on the operator algebra. -/
  modularGroup    : ModularGroupData H
  /-- Modular-invariant (KMS) state functional. -/
  stateFunctional : KMSStateFunctional modularGroup

namespace HeisenbergPictureQIF

variable (HQ : HeisenbergPictureQIF H)

/-- **Heisenberg stationarity**: the state functional is invariant
under the modular (Heisenberg) flow.

This is the load-bearing duality statement: in the Heisenberg
picture, the state functional `ω` does *not* evolve with time
(`ω(σ_t(A)) = ω(A)` for every `t` and `A`).  All time-dependence
is on the operator side `σ_t(A)`.

Equivalent (under expectation duality) to "in the Schrödinger
picture, the density matrix ρ is stationary: `Φ_t(ρ) = ρ`". -/
lemma heisenberg_stationarity (t : ℝ) (A : H →L[ℂ] H) :
    HQ.stateFunctional.ω (HQ.modularGroup.σ t A) =
      HQ.stateFunctional.ω A :=
  HQ.stateFunctional.ω_invariant t A

/-- **Identity at `t = 0`**: the operator-time evolution is trivial
at `t = 0`, so the state functional sees no change at all (which is
the trivial case of stationarity). -/
lemma heisenberg_stationarity_at_zero (A : H →L[ℂ] H) :
    HQ.stateFunctional.ω (HQ.modularGroup.σ 0 A) =
      HQ.stateFunctional.ω A := by
  rw [HQ.modularGroup.zero_eq]

/-- **Multiplicativity of operator-time evolution**: re-export of
the modular-group multiplicativity at the Heisenberg-picture level.

In the Heisenberg picture, `σ_t` is a `*`-homomorphism of the
operator algebra at every `t` (`σ_t(A·B) = σ_t(A)·σ_t(B)`); this
is the structural property that makes "operators evolve" coherent. -/
lemma heisenberg_multiplicativity (t : ℝ) (A B : H →L[ℂ] H) :
    HQ.modularGroup.σ t (A * B) =
      HQ.modularGroup.σ t A * HQ.modularGroup.σ t B :=
  HQ.modularGroup.mul_eq t A B

end HeisenbergPictureQIF


/-- **Heisenberg-picture wrapper for a kmsQIF + modular structure**.

Given a Schrödinger-picture `kmsQIF H_θ ℏ ℏ_pos β β_pos` (commit
`f45b2b11`, where `H_θ` is the modular Hamiltonian and the QIF is
reversible) together with any `ModularGroupData H` and
`KMSStateFunctional` supplied externally, package them as a
`HeisenbergPictureQIF`.

The Schrödinger-picture content (the kmsQIF's `H_θ` as Hamiltonian
+ ψ-evolution) is **dual** to the Heisenberg-picture content
(`σ_t` as Heisenberg evolution + ω as stationary state) — the same
physics viewed through two equivalent pictures.

This bridge does *not* construct `σ_t` from `H_θ` (that requires
matrix exponential machinery; future work).  It packages the
ingredients consumers already have. -/
def kmsQIF_to_heisenbergPicture
    (modularGroup : ModularGroupData H)
    (stateFunctional : KMSStateFunctional modularGroup) :
    HeisenbergPictureQIF H where
  modularGroup    := modularGroup
  stateFunctional := stateFunctional

/-- **Trivial Heisenberg-picture QIF**: identity modular flow +
zero state functional.  Vacuously satisfies all theorems. -/
def HeisenbergPictureQIF.trivial : HeisenbergPictureQIF H where
  modularGroup    := ModularGroupData.trivial H
  stateFunctional := KMSStateFunctional.trivial (ModularGroupData.trivial H)

end QuantumMechanics.FiniteTarget

end

/- ZIL-BEGIN -/

zil attach QuantumMechanics.FiniteTarget.HeisenbergPictureQIF.heisenberg_stationarity where
  formalizes @ "claim:the-quantum-inertial-frame-state-is-stationary-under-the-heisenberg-modular-evolution",
  supported_by @ "paper:tomita-takesaki-modular-theory"

zil attach QuantumMechanics.FiniteTarget.HeisenbergPictureQIF.heisenberg_multiplicativity where
  formalizes @ "claim:the-heisenberg-modular-evolution-is-multiplicative-an-algebra-automorphism",
  requires @ "claim:the-quantum-inertial-frame-state-is-stationary-under-the-heisenberg-modular-evolution",
  caveat @ "claim:finite-target-operator-algebra-realization-of-the-modular-heisenberg-flow"

zil_file_contract physlib.qifHeisenbergPicture where
  promises "The Heisenberg picture of the quantum inertial frame: the reference state is stationary under the Heisenberg modular evolution of observables, and that evolution is multiplicative, an automorphism of the operator algebra."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:QuantumMechanics.FiniteTarget.HeisenbergPictureQIF"]
  forbids_substitutes ["the continuous unbounded-generator modular flow, only the finite-target bounded realization"]
  witnessed_by [QuantumMechanics.FiniteTarget.HeisenbergPictureQIF.heisenberg_stationarity,
    QuantumMechanics.FiniteTarget.HeisenbergPictureQIF.heisenberg_multiplicativity]

/- ZIL-END -/
