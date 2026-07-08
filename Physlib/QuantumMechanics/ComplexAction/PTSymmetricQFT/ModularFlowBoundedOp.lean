/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator
public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameModularGroup

/-!
# The modular flow at the bounded-operator level: instantiating the superoperators on `H →L[ℂ] H`

Instantiates the open-system superoperators of `PTSymmetricQFT.LindbladSuperoperator` on the genuine operator
algebra `H →L[ℂ] H` of bounded operators on a complex Hilbert space `H` — a `*`-algebra
(`Ring`, `StarRing`, `Algebra ℂ`, `StarModule ℂ`) — and identifies the `heisenbergGenerator` `−i[K, ·]` as
the generator of a **Tomita–Takesaki modular flow** (`QuantumInertialFrame.ModularGroupData`).

The modular flow `σ_t(a) = Δ^{it} a Δ^{-it} = U(t) a U(t)^{-1}` of a faithful state is the conjugation by a
one-parameter unitary group `U(t) = Δ^{it}`. We:

* **build the modular group from a unitary group** (`conjugationModularGroup`): a one-parameter group
  `U : ℝ → (H →L[ℂ] H)` (`U(s+t) = U(s)U(t)`, `U(0) = 1`) yields a `ModularGroupData` via the conjugation
  `σ_t(a) = U(t) a U(-t)` — the group law, identity-at-zero, and `*`-automorphism multiplicativity all hold
  algebraically (no operator exponential needed);
* **record the Heisenberg intertwining** `σ_t(a) U(t) = U(t) a` (`conjugationFlow_intertwine`);
* **instantiate the generators** `heisenbergGenerator K`, `gksGenerator H L`, `lindbladDissipator L` on
  `H →L[ℂ] H` (`modularGenerator`, etc.), and identify `heisenbergGenerator K = −i[K, ·]` as the modular
  generator: an inner **derivation** (`modularGenerator_leibniz` — the infinitesimal form of the flow's
  multiplicativity `mul_eq`) that is **`*`-compatible** for a self-adjoint modular Hamiltonian `K`
  (`modularGenerator_star` — the infinitesimal `*`-automorphism property). Its open-system completion is the
  GKSL generator `gksGenerator K L`.

This makes the identification concrete: the modular flow is the conjugation one-parameter group on bounded
operators, and `heisenbergGenerator` is its generator. The analytic content — that `σ_t = e^{t·𝓛}` with
`𝓛 = heisenbergGenerator K` (operator exponential / Stone's theorem) — is the one piece not formalized here.

## References

* M. Tomita, M. Takesaki (1970); A. Connes, C. Rovelli (1994) — modular flow as the Heisenberg/thermal-time
  one-parameter automorphism group.
* Repo dependencies: `PTSymmetricQFT.LindbladSuperoperator` (`heisenbergGenerator`, `gksGenerator`,
  `lindbladDissipator`, and the derivation / `*`-compatibility lemmas);
  `QuantumInertialFrame.ModularGroupData` (the Tomita–Takesaki modular group).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ModularFlowBoundedOp

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator
open QuantumMechanics.FiniteTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## §A — the modular flow as a conjugation one-parameter group -/

/-- **The conjugation modular flow** `σ_t(a) = U(t) a U(-t)` from a one-parameter unitary group `U`
(`U(t) = Δ^{it}`). -/
def conjugationFlow (U : ℝ → (H →L[ℂ] H)) (t : ℝ) (a : H →L[ℂ] H) : H →L[ℂ] H := U t * a * U (-t)

/-- **[Tomita–Takesaki] A unitary one-parameter group gives a modular group.** The conjugation by
`U(t) = Δ^{it}` is a `ModularGroupData`: group law, identity-at-zero, and `*`-automorphism multiplicativity
all hold algebraically. -/
noncomputable def conjugationModularGroup (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s * U t) (hzero : U 0 = 1) : ModularGroupData H where
  σ := conjugationFlow U
  group_law s t a := by
    simp only [conjugationFlow]
    rw [show -(s + t) = -t + -s by ring, hgrp, hgrp]; noncomm_ring
  zero_eq a := by simp [conjugationFlow, hzero]
  mul_eq t a b := by
    have hinv : U (-t) * U t = 1 := by rw [← hgrp]; simp [hzero]
    simp only [conjugationFlow]
    rw [show U t * (a * b) * U (-t) = U t * a * (U (-t) * U t) * b * U (-t) by
      rw [hinv]; noncomm_ring]
    noncomm_ring

/-- **The Heisenberg intertwining** `σ_t(a) U(t) = U(t) a` — the modular flow conjugates operators by `U(t)`. -/
theorem conjugationFlow_intertwine (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s * U t) (hzero : U 0 = 1) (t : ℝ) (a : H →L[ℂ] H) :
    conjugationFlow U t a * U t = U t * a := by
  have hinv : U (-t) * U t = 1 := by rw [← hgrp]; simp [hzero]
  simp only [conjugationFlow]; rw [mul_assoc, mul_assoc, hinv, mul_one]

/-! ## §B — the modular generator on `H →L[ℂ] H` -/

/-- **The modular generator** `−i[K, ·]` on bounded operators — `heisenbergGenerator` of
`PTSymmetricQFT.LindbladSuperoperator` instantiated at `A = H →L[ℂ] H`, with `K = −log Δ` the modular
Hamiltonian. -/
noncomputable def modularGenerator (K : H →L[ℂ] H) : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
  heisenbergGenerator K

/-- **The open-system (GKSL) modular generator** `−i[K, ·] + 𝒟[L]` on bounded operators. -/
noncomputable def gksModularGenerator (K L : H →L[ℂ] H) : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
  gksGenerator K L

/-- **[Generator ↔ flow] The modular generator is a derivation** — the infinitesimal form of the modular
flow's multiplicativity `ModularGroupData.mul_eq` (`σ_t(ab) = σ_t(a)σ_t(b)`). -/
theorem modularGenerator_leibniz (K a b : H →L[ℂ] H) :
    modularGenerator K (a * b) = modularGenerator K a * b + a * modularGenerator K b :=
  heisenbergGenerator_leibniz K a b

/-- **[Generator ↔ flow] The modular generator is `*`-compatible** for a self-adjoint modular Hamiltonian
`K` — the infinitesimal form of the modular flow being a `*`-automorphism (preserving observables). -/
theorem modularGenerator_star (K a : H →L[ℂ] H) (hK : star K = K) :
    star (modularGenerator K a) = modularGenerator K (star a) :=
  heisenbergGenerator_star K a hK

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.ModularFlowBoundedOp

end
