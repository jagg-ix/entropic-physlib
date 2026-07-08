/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuasifreeStateCovarianceIsotony
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuantumKillingLieDerivativeClosability

/-!
# The stationary invariant quasi-free state under a time-like Killing flow (Labuschagne–Majewski §8)

Formalizes §8 of Labuschagne–Majewski (arXiv:2503.14107): on a **stationary** spacetime (a *time-like* Killing
field `Z` with one-parameter isometry group `β_t^Z`) there is a quasi-free state `ω_Z` on `𝒜(M)` **invariant**
under the Killing flow, `ω_Z ∘ α_t^Z = ω_Z` — an equilibrium/stationary state. Its GNS representation gives a
`W*`-dynamical system `(𝓜(M), α_t^Z)` whose flow is unitarily implemented, generating the natural Hamiltonian.

This is the special case of the covariance of the previous module where the isometry fixes the state:

* the **invariant quasi-free state** `ω_Z(W(β_t ψ)) = ω_Z(W(ψ))` (`killing_invariant_quasifree_state`) — the
 Killing flow preserving the two-point function (`IsTwoPointCovariant β s s`, self-covariance) leaves the
 quasi-free state invariant; the invariant flows compose (`killing_invariant_comp`), a one-parameter stationary
 group;
* **Remark 8.1** — the invariance makes Theorem 6.10 apply: an invariant (tracial) state annihilates the quantum
 Killing Lie derivative, `ω_Z ∘ δ_Z = 0` (`stationary_state_annihilates_generator`), so `δ_Z` is a closable
 unital `*`-derivation (`stationary_dynamical_system`). The stationary state is exactly the `δ_Z`-invariant
 faithful state whose existence guarantees the closable generator.

So a time-like Killing field yields a stationary invariant quasi-free state, and its very invariance is what makes
the quantum Killing Lie derivative (the natural Hamiltonian's generator) a closable `*`-derivation — §8 ties the
covariance (§7), the closability (§6), and the flow (§5) together.

* **§A — the invariant quasi-free state** (`killing_invariant_quasifree_state`, `killing_invariant_comp`).
* **§B — the stationary state makes `δ_Z` closable** (`stationary_state_annihilates_generator`,
 `stationary_dynamical_system`).

The invariance of the quasi-free state and the annihilation `ω_Z ∘ δ_Z = 0` are exact reuse
of `quasifree_state_covariant` and `killingGenerator_tracial_invariant`. The unitary implementation `U_t^Z`, the
GNS `W*`-dynamical system, and the strong continuity (Eq. 8.2) are *recorded* — the invariance and the
`*`-derivation closability are the algebraic content. No new axioms.

## References

* L.E. Labuschagne, W.A. Majewski, arXiv:2503.14107, §8 (invariant states, Eq. 8.1–8.2, Remark 8.1). Repo
 structures: `AlgebraicQFTQuasifree.QuasifreeStateCovarianceIsotony`,
 `AlgebraicQFTQuasifree.QuantumKillingLieDerivativeClosability`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuasifreeStateCovarianceIsotony
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuantumKillingLieDerivativeClosability
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KillingInvariantStationaryState

/-! ## §A — the invariant quasi-free state -/

/-- **[The stationary quasi-free state is Killing-invariant] `ω_Z(W(β_t ψ)) = ω_Z(W(ψ))`.** If the time-like
Killing flow `β_t` preserves the two-point function (`IsTwoPointCovariant β s s`, self-covariance), the
quasi-free state `ω_s` is invariant under it — the stationary/equilibrium state `ω_Z ∘ α_t^Z = ω_Z` of §8. -/
theorem killing_invariant_quasifree_state {s : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ}
    {β : (Fin 2 → ℝ) → (Fin 2 → ℝ)} (h : IsTwoPointCovariant β s s) (ψ : Fin 2 → ℝ) :
    quasifreeWeight s (β ψ) = quasifreeWeight s ψ :=
  quasifree_state_covariant h ψ

/-- **[Invariant Killing flows compose] the stationary group is closed.** If both `β` and `β'` preserve the
two-point function `s` (leave `ω_s` invariant), so does `β' ∘ β` — the invariant flow is a one-parameter
stationary group of state-preserving maps. -/
theorem killing_invariant_comp {s : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ}
    {β β' : (Fin 2 → ℝ) → (Fin 2 → ℝ)} (h : IsTwoPointCovariant β s s)
    (h' : IsTwoPointCovariant β' s s) : IsTwoPointCovariant (β' ∘ β) s s :=
  quasifree_covariant_comp h h'

/-! ## §B — the stationary state makes `δ_Z` closable -/

variable {R : Type*} [Ring R]

/-- **[The stationary state annihilates the quantum Killing Lie derivative] `ω_Z ∘ δ_Z = 0`.** A Killing-invariant
(tracial) state `ω_Z` satisfies `ω_Z(δ_Z a) = 0` — differentiating `ω_Z ∘ α_t^Z = ω_Z` at `t = 0`. This is
Remark 8.1: the stationary state is the `δ_Z`-invariant faithful state of Theorem 6.10. -/
theorem stationary_state_annihilates_generator (ω : R →+ ℂ)
    (htr : ∀ a b : R, ω (a * b) = ω (b * a)) (K a : R) :
    ω (quantumKillingLieDerivative K a) = 0 :=
  killingGenerator_tracial_invariant ω htr K a

/-- **[The stationary dynamical system: `δ_Z` is a closable unital `*`-derivation].** For a skew-adjoint Killing
generator `K* = −K` and a Killing-invariant tracial state `ω_Z`:

* `δ_Z` is a unital `*`-derivation (annihilates the unit, Leibniz, intertwines the involution);
* `ω_Z ∘ δ_Z = 0` — the invariant faithful state.

By Theorem 6.10 (via Remark 8.1) `δ_Z` is therefore a `σ`-strong* closable unital `*`-derivation: the generator
of the stationary `W*`-dynamical system `(𝓜(M), α_t^Z)`. -/
theorem stationary_dynamical_system [StarRing R] (K a b : R) (hK : star K = -K) (ω : R →+ ℂ)
    (htr : ∀ x y : R, ω (x * y) = ω (y * x)) :
    (quantumKillingLieDerivative K 1 = 0
      ∧ quantumKillingLieDerivative K (a * b)
          = quantumKillingLieDerivative K a * b + a * quantumKillingLieDerivative K b
      ∧ star (quantumKillingLieDerivative K a) = quantumKillingLieDerivative K (star a))
      ∧ ω (quantumKillingLieDerivative K a) = 0 :=
  ⟨quantumKillingLieDerivative_isStarDerivation K a b hK,
    stationary_state_annihilates_generator ω htr K a⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.KillingInvariantStationaryState

end
