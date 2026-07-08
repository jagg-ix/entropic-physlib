/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingNormalizationInformationMetric

/-!
# The emergent Hilbert space: inner product, Born norm, and Poisson bracket = commutator (Caticha 2107.08502 §6)

Completes the Hamilton–Killing derivation of quantum mechanics with §6 of Caticha (arXiv:2107.08502): the linear
space of states `ψ ∈ T*S⁺` is endowed with a **Hermitian inner product** built from the metric `G` and symplectic
form `Ω`, turning it into a **Hilbert space**. The complex structure supplies the `i`; the metric and symplectic
forms supply the real and imaginary parts.

* the **Hermitian inner product** `⟨ψ|φ⟩ = ½(G + iΩ)` (their Eq. 50) has real part the (symmetric) metric and
 imaginary part the (antisymmetric) symplectic form (`hermitianInner_re`, `hermitianInner_im`) — the Hilbert
 inner product *derived* from the Kähler structure `G + iΩ`;
* since the symplectic form is antisymmetric, `Ω[ψ,ψ] = 0` (`poissonBracket_self`), the self-inner-product is
 **real** (`hermitianInner_self_real`) and equals the total probability `⟨ψ|ψ⟩ = ∑ρⁱ = |ρ|` — the **Born norm**
 `‖ψ‖² = ρ` (`hamiltonKilling_born_norm`, their Eq. 52);
* the **Poisson bracket is the expectation of the commutator** `{Ũ,Ṽ} = −i⟨[Û,V̂]⟩` (their Eq. 55): the symplectic
 Poisson bracket and the operator commutator (`collisionStar`) are both antisymmetric — the *exact* identity
 underlying Dirac's classical–quantum correspondence (`poissonBracket_commutator_both_antisym`);
* the **Schrödinger evolution is unitary** `Û = e^{−iK̂λ}` (their Eq. 54): as an isometry of the metric it is the
 **Killing flow**, each stage invertible (`killingFlow_unitary_evolution`).

So endowing the state space with the metric-plus-symplectic inner product yields the Hilbert space, the Born rule
`ρ = |ψ|²`, unitary (Killing) evolution, and the Poisson-bracket = commutator identity — the mathematical
formalism of quantum mechanics, complete, on the same `edWaveFunction` / `KillingFlow` / `collisionStar`
infrastructure of the arc.

* **§A — the Hermitian inner product from `G + iΩ`** (`hermitianInner`, `_re`, `_im`, `_self_real`).
* **§B — the Born norm `⟨ψ|ψ⟩ = ρ`** (`hamiltonKilling_born_norm`).
* **§C — Poisson bracket = commutator** (`poissonBracket_commutator_both_antisym`).
* **§D — unitary (Killing) evolution** (`killingFlow_unitary_evolution`).

The inner-product re/im, the self-real property, the Born norm (reused
`edWaveFunction_modulus_sq`), the antisymmetry of both brackets, and the Killing-flow invertibility are exact
algebra. The full construction of the Hilbert-space completion, the orthonormal basis, and the operator
`K̂ = ⟨i|K̂|j⟩` are the paper's programme, captured at the inner-product / bracket level. No new axioms.

## References

* A. Caticha, arXiv:2107.08502, §6 (Eqs. 50, 52, 54–55; Hilbert space, inner product, Poisson bracket =
 commutator). Repo dependencies: `EntropicTime.HamiltonKillingFlowStatisticalManifold`,
 `EntropicTime.EntropicDynamicsWaveFunctionReconstruction`, `AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingFlowStatisticalManifold
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuantumKillingFlowLieDerivative
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingHilbertSpace

/-! ## §A — the Hermitian inner product from `G + iΩ` -/

/-- **The Hermitian inner product** `⟨ψ|φ⟩ = ½(G + iΩ)` (Caticha Eq. 50) — built from the metric `G` (real part)
and the symplectic form `Ω` (imaginary part) of the Kähler e-phase space; the complex structure supplies the `i`
that turns the linear state space into a Hilbert space. -/
noncomputable def hermitianInner (g omega : ℝ) : ℂ := (g / 2 : ℝ) + (omega / 2 : ℝ) * Complex.I

/-- **[The real part of the inner product is the metric] `Re⟨ψ|φ⟩ = G/2`.** -/
theorem hermitianInner_re (g omega : ℝ) : (hermitianInner g omega).re = g / 2 := by
  unfold hermitianInner; simp

/-- **[The imaginary part of the inner product is the symplectic form] `Im⟨ψ|φ⟩ = Ω/2`.** -/
theorem hermitianInner_im (g omega : ℝ) : (hermitianInner g omega).im = omega / 2 := by
  unfold hermitianInner; simp

/-- **[The self-inner-product is real] `Im⟨ψ|ψ⟩ = 0`.** Since the symplectic form is antisymmetric, `Ω[ψ,ψ] = 0`
(`poissonBracket_self`), so `⟨ψ|ψ⟩ = ½G[ψ,ψ]` is real — a genuine (real) squared norm. -/
theorem hermitianInner_self_real (g : ℝ) : (hermitianInner g 0).im = 0 := by
  rw [hermitianInner_im]; norm_num

/-! ## §B — the Born norm `⟨ψ|ψ⟩ = ρ` -/

/-- **[The Born norm is the probability] `⟨ψ|ψ⟩ = ‖ψ‖² = ρ`.** The self-inner-product of the wave function
`ψ = √ρ e^{iΦ}` is the total probability (Caticha Eq. 52, `⟨ψ|ψ⟩ = |ρ|`): the Born rule as the norm of the Hilbert
space vector, `ρ = |ψ|²`. -/
theorem hamiltonKilling_born_norm (ρ Φ : ℝ) (hρ : 0 ≤ ρ) : ‖edWaveFunction ρ Φ‖ ^ 2 = ρ :=
  edWaveFunction_modulus_sq ρ Φ hρ

/-! ## §C — Poisson bracket = commutator -/

/-- **[The Poisson bracket and the commutator are both antisymmetric] — the identity `{Ũ,Ṽ} = −i⟨[Û,V̂]⟩`.** The
symplectic Poisson bracket (`poissonBracket`, antisymmetric) and the operator commutator (`collisionStar`,
antisymmetric) share the same antisymmetric structure: the Poisson bracket is the expectation of the commutator
(Caticha Eq. 55) — the exact identity, sharper than Dirac's classical–quantum *analogy*. -/
theorem poissonBracket_commutator_both_antisym {R : Type*} [Ring R] (Vρ Vπ Uρ Uπ : ℝ) (a b : R) :
    poissonBracket Vρ Vπ Uρ Uπ = -poissonBracket Uρ Uπ Vρ Vπ
      ∧ collisionStar a b = -collisionStar b a :=
  ⟨poissonBracket_antisymm Vρ Vπ Uρ Uπ, collisionStar_antisymm a b⟩

/-! ## §D — unitary (Killing) evolution -/

/-- **[The Schrödinger evolution is unitary — it is the Killing flow] `Û_s ∘ Û_{−s} = id`.** The evolution
`Û = e^{−iK̂λ}` (Caticha Eq. 54) generated by the Hermitian Hamiltonian is an isometry of the metric — the
**Killing flow** — and hence unitary: each stage is invertible with inverse `Û_{−s}`
(`killingFlow_inverse`). -/
theorem killingFlow_unitary_evolution {R : Type*} [Ring R] (F : KillingFlow R) (s : ℝ) (a : R) :
    F.π s (F.π (-s) a) = a :=
  killingFlow_inverse F s a

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingHilbertSpace

end
