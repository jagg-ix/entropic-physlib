/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorPurification

/-!
# Continuity of symplectically adjoint maps — the algebraic core of Theorem 2.2 (Verch 1996)

Formalizes the algebraic kernel of the **title theorem** of *R. Verch, arXiv:funct-an/9609004*, **Theorem 2.2**
(relative `μ–μ_s` continuity of symplectically adjoint maps), continuing the §2.1 polarizator work
(`AlgebraicQFTQuasifree.PolarizatorPurification`).

Verch's setup (Eq 2.15): a normal operator `R` and two maps `V, W` that are **`R`-adjoint**, `V*R = RW`. The
theorem propagates `μ`-boundedness of `V, W` to the interpolated norms `μ_s(x,y) = μ(|R|^{s/2}x, |R|^{s/2}y)`
with the Hadamard three-lines bound `‖Vx‖_s ≤ w^{s/2}v^{1−s/2}‖x‖_s` (Eq 2.17). The corollary (b): for a pair
`V, W` of **symplectically adjoint** maps of `(S,σ)` (`σ(Vφ,ψ) = σ(φ,Wψ)`), one has relative `μ–μ_s`
continuity — a symplectomorphism `T` and its inverse `T⁻¹` being the canonical example (Remark ii).

The full theorem is an **operator-interpolation** result (Appendix A's complex/Hadamard three-lines argument,
spectral measures for unbounded `R`) — the analytic layer. Its purely algebraic heart, formalized here, is the
identity that starts the proof: from the `R`-adjoint relation `VᵀR = RW`,

  `Vᵀ(R Rᵀ)V = R(W Wᵀ)Rᵀ`   (`rAdjoint_quadratic`),

the matrix form of `V*|R|²V = R W W* R*` (the `s = 2` endpoint, from which the `ε`-shifted operator
inequality `V*(|R|²+ε)V ≤ w²|R|²+εv²` and then the interpolation follow).

* **§A — the `R`-adjoint relation and the quadratic identity** (`IsRAdjoint`, `rAdjoint_quadratic`). Verch
  Eq 2.15 `VᵀR = RW`, and the endpoint identity `Vᵀ(RRᵀ)V = R(WWᵀ)Rᵀ`.
* **§B — symplectomorphisms `T, T⁻¹`** (`sympForm_mul_transpose`, `symplectomorphism_quadratic`,
  `symplectomorphism_quadratic_pure`). The canonical symplectically adjoint pair (Remark ii): a
  symplectomorphism `M` and inverse `Mi` satisfy the `R`-adjoint relation (`symplectic_adjoint_pair`, with
  `R = sympForm`), hence the quadratic identity; for the *pure* polarizator `|R| = 1` (`J Jᵀ = 1`) the `s = 2`
  endpoint collapses to `MᵀM = J(Mi Miᵀ)Jᵀ` — the `μ_s` all coincide with `μ` (`μ = μ̃`, the pure case where
  continuity is automatic).

## References

* R. Verch, arXiv:funct-an/9609004, Theorem 2.2 (relative `μ–μ_s` continuity of symplectically adjoint maps;
  Eq 2.15 the `R`-adjoint relation, Eq 2.17 the interpolation bound, Remark ii symplectomorphisms).
* Repo carriers: `AlgebraicQFT.SymplecticAdjointHadamard` (`sympForm`, `sympForm_sq`, `sympForm_antisymm`,
  `Symplectomorphism`, `symplectic_adjoint_pair`), `AlgebraicQFTQuasifree.PolarizatorPurification` (the polarizator `R_μ`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.SymplecticAdjointContinuity

open Matrix
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard


section RAdjoint
variable {n : Type*} [Fintype n]

/-- **[Verch Eq 2.15] The `R`-adjoint relation** `Vᵀ R = R W` — `V` and `W` are adjoint with respect to `R`
(the polarizator). For `R = sympForm` this is symplectic adjointness `σ(Vφ,ψ) = σ(φ,Wψ)`. -/
def IsRAdjoint (R V W : Matrix n n ℝ) : Prop := Vᵀ * R = R * W

/-- **[Theorem 2.2(a), the algebraic core] `Vᵀ(R Rᵀ)V = R(W Wᵀ)Rᵀ`.** From the `R`-adjoint relation `VᵀR = RW`
(and its transpose `RᵀV = WᵀRᵀ`), the `s = 2` endpoint quadratic form `V*|R|²V = R W W* R*` — the identity that
seeds Verch's `ε`-shifted operator inequality and the Hadamard three-lines interpolation. -/
lemma rAdjoint_quadratic {V W R : Matrix n n ℝ} (h : IsRAdjoint R V W) :
    Vᵀ * (R * Rᵀ) * V = R * (W * Wᵀ) * Rᵀ := by
  have hT : Rᵀ * V = Wᵀ * Rᵀ := by
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul] using this
  have e1 : Vᵀ * (R * Rᵀ) * V = (Vᵀ * R) * (Rᵀ * V) := by noncomm_ring
  have e2 : R * (W * Wᵀ) * Rᵀ = (R * W) * (Wᵀ * Rᵀ) := by noncomm_ring
  rw [e1, h, hT, e2]

end RAdjoint


/-- **[`|R| = 1` for the pure polarizator] `J Jᵀ = 1`.** The symplectic form is `μ`-orthogonal
(`= −J²= 1`), so `|R_μ| = 1` in the pure case and all the `μ_s` coincide. -/
lemma sympForm_mul_transpose : sympForm * sympFormᵀ = 1 := by
  rw [sympForm_antisymm, mul_neg, sympForm_sq, neg_neg]

/-- **[Remark ii, the symplectomorphism pair] `Mᵀ(J Jᵀ)M = J(Mi Miᵀ)Jᵀ`.** A symplectomorphism `M` and its
inverse `Mi` form the canonical symplectically adjoint pair (`symplectic_adjoint_pair` gives the `R`-adjoint
relation `Mᵀ J = J Mi`), so the Theorem 2.2 quadratic identity holds with `R = sympForm`. -/
lemma symplectomorphism_quadratic (M Mi : Matrix (Fin 2) (Fin 2) ℝ)
    (hsymp : Symplectomorphism M) (hinv : M * Mi = 1) :
    Mᵀ * (sympForm * sympFormᵀ) * M = sympForm * (Mi * Miᵀ) * sympFormᵀ :=
  rAdjoint_quadratic (symplectic_adjoint_pair M Mi hsymp hinv)

/-- **[Pure-case `s = 2` endpoint] `MᵀM = J(Mi Miᵀ)Jᵀ`.** With the pure polarizator `|R| = 1` (`J Jᵀ = 1`) the
quadratic identity collapses: the `μ_s`-norm of a symplectomorphism equals its `μ`-norm — the pure case
(`μ = μ̃`) where relative continuity of symplectomorphisms is automatic. -/
lemma symplectomorphism_quadratic_pure (M Mi : Matrix (Fin 2) (Fin 2) ℝ)
    (hsymp : Symplectomorphism M) (hinv : M * Mi = 1) :
    Mᵀ * M = sympForm * (Mi * Miᵀ) * sympFormᵀ := by
  have h := symplectomorphism_quadratic M Mi hsymp hinv
  rwa [sympForm_mul_transpose, Matrix.mul_one] at h

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.SymplecticAdjointContinuity

end
