/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.TimeEvolution
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Variational quantum dynamics: the time-dependent variational principle and entropic gradient flow

The variational time-evolution regime of the quantum-computational-chemistry review (McArdle et al, Rev. Mod.
Phys. **92** (2020) 015003, arXiv:1808.10402 §IV). A parametrized ansatz `|ψ(θ(t))⟩` evolves by projecting the
true dynamics onto the tangent space, giving the linear system

  `Σ_j A_ij θ̇_j = C_i`,

with the **quantum-geometric metric** `A_ij` (the real Fubini–Study tensor) and a force vector `C_i`. For
**real time** `C_i = Im⟨∂_iψ|H|ψ⟩`; for **imaginary / entropic time** `C_i = −∂_i E` (or `−∂_i S_I`), turning
the variational flow into **gradient descent** — the CAT/EPT identification of entropic time with dissipative
imaginary-time flow.

* **§A — well-posedness.** When the metric `A` is invertible the variational equation `A θ̇ = C` has a **unique**
  parameter velocity `θ̇` (`variational_velocity_unique`).
* **§B — entropic / imaginary-time gradient flow.** `gradientFlowVelocity Ainv ∇S = −A⁻¹∇S`; along it the cost
  decreases, `dS/dt = ⟨∇S, θ̇⟩ ≤ 0` for a positive-semidefinite metric (`gradient_flow_nonincreasing`), with
  `dS/dt = 0` exactly at a variational fixed point (`gradient_flow_stationary_iff`) — monotone entropy/energy
  descent, `dτ_ent/dt ≥ 0` realized variationally.
* **§C — the moving-basis connection.** For a time-dependent orthonormal basis the connection
  `A_pq = ⟨φ_p|∂_tφ_q⟩` is **anti-Hermitian** (`connection_antiHermitian`), so the geometric term `iℏ A` added
  to `H` is **Hermitian** (`moving_basis_term_hermitian`) — a consistent "time-geometry" correction for
  reaction dynamics with adapting orbitals.

**Honest layering.** Proven: well-posedness of the variational linear system under an invertible metric, the
monotone descent of the gradient flow for a PSD metric (the rate `⟨∇S, θ̇⟩ ≤ 0`), and the anti-Hermiticity /
Hermitian-correction algebra of the moving-basis connection. The metric `A` is taken as an abstract (symmetric,
PSD) matrix — the actual quantum-geometric tensor `Re⟨∂_iψ|∂_jψ⟩`, the force assembly, and the ODE integration
are the analytic content, named but not derived.

## References

* J. McLachlan, Mol. Phys. **8** (1964) 39 (variational principle); S. McArdle et al, Rev. Mod. Phys. **92**
  (2020) 015003, doi:10.1103/RevModPhys.92.015003; arXiv:1808.10402 §IV — `Σ_j A_ij θ̇_j = C_i`,
  imaginary-time `= −∂_i E`, the moving-basis connection `A_pq(t) = ⟨φ_p|∂_tφ_q⟩`. `Physlib`
  (`QuantumChemistry.TimeEvolution`).


-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.VariationalQuantumDynamics

variable {n : ℕ}


/-- **[The variational parameter velocity is unique]** when the quantum-geometric metric `A` is invertible, the
time-dependent variational equation `A θ̇ = C` has a **unique** solution `θ̇ = A⁻¹C` — the ansatz evolution is
well-posed. -/
lemma variational_velocity_unique (A : Matrix (Fin n) (Fin n) ℝ) [Invertible A] (C : Fin n → ℝ) :
    ∃! θdot : Fin n → ℝ, A *ᵥ θdot = C := by
  refine ⟨A⁻¹ *ᵥ C, ?_, ?_⟩
  · show A *ᵥ (A⁻¹ *ᵥ C) = C
    rw [mulVec_mulVec, mul_inv_of_invertible, one_mulVec]
  · intro y hy
    apply mulVec_injective_of_invertible A
    rw [hy, mulVec_mulVec, mul_inv_of_invertible, one_mulVec]


/-- The **imaginary / entropic-time gradient-flow velocity** `θ̇ = −A⁻¹ ∇S` (with `A⁻¹` the inverse metric and
`∇S` the gradient of the cost, energy `E` or imaginary action `S_I`). -/
def gradientFlowVelocity (Ainv : Matrix (Fin n) (Fin n) ℝ) (gradS : Fin n → ℝ) : Fin n → ℝ :=
  -(Ainv *ᵥ gradS)

/-- **[The descent rate]** `dS/dt = ⟨∇S, θ̇⟩ = −⟨∇S, A⁻¹∇S⟩` along the gradient flow. -/
lemma gradient_flow_rate (Ainv : Matrix (Fin n) (Fin n) ℝ) (gradS : Fin n → ℝ) :
    gradS ⬝ᵥ gradientFlowVelocity Ainv gradS = -(gradS ⬝ᵥ (Ainv *ᵥ gradS)) := by
  rw [gradientFlowVelocity, dotProduct_neg]

/-- **[Monotone entropic descent]** for a positive-semidefinite inverse metric the cost is **non-increasing**
along the flow, `dS/dt = ⟨∇S, θ̇⟩ ≤ 0` — entropic / imaginary-time evolution is gradient descent. -/
lemma gradient_flow_nonincreasing (Ainv : Matrix (Fin n) (Fin n) ℝ)
    (hpos : ∀ y : Fin n → ℝ, 0 ≤ y ⬝ᵥ (Ainv *ᵥ y)) (gradS : Fin n → ℝ) :
    gradS ⬝ᵥ gradientFlowVelocity Ainv gradS ≤ 0 := by
  rw [gradient_flow_rate]; exact neg_nonpos.mpr (hpos gradS)

/-- **[Stationarity at the variational fixed point]** `dS/dt = 0 ⟺ ⟨∇S, A⁻¹∇S⟩ = 0` — the flow halts exactly
where the projected gradient vanishes (the variational ground state / equilibrium). -/
lemma gradient_flow_stationary_iff (Ainv : Matrix (Fin n) (Fin n) ℝ) (gradS : Fin n → ℝ) :
    gradS ⬝ᵥ gradientFlowVelocity Ainv gradS = 0 ↔ gradS ⬝ᵥ (Ainv *ᵥ gradS) = 0 := by
  rw [gradient_flow_rate, neg_eq_zero]


/-- **[The moving-basis connection is anti-Hermitian]** `A_pq = ⟨φ_p|∂_tφ_q⟩` with `Aᴴ = −A`, the consequence
of preserving orthonormality `∂_t⟨φ_p|φ_q⟩ = 0` (so `⟨∂_tφ_p|φ_q⟩ = −⟨φ_p|∂_tφ_q⟩`). -/
lemma connection_antiHermitian (A : Matrix (Fin n) (Fin n) ℂ)
    (hortho : ∀ p q, star (A q p) + A p q = 0) : Aᴴ = -A := by
  ext p q
  rw [Matrix.conjTranspose_apply, Matrix.neg_apply]
  linear_combination hortho p q

/-- **[The geometric time term is Hermitian]** with the anti-Hermitian connection `A` (`Aᴴ = −A`), the
correction `iℏ A` added to the Hamiltonian of a moving basis is **Hermitian** (`(iA)ᴴ = iA`) — a consistent
self-adjoint "time-geometry" term for reaction dynamics with time-dependent orbitals. -/
lemma moving_basis_term_hermitian (A : Matrix (Fin n) (Fin n) ℂ) (hA : Aᴴ = -A) :
    (Complex.I • A)ᴴ = Complex.I • A := by
  have hI : (star Complex.I : ℂ) = -Complex.I := by rw [← starRingEnd_apply, Complex.conj_I]
  rw [Matrix.conjTranspose_smul, hA, hI, smul_neg, neg_smul, neg_neg]

end Physlib.QuantumMechanics.ComplexAction.VariationalQuantumDynamics

end
