/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Data.Complex.Basic

/-!
# MQM singlet sector: the free-fermion Slater determinant (Alexandrov §III.2)

In the singlet sector of Matrix Quantum Mechanics the `N²` bosonic matrix degrees of freedom reduce to `N`
**free fermions** in the one-particle potential (Alexandrov, hep-th/0311273, Eqs. III.19–III.22). Because the
singlet wavefunction `Φ^{sing}(x)` is *symmetric* under permutations of the matrix eigenvalues (a permutation
is a unitary transformation), the redefined wavefunction `Ψ^{sing} = Δ(x)·Φ^{sing}` is **completely
antisymmetric** — the system is `N` fermions, described by a Slater determinant `Ψ = det[ψ_{n_k}(x_l)]`
(Eq. III.22).

This file formalizes that antisymmetry — the fermionic counterpart of the *symmetric* eigenvalue density of
the IIB matrix model (`[[project_iso_kawai_iib_matrix_model]]`, `eigenvalueDensity_perm_invariant`):

* `slaterDeterminant_perm`: `Ψ(x∘σ) = sign(σ)·Ψ(x)` — the Slater determinant changes by the sign of the
  permutation of the eigenvalues (Eq. III.22; Fermi statistics).
* `slaterDeterminant_eq_zero_of_coord_eq`: if two eigenvalues coincide, `Ψ = 0` — the Pauli exclusion
  principle (two fermions cannot occupy the same point).

## References

* S. Yu. Alexandrov, *Matrix Quantum Mechanics and Two-dimensional String Theory in Non-trivial
  Backgrounds*, hep-th/0311273, Ch. III §2, Eqs. (III.19)–(III.24).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.MQMSlaterDeterminant

variable {N : ℕ}

/-- **The free-fermion Slater determinant** `Ψ(x) = det[ψ_{n_k}(x_l)]` (Eq. III.22, up to the `1/√N!`
normalization): `N` fermions occupying one-particle states `ψ_{n_k}` at the eigenvalue positions `x_l`. -/
noncomputable def slaterDeterminant (ψ : Fin N → ℝ → ℂ) (x : Fin N → ℝ) : ℂ :=
  Matrix.det (fun k l => ψ k (x l))

/-- **[Fermi antisymmetry, Eq. III.22]** `Ψ(x∘σ) = sign(σ)·Ψ(x)`. Permuting the eigenvalues `x_l → x_{σ(l)}`
multiplies the Slater determinant by the sign of the permutation — the singlet sector is a system of
fermions. This is the antisymmetric counterpart of the *symmetric* eigenvalue density of the IIB matrix
model. -/
theorem slaterDeterminant_perm (ψ : Fin N → ℝ → ℂ) (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    slaterDeterminant ψ (x ∘ σ) = Equiv.Perm.sign σ * slaterDeterminant ψ x := by
  unfold slaterDeterminant
  simp only [Function.comp_apply]
  exact Matrix.det_permute' σ (fun k l => ψ k (x l))

/-- **[Pauli exclusion]** if two eigenvalues coincide (`x_i = x_j`, `i ≠ j`) then `Ψ = 0`: two free fermions
cannot occupy the same point. -/
theorem slaterDeterminant_eq_zero_of_coord_eq (ψ : Fin N → ℝ → ℂ) (x : Fin N → ℝ)
    {i j : Fin N} (hij : i ≠ j) (hx : x i = x j) :
    slaterDeterminant ψ x = 0 := by
  unfold slaterDeterminant
  exact Matrix.det_zero_of_column_eq hij (fun k => by rw [hx])

/-- **[The Vandermonde determinant is the monomial Slater determinant]** With the fermions occupying the
lowest monomial states `ψ_k(y) = y^k`, the Slater determinant is the Vandermonde determinant
`Δ(x) = ∏_{i<j}(x_j − x_i)` — exactly the measure `Δ(x)` relating `Ψ = Δ·Φ^{sing}` (Eq. III.20). It vanishes
when two eigenvalues coincide, recovering Pauli exclusion as the antisymmetric factor. -/
theorem slaterDeterminant_vandermonde (x : Fin N → ℝ) :
    slaterDeterminant (fun k y => (y : ℂ) ^ (k : ℕ)) x
      = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((x j : ℂ) - (x i : ℂ)) := by
  have key : slaterDeterminant (fun k y => (y : ℂ) ^ (k : ℕ)) x
      = (Matrix.vandermonde (fun l => (x l : ℂ))).transpose.det := by
    unfold slaterDeterminant
    congr 1
  rw [key, Matrix.det_transpose, Matrix.det_vandermonde]

end Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.MQMSlaterDeterminant

end
