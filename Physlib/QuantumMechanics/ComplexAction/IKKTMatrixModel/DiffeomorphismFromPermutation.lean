/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Real.Basic

/-!
# Diffeomorphism from permutation of eigenvalues in the IIB matrix model (Iso–Kawai §4)

In the type IIB matrix model the space-time is the **distribution of the matrix eigenvalues** `x^i`, and the
eigenvalue density `ρ(x) = Σ_i δ(x − x^i)` (Eq. 4.3) is the fundamental object: space-time emerges from the
eigenvalue distribution, and its symmetry is the permutation group `S_N` acting on the eigenvalues (Eq. 4.9),
which Iso–Kawai identify with the **diffeomorphism** group (Eq. 4.10, `x → ξ(x)` with `ξ(x^i) = x^{σ(i)}`).

This file formalizes the algebraic heart of that identification — that the eigenvalue distribution and the
low-energy effective action are invariant under simultaneous permutation of the eigenvalues:

* `eigenvalueDensity_perm_invariant`: `Σ_i g(x^{σ(i)}) = Σ_i g(x^i)` — any symmetric functional of the
  eigenvalue set (in particular the density `ρ`) is `S_N`-invariant.
* `iibScalarAction_perm_invariant`: the scalar-field effective action
  `S = Σ_{ij}(φ^i−φ^j)²/2·f(x^i−x^j) + Σ_i m(φ^i)²` (Eq. 4.2) is invariant under
  `(x^i, φ^i) → (x^{σ(i)}, φ^{σ(i)})` (Eq. 4.9) — the permutation invariance that becomes diffeomorphism
  invariance of the emergent space-time.

## References

* S. Iso, H. Kawai (1999), hep-th/9903217, §4, Eqs. (4.2), (4.3), (4.9), (4.10).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.DiffeomorphismFromPermutation

variable {N : ℕ} {V : Type*}

/-- **[Eq. 4.3 / 4.9 — the eigenvalue density is `S_N`-invariant]** `Σ_i g(x^{σ(i)}) = Σ_i g(x^i)`. Any
symmetric functional of the eigenvalue set — in particular the density `ρ(x) = Σ_i δ(x − x^i)` — is invariant
under permutation of the eigenvalues: the space-time-as-eigenvalue-distribution carries the full `S_N`
symmetry. -/
lemma eigenvalueDensity_perm_invariant {M : Type*} [AddCommMonoid M] (g : V → M)
    (xv : Fin N → V) (σ : Equiv.Perm (Fin N)) :
    (∑ i, g (xv (σ i))) = ∑ i, g (xv i) :=
  Equiv.sum_comp σ (fun i => g (xv i))

/-- **The IIB scalar-field effective action** (Eq. 4.2) `S = Σ_{ij}(φ^i−φ^j)²/2·f(x^i−x^j) + Σ_i m(φ^i)²` for
a scalar field `φ^i` propagating in the distributed eigenvalues `x^i`. -/
noncomputable def iibScalarAction [Sub V] (f : V → ℝ) (m : ℝ) (xv : Fin N → V) (φ : Fin N → ℝ) : ℝ :=
  (∑ i, ∑ j, (φ i - φ j) ^ 2 / 2 * f (xv i - xv j)) + ∑ i, m * (φ i) ^ 2

/-- **[Eq. 4.9 — the scalar action is permutation invariant]** `S[x∘σ, φ∘σ] = S[x, φ]`. Under the
simultaneous permutation `x^i → x^{σ(i)}`, `φ^i → φ^{σ(i)}` (`σ ∈ S_N`) the effective action is unchanged.
This permutation invariance of the eigenvalue distribution is the matrix-model origin of the diffeomorphism
invariance (Eq. 4.10) of the emergent space-time. -/
lemma iibScalarAction_perm_invariant [Sub V] (f : V → ℝ) (m : ℝ) (xv : Fin N → V) (φ : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) :
    iibScalarAction f m (xv ∘ σ) (φ ∘ σ) = iibScalarAction f m xv φ := by
  simp only [iibScalarAction, Function.comp_apply]
  congr 1
  · have hinner : (∑ i, ∑ j, (φ (σ i) - φ (σ j)) ^ 2 / 2 * f (xv (σ i) - xv (σ j)))
        = ∑ i, ∑ j, (φ (σ i) - φ j) ^ 2 / 2 * f (xv (σ i) - xv j) :=
      Finset.sum_congr rfl fun i _ =>
        Equiv.sum_comp σ (fun j => (φ (σ i) - φ j) ^ 2 / 2 * f (xv (σ i) - xv j))
    rw [hinner]
    exact Equiv.sum_comp σ (fun i => ∑ j, (φ i - φ j) ^ 2 / 2 * f (xv i - xv j))
  · exact Equiv.sum_comp σ (fun i => m * (φ i) ^ 2)

end Physlib.QuantumMechanics.ComplexAction.IKKTMatrixModel.DiffeomorphismFromPermutation

end
