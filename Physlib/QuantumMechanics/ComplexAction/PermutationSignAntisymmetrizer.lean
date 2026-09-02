/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Physlib.QuantumMechanics.ComplexAction.A4StandardRepresentation
public import Physlib.QuantumMechanics.SpinDensityFunctionalOperators

/-!
# The permutation representation's determinant is the fermionic (Slater) sign

The bridge tying the permutation-representation-character infrastructure (`A4StandardRepresentation`) to the
second-quantized / spin-DFT antisymmetrizer (`SpinDensityFunctionalOperators`). The **determinant** of the
permutation representation is the **sign character** `sign(g)`, which is exactly:

* the coefficient `sign(p)` in the Slater antisymmetrizer `Â = (1/√N!) Σ_p sign(p) P̂_p`
  (`SpinDensityFunctionalOperators.antisymmetrizer_of_antisymmetric`, `perm_sign_sq`); and
* the character by which the permutation representation acts on the top exterior power — the fully-filled
  Slater determinant of the fermionic Fock space `FermionFock = ExteriorAlgebra` (`Fermion.SecondQuantizationFunctor`,
  where `creation_sq = 0` is Pauli exclusion).

So the one-dimensional "determinant representation" `det ∘ permRep` of the permutation representation *is* the
totally-antisymmetric (fermionic) sign representation that the antisymmetrizer projects onto.

* **`permRep_det_eq_sign`** — `det(permRep g) = sign(g)`: the determinant of the permutation representation is
  the sign character.
* **`antisymmetrizer_coeff_eq_permMatrix_det`** — `sign(p) = det(P_p)`: the Slater antisymmetrizer coefficient
  is the determinant of the permutation matrix, tying the coefficient of
  `SpinDensityFunctionalOperators`'s `Â` to the permutation representation.
* **`permMatrix_det_mul_self`** — `det(P_p)·det(P_p) = 1`: the sign coefficient is `±1`, discharged through the
  spin-DFT `perm_sign_sq` — the ` (−1)^p` structure of the antisymmetrizer / the Pauli `creation_sq = 0`.

**Honest layering.** Exact: `det(permRep) = sign` (via `Matrix.det_permutation`, `LinearMap.det_toLin'`,
`Equiv.Perm.sign_inv`), its identification with the antisymmetrizer coefficient, and the `±1` property routed
through the spin-DFT `perm_sign_sq`. Interpretive (docstring only): the identification of the sign character
with the top-exterior-power / filled-Slater-determinant action on `FermionFock`.

## References

* `Matrix.det_permutation` (`det P_σ = sign σ`); `SpinDensityFunctionalOperators` (the Slater antisymmetrizer,
  `perm_sign_sq`, `antisymmetrizer_of_antisymmetric`); `A4StandardRepresentation` (`permRep`);
  `Fermion.SecondQuantizationFunctor` (`FermionFock = ExteriorAlgebra`, `creation_sq`).


-/

set_option autoImplicit false

open Equiv (Perm)
open Matrix

noncomputable section

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PermutationSignAntisymmetrizer

open Physlib.QuantumMechanics.ComplexAction.A4StandardRepresentation

/-- **The determinant of the permutation representation is the sign character** `det(permRep g) = sign(g)`.
The one-dimensional determinant representation `det ∘ permRep` is the totally-antisymmetric sign
representation — the fermionic character. -/
lemma permRep_det_eq_sign (g : G) :
    LinearMap.det (permRep g) = (Equiv.Perm.sign g.val : ℂ) := by
  rw [show permRep g = (permMatrixHom (R := ℂ) g.val).toLin' from rfl,
    LinearMap.det_toLin', Matrix.permMatrixHom_apply, Matrix.det_permutation, Equiv.Perm.sign_inv]

/-- **The Slater antisymmetrizer coefficient is the permutation-matrix determinant** `sign(p) = det(P_p)`: the
coefficient `sign(p)` weighting each permutation operator in `Â = (1/√N!) Σ_p sign(p) P̂_p`
(`SpinDensityFunctionalOperators.antisymmetrizer_of_antisymmetric`) is the determinant of the permutation
matrix `P_p` of the permutation representation. -/
lemma antisymmetrizer_coeff_eq_permMatrix_det {n : ℕ} (p : Perm (Fin n)) :
    (Equiv.Perm.sign p : ℂ) = Matrix.det (p.permMatrix ℂ) :=
  (Matrix.det_permutation p).symm

/-- **The fermionic sign coefficient squares to one** `det(P_p)·det(P_p) = 1` — the antisymmetrizer weight is
`±1`, routed through the spin-DFT `perm_sign_sq` (the `(−1)^p` alternating structure of the Slater determinant,
equivalently the Pauli `creation_sq = 0` of the exterior-algebra Fock space). -/
lemma permMatrix_det_mul_self {n : ℕ} (p : Perm (Fin n)) :
    Matrix.det (p.permMatrix ℝ) * Matrix.det (p.permMatrix ℝ) = 1 := by
  rw [Matrix.det_permutation]
  exact_mod_cast Physlib.QuantumMechanics.SpinDensityFunctionalOperators.perm_sign_sq p

end Physlib.QuantumMechanics.ComplexAction.PermutationSignAntisymmetrizer
