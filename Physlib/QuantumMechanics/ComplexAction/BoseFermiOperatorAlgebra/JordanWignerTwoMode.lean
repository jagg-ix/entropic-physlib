/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.FermionNetLocality
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# The two-mode Kálnay/Jordan-Wigner finite matrix representation

`BoseFermiOperatorAlgebra.CompositeFermionCAR` and `BoseFermiOperatorAlgebra.BoseBilinearRealization` isolate the one-mode CAR content of
Kálnay's construction. This file adds the first genuinely multi-mode finite layer: the two-mode
Jordan-Wigner/Kálnay matrices, the finite shadow of Theorem 4.1 and its note identifying the finite matrices
with Jordan-Wigner's Eq. (69).

On the four-dimensional occupation basis ordered as

  `|00⟩, |10⟩, |01⟩, |11⟩`,

the annihilation operators are

  `f₀ |10⟩ = |00⟩`, `f₀ |11⟩ = |01⟩`,
  `f₁ |01⟩ = |00⟩`, `f₁ |11⟩ = - |10⟩`,

with all other basis vectors killed. The minus sign is the Jordan-Wigner parity string; algebraically it is
exactly what makes the cross-anticommutators vanish. We prove:

* each matrix is a fermion mode (`kalnayJW0_isFermionMode`, `kalnayJW1_isFermionMode`);
* the two modes anticommute, including `{f₀, f₁†} = 0` (`kalnayJW_anticommutingModes`);
* the number operators are the expected diagonal occupation projectors and commute
  (`kalnay_two_mode_finite_realization`).

This is deliberately finite-dimensional and distribution-free: it formalizes the exact algebraic mechanism
behind Kálnay's finite matrix construction before the paper passes to countably many modes and fields.

## References

* A. J. Kálnay, E. Mac Cotrina, K. V. Kademova, "Quantum Field Theory of Fermions Constructed from
  Bosons. Generalization to Para-Fermi Statistics", Theorem 4.1 and Theorem 4.4.
* P. Jordan and E. Wigner (1928), as cited in Kálnay's note added in proof.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.JordanWignerTwoMode

open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.FermionNetLocality


/-- **The first two-mode Kálnay/Jordan-Wigner annihilation matrix.** On the basis
`|00⟩, |10⟩, |01⟩, |11⟩`, this sends `|10⟩ ↦ |00⟩` and `|11⟩ ↦ |01⟩`. -/
def kalnayJW0 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 0, 0]

/-- **The second two-mode Kálnay/Jordan-Wigner annihilation matrix.** It sends `|01⟩ ↦ |00⟩` and
`|11⟩ ↦ -|10⟩`; the sign is the parity string needed for the cross-CAR. -/
def kalnayJW1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, -1;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- The adjoint of `kalnayJW0`. -/
lemma star_kalnayJW0 :
    star kalnayJW0 =
      !![0, 0, 0, 0;
         1, 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kalnayJW0]

/-- The adjoint of `kalnayJW1`. -/
lemma star_kalnayJW1 :
    star kalnayJW1 =
      !![0, 0, 0, 0;
         0, 0, 0, 0;
         1, 0, 0, 0;
         0, -1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kalnayJW1]


/-- **Pauli nilpotence for the first finite mode**: `f₀² = 0`. -/
lemma kalnayJW0_mul_self : kalnayJW0 * kalnayJW0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kalnayJW0, Matrix.mul_apply, Fin.sum_univ_four]

/-- **Pauli nilpotence for the second finite mode**: `f₁² = 0`. -/
lemma kalnayJW1_mul_self : kalnayJW1 * kalnayJW1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kalnayJW1, Matrix.mul_apply, Fin.sum_univ_four]

/-- **The first Kálnay/Jordan-Wigner matrix is a fermion mode.** -/
lemma kalnayJW0_isFermionMode : IsFermionMode kalnayJW0 := by
  refine ⟨kalnayJW0_mul_self, ?_⟩
  rw [star_kalnayJW0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kalnayJW0]

/-- **The second Kálnay/Jordan-Wigner matrix is a fermion mode.** -/
lemma kalnayJW1_isFermionMode : IsFermionMode kalnayJW1 := by
  refine ⟨kalnayJW1_mul_self, ?_⟩
  rw [star_kalnayJW1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kalnayJW1]

/-- **The two annihilation matrices anticommute**: `{f₀, f₁} = 0`. -/
lemma kalnayJW_cross_anticomm :
    kalnayJW0 * kalnayJW1 + kalnayJW1 * kalnayJW0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kalnayJW0, kalnayJW1]

/-- **The mixed annihilation/creation cross-CAR**: `{f₀, f₁†} = 0`. -/
lemma kalnayJW_cross_anticomm_star :
    kalnayJW0 * star kalnayJW1 + star kalnayJW1 * kalnayJW0 = 0 := by
  rw [star_kalnayJW1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kalnayJW0]

/-- **The concrete two-mode Kálnay/Jordan-Wigner pair is a pair of anticommuting fermion modes.** -/
lemma kalnayJW_anticommutingModes :
    AnticommutingFermionModes kalnayJW0 kalnayJW1 :=
  ⟨kalnayJW0_isFermionMode, kalnayJW1_isFermionMode,
    kalnayJW_cross_anticomm, kalnayJW_cross_anticomm_star⟩


/-- **The first number operator is the diagonal projector onto states with mode `0` occupied.** -/
lemma fermionNumber_kalnayJW0 :
    fermionNumber kalnayJW0 =
      !![0, 0, 0, 0;
         0, 1, 0, 0;
         0, 0, 0, 0;
         0, 0, 0, 1] := by
  rw [fermionNumber, star_kalnayJW0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kalnayJW0, Matrix.mul_apply, Fin.sum_univ_four]

/-- **The second number operator is the diagonal projector onto states with mode `1` occupied.** -/
lemma fermionNumber_kalnayJW1 :
    fermionNumber kalnayJW1 =
      !![0, 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 1] := by
  rw [fermionNumber, star_kalnayJW1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kalnayJW1, Matrix.mul_apply, Fin.sum_univ_four]

/-- **[Finite Kálnay/Jordan-Wigner two-mode realization].** The two concrete `4×4` matrices satisfy the
two-mode CAR, their number operators are the expected diagonal occupation projectors, and those projectors
commute. This is the smallest finite multi-mode instance of the Kálnay/Jordan-Wigner matrix construction. -/
lemma kalnay_two_mode_finite_realization :
    AnticommutingFermionModes kalnayJW0 kalnayJW1
      ∧ fermionNumber kalnayJW0 =
        !![0, 0, 0, 0;
           0, 1, 0, 0;
           0, 0, 0, 0;
           0, 0, 0, 1]
      ∧ fermionNumber kalnayJW1 =
        !![0, 0, 0, 0;
           0, 0, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 1]
      ∧ fermionNumber kalnayJW0 * fermionNumber kalnayJW1 =
          fermionNumber kalnayJW1 * fermionNumber kalnayJW0 :=
  ⟨kalnayJW_anticommutingModes, fermionNumber_kalnayJW0, fermionNumber_kalnayJW1,
    fermionNumbers_commute kalnayJW0 kalnayJW1 kalnayJW_anticommutingModes⟩

end Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.JordanWignerTwoMode

end
