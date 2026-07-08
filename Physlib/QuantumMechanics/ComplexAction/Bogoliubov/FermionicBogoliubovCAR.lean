/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.FoldyWouthuysenBogoliubovIdentity

/-!
# Second-quantized Bogoliubov: the canonical anticommutation relations (CAR) for the Foldy–Wouthuysen
# particle/antiparticle pair

`Bogoliubov.FoldyWouthuysenBogoliubovIdentity` proved the *single-particle* statement: the Foldy–Wouthuysen
rotation is a Bogoliubov transformation, with `u² + v² = 1`. This file takes the **second-quantized**
step: on the Fock space of one **particle** mode `a` and one **antiparticle** mode `b`, the
Bogoliubov-transformed operators `ã = u a + v b†` are **canonical** — they preserve the **canonical
anticommutation relations (CAR)** — *exactly when* `u² + v² = 1`, the Foldy–Wouthuysen normalization.

This is the finite-mode realization of "the Dirac field's particle/antiparticle creation operators are
the Bogoliubov-transformed vacuum operators": the Bogoliubov map is a CAR-algebra automorphism iff the
Foldy–Wouthuysen condition holds.

## The Fock space and the CAR

On the four-dimensional two-mode Fock space (basis `|n_a n_b⟩`), the Jordan–Wigner fermionic operators
`a, a†, b, b†` (4×4 matrices) satisfy the **canonical anticommutation relations**:

 `{a, a†} = 1`, `{b, b†} = 1`, `{a, b} = 0`, `{a, b†} = 0`, `{a†, b†} = 0`

(`car_a_aDag`, `car_b_bDag`, `car_a_b`, `car_a_bDag`, `car_aDag_bDag`). These are the
`FieldStatistic.fermionic` case of physlib's graded `superCommuteF` (`QFT/PerturbationTheory`) — here
realized concretely on a finite Fock space.

## The Bogoliubov transformation is canonical iff `u² + v² = 1`

The Bogoliubov-mixed operator `ã = u a + v b†` and its conjugate `ã† = u a† + v b` satisfy

 `{ã, ã†} = (u² + v²)·1` (`bogoliubov_preserves_CAR`),

so the transformation is **canonical** (`{ã, ã†} = 1`) iff `u² + v² = 1` (`bogoliubov_canonical_iff`) —
the Foldy–Wouthuysen normalization. With the Foldy–Wouthuysen amplitudes (`fw_weights_normalization`
gives `u² + v² = 1`), the Dirac particle/antiparticle Bogoliubov is a CAR automorphism
(`fw_bogoliubov_canonical`).

## Scope (the remaining frontier)

This is the **finite-mode** (one particle/antiparticle pair) second-quantized statement: a genuine Fock
space, creation/annihilation operators, the CAR, and the Bogoliubov canonicity. What remains is the
**continuum field** `ψ(x) = ∫ d³k [a_k u_k e^{−ikx} + b†_k v_k e^{ikx}]` over a measure-theoretic
(infinite-mode) Fock space, and the Bogoliubov automorphism of the full CAR `C*`-algebra — that needs
an operator-algebra / second-quantization layer beyond the finite matrices here (physlib's
`FieldOpFreeAlgebra` is the abstract free-algebra step toward it).

## References

* This development: `Bogoliubov.FoldyWouthuysenBogoliubovIdentity`, `Dirac.FoldyWouthuysenExact`; physlib
 `QFT/PerturbationTheory/FieldOpFreeAlgebra` (the graded `superCommuteF`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix

namespace Physlib.QuantumMechanics.ComplexAction.Bogoliubov.FermionicBogoliubovCAR

/-! ## §A — the two-mode Fock space operators (Jordan–Wigner) -/

/-- **The particle annihilation operator** `a` (Jordan–Wigner, basis `|n_a n_b⟩`). -/
def aOp : Matrix (Fin 4) (Fin 4) ℂ := !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0]

/-- **The particle creation operator** `a† = aᴴ`. -/
def aDagOp : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0]

/-- **The antiparticle annihilation operator** `b` (with the Jordan–Wigner string). -/
def bOp : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 1, 0; 0, 0, 0, -1; 0, 0, 0, 0; 0, 0, 0, 0]

/-- **The antiparticle creation operator** `b† = bᴴ`. -/
def bDagOp : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, -1, 0, 0]

/-- **The anticommutator** `{A, B} = AB + BA`. -/
def anticomm (A B : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ := A * B + B * A

/-! ## §B — the canonical anticommutation relations (CAR) -/

/-- **`{a, a†} = 1`**. -/
theorem car_a_aDag : anticomm aOp aDagOp = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [anticomm, aOp, aDagOp, Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply,
      Matrix.one_apply]

/-- **`{b, b†} = 1`**. -/
theorem car_b_bDag : anticomm bOp bDagOp = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [anticomm, bOp, bDagOp, Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply,
      Matrix.one_apply]

/-- **`{a, b} = 0`** — different fermionic modes anticommute. -/
theorem car_a_b : anticomm aOp bOp = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [anticomm, aOp, bOp, Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply]

/-- **`{a, b†} = 0`**. -/
theorem car_a_bDag : anticomm aOp bDagOp = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [anticomm, aOp, bDagOp, Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply]

/-- **`{a†, b†} = 0`**. -/
theorem car_aDag_bDag : anticomm aDagOp bDagOp = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [anticomm, aDagOp, bDagOp, Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply]

/-! ## §C — the Bogoliubov transformation and its canonicity -/

/-- **The Bogoliubov-mixed annihilation operator** `ã = u a + v b†`. -/
def bogA (u v : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := u • aOp + v • bDagOp

/-- **The Bogoliubov-mixed creation operator** `ã† = u a† + v b`. -/
def bogADag (u v : ℂ) : Matrix (Fin 4) (Fin 4) ℂ := u • aDagOp + v • bOp

/-- **The Bogoliubov transformation acts on the CAR by `u² + v²`**: `{ã, ã†} = (u² + v²)·1`. The
cross terms `{a, b}`, `{a†, b†}` vanish; the diagonal terms give `u²{a,a†} + v²{b,b†} = (u²+v²)·1`. -/
theorem bogoliubov_preserves_CAR (u v : ℂ) :
    anticomm (bogA u v) (bogADag u v) = ((u ^ 2 + v ^ 2 : ℂ)) • 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [anticomm, bogA, bogADag, aOp, aDagOp, bOp, bDagOp, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] <;> ring

/-- **The Bogoliubov transformation is canonical iff `u² + v² = 1`**: `{ã, ã†} = 1 ⟺ u² + v² = 1`.
Canonicity (preserving the CAR) is exactly the Foldy–Wouthuysen normalization. -/
theorem bogoliubov_canonical_iff (u v : ℂ) :
    anticomm (bogA u v) (bogADag u v) = 1 ↔ u ^ 2 + v ^ 2 = 1 := by
  rw [bogoliubov_preserves_CAR]
  constructor
  · intro h
    have := congrFun (congrFun h 0) 0
    simpa [Matrix.smul_apply, Matrix.one_apply] using this
  · rintro h; rw [h, one_smul]

/-- **The Foldy–Wouthuysen Bogoliubov is a CAR automorphism.** For Foldy–Wouthuysen amplitudes
`u² + v² = 1` (`fw_weights_normalization`: `bogoliubovU2 + bogoliubovV2 = 1`), the particle/antiparticle
Bogoliubov transformation preserves the canonical anticommutation relations — the second-quantized
statement that the Dirac field's mixed operators are canonical creation/annihilation operators. -/
theorem fw_bogoliubov_canonical (u v : ℂ) (h : u ^ 2 + v ^ 2 = 1) :
    anticomm (bogA u v) (bogADag u v) = 1 :=
  (bogoliubov_canonical_iff u v).mpr h

end Physlib.QuantumMechanics.ComplexAction.Bogoliubov.FermionicBogoliubovCAR

end
