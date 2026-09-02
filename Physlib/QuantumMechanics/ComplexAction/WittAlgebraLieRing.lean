/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# A genuine Lie-algebra realization of the global-conformal `sl(2,ℝ)` subalgebra

`VirasoroCentralExtension` characterized the full Virasoro algebra by its structure constants and cocycle.
This module supplies a genuine `LieRing` *object* for its finite-dimensional global-conformal subalgebra,
`sl(2,ℝ) = ⟨L_{−1}, L_0, L_1⟩` — the Möbius algebra of `ConformalModularEntanglement` — realized as an
actual Lie algebra of `2×2` real matrices, so the bracket is the genuine matrix commutator and the Jacobi
identity is *inherited* from Mathlib's Lie ring of an associative ring, not re-proved.

We take `Matrix (Fin 2) (Fin 2) ℝ` with its Lie ring structure `⁅X, Y⁆ = XY − YX`
(`LieRing.ofAssociativeRing`), and realize the Virasoro generators (in the standard convention
`[L_m, L_n] = (m − n) L_{m+n}`, which is `wittCoeff` of `VirasoroCentralExtension`) as

  `L_1 = e`,  `L_{−1} = −f`,  `L_0 = −h/2`,

with `e, f, h` the standard `sl(2)` triple. Then the three defining brackets hold:

  `⁅L_1, L_{−1}⁆ = 2 L_0`,  `⁅L_0, L_1⁆ = −L_1`,  `⁅L_0, L_{−1}⁆ = L_{−1}`,

exactly `(m − n) L_{m+n}` on `⟨L_{−1}, L_0, L_1⟩`, with no central term (the `sl(2)` descendants are null,
`VirasoroCentralExtension.sl2_subalgebra`). The full Witt/Virasoro central extension is infinite-dimensional
and is *not* realized as an object here (its natural realization, derivations of `ℝ[T, T⁻¹]`, is blocked by
the absence of a Laurent-polynomial derivation in Mathlib); the structure-constant characterization of
`VirasoroCentralExtension` remains the complete algebra.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WittAlgebraLieRing

open Matrix

attribute [local instance] LieRing.ofAssociativeRing

/-- The raising generator `L_1 = e` of `sl(2,ℝ)`. -/
def L1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- The lowering generator `L_{−1} = −f` of `sl(2,ℝ)`. -/
def Lm1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; -1, 0]

/-- The Cartan generator `L_0 = −h/2` of `sl(2,ℝ)`. -/
noncomputable def L0 : Matrix (Fin 2) (Fin 2) ℝ := !![-(1 / 2), 0; 0, 1 / 2]

/-- **`⁅L_1, L_{−1}⁆ = 2 L_0`** — the Virasoro relation `[L_1, L_{−1}] = (1 − (−1)) L_0` on the genuine
matrix Lie ring. -/
theorem bracket_L1_Lm1 : ⁅L1, Lm1⁆ = (2 : ℝ) • L0 := by
  rw [LieRing.of_associative_ring_bracket]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L0, L1, Lm1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> norm_num

/-- **`⁅L_0, L_1⁆ = −L_1`** — the Virasoro relation `[L_0, L_1] = (0 − 1) L_1`. -/
theorem bracket_L0_L1 : ⁅L0, L1⁆ = -L1 := by
  rw [LieRing.of_associative_ring_bracket]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L0, L1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply] <;> norm_num

/-- **`⁅L_0, L_{−1}⁆ = L_{−1}`** — the Virasoro relation `[L_0, L_{−1}] = (0 − (−1)) L_{−1}`. -/
theorem bracket_L0_Lm1 : ⁅L0, Lm1⁆ = Lm1 := by
  rw [LieRing.of_associative_ring_bracket]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L0, Lm1, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- **The global-conformal `sl(2,ℝ)` closes on the genuine matrix Lie ring.**  All three Virasoro brackets
`[L_m, L_n] = (m − n) L_{m+n}` hold on `⟨L_{−1}, L_0, L_1⟩` — a genuine `LieRing`, with Jacobi inherited from
the matrix commutator. -/
theorem sl2_lie_ring_closes :
    ⁅L1, Lm1⁆ = (2 : ℝ) • L0 ∧ ⁅L0, L1⁆ = -L1 ∧ ⁅L0, Lm1⁆ = Lm1 :=
  ⟨bracket_L1_Lm1, bracket_L0_L1, bracket_L0_Lm1⟩

end Physlib.QuantumMechanics.ComplexAction.WittAlgebraLieRing

end
