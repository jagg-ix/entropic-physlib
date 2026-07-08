/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionLieAlgebra
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# The Levi-Civita tensor on `ℝ³`: antisymmetry, the ε–δ identity, and the cross product

Formalizes the defining tensor properties of the three-dimensional **Levi-Civita symbol** `ε_{ijk}`
(`CollisionOperatorSl2.CollisionLieAlgebra.leviCivita3`, `ε₀₁₂ = 1`), which the repo so far only used as a buried
helper for the `so(2,1)` structure constants. None of the genuine tensor identities existed (and Mathlib
has no Levi-Civita symbol at all):

* **complete antisymmetry** — `ε` flips sign under a swap of any pair of indices
  (`leviCivita3_swap₁₂`, `leviCivita3_swap₂₃`, `leviCivita3_swap₁₃`) and is **cyclic**
  (`leviCivita3_cyclic`);
* **vanishing on repeated indices** (`leviCivita3_repeated₁₂`, `leviCivita3_repeated₂₃`,
  `leviCivita3_repeated₁₃`), with normalization `ε₀₁₂ = 1` (`leviCivita3_zeroOneTwo`);
* the **ε–δ contraction identity** `∑_i ε_{ijk} ε_{ilm} = δ_{jl}δ_{km} − δ_{jm}δ_{kl}`
  (`leviCivita3_contraction`) and its full contraction `∑_{ij} ε_{ijk}ε_{ijl} = 2δ_{kl}`
  (`leviCivita3_double_contraction`);
* the **cross product** `(a × b)_i = ∑_{jk} ε_{ijk} a_j b_k` (`crossProduct_eq_leviCivita`) — the
  Levi-Civita tensor *is* Mathlib's `crossProduct`.

* **§A — antisymmetry and normalization** (`leviCivita3_swap₁₂`, `leviCivita3_swap₂₃`,
  `leviCivita3_swap₁₃`, `leviCivita3_cyclic`, `leviCivita3_repeated₁₂`, `leviCivita3_repeated₂₃`,
  `leviCivita3_repeated₁₃`, `leviCivita3_zeroOneTwo`).
* **§B — the ε–δ contraction identities** (`leviCivita3_contraction`,
  `leviCivita3_double_contraction`).
* **§C — the cross product** (`crossProduct_eq_leviCivita`).

## References

* The Levi-Civita symbol `ε_{ijk}` and the identity `ε_{ijk}ε_{ilm} = δ_{jl}δ_{km} − δ_{jm}δ_{kl}`.
  structure: `CollisionOperatorSl2.CollisionLieAlgebra` (`leviCivita3`); Mathlib's `crossProduct` / `cross_apply`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.Tensor

open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionLieAlgebra
open Matrix

/-! ## §A — complete antisymmetry and normalization -/

/-- **[Antisymmetry in the first pair] `ε_{jik} = −ε_{ijk}`.** -/
theorem leviCivita3_swap₁₂ (i j k : Fin 3) : leviCivita3 j i k = -leviCivita3 i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- **[Antisymmetry in the last pair] `ε_{ikj} = −ε_{ijk}`.** -/
theorem leviCivita3_swap₂₃ (i j k : Fin 3) : leviCivita3 i k j = -leviCivita3 i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- **[Antisymmetry in the outer pair] `ε_{kji} = −ε_{ijk}`.** -/
theorem leviCivita3_swap₁₃ (i j k : Fin 3) : leviCivita3 k j i = -leviCivita3 i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- **[Cyclic symmetry] `ε_{ijk} = ε_{jki}`.** -/
theorem leviCivita3_cyclic (i j k : Fin 3) : leviCivita3 i j k = leviCivita3 j k i := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- **[Vanishing on a repeated first pair] `ε_{iik} = 0`.** -/
theorem leviCivita3_repeated₁₂ (i k : Fin 3) : leviCivita3 i i k = 0 := by
  fin_cases i <;> fin_cases k <;> decide

/-- **[Vanishing on a repeated last pair] `ε_{ijj} = 0`.** -/
theorem leviCivita3_repeated₂₃ (i j : Fin 3) : leviCivita3 i j j = 0 := by
  fin_cases i <;> fin_cases j <;> decide

/-- **[Vanishing on a repeated outer pair] `ε_{iji} = 0`.** -/
theorem leviCivita3_repeated₁₃ (i j : Fin 3) : leviCivita3 i j i = 0 := by
  fin_cases i <;> fin_cases j <;> decide

/-- **[Normalization] `ε₀₁₂ = 1`.** -/
theorem leviCivita3_zeroOneTwo : leviCivita3 0 1 2 = 1 := rfl

/-! ## §B — the ε–δ contraction identities -/

/-- **[The ε–δ identity] `∑_i ε_{ijk} ε_{ilm} = δ_{jl}δ_{km} − δ_{jm}δ_{kl}`.** The fundamental contraction
of two Levi-Civita symbols over one shared index. -/
theorem leviCivita3_contraction (j k l m : Fin 3) :
    (∑ i, leviCivita3 i j k * leviCivita3 i l m)
      = (if j = l then 1 else 0) * (if k = m then 1 else 0)
        - (if j = m then 1 else 0) * (if k = l then 1 else 0) := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;> fin_cases m <;> decide

/-- **[The double contraction] `∑_{ij} ε_{ijk} ε_{ijl} = 2 δ_{kl}`.** Contracting two shared indices gives
twice the Kronecker delta. -/
theorem leviCivita3_double_contraction (k l : Fin 3) :
    (∑ i, ∑ j, leviCivita3 i j k * leviCivita3 i j l) = if k = l then 2 else 0 := by
  fin_cases k <;> fin_cases l <;> decide

/-! ## §C — the cross product is the Levi-Civita tensor -/

/-- **[The cross product is the Levi-Civita tensor] `(a × b)_i = ∑_{jk} ε_{ijk} a_j b_k`.** Mathlib's
`crossProduct` over any commutative ring is exactly the Levi-Civita contraction. -/
theorem crossProduct_eq_leviCivita {R : Type*} [CommRing R] (a b : Fin 3 → R) (i : Fin 3) :
    crossProduct a b i = ∑ j, ∑ k, (leviCivita3 i j k : R) * a j * b k := by
  rw [cross_apply]
  fin_cases i <;>
    (simp only [Fin.sum_univ_three]; dsimp only [Matrix.cons_val, leviCivita3]; push_cast; ring)

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.Tensor

end
