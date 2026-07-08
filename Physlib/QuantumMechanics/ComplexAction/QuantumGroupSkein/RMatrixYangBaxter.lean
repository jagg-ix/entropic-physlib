/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.QuantumGroupSl2Casimir
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FieldSimp

/-!
# The `sl₂` R-matrix satisfies the Yang–Baxter equation (Sawin §3, Eq. 9)

The braiding `c` of `U_s(sl₂)` on `V₂ ⊗ V₂` (the `R`-matrix of `QuantumGroupSkein.KauffmanRMatrixSkein`, here indexed by
pairs, `braidPair`) satisfies the **Yang–Baxter equation** `(c⊗1)(1⊗c)(c⊗1) = (1⊗c)(c⊗1)(1⊗c)` on
`V₂ ⊗ V₂ ⊗ V₂` (Sawin, q-alg/9506002, Eq. 9). This is the braid relation `c₁c₂c₁ = c₂c₁c₂` that, applied at
each crossing, makes the Kauffman bracket a link invariant (invariance under Reidemeister move III).

The triple tensor product is `Matrix (Fin 2 × Fin 2 × Fin 2) … ℂ`. `braidC1` is `c` on the first two
tensor factors (`= c ⊗ 1`), `braidC2` is `c` on the last two (`= 1 ⊗ c`).

* `braid_yangBaxter`: `c₁ * c₂ * c₁ = c₂ * c₁ * c₂` (for `s ≠ 0`).

## References

* S. Sawin, *Links, Quantum Groups and TQFT's*, q-alg/9506002, §3, Eq. 9 (Yang–Baxter equation
  `R₁₂R₁₃R₂₃ = R₂₃R₁₃R₁₂`, giving Reidemeister move III), p. 17 (the `sl₂` `R`-matrix on `V₂ ⊗ V₂`).

No additional assumptions.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.RMatrixYangBaxter

/-- **The `sl₂` braiding on `V₂ ⊗ V₂`**, indexed by pairs (`A = s`): `c(v₁v₁)=s v₁v₁`, `c(v₁v₂)=s⁻¹ v₂v₁`,
`c(v₂v₁)=s⁻¹ v₁v₂ + (s−s⁻³) v₂v₁`, `c(v₂v₂)=s v₂v₂` (Sawin p. 17). -/
noncomputable def braidPair (s : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q =>
    if p.1 = 0 ∧ p.2 = 0 ∧ q.1 = 0 ∧ q.2 = 0 then s
    else if p.1 = 0 ∧ p.2 = 1 ∧ q.1 = 1 ∧ q.2 = 0 then s⁻¹
    else if p.1 = 1 ∧ p.2 = 0 ∧ q.1 = 0 ∧ q.2 = 1 then s⁻¹
    else if p.1 = 1 ∧ p.2 = 0 ∧ q.1 = 1 ∧ q.2 = 0 then s - (s⁻¹) ^ 3
    else if p.1 = 1 ∧ p.2 = 1 ∧ q.1 = 1 ∧ q.2 = 1 then s
    else 0

/-- **`c₁ = c ⊗ 1`**: the braiding on the first two of three tensor factors. -/
noncomputable def braidC1 (s : ℂ) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => braidPair s (p.1, p.2.1) (q.1, q.2.1) * (if p.2.2 = q.2.2 then 1 else 0)

/-- **`c₂ = 1 ⊗ c`**: the braiding on the last two of three tensor factors. -/
noncomputable def braidC2 (s : ℂ) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => (if p.1 = q.1 then 1 else 0) * braidPair s (p.2.1, p.2.2) (q.2.1, q.2.2)

/-- **[The Yang–Baxter equation]** `c₁ c₂ c₁ = c₂ c₁ c₂` on `V₂ ⊗ V₂ ⊗ V₂` (Sawin Eq. 9, for `s ≠ 0`): the
braid relation that gives invariance under Reidemeister move III, hence the link invariant. -/
theorem braid_yangBaxter (s : ℂ) (hs : s ≠ 0) :
    braidC1 s * braidC2 s * braidC1 s = braidC2 s * braidC1 s * braidC2 s := by
  ext p q
  obtain ⟨a, b, c⟩ := p; obtain ⟨d, e, f⟩ := q
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> fin_cases f <;>
    simp [braidC1, braidC2, braidPair, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two] <;> field_simp <;> ring

end Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.RMatrixYangBaxter

end
