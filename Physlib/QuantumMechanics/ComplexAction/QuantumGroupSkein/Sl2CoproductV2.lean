/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.Sl2FundamentalRep
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Tactic.FieldSimp

/-!
# The `U_s(sl₂)` coproduct, realized on `V₂ ⊗ V₂` (Sawin §3, Eq. 11)

The Hopf-algebra coproduct of the quantum group `U_s(sl₂)` is (Sawin, q-alg/9506002, Eq. 11)
`Δ(x) = x ⊗ s^h + s^{−h} ⊗ x`, `Δ(y) = y ⊗ s^h + s^{−h} ⊗ y`, with `h` primitive,
`Δ(h) = h ⊗ 1 + 1 ⊗ h`. Rather than build the abstract Hopf algebra and its tensor square, we realize the
coproduct on the tensor square of the fundamental representation `V₂ ⊗ V₂` (`Matrix (Fin 2 × Fin 2) … ℂ`,
the Kronecker product), where the group-like `s^h` acts as `diag(s, s⁻¹)` (`coSH`). The coproduct operators

* `coΔX = x ⊗ s^h + s^{−h} ⊗ x`, `coΔY = y ⊗ s^h + s^{−h} ⊗ y`, `coΔH = h ⊗ 1 + 1 ⊗ h`

must again satisfy the `U_s(sl₂)` relations — that `Δ` is an algebra homomorphism is exactly the statement
that the tensor square is a representation:

* `coproduct_relation_hx` / `coproduct_relation_hy`: `[ΔH, ΔX] = 2ΔX`, `[ΔH, ΔY] = −2ΔY` (the non-trivial
  intertwining of the *non-cocommutative* `Δ(x)` with `Δ(h)`).
* `coproduct_relation_xy`: the `q`-deformed relation in cleared-denominator form
  `(s² − s⁻²)·[ΔX, ΔY] = s^{2ΔH} − s^{−2ΔH}`, where `s^{2Δh} = s^{2h} ⊗ s^{2h}` (`coSPow2H`). This is
  `Δ` applied to `[x, y] = (s^{2h} − s^{−2h})/(s² − s^{−2})` (Sawin Eq. 10), confirming `Δ` preserves the
  defining `q`-commutator.

## References

* S. Sawin, *Links, Quantum Groups and TQFT's*, q-alg/9506002, §3, Eqs. 10–11 (`U_s(sl₂)` relations and the
  coproduct `Δ(x) = x ⊗ s^h + s^{−h} ⊗ x`), Eq. 13 (`V₂`).

No additional assumptions.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.Sl2FundamentalRep
open scoped Kronecker

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.Sl2CoproductV2

/-- **The group-like `s^h` on `V₂`**: `diag(s, s⁻¹)`. -/
noncomputable def coSH (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![s, 0; 0, s⁻¹]

/-- **`s^{−h}` on `V₂`**: `diag(s⁻¹, s)`. -/
noncomputable def coSHm (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![s⁻¹, 0; 0, s]

/-- **`s^{2h}` on `V₂`**: `diag(s², s⁻²)`. -/
noncomputable def coS2H (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![s ^ 2, 0; 0, (s ^ 2)⁻¹]

/-- **`s^{−2h}` on `V₂`**: `diag(s⁻², s²)`. -/
noncomputable def coSm2H (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![(s ^ 2)⁻¹, 0; 0, s ^ 2]

/-- **The coproduct of the raising generator** `Δx = x ⊗ s^h + s^{−h} ⊗ x` on `V₂ ⊗ V₂`. -/
noncomputable def coΔX (s : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fundX ⊗ₖ coSH s + coSHm s ⊗ₖ fundX

/-- **The coproduct of the lowering generator** `Δy = y ⊗ s^h + s^{−h} ⊗ y`. -/
noncomputable def coΔY (s : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fundY ⊗ₖ coSH s + coSHm s ⊗ₖ fundY

/-- **The coproduct of the Cartan generator** `Δh = h ⊗ 1 + 1 ⊗ h` (`h` is primitive). -/
noncomputable def coΔH : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fundH ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ fundH

/-- **`s^{2Δh} = s^{2h} ⊗ s^{2h}`** on `V₂ ⊗ V₂` `= diag(s⁴, 1, 1, s⁻⁴)`. -/
noncomputable def coSPow2H (s : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := coS2H s ⊗ₖ coS2H s

/-- **`s^{−2Δh} = s^{−2h} ⊗ s^{−2h}`** on `V₂ ⊗ V₂` `= diag(s⁻⁴, 1, 1, s⁴)`. -/
noncomputable def coSPowm2H (s : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := coSm2H s ⊗ₖ coSm2H s

/-- **[`[ΔH, ΔX] = 2ΔX`]** the coproduct preserves `[h, x] = 2x`: the non-cocommutative `Δx` still has
weight `+2` under `Δh`. -/
theorem coproduct_relation_hx (s : ℂ) (hs : s ≠ 0) : coΔH * coΔX s - coΔX s * coΔH = 2 * coΔX s := by
  unfold coΔH coΔX coSH coSHm fundH fundX
  ext p q
  obtain ⟨i₁, i₂⟩ := p; obtain ⟨j₁, j₂⟩ := q
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.sub_apply, Matrix.kronecker_apply, Matrix.one_apply, Matrix.ofNat_apply, hs] <;>
      ring

/-- **[`[ΔH, ΔY] = −2ΔY`]** the coproduct preserves `[h, y] = −2y`. -/
theorem coproduct_relation_hy (s : ℂ) : coΔH * coΔY s - coΔY s * coΔH = -(2 * coΔY s) := by
  unfold coΔH coΔY coSH coSHm fundH fundY
  ext p q
  obtain ⟨i₁, i₂⟩ := p; obtain ⟨j₁, j₂⟩ := q
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.sub_apply, Matrix.neg_apply, Matrix.one_apply, Matrix.ofNat_apply] <;> ring

/-- **[The `q`-deformed relation `(s²−s⁻²)·[ΔX, ΔY] = s^{2ΔH} − s^{−2ΔH}`]** the coproduct preserves the
defining commutator `[x, y] = (s^{2h} − s^{−2h})/(s² − s^{−2})` (Sawin Eq. 10), in cleared-denominator form
— `Δ` is an algebra homomorphism. -/
theorem coproduct_relation_xy (s : ℂ) (hs : s ≠ 0) :
    (s ^ 2 - (s ^ 2)⁻¹) • (coΔX s * coΔY s - coΔY s * coΔX s) = coSPow2H s - coSPowm2H s := by
  unfold coΔX coΔY coSH coSHm coSPow2H coSPowm2H coS2H coSm2H fundX fundY
  ext p q
  obtain ⟨i₁, i₂⟩ := p; obtain ⟨j₁, j₂⟩ := q
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.kronecker_apply, smul_eq_mul, hs] <;>
      (first | ring | (field_simp; ring))

end Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.Sl2CoproductV2

end
