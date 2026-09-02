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
# The `sl₂` R-matrix as the Kauffman bracket: skein relation and Temperley–Lieb (Sawin §3, p. 17)

On `V₂ ⊗ V₂` the braiding of `U_s(sl₂)` (the `R`-matrix composed with the flip) is the explicit `4×4` matrix
(Sawin, *Links, Quantum Groups and TQFT's*, q-alg/9506002, p. 17, in the basis `v₁v₁, v₁v₂, v₂v₁, v₂v₂`)

```
       ⎡ s   0      0       0 ⎤
braidR ⎢ 0   0      s⁻¹     0 ⎥
     = ⎢ 0   s⁻¹    s−s⁻³   0 ⎥ .
       ⎣ 0   0      0       s ⎦
```

Sawin observes (p. 17) this "is almost the Kauffman bracket functor … with `A = s`". This file makes that
precise as two diagram-free `4×4` matrix identities, the algebraic content of the Kauffman bracket:

* **The Kauffman skein relation** (`braidR_skein`): `braidR = s·𝟙 + s⁻¹·E`, i.e. crossing `= A·(identity) +
  A⁻¹·(cup-cap)` with `A = s` (for `s ≠ 0`). Here `E = tlE` is the Temperley–Lieb cup-cap generator
  `E = diag-block !![−s², 1; 1, −s⁻²]` on the middle `{v₁v₂, v₂v₁}` block.
* **The Temperley–Lieb relation** (`tlE_mul_self`): `E² = δ·E` with the loop parameter
  `δ = −s² − s⁻² = kauffmanLoopValue s` — exactly the disjoint-unknot value of §1, equal to `−[2]_q`, the
  quantum dimension of the fundamental representation (`QuantumGroupSkein.QuantumGroupSl2Casimir.kauffmanLoopValue_eq_neg_qInt_two`).
* **Idempotent-up-to-scale** (`tlE_proj`): `E·(δ⁻¹ • E) = E` for `δ ≠ 0` — `E/δ` is the Jones–Wenzl projection.

So the R-matrix loop value, the Kauffman disjoint-unknot value, and the `sl₂` quantum dimension `[2]_q` are
one and the same `−s² − s⁻²`.

## References

* S. Sawin, *Links, Quantum Groups and TQFT's*, q-alg/9506002, §1 (Kauffman bracket, Eqs. 2–3, 7–8), §3 p. 17
  (the `sl₂` `R`-matrix on `V₂ ⊗ V₂` and `A = s`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.QuantumGroupSl2Casimir

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.KauffmanRMatrixSkein

/-- **The `sl₂` braiding `R`-matrix on `V₂ ⊗ V₂`** with `A = s` (Sawin p. 17). -/
noncomputable def braidR (s : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![s, 0, 0, 0; 0, 0, s⁻¹, 0; 0, s⁻¹, s - (s⁻¹) ^ 3, 0; 0, 0, 0, s]

/-- **The Temperley–Lieb cup-cap generator `E`** on `V₂ ⊗ V₂`, the projection-up-to-scale onto the trivial
sub-representation of `V₂ ⊗ V₂` (Sawin §1, the `≍` fragment of the skein relation). -/
noncomputable def tlE (s : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0; 0, -s ^ 2, 1, 0; 0, 1, -(s⁻¹) ^ 2, 0; 0, 0, 0, 0]

/-- **[The Kauffman skein relation]** `braidR = s·𝟙 + s⁻¹·E`: the crossing equals `A·(identity) +
A⁻¹·(cup-cap)` with `A = s` (Sawin Eqs. 7–8, p. 17). Holds for every `s`. -/
lemma braidR_skein (s : ℂ) (hs : s ≠ 0) :
    braidR s = s • (1 : Matrix (Fin 4) (Fin 4) ℂ) + s⁻¹ • tlE s := by
  unfold braidR tlE
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] <;>
      field_simp <;> ring

/-- **[The Temperley–Lieb relation `E² = δ·E`]** the cup-cap squares to the loop value `δ = −s² − s⁻²`
times itself — the disjoint-unknot value of the Kauffman bracket, equal to `−[2]_q`
(`kauffmanLoopValue`). -/
lemma tlE_mul_self (s : ℂ) (hs : s ≠ 0) :
    tlE s * tlE s = kauffmanLoopValue s • tlE s := by
  unfold tlE kauffmanLoopValue
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.smul_apply, smul_eq_mul] <;>
      field_simp <;> ring

/-- **[`E/δ` is idempotent]** `E · (δ⁻¹ • E) = E` for `δ = kauffmanLoopValue s ≠ 0`: the Jones–Wenzl
projection onto the trivial sub-representation. -/
lemma tlE_proj (s : ℂ) (hs : s ≠ 0) (hδ : kauffmanLoopValue s ≠ 0) :
    tlE s * ((kauffmanLoopValue s)⁻¹ • tlE s) = tlE s := by
  rw [Matrix.mul_smul, tlE_mul_self s hs, smul_smul, inv_mul_cancel₀ hδ, one_smul]

end Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.KauffmanRMatrixSkein

end
