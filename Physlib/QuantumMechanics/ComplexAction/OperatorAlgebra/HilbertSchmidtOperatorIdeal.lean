/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import QuantumInfo.ForMathlib.HermitianMat.Inner

/-!
# The Hilbert–Schmidt operator ideal

`Fermion.SecondQuantizationFunctor` flagged the **Shale–Stinespring** criterion — a Bogoliubov rotation is
unitarily implementable on Fock space iff its off-diagonal block is **Hilbert–Schmidt** — as unstatable,
because Mathlib has no Hilbert–Schmidt operator class. This file constructs it.

For a Hilbert space `E` with Hilbert basis `b : HilbertBasis ι ℂ E`, a bounded operator `T : E →L[ℂ] E` is
**Hilbert–Schmidt** when its squared column norms are summable,

 `IsHilbertSchmidt b T := Summable (fun i ↦ ‖T (b i)‖²)`,

with **Hilbert–Schmidt norm squared** `‖T‖²_HS = ∑ᵢ ‖T(bᵢ)‖²` (`hsNormSq`). The Hilbert–Schmidt operators
form:

* a **submodule** of `E →L[ℂ] E` (`hilbertSchmidt`): closed under `0`, `+`
 (`IsHilbertSchmidt.add`, via `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²`), and scalar multiplication
 (`IsHilbertSchmidt.smul`);
* a **left ideal**: for any bounded `A`, `A ∘ T` is Hilbert–Schmidt (`IsHilbertSchmidt.comp_left`, via
 `‖A(T bᵢ)‖² ≤ ‖A‖²‖T bᵢ‖²`).

This is exactly the operator class needed to **state** Shale–Stinespring (the off-diagonal Bogoliubov block
`β` is required to satisfy `IsHilbertSchmidt b β`), and the membership/normed structure used in the criterion.

**Scope.** What is proved here is Parseval-free and complete: the Hilbert–Schmidt **submodule** and the
**left**-ideal absorption. The **two-sided** ideal (right absorption `T ∘ A`) and the **basis-independence** of
`‖·‖_HS` both reduce to **adjoint-invariance** `∑ᵢ ‖T bᵢ‖² = ∑ⱼ ‖T† bⱼ‖²` (Parseval `‖y‖² = ∑ⱼ |⟨bⱼ, y⟩|²`
summed in two orders) — the one genuinely analytic step, not done here. So this constructs the
Hilbert–Schmidt class as a normed left ideal; promoting it to the full two-sided ideal is the remaining step.

## References

* The Hilbert–Schmidt operators; Shale–Stinespring quasi-equivalence. structures: `Mathlib`
 (`HilbertBasis`, `ContinuousLinearMap`, `Summable`); cf. `Fermion.SecondQuantizationFunctor`,
 `Bogoliubov.CARAlgebraAutomorphism`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HilbertSchmidtOperatorIdeal

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **A Hilbert–Schmidt operator** (relative to a Hilbert basis `b`): the squared column norms
`‖T(bᵢ)‖²` are summable. -/
def IsHilbertSchmidt (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) : Prop :=
  Summable (fun i => ‖T (b i)‖ ^ 2)

/-- **The Hilbert–Schmidt norm squared** `‖T‖²_HS = ∑ᵢ ‖T(bᵢ)‖²` (the genuine value when `T` is
Hilbert–Schmidt). -/
noncomputable def hsNormSq (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) : ℝ :=
  ∑' i, ‖T (b i)‖ ^ 2

theorem hsNormSq_nonneg (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) : 0 ≤ hsNormSq b T :=
  tsum_nonneg fun _ => sq_nonneg _

/-- Plain-reals helper: `(a + b)² ≤ 2a² + 2b²`. -/
private theorem two_mul_sq_add (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-! ### The submodule structure -/

/-- **`0` is Hilbert–Schmidt.** -/
theorem isHilbertSchmidt_zero (b : HilbertBasis ι ℂ E) : IsHilbertSchmidt b 0 := by
  have h : (fun i : ι => ‖(0 : E →L[ℂ] E) (b i)‖ ^ 2) = fun _ => 0 := by funext i; simp
  rw [IsHilbertSchmidt, h]; exact summable_zero

/-- **Scalar multiples of a Hilbert–Schmidt operator are Hilbert–Schmidt.** -/
theorem IsHilbertSchmidt.smul {b : HilbertBasis ι ℂ E} {T : E →L[ℂ] E}
    (h : IsHilbertSchmidt b T) (c : ℂ) : IsHilbertSchmidt b (c • T) := by
  have hfun : (fun i => ‖(c • T) (b i)‖ ^ 2) = fun i => ‖c‖ ^ 2 * ‖T (b i)‖ ^ 2 := by
    funext i; rw [ContinuousLinearMap.smul_apply, norm_smul, mul_pow]
  rw [IsHilbertSchmidt, hfun]
  exact h.mul_left (‖c‖ ^ 2)

/-- **Sums of Hilbert–Schmidt operators are Hilbert–Schmidt** (via `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²`). -/
theorem IsHilbertSchmidt.add {b : HilbertBasis ι ℂ E} {S T : E →L[ℂ] E}
    (hS : IsHilbertSchmidt b S) (hT : IsHilbertSchmidt b T) : IsHilbertSchmidt b (S + T) := by
  have hb : ∀ i, ‖(S + T) (b i)‖ ^ 2 ≤ 2 * ‖S (b i)‖ ^ 2 + 2 * ‖T (b i)‖ ^ 2 := by
    intro i
    rw [ContinuousLinearMap.add_apply]
    calc ‖S (b i) + T (b i)‖ ^ 2
        ≤ (‖S (b i)‖ + ‖T (b i)‖) ^ 2 := by
          refine sq_le_sq' ?_ (norm_add_le _ _)
          have h1 := norm_nonneg (S (b i) + T (b i))
          have h2 := norm_nonneg (S (b i)); have h3 := norm_nonneg (T (b i)); linarith
      _ ≤ 2 * ‖S (b i)‖ ^ 2 + 2 * ‖T (b i)‖ ^ 2 := two_mul_sq_add _ _
  show Summable (fun i => ‖(S + T) (b i)‖ ^ 2)
  exact Summable.of_nonneg_of_le (fun i => sq_nonneg _) hb ((hS.mul_left 2).add (hT.mul_left 2))

/-- **The Hilbert–Schmidt operators as a submodule** of `E →L[ℂ] E`. -/
noncomputable def hilbertSchmidt (b : HilbertBasis ι ℂ E) : Submodule ℂ (E →L[ℂ] E) where
  carrier := {T | IsHilbertSchmidt b T}
  zero_mem' := isHilbertSchmidt_zero b
  add_mem' := fun hS hT => hS.add hT
  smul_mem' := fun c _ hT => hT.smul c

/-! ### The left-ideal property -/

/-- **[Left ideal] `A ∘ T` is Hilbert–Schmidt** for any bounded `A` (via `‖A(T bᵢ)‖² ≤ ‖A‖²‖T bᵢ‖²`). The
Hilbert–Schmidt operators absorb left composition by bounded operators. -/
theorem IsHilbertSchmidt.comp_left {b : HilbertBasis ι ℂ E} {T : E →L[ℂ] E}
    (h : IsHilbertSchmidt b T) (A : E →L[ℂ] E) : IsHilbertSchmidt b (A.comp T) := by
  have hb : ∀ i, ‖(A.comp T) (b i)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖T (b i)‖ ^ 2 := by
    intro i
    rw [ContinuousLinearMap.comp_apply]
    calc ‖A (T (b i))‖ ^ 2
        ≤ (‖A‖ * ‖T (b i)‖) ^ 2 := by
          refine sq_le_sq' ?_ (A.le_opNorm _)
          have h1 := norm_nonneg (A (T (b i)))
          have h2 := mul_nonneg (norm_nonneg A) (norm_nonneg (T (b i))); linarith
      _ = ‖A‖ ^ 2 * ‖T (b i)‖ ^ 2 := by rw [mul_pow]
  show Summable (fun i => ‖(A.comp T) (b i)‖ ^ 2)
  exact Summable.of_nonneg_of_le (fun i => sq_nonneg _) hb (h.mul_left (‖A‖ ^ 2))

/-! ## Finite matrix Hilbert-Schmidt inner product -/

/-- **Hilbert-Schmidt operator inner product** on finite complex matrices:
`⟨A, B⟩_HS := Tr(Aᴴ · B)`. -/
noncomputable def matrixHSInner
    {d : Type*} [Fintype d] [DecidableEq d]
    (A B : Matrix d d ℂ) : ℂ :=
  (Matrix.conjTranspose A * B).trace

/-- **HS inner of `A` with itself** vanishes iff `A = 0`. -/
theorem matrixHSInner_self_eq_zero_iff
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) :
    matrixHSInner A A = 0 ↔ A = 0 := by
  unfold matrixHSInner
  open ComplexOrder in
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff

/-- **Sesquilinear conjugate symmetry** of the finite-matrix HS inner product. -/
theorem matrixHSInner_conj_symm
    {d : Type*} [Fintype d] [DecidableEq d]
    (A B : Matrix d d ℂ) :
    matrixHSInner A B = star (matrixHSInner B A) := by
  unfold matrixHSInner
  rw [show Matrix.conjTranspose A * B
        = Matrix.conjTranspose (Matrix.conjTranspose B * A) by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]]
  rw [Matrix.trace_conjTranspose]

/-- **For Hermitian left input**, the HS inner reduces to `Tr(A·B)`. -/
theorem matrixHSInner_of_isHermitian_left
    {d : Type*} [Fintype d] [DecidableEq d]
    {A B : Matrix d d ℂ} (hA : A.IsHermitian) :
    matrixHSInner A B = (A * B).trace := by
  unfold matrixHSInner
  rw [hA]

/-- **Bridge: finite-matrix HS inner on `HermitianMat` agrees with
`HermitianMat.inner`, coerced from `ℝ` to `ℂ`. -/
theorem matrixHSInner_eq_hermitianMat_inner_complex
    {d : Type*} [Fintype d] [DecidableEq d]
    (A B : HermitianMat d ℂ) :
    matrixHSInner A.mat B.mat = ((inner ℝ A B : ℝ) : ℂ) := by
  rw [matrixHSInner_of_isHermitian_left A.H]
  exact (HermitianMat.inner_eq_trace_rc A B).symm

/-- **HS inner is ℂ-linear in the right argument.** -/
theorem matrixHSInner_add_right
    {d : Type*} [Fintype d] [DecidableEq d]
    (A B C : Matrix d d ℂ) :
    matrixHSInner A (B + C) = matrixHSInner A B + matrixHSInner A C := by
  unfold matrixHSInner
  rw [Matrix.mul_add, Matrix.trace_add]

/-- **HS inner is ℂ-linear in the right argument under scalar multiplication.** -/
theorem matrixHSInner_smul_right
    {d : Type*} [Fintype d] [DecidableEq d]
    (A B : Matrix d d ℂ) (c : ℂ) :
    matrixHSInner A (c • B) = c * matrixHSInner A B := by
  unfold matrixHSInner
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- **HS inner with zero on the right.** -/
@[simp]
theorem matrixHSInner_zero_right
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) :
    matrixHSInner A 0 = 0 := by
  unfold matrixHSInner; simp

/-- **HS inner with zero on the left.** -/
@[simp]
theorem matrixHSInner_zero_left
    {d : Type*} [Fintype d] [DecidableEq d]
    (B : Matrix d d ℂ) :
    matrixHSInner 0 B = 0 := by
  unfold matrixHSInner; simp

end Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HilbertSchmidtOperatorIdeal

end
