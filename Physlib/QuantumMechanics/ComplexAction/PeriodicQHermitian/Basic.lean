/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.Module

/-!
# The Q-metric / Q-Hermitian matrix formalism of the periodic complex action theory

Matrix-level formalization of the Nagao–Nielsen periodic complex action theory
(*Reality from maximizing overlap in the periodic complex action theory*,
arXiv:2203.07795, §2). A non-normal but diagonalizable Hamiltonian `Ĥ = P D P⁻¹`
(`D = diagonal d` the eigenvalues) is made **normal with respect to a modified inner
product** `I_Q(u,v) = ⟨u|Q|v⟩` by the Hermitian metric `Q = (P†)⁻¹ P⁻¹`. The
Q-Hermitian conjugate is `A^{†Q} = Q⁻¹ A† Q`.

This is the matrix counterpart of the operator-level Nagao–Nielsen Hamiltonian
`H_C = H_R − iH_I` of `FiniteTarget.NagaoNielsenSchrodinger`, and the metric `Q` realizes
the "automatic hermiticity" mechanism the complex-action uses to extract real expectation values.

* `mconj P X = P X P⁻¹` — conjugation by `P`; `mconj_mul` makes it a homomorphism.
* `qMetric P = (P†)⁻¹ P⁻¹` — the metric `Q`; `qMetric_isHermitian`, and
 `qMetric_inv : Q⁻¹ = P P†`.
* `qDagger Q A = Q⁻¹ A† Q` — the Q-Hermitian conjugate; `qDagger_mconj`:
 `(P X P⁻¹)^{†Q} = P X† P⁻¹` (the Q-dagger of a `P`-conjugate is the `P`-conjugate of the
 ordinary dagger), and `qDagger_mconj_isHermitian` (`P`-conjugates of Hermitian matrices
 are `Q`-Hermitian).
* `hamiltonian P d = P (diagonal d) P⁻¹` — `Ĥ`. Then:
 * `hamiltonian_qDagger` — `Ĥ^{†Q} = P D† P⁻¹` (the paper's `P⁻¹ Ĥ^{†Q} P = D†`).
 * `hamiltonian_qNormal` — **`Ĥ Ĥ^{†Q} = Ĥ^{†Q} Ĥ`**: `Ĥ` is `Q`-normal, because the
 eigenvalue matrix `D` commutes with `D†` (diagonal matrices commute). This is the key
 structural fact `[Ĥ, Ĥ^{†Q}] = P[D, D†]P⁻¹ = 0`.
 * `qHermPart_add_qAntiHermPart` — the Q-Hermitian decomposition `Ĥ = Ĥ_Qh + Ĥ_Qa`
 (`Ĥ_Qh = (Ĥ + Ĥ^{†Q})/2`); with `qDagger_mconj_isHermitian`, `Ĥ_Qh` is `Q`-Hermitian.
* `periodicExpectation U O = Tr(U O)/Tr U` — the periodic-time expectation
 `⟨Ô⟩_periodic = Tr(e^{−iĤt_p/ℏ} Ô)/Tr(e^{−iĤt_p/ℏ})` (Eq. of §3, with `U = e^{−iĤt_p/ℏ}`
 abstracted); `periodicExpectation_one` (normalization), `periodicExpectation_smul`,
 `periodicExpectation_comm` (trace cyclicity).

scope: this formalizes the matrix algebra of the `Q`-formalism (the metric,
conjugate, normality, decomposition) and the periodic-trace definition. The paper's two
*reality* theorems (that `⟨Ô⟩` is real, via eigenvalue-maximization and a number-theoretic
argument) depend on the analytic maximization principle and are not formalized here.

Reference: K. Nagao, H. B. Nielsen, arXiv:2203.07795v2, §2–3.
-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic

variable {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (d : n → ℂ)

/-- `IsUnit Pᴴ.det` from `IsUnit P.det`. -/
theorem isUnit_conjTranspose_det (hP : IsUnit P.det) : IsUnit (Pᴴ).det := by
  rw [Matrix.det_conjTranspose]; exact hP.star

/-! ## Conjugation by `P` -/

/-- Conjugation by `P`: `mconj P X = P X P⁻¹`. -/
noncomputable def mconj (X : Matrix n n ℂ) : Matrix n n ℂ := P * X * P⁻¹

/-- Conjugation is multiplicative: `(P X P⁻¹)(P Y P⁻¹) = P (XY) P⁻¹`. -/
theorem mconj_mul (hP : IsUnit P.det) (X Y : Matrix n n ℂ) :
    mconj P X * mconj P Y = mconj P (X * Y) := by
  simp only [mconj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P⁻¹ P, Matrix.nonsing_inv_mul P hP, Matrix.one_mul]

/-! ## The metric `Q` and the `Q`-Hermitian conjugate -/

/-- The modified-inner-product metric `Q = (P†)⁻¹ P⁻¹` (Hermitian, positive). -/
noncomputable def qMetric : Matrix n n ℂ := (Pᴴ)⁻¹ * P⁻¹

/-- The `Q`-Hermitian conjugate `A^{†Q} = Q⁻¹ A† Q`. -/
noncomputable def qDagger (Q A : Matrix n n ℂ) : Matrix n n ℂ := Q⁻¹ * Aᴴ * Q

/-- **`Q` is Hermitian**: `Q† = Q`. -/
theorem qMetric_isHermitian : (qMetric P)ᴴ = qMetric P := by
  rw [qMetric, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose]

/-- **`Q⁻¹ = P P†`.** -/
theorem qMetric_inv (hP : IsUnit P.det) : (qMetric P)⁻¹ = P * Pᴴ := by
  rw [qMetric, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hP,
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_conjTranspose_det P hP)]

/-- **The `Q`-dagger of a `P`-conjugate is the `P`-conjugate of the ordinary dagger**:
`(P X P⁻¹)^{†Q} = P X† P⁻¹`. The crux: the metric `Q = (P†)⁻¹P⁻¹` "un-tilts" the
non-orthogonality so that `†Q` acts on the eigenbasis like an ordinary `†`. -/
theorem qDagger_mconj (hP : IsUnit P.det) (X : Matrix n n ℂ) :
    qDagger (qMetric P) (mconj P X) = mconj P Xᴴ := by
  have hPH : IsUnit (Pᴴ).det := isUnit_conjTranspose_det P hP
  unfold qDagger mconj
  rw [qMetric_inv P hP, qMetric, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_nonsing_inv]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Pᴴ Pᴴ⁻¹, Matrix.mul_nonsing_inv Pᴴ hPH, Matrix.one_mul,
    ← Matrix.mul_assoc Pᴴ Pᴴ⁻¹, Matrix.mul_nonsing_inv Pᴴ hPH, Matrix.one_mul]

/-- **`P`-conjugates of Hermitian matrices are `Q`-Hermitian**: if `X† = X` then
`(P X P⁻¹)^{†Q} = P X P⁻¹`. This is why the symmetric/Hermitian eigenvalue combinations
give `Q`-Hermitian operators (used for the `Q`-Hermitian part of `Ĥ`). -/
theorem qDagger_mconj_isHermitian (hP : IsUnit P.det) {X : Matrix n n ℂ} (hX : Xᴴ = X) :
    qDagger (qMetric P) (mconj P X) = mconj P X := by
  rw [qDagger_mconj P hP, hX]

/-! ## The Hamiltonian, its `Q`-conjugate, and `Q`-normality -/

/-- `Ĥ = P D P⁻¹` with `D = diagonal d`. -/
noncomputable def hamiltonian : Matrix n n ℂ := mconj P (diagonal d)

/-- **`Ĥ^{†Q} = P D† P⁻¹`** (the paper's `P⁻¹ Ĥ^{†Q} P = D†`): the `Q`-conjugate of `Ĥ`
has the conjugated eigenvalues `D† = diagonal (star d)`. -/
theorem hamiltonian_qDagger (hP : IsUnit P.det) :
    qDagger (qMetric P) (hamiltonian P d) = hamiltonian P (star d) := by
  simp only [hamiltonian]
  rw [qDagger_mconj P hP, Matrix.diagonal_conjTranspose]

/-- **`Ĥ` is `Q`-normal: `Ĥ Ĥ^{†Q} = Ĥ^{†Q} Ĥ`.** The commutator
`[Ĥ, Ĥ^{†Q}] = P[D, D†]P⁻¹` vanishes because the eigenvalue matrix `D` and its conjugate
`D†` are diagonal, hence commute. This is the structural heart of the `Q`-formalism: every
diagonalizable Hamiltonian is normal in the right inner product. -/
theorem hamiltonian_qNormal (hP : IsUnit P.det) :
    hamiltonian P d * qDagger (qMetric P) (hamiltonian P d)
      = qDagger (qMetric P) (hamiltonian P d) * hamiltonian P d := by
  rw [hamiltonian_qDagger P d hP]
  simp only [hamiltonian]
  rw [mconj_mul P hP, mconj_mul P hP]
  congr 1
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/-! ## The `Q`-Hermitian decomposition `Ĥ = Ĥ_Qh + Ĥ_Qa` -/

/-- The `Q`-Hermitian part `A_Qh = (A + A^{†Q})/2`. -/
noncomputable def qHermPart (Q A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2⁻¹ : ℂ) • (A + qDagger Q A)

/-- The `Q`-anti-Hermitian part `A_Qa = (A − A^{†Q})/2`. -/
noncomputable def qAntiHermPart (Q A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2⁻¹ : ℂ) • (A - qDagger Q A)

/-- **`A = A_Qh + A_Qa`**: the `Q`-Hermitian decomposition. -/
theorem qHermPart_add_qAntiHermPart (Q A : Matrix n n ℂ) :
    qHermPart Q A + qAntiHermPart Q A = A := by
  unfold qHermPart qAntiHermPart; module

/-! ## The periodic-time expectation `Tr(U O)/Tr U` (§3) -/

/-- **The periodic-time expectation** `⟨Ô⟩_periodic = Tr(e^{−iĤt_p/ℏ} Ô)/Tr(e^{−iĤt_p/ℏ})`
(Nagao–Nielsen §3), with the evolution `U = e^{−iĤt_p/ℏ}` abstracted. -/
noncomputable def periodicExpectation (U O : Matrix n n ℂ) : ℂ := (U * O).trace / U.trace

/-- **Normalization**: `⟨1⟩_periodic = 1` (for `Tr U ≠ 0`). -/
theorem periodicExpectation_one (U : Matrix n n ℂ) (hU : U.trace ≠ 0) :
    periodicExpectation U 1 = 1 := by
  rw [periodicExpectation, Matrix.mul_one, div_self hU]

omit [DecidableEq n] in
/-- **Linearity** in the operator: `⟨c·Ô⟩ = c·⟨Ô⟩`. -/
theorem periodicExpectation_smul (U O : Matrix n n ℂ) (c : ℂ) :
    periodicExpectation U (c • O) = c * periodicExpectation U O := by
  rw [periodicExpectation, periodicExpectation, mul_smul_comm, Matrix.trace_smul,
    smul_eq_mul, mul_div_assoc]

omit [DecidableEq n] in
/-- **Cyclicity**: `Tr(U O) = Tr(O U)`, so the periodic weight may be written with the
operator on either side — the trace property underlying the `§3` reality argument. -/
theorem periodicExpectation_comm (U O : Matrix n n ℂ) :
    (U * O).trace = (O * U).trace := Matrix.trace_mul_comm U O

end Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic

end
