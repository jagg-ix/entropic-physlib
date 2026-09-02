/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Hermitian
meta import Zil

/-!
# The Moyal plane's oscillator basis as matrix units (Gayral–Gracia-Bondía–Iochum–Schücker–Várilly)

Formalizes the *matricial form of the Moyal product* — the algebraic core of §2.2 of
*V. Gayral, J. M. Gracia-Bondía, B. Iochum, T. Schücker, J. C. Várilly, "Moyal Planes are Spectral
Triples", Commun. Math. Phys. 246 (2004) 569–623*. The Moyal algebra `A_θ = (𝒮(ℝ^{2N}), ⋆_θ)` has a
natural basis of harmonic-oscillator eigentransitions `f_{mn}` (the Wigner eigentransitions, Def. 2.3)
which, under the Moyal product, obey exactly the **matrix-unit relations** (Lemma 2.4):

  `f_{mn} ⋆ f_{kl} = δ_{nk} f_{ml}`,   `f_{mn}^* = f_{nm}`,

so `f_{nn}` is an orthogonal projector, `f_{mn}` (`m ≠ n`) is nilpotent, and the family is orthogonal
for the tracial inner product `⟨f, g⟩ = (πθ)^{-N} ∫ f ⋆ g`. The harmonic-oscillator Hamiltonians are
diagonal on this basis (Eq. 2.9):

  `H_l ⋆ f_{mn} = θ(m_l + ½) f_{mn}`.

On the finite truncation `span{f_{mn} : m, n < d}` — the honest finite-rank model of the matricial
Moyal product — these relations are exactly the `Matrix (Fin d) (Fin d) ℂ` matrix units
`Matrix.single`, and the oscillator Hamiltonian is `Matrix.diagonal` of the eigenvalues `θ(m + ½)`.
This is the Tomita–Takesaki / modular reading of the Moyal plane: the (diagonal) oscillator
Hamiltonian is the modular generator, and the eigentransitions are its modular eigenvectors — the same
diagonal-generator/eigentransition structure carried by the modular quantum inertial frame.

* `moyalUnit_mul` — Lemma 2.4 multiplication `f_{mn} f_{kl} = δ_{nk} f_{ml}`.
* `moyalUnit_star` — Lemma 2.4 involution `f_{mn}^* = f_{nm}`.
* `moyalUnit_diag_projector` / `moyalUnit_diag_isHermitian` — `f_{nn}` is a self-adjoint projector.
* `moyalUnit_offDiag_nilpotent` — `f_{mn}^2 = 0` for `m ≠ n`.
* `oscillatorHamiltonian_moyalUnit` — Eq. 2.9 diagonalization on the finite basis.
* `moyalUnit_trace_orthogonality` — orthogonality of the eigentransitions under the trace.
-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits

variable {d : ℕ}

/-- The **Wigner eigentransition** `f_{mn}` of the Moyal oscillator basis, realized on the finite
truncation as the matrix unit `Matrix.single m n 1` of `Matrix (Fin d) (Fin d) ℂ`. -/
def moyalUnit (m n : Fin d) : Matrix (Fin d) (Fin d) ℂ := Matrix.single m n 1

/-- **[Gayral Lemma 2.4, multiplication] `f_{mn} ⋆ f_{kl} = δ_{nk} f_{ml}`.** The Moyal product of
two eigentransitions is the matrix-unit product: it is `f_{ml}` when the inner indices match
(`n = k`) and `0` otherwise. This is the matricial form of the Moyal product. -/
theorem moyalUnit_mul (m n k l : Fin d) :
    moyalUnit m n * moyalUnit k l = if n = k then moyalUnit m l else 0 := by
  unfold moyalUnit
  by_cases h : n = k
  · subst h
    rw [single_mul_single_same, mul_one, if_pos rfl]
  · rw [single_mul_single_of_ne (h := h), if_neg h]

/-- **[Gayral Lemma 2.4, involution] `f_{mn}^* = f_{nm}`.** The Moyal involution of an eigentransition
transposes its indices: the conjugate transpose of the matrix unit `single m n 1` is `single n m 1`. -/
theorem moyalUnit_star (m n : Fin d) : (moyalUnit m n)ᴴ = moyalUnit n m := by
  unfold moyalUnit
  ext i j
  rw [Matrix.conjTranspose_apply, single_apply, single_apply]
  by_cases h : m = j ∧ n = i
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩, star_one]
  · rw [if_neg h, if_neg (fun hc => h ⟨hc.2, hc.1⟩), star_zero]

/-- **[Gayral Lemma 2.4, diagonal projector] `f_{nn} ⋆ f_{nn} = f_{nn}`.** Every diagonal
eigentransition is idempotent under the Moyal product — an orthogonal projector onto the `n`-th
oscillator level. -/
theorem moyalUnit_diag_projector (n : Fin d) :
    moyalUnit n n * moyalUnit n n = moyalUnit n n := by
  rw [moyalUnit_mul, if_pos rfl]

/-- The diagonal eigentransition is an idempotent element (projector), packaged as `IsIdempotentElem`. -/
theorem moyalUnit_diag_isIdempotentElem (n : Fin d) : IsIdempotentElem (moyalUnit n n) :=
  moyalUnit_diag_projector n

/-- The diagonal eigentransition is self-adjoint (`f_{nn}^* = f_{nn}`) — a genuine orthogonal
projection. -/
theorem moyalUnit_diag_isHermitian (n : Fin d) : (moyalUnit n n).IsHermitian :=
  moyalUnit_star n n

/-- **[Gayral Lemma 2.4, off-diagonal nilpotence] `f_{mn}^2 = 0` for `m ≠ n`.** An off-diagonal
eigentransition squares to zero — a raising/lowering transition between distinct oscillator levels. -/
theorem moyalUnit_offDiag_nilpotent {m n : Fin d} (hmn : m ≠ n) :
    moyalUnit m n * moyalUnit m n = 0 := by
  rw [moyalUnit_mul, if_neg (fun hc => hmn hc.symm)]

/-- **[Gayral Eq. 2.9] The harmonic-oscillator Hamiltonian is diagonal on the eigentransition basis.**
For any eigenvalue assignment `E : Fin d → ℂ` (the total oscillator energies `θ(m + ½)`), the diagonal
operator acts on `f_{mn}` by its *row* (left) eigenvalue:

  `diagonal E ⋆ f_{mn} = E m • f_{mn}`.

With `E m = θ(|m| + N/2)` this is Gayral's `H ⋆ f_{mn} = θ(|m| + N/2) f_{mn}`: the eigentransitions
diagonalize the oscillator Hamiltonian. This is the Moyal plane's modular-generator structure — the
diagonal Hamiltonian playing the role of the modular Hamiltonian `−log ρ`, with the `f_{mn}` its
eigentransitions. -/
theorem oscillatorHamiltonian_moyalUnit (E : Fin d → ℂ) (m n : Fin d) :
    Matrix.diagonal E * moyalUnit m n = E m • moyalUnit m n := by
  unfold moyalUnit
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.smul_apply, single_apply, smul_eq_mul]
  by_cases h : m = i ∧ n = j
  · rw [if_pos h, h.1]
  · rw [if_neg h, mul_zero, mul_zero]

/-- **[Gayral Lemma 2.4, orthogonality] The eigentransitions are orthogonal under the trace.**
`Tr(f_{mn}^* ⋆ f_{kl}) = δ_{mk} δ_{nl}` — the tracial inner product `⟨f_{mn}, f_{kl}⟩` (Gayral's
`(πθ)^{-N}∫ f_{mn} ⋆ f_{kl} = 2^N δ_{mk} δ_{nl}`, here on the normalized finite model): the family
`{f_{mn}}` is an orthogonal basis and the trace is faithful. -/
theorem moyalUnit_trace_orthogonality (m n k l : Fin d) :
    ((moyalUnit m n)ᴴ * moyalUnit k l).trace = if m = k ∧ n = l then 1 else 0 := by
  rw [moyalUnit_star, moyalUnit_mul]
  by_cases hmk : m = k
  · rw [if_pos hmk]
    by_cases hnl : n = l
    · rw [if_pos ⟨hmk, hnl⟩]
      unfold moyalUnit
      subst hnl
      rw [Matrix.trace_single_eq_same]
    · rw [if_neg (fun hc => hnl hc.2)]
      unfold moyalUnit
      rw [Matrix.trace_single_eq_of_ne (h := hnl)]
  · rw [if_neg hmk, Matrix.trace_zero, if_neg (fun hc : m = k ∧ n = l => hmk hc.1)]

end Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.moyalUnit_mul where
  formalizes @ "claim:the-moyal-product-of-two-oscillator-eigentransitions-is-the-matrix-unit-product-delta-nk-f-ml",
  supported_by @ "paper:gayral-gracia-bondia-iochum-schucker-varilly-moyal-planes-are-spectral-triples"

zil attach Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.moyalUnit_star where
  formalizes @ "claim:the-moyal-involution-of-an-oscillator-eigentransition-transposes-its-indices-f-mn-star-equals-f-nm"

zil attach Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.moyalUnit_diag_projector where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.moyalUnit_mul",
  formalizes @ "claim:every-diagonal-oscillator-eigentransition-is-an-idempotent-projector-onto-its-oscillator-level",
  requires @ "claim:the-moyal-product-of-two-oscillator-eigentransitions-is-the-matrix-unit-product-delta-nk-f-ml"

zil attach Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.oscillatorHamiltonian_moyalUnit where
  supported_by @ "lean:HermitianMat.diagonal_mul",
  supported_by @ "lean:RelEntropy.faithful",
  formalizes @ "claim:the-harmonic-oscillator-hamiltonian-is-diagonal-on-the-eigentransition-basis-with-eigenvalue-theta-m-plus-half"

zil attach Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.moyalUnit_trace_orthogonality where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.moyalUnit_mul",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.moyalUnit_star",
  formalizes @ "claim:the-oscillator-eigentransitions-are-orthogonal-under-the-faithful-moyal-trace",
  requires @ "claim:the-moyal-involution-of-an-oscillator-eigentransition-transposes-its-indices-f-mn-star-equals-f-nm"

zil_file_contract physlib.moyalOscillatorMatrixUnits where
  promises "The matricial form of the Moyal product: on the harmonic-oscillator eigentransition basis f_mn of the Moyal plane, the Moyal product is the matrix-unit product f_mn f_kl = delta_nk f_ml with involution f_mn* = f_nm, so the diagonal transitions f_nn are self-adjoint orthogonal projectors, the off-diagonal ones are nilpotent, the oscillator Hamiltonian is diagonal (eigenvalue theta(m+1/2)), and the family is orthogonal under the faithful trace. On the finite truncation this is exactly the Matrix.single matrix units, the honest finite-rank model of the Moyal spectral triple's algebra, with the diagonal oscillator Hamiltonian as the modular generator."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.moyalUnit"]
  forbids_substitutes ["the full nonunital Frechet algebra of Schwartz functions, this is the finite-rank matricial truncation of the Moyal product",
    "the oscillatory Lebesgue integral over R^2N, the integral functional with its tracial, faithful, and bracket-annihilating properties is carried by MoyalTraceIntegral"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.moyalUnit_mul,
    Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.moyalUnit_star,
    Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.moyalUnit_diag_projector,
    Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.moyalUnit_offDiag_nilpotent,
    Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.oscillatorHamiltonian_moyalUnit,
    Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.moyalUnit_trace_orthogonality]

/- ZIL-END -/
