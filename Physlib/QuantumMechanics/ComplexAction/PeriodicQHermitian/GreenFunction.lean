/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.ComplexHamiltonian
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The matrix Green function of `H_C = H_R − i H_I` and its dissipative decay

This file links the periodic Q-Hermitian `Q`-formalism (`PeriodicQHermitian.Basic`,
`NonHermitianComplexAction.ComplexHamiltonian`) to the **complex Schrödinger generator** and the
**modified (dissipative) Green function** already on this branch.

* The complex Schrödinger generator is `H_C = H_R − i H_I`
  (`FiniteTarget.NagaoNielsenSchrodinger.complexHamiltonian`); its operator propagator is
  `U(t) = exp(t·(−i H_C/ℏ))` (`NonHermitian.Propagator`).
* The modified Green function is the proper-time (Schwinger) kernel
  `G(σ) = exp(i E_R σ − Γ σ)` with modulus `e^{−Γσ}`
  (`Lindblad.GreensFunction.properTimeGreenKernel`, `norm_properTimeGreenKernel`); it is the
  complex action weight `complexActionWeight(E_R σ, Γ σ, 1)` (`QFT.Wick.Consistency`).

For a diagonalizable `Ĥ = P D P⁻¹` (eigenvalues `λ_i = Re λ_i + i Im λ_i`) the propagator is

  `greenMatrix P d ℏ t = e^{−iĤt/ℏ} = P·diagonal(e^{−iλ t/ℏ})·P⁻¹`,

the **finite-dimensional matrix realization** of `U(t)`. Its diagonal entries are the scalar
Green kernels `greenKernel λ ℏ t = e^{−iλt/ℏ}` (the `evolutionFactor` of
`NonHermitian.WickRotation` on an `H_C`-eigenvector).

* `greenMatrix_zero`, `greenMatrix_mul` — `e^{−iĤ·0} = 1` and the one-parameter group
  `e^{−iĤs}·e^{−iĤt} = e^{−iĤ(s+t)}`: `greenMatrix` is a genuine propagator.
* `norm_greenKernel` — **`‖e^{−iλt/ℏ}‖ = e^{Im λ·t/ℏ}`** (the kernel factors as a unitary
  phase `e^{−i Re λ·t/ℏ}` times this real dissipative exponential). With `Γ := −Im λ` (the eigenvalue
  of `H_I = hamiltonianHI`, `NonHermitianComplexAction.ComplexHamiltonian`), this is `e^{−Γ t/ℏ}` — the
  **same dissipative decay as the modified Green function** `‖G(σ)‖ = e^{−Γσ}`
  (`σ = t/ℏ`), and the same as the entropic weight `e^{−S_I/ℏ}` (`S_I = Γ t`,
  `NonHermitianComplexAction.EntropicDampingEquivalence`). So the propagator's decay rate is exactly the `H_I` /
  anti-`Q`-Hermitian eigenvalue, the rate that drove `PeriodicQHermitian.Ehrenfest`'s
  probability loss `−(2/ℏ)⟨H_I⟩`.

Thus the chain closes: the complex Schrödinger generator `H_C = H_R − i H_I` ⟶ its
propagator/Green function `greenMatrix` ⟶ eigenvalue Green kernels ⟶ decay rate `Γ = −Im λ
= H_I`-eigenvalue ⟶ the modified Green function `e^{−Γσ}` and the entropic damping
`e^{−S_I/ℏ}`.

Reference: K. Nagao, H. B. Nielsen, arXiv:1104.3381; Sergi & Giaquinta 2016
(`H_C = H_R − iH_I`); the modified Green function of `Lindblad.GreensFunction` /
`NonHermitian.Propagator` (this development).
-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic

variable {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (d : n → ℂ)

/-! ## The scalar Green kernel `e^{−iλt/ℏ}` -/

/-- **The eigenvalue Green kernel** `e^{−iλt/ℏ}` — the scalar evolution factor of `H_C` on
an eigenvector with eigenvalue `λ` (`NonHermitian.WickRotation.evolutionFactor`). -/
noncomputable def greenKernel (lam : ℂ) (ℏ t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * lam * (t : ℂ) / (ℏ : ℂ))

/-- **The Green kernel modulus is the dissipative decay** `‖e^{−iλt/ℏ}‖ = e^{Im λ·t/ℏ}`.
With `Γ = −Im λ` (the `H_I` eigenvalue) this is `e^{−Γt/ℏ}`, identical to the modified
Green function's `‖G(σ)‖ = e^{−Γσ}` (`σ = t/ℏ`) and the entropic damping `e^{−S_I/ℏ}`. -/
theorem norm_greenKernel (lam : ℂ) (ℏ t : ℝ) :
    ‖greenKernel lam ℏ t‖ = Real.exp (lam.im * t / ℏ) := by
  rw [greenKernel, Complex.norm_exp]
  congr 1
  rw [show -Complex.I * lam * (t : ℂ) / (ℏ : ℂ) = ((t / ℏ : ℝ) : ℂ) * (-Complex.I * lam) by
    push_cast; ring, Complex.re_ofReal_mul, Complex.mul_re]
  simp only [Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im, neg_zero,
    zero_mul, zero_sub]
  ring

/-! ## The matrix propagator / Green function `e^{−iĤt/ℏ}` -/

/-- **The matrix Green function / propagator** `e^{−iĤt/ℏ} = P·diagonal(e^{−iλt/ℏ})·P⁻¹` —
the finite-dimensional realization of `NonHermitian.Propagator`'s `U(t) = exp(t·(−iH_C/ℏ))`
for the complex Schrödinger generator `H_C = Ĥ = P D P⁻¹`. -/
noncomputable def greenMatrix (ℏ t : ℝ) : Matrix n n ℂ :=
  mconj P (diagonal (fun i => greenKernel (d i) ℏ t))

/-- **`e^{−iĤ·0} = 1`**: the propagator at `t = 0` is the identity. -/
theorem greenMatrix_zero (ℏ : ℝ) (hP : IsUnit P.det) : greenMatrix P d ℏ 0 = 1 := by
  rw [greenMatrix]
  simp only [greenKernel, Complex.ofReal_zero, mul_zero, zero_div, Complex.exp_zero]
  rw [Matrix.diagonal_one, mconj, Matrix.mul_one, Matrix.mul_nonsing_inv P hP]

/-- **The one-parameter group law** `e^{−iĤs}·e^{−iĤt} = e^{−iĤ(s+t)}`: `greenMatrix` is a
genuine time-evolution propagator (and a `DueringEvolution`-style conjugation flow). -/
theorem greenMatrix_mul (ℏ : ℝ) (hP : IsUnit P.det) (s t : ℝ) :
    greenMatrix P d ℏ s * greenMatrix P d ℏ t = greenMatrix P d ℏ (s + t) := by
  have hfun : (fun i => greenKernel (d i) ℏ s * greenKernel (d i) ℏ t)
      = (fun i => greenKernel (d i) ℏ (s + t)) := by
    funext i
    simp only [greenKernel, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [greenMatrix, greenMatrix, greenMatrix, mconj_mul P hP, Matrix.diagonal_mul_diagonal, hfun]

end Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic

end
