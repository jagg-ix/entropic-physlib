/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Complex angular momentum in the spinor Bethe–Salpeter equation (Swift–Lee 1963)

This file formalizes the **algebraic core** of A. R. Swift and B. W. Lee, *Complex Angular Momentum
in Spinor Bethe–Salpeter Equation*, Phys. Rev. **131** (1963) 4, 1857–1869 — fermion–antifermion
(`NN̄`) scattering by pseudoscalar exchange in the ladder approximation, continued into the complex
angular-momentum `J`-plane — and links it to this development's complex-action arc.

## Complex angular momentum is the angular-momentum complexification of the complex action

The paper continues the partial-wave Bethe–Salpeter amplitude from integer `J` into the **complex
`J`-plane** (Regge theory). Writing `J = J_R + i J_I`, the **Regge signature factor** `e^{iπJ}` (the
`(−1)^J` parity assignment continued to complex `J`) has modulus

  `‖e^{iπJ}‖ = e^{−π J_I}`   (`norm_reggeSignature`),

an exponential **damping by the imaginary angular momentum** `J_I` — exactly the form of this arc's
complex-action / entropic damping `e^{−S_I/ℏ}` (`π J_I ↔ S_I/ℏ`). A real angular momentum (`J_I = 0`)
gives a unimodular signature (`reggeSignature_real_unimodular`); at integer `J = n` it is the parity
`(−1)^n` (`reggeSignature_nat`). So the imaginary angular momentum plays, for the Regge amplitude, the
role the imaginary action plays for the path-integral weight — another face of the same
complexification.

## The `γ₀` parity operation (Swift–Lee Eqs. 2, 8)

The spinor BS equation uses `γ₀ = diag(1, −1)` (the paper's `γ₀`), and the BS amplitude satisfies the
**parity operation** `𝒫(Ψ) = γ₀ Ψ γ₀` (Eq. 8), whose invariance decouples the equations into
even/odd-parity sectors. We formalize `γ₀` (matching the existing
`Dirac.KleinGordonDiracFactorization.diracHamiltonian 1 0`), the involution `𝒫² = id`, and the
diagonal/off-diagonal (even/odd) decoupling.

## Main results

* `gamma0`, `gamma0_sq`, `gamma0_eq_dirac` — the parity matrix `γ₀` (`= diag(1,−1) = diracHamiltonian
  1 0`), `γ₀² = 1`.
* `parityConj`, `parityConj_involutive`, `parityConj_diagonal`, `parityConj_offDiag` — the parity
  operation and even/odd decoupling.
* `reggeSignature`, `norm_reggeSignature`, `reggeSignature_real_unimodular`, `reggeSignature_nat` —
  the Regge signature `e^{iπJ}` and its entropic-style damping `e^{−πJ_I}`.
* `reggeCasimir` — the `J(J+1)` partial-wave coefficient, analytic in complex `J`.
* `complex_angular_momentum_summary` — the bundled statement.

## References

* A. R. Swift, B. W. Lee, Phys. Rev. **131** (1963) 1857–1869. doi:10.1103/PhysRev.131.1857.
* T. Regge, Nuovo Cim. **14** (1959) 951. This development: `Dirac.KleinGordonDiracFactorization`;
  complex-action damping `e^{−S_I/ℏ}` (`ThermoFieldDynamics.ThermodynamicCanonicalQuantization`, `NonHermitianComplexAction.EntropicDampingEquivalence`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Complex
open Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization

namespace Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeComplexAngularMomentum

/-! ## §A — the `γ₀` parity matrix and the parity operation (Swift–Lee Eqs. 2, 8) -/

/-- **The Swift–Lee `γ₀ = diag(1, −1)`** (the parity matrix of the spinor BS equation). -/
def gamma0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- **`γ₀` is the existing Dirac diagonal** `diracHamiltonian 1 0` (no new matrix). -/
theorem gamma0_eq_dirac : gamma0 = (diracHamiltonian 1 0).map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma0, diracHamiltonian, Matrix.map_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]

/-- **`γ₀² = 1`** (the parity matrix is an involution). -/
theorem gamma0_sq : gamma0 * gamma0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] <;> ring

/-- **The parity operation** `𝒫(Ψ) = γ₀ Ψ γ₀` (Swift–Lee Eq. 8). -/
def parityConj (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := gamma0 * M * gamma0

/-- **The parity operation is an involution** `𝒫² = id` (`γ₀² = 1`). -/
theorem parityConj_involutive (M : Matrix (Fin 2) (Fin 2) ℂ) :
    parityConj (parityConj M) = M := by
  unfold parityConj
  rw [show gamma0 * (gamma0 * M * gamma0) * gamma0
        = gamma0 * gamma0 * M * (gamma0 * gamma0) from by simp only [Matrix.mul_assoc],
    gamma0_sq, Matrix.one_mul, Matrix.mul_one]

/-- **Even-parity sector**: diagonal amplitudes are fixed, `𝒫(diag) = diag`. -/
theorem parityConj_diagonal (a d : ℂ) :
    parityConj !![a, 0; 0, d] = !![a, 0; 0, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parityConj, gamma0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]

/-- **Odd-parity sector**: off-diagonal amplitudes flip sign, `𝒫(offDiag) = −offDiag`. The parity
operation decouples even (diagonal) from odd (off-diagonal). -/
theorem parityConj_offDiag (b c : ℂ) :
    parityConj !![0, b; c, 0] = -!![0, b; c, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parityConj, gamma0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

/-! ## §B — complex angular momentum and the Regge signature `e^{iπJ}` -/

/-- **The Regge signature factor** `e^{iπJ}` (the `(−1)^J` parity assignment continued to complex
angular momentum `J`). -/
def reggeSignature (J : ℂ) : ℂ := Complex.exp (Complex.I * (Real.pi : ℂ) * J)

/-- **The Regge signature modulus is the entropic damping** `‖e^{iπJ}‖ = e^{−π J_I}` — exponential
damping by the imaginary angular momentum `J_I = Im J` (the `S_I/ℏ` of the Regge amplitude). -/
theorem norm_reggeSignature (J : ℂ) :
    ‖reggeSignature J‖ = Real.exp (-(Real.pi) * J.im) := by
  unfold reggeSignature
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]

/-- **A real angular momentum gives a unimodular signature** `J_I = 0 ⟹ ‖e^{iπJ}‖ = 1`: the
physical (un-damped) angular momentum, the reversible fiber. -/
theorem reggeSignature_real_unimodular (J : ℂ) (h : J.im = 0) :
    ‖reggeSignature J‖ = 1 := by
  rw [norm_reggeSignature, h, mul_zero, Real.exp_zero]

/-- **At integer `J = n` the signature is the parity** `(−1)^n` (`e^{iπn} = (−1)^n`). -/
theorem reggeSignature_nat (n : ℕ) : reggeSignature (n : ℂ) = (-1) ^ n := by
  unfold reggeSignature
  rw [show Complex.I * (Real.pi : ℂ) * (n : ℂ) = (n : ℂ) * ((Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-! ## §C — the `J(J+1)` partial-wave coefficient, analytic in complex `J` -/

/-- **The angular-momentum Casimir** `J(J+1)` (a Swift–Lee Table I coefficient): a polynomial in `J`,
hence analytic and continued to all complex `J`. -/
def reggeCasimir (J : ℂ) : ℂ := J * (J + 1)

/-- At integer `J = n` the Casimir is the physical eigenvalue `n(n+1)`. -/
theorem reggeCasimir_nat (n : ℕ) : reggeCasimir (n : ℂ) = (n : ℂ) * ((n : ℂ) + 1) := rfl

/-! ## §D — the bundled statement -/

/-- **Complex angular momentum in the spinor BS equation, summarized.**

* the parity operation `𝒫(Ψ) = γ₀ Ψ γ₀` is an involution decoupling even/odd sectors;
* the Regge signature `e^{iπJ}` damps by the imaginary angular momentum, `‖e^{iπJ}‖ = e^{−πJ_I}`
  (the angular-momentum analogue of the complex-action damping `e^{−S_I/ℏ}`), unimodular for real
  `J`, and the parity `(−1)^n` at integers. -/
theorem complex_angular_momentum_summary (M : Matrix (Fin 2) (Fin 2) ℂ) (J : ℂ) (n : ℕ) :
    parityConj (parityConj M) = M
      ∧ ‖reggeSignature J‖ = Real.exp (-(Real.pi) * J.im)
      ∧ (J.im = 0 → ‖reggeSignature J‖ = 1)
      ∧ reggeSignature (n : ℂ) = (-1) ^ n :=
  ⟨parityConj_involutive M, norm_reggeSignature J, fun h => reggeSignature_real_unimodular J h,
   reggeSignature_nat n⟩

end Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeComplexAngularMomentum

end

end
