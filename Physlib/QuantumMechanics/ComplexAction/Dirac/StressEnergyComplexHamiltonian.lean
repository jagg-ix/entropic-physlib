/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMatterEnergyDensity
public import Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization

/-!
# The Dirac stress-energy generator as the complex Hamiltonian `H_C = H_R − iH_I` (roadmap B1)

This is target **B1**: the Dirac field's energy operator (the generator of its stress-energy)
written as the Nagao–Nielsen / complex-action complex Hamiltonian `H_C = H_R − iH_I`, with a Hermitian real
part `H_R` (the reversible Dirac Hamiltonian, `T_R`) and a Hermitian imaginary part `H_I` sourced by
the imaginary mass (the dissipative generator). This is the matrix-level `HR + J` structure of
reference tree's `ComplexStressEnergyBridge.complex-action matrix`.

## No duplicated infrastructure

`H_R` and `H_I` are **both** the existing `Dirac.KleinGordonDiracFactorization.diracHamiltonian`
(`!![Δ, vp; vp, −Δ] = Δσ₃ + vp σ₁`) — no new Dirac matrix is introduced:

* `H_R = diracHamiltonian Δ_R vp` (real Dirac Hamiltonian, `Δ_R = m_R c²` the real gap, `vp = cp`);
* `H_I = diracHamiltonian Δ_I 0 = Δ_I σ₃` (the diagonal part, `Δ_I = m_I c²` from the imaginary mass).

The complex-mass Dirac Hamiltonian is then

  `H_C = H_R − i H_I = !![Δ_R − iΔ_I, vp; vp, −(Δ_R − iΔ_I)]`
       (`complexDiracHamiltonian`, `complexDiracHamiltonian_eq_HR_sub_I_HI`).

Its diagonal entry is exactly the damped complex energy `E_C = E_R − iE_I` of A2's
`WickRotation.complexEnergy` (`complexDiracHamiltonian_diag_eq_complexEnergy`).

## Structure

* **Hermitian parts.** `diracHamiltonian` is real symmetric (`diracHamiltonian_isSymm`), so `H_R` and
  `H_I` are Hermitian — the `HR` (Hermitian `T_R`) and `J` (Hermitian dissipative) of the complex-action matrix.
  (Caveat: `H_I = Δ_I σ₃` is sign-indefinite — PSD on the positive-energy/particle branch `+Δ_I ≥ 0`,
  the antiparticle branch is its CPT conjugate; the PSD condition on the imaginary stress-energy holds
  per branch.)
* **Reduction.** At `Δ_I = 0` (real mass, reversible) `H_C` is the real Dirac Hamiltonian
  (`complexDiracHamiltonian_reversible`).
* **Clifford / mass shell.** `H_C² = ((Δ_R − iΔ_I)² + vp²)·1`
  (`complexDiracHamiltonian_sq`) — the Klein–Gordon factorization with complex mass; the eigenvalue
  `±√(Δ_C² + vp²)` is the full Einstein complex energy.

## Main results

* `complexDiracHamiltonian`, `complexDiracHamiltonian_eq_HR_sub_I_HI` — `H_C = H_R − iH_I` (reusing
  `diracHamiltonian` for both).
* `diracHamiltonian_isSymm` — `H_R`, `H_I` Hermitian (real symmetric).
* `complexDiracHamiltonian_diag_eq_complexEnergy` — diagonal = A2's damped complex energy.
* `complexDiracHamiltonian_reversible` — `Δ_I = 0 ⟹` real Dirac.
* `complexDiracHamiltonian_sq` — Clifford square (complex-mass Klein–Gordon).
* `dirac_stress_energy_complex_hamiltonian` — the bundled `H_C = H_R − iH_I` structure.

## References

* P. A. M. Dirac, Proc. R. Soc. A **117** (1928) 610. doi:10.1098/rspa.1928.0023. K. Nagao,
  H. B. Nielsen (complex `H_C = H_R − iH_I`).
* This development: `Dirac.KleinGordonDiracFactorization`, `ComplexEinstein.ComplexMatterEnergyDensity`,
  `NonHermitian.WickRotation`; reference tree `ComplexStressEnergyBridge`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
open Physlib.QuantumMechanics.NonHermitian.WickRotation (complexEnergy)

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.StressEnergyComplexHamiltonian

/-! ## §A — the real Dirac Hamiltonian is Hermitian (the `H_R`, `H_I` sectors) -/

/-- **The real Dirac Hamiltonian is symmetric** (`= Hermitian`): `H_R = diracHamiltonian Δ_R vp` and
`H_I = diracHamiltonian Δ_I 0` are both Hermitian. -/
theorem diracHamiltonian_isSymm (Δ vp : ℝ) :
    (diracHamiltonian Δ vp)ᵀ = diracHamiltonian Δ vp := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracHamiltonian, Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]

/-! ## §B — the complex Dirac Hamiltonian `H_C = H_R − iH_I` -/

/-- **The complex-mass Dirac Hamiltonian** `H_C = !![Δ_R − iΔ_I, vp; vp, −(Δ_R − iΔ_I)]` — the
Dirac energy operator with complex gap `Δ_C = Δ_R − iΔ_I` (`Δ_R = m_R c²`, `Δ_I = m_I c²`). -/
def complexDiracHamiltonian (Δ_R Δ_I vp : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Δ_R : ℂ) - Complex.I * (Δ_I : ℂ), (vp : ℂ);
     (vp : ℂ), -((Δ_R : ℂ) - Complex.I * (Δ_I : ℂ))]

/-- **`H_C = H_R − i H_I`** with `H_R = diracHamiltonian Δ_R vp` and `H_I = diracHamiltonian Δ_I 0`
(both the existing Dirac Hamiltonian — no duplication). -/
theorem complexDiracHamiltonian_eq_HR_sub_I_HI (Δ_R Δ_I vp : ℝ) :
    complexDiracHamiltonian Δ_R Δ_I vp
      = (diracHamiltonian Δ_R vp).map Complex.ofReal
        - Complex.I • (diracHamiltonian Δ_I 0).map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexDiracHamiltonian, diracHamiltonian, Matrix.map_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

/-- **The diagonal of `H_C` is the damped complex energy** `Δ_R − iΔ_I = complexEnergy Δ_R Δ_I` (A2's
`WickRotation.complexEnergy`) — the complex rest energy. -/
theorem complexDiracHamiltonian_diag_eq_complexEnergy (Δ_R Δ_I vp : ℝ) :
    complexDiracHamiltonian Δ_R Δ_I vp 0 0 = complexEnergy Δ_R Δ_I := by
  simp [complexDiracHamiltonian, complexEnergy, Matrix.cons_val_zero, Matrix.head_cons]

/-! ## §C — reduction and the Clifford square -/

/-- **Reversible reduction**: at `Δ_I = 0` (real mass) `H_C` is the real Dirac Hamiltonian. -/
theorem complexDiracHamiltonian_reversible (Δ_R vp : ℝ) :
    complexDiracHamiltonian Δ_R 0 vp = (diracHamiltonian Δ_R vp).map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexDiracHamiltonian, diracHamiltonian, Matrix.map_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]

/-- **The Clifford square** `H_C² = ((Δ_R − iΔ_I)² + vp²)·1` — the Klein–Gordon factorization with
complex mass; the eigenvalue `±√(Δ_C² + vp²)` is the full Einstein complex energy. -/
theorem complexDiracHamiltonian_sq (Δ_R Δ_I vp : ℝ) :
    complexDiracHamiltonian Δ_R Δ_I vp * complexDiracHamiltonian Δ_R Δ_I vp
      = (((Δ_R : ℂ) - Complex.I * (Δ_I : ℂ)) ^ 2 + (vp : ℂ) ^ 2) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexDiracHamiltonian, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

/-! ## §D — the bundled structure -/

/-- **The Dirac stress-energy generator is the complex-action complex Hamiltonian `H_C = H_R − iH_I`.** For the
complex gap `Δ_C = Δ_R − iΔ_I` (`Δ_R = m_R c²`, `Δ_I = m_I c²`):

* `H_C = H_R − iH_I`, with `H_R = diracHamiltonian Δ_R vp`, `H_I = diracHamiltonian Δ_I 0` (both the
  existing Dirac Hamiltonian);
* `H_R`, `H_I` are Hermitian (real symmetric) — the `HR`/`J` of the complex-action matrix;
* at `Δ_I = 0` (real mass) `H_C` reduces to the real Dirac Hamiltonian;
* `H_C² = (Δ_C² + vp²)·1` (complex-mass Klein–Gordon). -/
theorem dirac_stress_energy_complex_hamiltonian (Δ_R Δ_I vp : ℝ) :
    complexDiracHamiltonian Δ_R Δ_I vp
        = (diracHamiltonian Δ_R vp).map Complex.ofReal
          - Complex.I • (diracHamiltonian Δ_I 0).map Complex.ofReal
      ∧ (diracHamiltonian Δ_R vp)ᵀ = diracHamiltonian Δ_R vp
      ∧ (diracHamiltonian Δ_I 0)ᵀ = diracHamiltonian Δ_I 0
      ∧ complexDiracHamiltonian Δ_R 0 vp = (diracHamiltonian Δ_R vp).map Complex.ofReal
      ∧ complexDiracHamiltonian Δ_R Δ_I vp * complexDiracHamiltonian Δ_R Δ_I vp
          = (((Δ_R : ℂ) - Complex.I * (Δ_I : ℂ)) ^ 2 + (vp : ℂ) ^ 2) • 1 :=
  ⟨complexDiracHamiltonian_eq_HR_sub_I_HI Δ_R Δ_I vp, diracHamiltonian_isSymm Δ_R vp,
   diracHamiltonian_isSymm Δ_I 0, complexDiracHamiltonian_reversible Δ_R vp,
   complexDiracHamiltonian_sq Δ_R Δ_I vp⟩

end Physlib.QuantumMechanics.ComplexAction.Dirac.StressEnergyComplexHamiltonian

end

end
