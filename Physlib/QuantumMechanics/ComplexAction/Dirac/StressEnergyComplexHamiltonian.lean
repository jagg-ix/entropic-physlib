/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMatterEnergyDensity
public import Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization

/-!
# The Dirac stress-energy generator with a complexified mass gap `H_C = H_R − iH_I`

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

The Dirac Hamiltonian with a complexified mass gap is then

  `H_C = H_R − i H_I = !![Δ_R − iΔ_I, vp; vp, −(Δ_R − iΔ_I)]`
       (`complexMassDiracHamiltonian`, `complexMassDiracHamiltonian_eq_HR_sub_I_HI`).

Its diagonal entry is exactly the damped complex energy `E_C = E_R − iE_I` of A2's
`WickRotation.complexEnergy` (`complexMassDiracHamiltonian_diag_eq_complexEnergy`).

## Structure

* **Hermitian parts.** `diracHamiltonian` is real symmetric (`diracHamiltonian_isSymm`), so `H_R` and
  `H_I` are Hermitian — the `HR` (Hermitian `T_R`) and `J` (Hermitian dissipative) of the complex-action matrix.
  (Caveat: `H_I = Δ_I σ₃` is sign-indefinite — PSD on the positive-energy/particle branch `+Δ_I ≥ 0`,
  the antiparticle branch is its CPT conjugate; the PSD condition on the imaginary stress-energy holds
  per branch.)
* **Reduction.** At `Δ_I = 0` (real mass, reversible) `H_C` is the real Dirac Hamiltonian
  (`complexMassDiracHamiltonian_reversible`).
* **Clifford / mass shell.** `H_C² = ((Δ_R − iΔ_I)² + vp²)·1`
  (`complexMassDiracHamiltonian_sq`) — the Klein–Gordon factorization with complex mass; the eigenvalue
  `±√(Δ_C² + vp²)` is the full Einstein complex energy.

## Main results

* `complexMassDiracHamiltonian`, `complexMassDiracHamiltonian_eq_HR_sub_I_HI` — `H_C = H_R − iH_I` (reusing
  `diracHamiltonian` for both).
* `diracHamiltonian_isSymm` — `H_R`, `H_I` Hermitian (real symmetric).
* `complexMassDiracHamiltonian_diag_eq_complexEnergy` — diagonal = A2's damped complex energy.
* `complexMassDiracHamiltonian_reversible` — `Δ_I = 0 ⟹` real Dirac.
* `complexMassDiracHamiltonian_sq` — Clifford square (complex-mass Klein–Gordon).
* `diracLiouvillian`, `dirac_liouvillian_complex_decompose`, `dirac_liouvillian_reversible` — the local
  Dirac Liouvillian of `H_C` splits into reversible and imaginary-gap commutator parts.
* `dirac_stress_energy_complex_hamiltonian` — the bundled `H_C = H_R − iH_I` structure.

## References

* P. A. M. Dirac, Proc. R. Soc. A **117** (1928) 610. doi:10.1098/rspa.1928.0023. K. Nagao,
  H. B. Nielsen (complex `H_C = H_R − iH_I`).
* This development: `Dirac.KleinGordonDiracFactorization`, `ComplexEinstein.ComplexMatterEnergyDensity`,
  `NonHermitian.WickRotation`; reference tree `ComplexStressEnergyBridge`.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
open Physlib.QuantumMechanics.NonHermitian.WickRotation (complexEnergy)

namespace Physlib.QuantumMechanics.ComplexAction.Dirac.StressEnergyComplexHamiltonian


/-- **The real Dirac Hamiltonian is symmetric** (`= Hermitian`): `H_R = diracHamiltonian Δ_R vp` and
`H_I = diracHamiltonian Δ_I 0` are both Hermitian. -/
lemma diracHamiltonian_isSymm (Δ vp : ℝ) :
    (diracHamiltonian Δ vp)ᵀ = diracHamiltonian Δ vp := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracHamiltonian, Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]


/-- **The Dirac Hamiltonian with a complexified mass gap**
`H_C = !![Δ_R − iΔ_I, vp; vp, −(Δ_R − iΔ_I)]`.  This is not a new Dirac equation: it is the ordinary
Dirac Hamiltonian, already over complex matrices, with the real mass gap replaced by the complex-action
gap `Δ_C = Δ_R − iΔ_I` (`Δ_R = m_R c²`, `Δ_I = m_I c²`). -/
def complexMassDiracHamiltonian (Δ_R Δ_I vp : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Δ_R : ℂ) - Complex.I * (Δ_I : ℂ), (vp : ℂ);
     (vp : ℂ), -((Δ_R : ℂ) - Complex.I * (Δ_I : ℂ))]

/-- **`H_C = H_R − i H_I`** with `H_R = diracHamiltonian Δ_R vp` and `H_I = diracHamiltonian Δ_I 0`
(both the existing Dirac Hamiltonian — no duplication). -/
lemma complexMassDiracHamiltonian_eq_HR_sub_I_HI (Δ_R Δ_I vp : ℝ) :
    complexMassDiracHamiltonian Δ_R Δ_I vp
      = (diracHamiltonian Δ_R vp).map Complex.ofReal
        - Complex.I • (diracHamiltonian Δ_I 0).map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexMassDiracHamiltonian, diracHamiltonian, Matrix.map_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

/-- **The diagonal of `H_C` is the damped complex energy** `Δ_R − iΔ_I = complexEnergy Δ_R Δ_I` (A2's
`WickRotation.complexEnergy`) — the complex rest energy. -/
lemma complexMassDiracHamiltonian_diag_eq_complexEnergy (Δ_R Δ_I vp : ℝ) :
    complexMassDiracHamiltonian Δ_R Δ_I vp 0 0 = complexEnergy Δ_R Δ_I := by
  simp [complexMassDiracHamiltonian, complexEnergy, Matrix.cons_val_zero, Matrix.head_cons]


/-- **Reversible reduction**: at `Δ_I = 0` (real mass) `H_C` is the real Dirac Hamiltonian. -/
lemma complexMassDiracHamiltonian_reversible (Δ_R vp : ℝ) :
    complexMassDiracHamiltonian Δ_R 0 vp = (diracHamiltonian Δ_R vp).map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexMassDiracHamiltonian, diracHamiltonian, Matrix.map_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]

/-- **The local Dirac Liouvillian** `𝓛_H(Y) = -i[H,Y]` for the finite Dirac
matrix algebra. This keeps the Dirac-specific split in the Dirac module without
importing the higher-level open-system superoperator layer. -/
noncomputable def diracLiouvillian
    (H Y : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  -Complex.I • (H * Y - Y * H)

/-- **[Complex-mass Dirac Liouvillian split].** The local Dirac Liouvillian of
`H_C = H_R - iH_I` splits into the reversible real-Dirac part and the
real-coefficient commutator generated by the imaginary Dirac gap. -/
lemma dirac_liouvillian_complex_decompose (Δ_R Δ_I vp : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    diracLiouvillian (complexMassDiracHamiltonian Δ_R Δ_I vp) Y
      = -Complex.I • (((diracHamiltonian Δ_R vp).map Complex.ofReal) * Y
                       - Y * ((diracHamiltonian Δ_R vp).map Complex.ofReal))
        - (((diracHamiltonian Δ_I 0).map Complex.ofReal) * Y
            - Y * ((diracHamiltonian Δ_I 0).map Complex.ofReal)) := by
  unfold diracLiouvillian
  rw [complexMassDiracHamiltonian_eq_HR_sub_I_HI]
  have hc :
      (((diracHamiltonian Δ_R vp).map Complex.ofReal
          - Complex.I • (diracHamiltonian Δ_I 0).map Complex.ofReal) * Y
          - Y * ((diracHamiltonian Δ_R vp).map Complex.ofReal
          - Complex.I • (diracHamiltonian Δ_I 0).map Complex.ofReal))
        =
          ((diracHamiltonian Δ_R vp).map Complex.ofReal * Y
            - Y * (diracHamiltonian Δ_R vp).map Complex.ofReal)
          - Complex.I •
            ((diracHamiltonian Δ_I 0).map Complex.ofReal * Y
              - Y * (diracHamiltonian Δ_I 0).map Complex.ofReal) := by
    rw [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub]
    abel
  rw [hc, smul_sub, smul_smul,
    show -Complex.I * Complex.I = (1 : ℂ) by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]

/-- **[Reversible Dirac Liouvillian].** At `Δ_I = 0`, the complex-mass Dirac
Liouvillian reduces to the real Dirac Liouvillian. -/
lemma dirac_liouvillian_reversible (Δ_R vp : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    diracLiouvillian (complexMassDiracHamiltonian Δ_R 0 vp) Y
      = diracLiouvillian ((diracHamiltonian Δ_R vp).map Complex.ofReal) Y := by
  rw [complexMassDiracHamiltonian_reversible]

/-- **The Clifford square** `H_C² = ((Δ_R − iΔ_I)² + vp²)·1` — the Klein–Gordon factorization with
complex mass; the eigenvalue `±√(Δ_C² + vp²)` is the full Einstein complex energy. -/
lemma complexMassDiracHamiltonian_sq (Δ_R Δ_I vp : ℝ) :
    complexMassDiracHamiltonian Δ_R Δ_I vp * complexMassDiracHamiltonian Δ_R Δ_I vp
      = (((Δ_R : ℂ) - Complex.I * (Δ_I : ℂ)) ^ 2 + (vp : ℂ) ^ 2) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexMassDiracHamiltonian, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring


/-- **The Dirac stress-energy generator is the complex-action complex Hamiltonian `H_C = H_R − iH_I`.** For the
complex gap `Δ_C = Δ_R − iΔ_I` (`Δ_R = m_R c²`, `Δ_I = m_I c²`):

* `H_C = H_R − iH_I`, with `H_R = diracHamiltonian Δ_R vp`, `H_I = diracHamiltonian Δ_I 0` (both the
  existing Dirac Hamiltonian);
* `H_R`, `H_I` are Hermitian (real symmetric) — the `HR`/`J` of the complex-action matrix;
* at `Δ_I = 0` (real mass) `H_C` reduces to the real Dirac Hamiltonian;
* `H_C² = (Δ_C² + vp²)·1` (complex-mass Klein–Gordon). -/
lemma dirac_stress_energy_complex_hamiltonian (Δ_R Δ_I vp : ℝ) :
    complexMassDiracHamiltonian Δ_R Δ_I vp
        = (diracHamiltonian Δ_R vp).map Complex.ofReal
          - Complex.I • (diracHamiltonian Δ_I 0).map Complex.ofReal
      ∧ (diracHamiltonian Δ_R vp)ᵀ = diracHamiltonian Δ_R vp
      ∧ (diracHamiltonian Δ_I 0)ᵀ = diracHamiltonian Δ_I 0
      ∧ complexMassDiracHamiltonian Δ_R 0 vp = (diracHamiltonian Δ_R vp).map Complex.ofReal
      ∧ complexMassDiracHamiltonian Δ_R Δ_I vp * complexMassDiracHamiltonian Δ_R Δ_I vp
          = (((Δ_R : ℂ) - Complex.I * (Δ_I : ℂ)) ^ 2 + (vp : ℂ) ^ 2) • 1 :=
  ⟨complexMassDiracHamiltonian_eq_HR_sub_I_HI Δ_R Δ_I vp, diracHamiltonian_isSymm Δ_R vp,
   diracHamiltonian_isSymm Δ_I 0, complexMassDiracHamiltonian_reversible Δ_R vp,
   complexMassDiracHamiltonian_sq Δ_R Δ_I vp⟩

end Physlib.QuantumMechanics.ComplexAction.Dirac.StressEnergyComplexHamiltonian

end

end
