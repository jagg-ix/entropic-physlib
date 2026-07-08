/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorPurification
public import Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism

/-!
# Verch's polarizator is the Bloch/Poincaré-sphere generator `iσ₂` (Verch 1996 ↔ Saito 2024)

Links the Verch pure-state **polarizator** `R_μ = sympForm = J` (`AlgebraicQFTQuasifree.PolarizatorPurification`, the complex
structure `J² = −1` that is the "imaginary unit" of the one-particle space) to the **Bloch / Poincaré sphere**
of Saito's polarization optics (`Hopf.StokesSpinorIsomorphism`, *S. Saito, Front. Phys. 11 (2024) 1225334*): the
Stokes parameters `Sᵢ = ⟨χ|σⁱ|χ⟩` of a Jones-vector qubit `χ ∈ ℂ²` lie on the Poincaré sphere
`S₁² + S₂² + S₃² = S₀²` — the Bloch sphere of polarization.

The bridge is the elementary but exact identity

  `J = i·σ₂`   (`sympFormC_eq_I_smul_pauliY`),

i.e. Verch's symplectic complex structure, complexified, is `i` times the Pauli-`Y` matrix. Consequences:

* the pure-state condition `J² = −1` is the **Pauli involution** `σ₂² = 1` dressed by `i²`
  (`pauliY_sq`, `sympFormC_sq`);
* the polarizator's spin expectation is the **circular-polarization Stokes parameter** `S₂`
  (`spinExpectation_polarizator`): `⟨χ|J|χ⟩ = i·S₂`. So Verch's complex structure is the generator of
  rotations about the `S₂` (circular-polarization) axis of the Bloch/Poincaré sphere, and a pure quasifree
  state's choice of `J` is a point on that sphere (`pure_state_poincare_sphere`).

This identifies the abstract "one-particle complex structure" of the Hadamard/Weyl construction with the
concrete `SU(2)` qubit / polarization Bloch sphere, tying the Verch arc to Saito's Stokes-spinor isomorphism
(and, through the shared `SU(2)`/symplectic structure, to `AlgebraicQFT.SymplecticAdjointHadamard`'s Bogoliubov maps).

## References

* R. Verch, arXiv:funct-an/9609004 (the polarizator `R_μ`, pure-state complex structure `R_μ² = −1`).
* S. Saito, Front. Phys. 11 (2024) 1225334 (Stokes ↔ spin isomorphism, the Poincaré sphere).
* Repo dependencies: `AlgebraicQFTQuasifree.PolarizatorPurification` (`sympForm`, the pure polarizator), `Hopf.StokesSpinorIsomorphism`
  (`spinExpectation`, `stokesS`, `poincare_sphere`), `Relativity.PauliMatrices` (`σ`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorBlochSphere

open Matrix PauliMatrix
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SymplecticAdjointHadamard
open Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism

/-! ## §A — the polarizator is `iσ₂` -/

/-- **[`J = i·σ₂`] The Verch polarizator is `i` times Pauli-`Y`.** Complexifying the real symplectic complex
structure `sympForm = !![0,1;−1,0]` gives `i·σ₂` (`σ₂ = !![0,−i;i,0]`) — the generator of Bloch/Poincaré-sphere
rotations about the circular-polarization (`S₂`) axis. The "imaginary unit of the one-particle space" is the
Pauli-`Y` generator. -/
theorem sympFormC_eq_I_smul_pauliY :
    sympForm.map (Complex.ofReal) = Complex.I • (σ (Sum.inr 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sympForm, pauliMatrix, Matrix.map_apply, Matrix.smul_apply, Complex.I_mul_I]

/-! ## §B — pure state ⟺ Pauli involution `σ₂² = 1` -/

/-- **[Pauli involution] `σ₂² = 1`** — Pauli-`Y` is a unitary involution, the `SU(2)` reflection underlying the
`S₂` axis of the Bloch sphere. -/
theorem pauliY_sq : (σ (Sum.inr 1)) * (σ (Sum.inr 1)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- **[Pure-state complex structure from the Pauli involution] `J² = −1`** derived via `J = iσ₂` and
`σ₂² = 1`: the Verch pure-state condition `R_μ² = −1` (`AlgebraicQFTQuasifree.PolarizatorPurification`) *is* the Pauli involution
`σ₂² = 1` dressed by `i² = −1`. -/
theorem sympFormC_sq :
    (sympForm.map (Complex.ofReal)) * (sympForm.map (Complex.ofReal)) = -1 := by
  rw [sympFormC_eq_I_smul_pauliY, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I,
    pauliY_sq]
  simp

/-! ## §C — the polarizator axis is the `S₂` Stokes parameter on the Poincaré sphere -/

/-- **[Polarizator expectation = `i·S₂`] `⟨χ|J|χ⟩ = i·S₂`.** The spin expectation of the (complexified)
polarizator is `i` times the circular-polarization Stokes parameter `S₂ = ⟨χ|σ₂|χ⟩` — Verch's complex
structure measures the `S₂` axis of the Bloch/Poincaré sphere. -/
theorem spinExpectation_polarizator (χ : Fin 2 → ℂ) :
    spinExpectation (sympForm.map (Complex.ofReal)) χ = Complex.I * stokesS (Sum.inr 1) χ := by
  rw [sympFormC_eq_I_smul_pauliY, spinExpectation, stokesS, spinExpectation, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]

/-- **[Pure quasifree state ↔ a point on the Bloch/Poincaré sphere]** A Jones-vector qubit `χ` lies on Saito's
Poincaré sphere `S₁² + S₂² + S₃² = S₀²` (`poincare_sphere`), and the Verch polarizator's expectation is its
`S₂` (circular-polarization) coordinate. The abstract one-particle complex structure is a concrete point/axis
of the `SU(2)` Bloch sphere. -/
theorem pure_state_poincare_sphere (χ : Fin 2 → ℂ) :
    stokesS (Sum.inr 0) χ ^ 2 + stokesS (Sum.inr 1) χ ^ 2 + stokesS (Sum.inr 2) χ ^ 2
        = stokesS (Sum.inl 0) χ ^ 2
      ∧ spinExpectation (sympForm.map (Complex.ofReal)) χ = Complex.I * stokesS (Sum.inr 1) χ :=
  ⟨poincare_sphere χ, spinExpectation_polarizator χ⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorBlochSphere

end
