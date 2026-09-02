/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.Spinors
meta import Zil

/-!
# Stokes parameters as spin expectation values, and the Poincaré sphere (Saito 2024)

This file formalizes the central result of **S. Saito, *Quantum field theory for coherent
photons: isomorphism between Stokes parameters and spin expectation values*, Front. Phys. 11
(2024) 1225334**: the polarisation **Stokes parameters are the expectation values of the spin
(Pauli) operators**, `Sᵢ = ⟨χ|σᵢ|χ⟩`, and they lie on the **Poincaré sphere**
`S₁² + S₂² + S₃² = S₀²`.

The polarisation state is a 2-spinor `χ ∈ ℂ²` (the **Jones vector**) — exactly the spin part of
the Dirac spinor `Dirac.Spinors.restPositiveSpinor χ`. The spin operators are the physlib Pauli
matrices `σⁱ` (`Relativity.PauliMatrices`); `S₀ = ⟨χ|1|χ⟩` is the intensity.

## Main results

* `spinExpectation M χ = ⟨χ|M|χ⟩`; `stokesS i χ = ⟨χ|σⁱ|χ⟩` — the Stokes parameter = spin
  expectation (`S = ⟨Ŝ⟩`).
* `stokesS0_eq_normSq` — `S₀ = ‖χ₀‖² + ‖χ₁‖²` (the intensity).
* `poincare_sphere` — **`S₁² + S₂² + S₃² = S₀²`**: the Stokes/spin vector lies on the Poincaré
  sphere.
* `jonesVector_eq_diracSpin` — the Jones vector is the spin 2-spinor of the Dirac spinor.

## References

* S. Saito, Front. Phys. 11 (2024) 1225334 (Stokes ↔ spin isomorphism, Poincaré sphere).
* `Dirac.Spinors`, `Relativity.PauliMatrices` (this development).


-/

set_option autoImplicit false

@[expose] public section

open Matrix PauliMatrix
open Physlib.QuantumMechanics.ComplexAction.Dirac.Spinors

namespace Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism


/-- **The spin expectation value** `⟨χ|M|χ⟩ = χ† M χ`. -/
noncomputable def spinExpectation (M : Matrix (Fin 2) (Fin 2) ℂ) (χ : Fin 2 → ℂ) : ℂ :=
  star χ ⬝ᵥ M *ᵥ χ

/-- **The Stokes parameter** `Sᵢ = ⟨χ|σⁱ|χ⟩` — the expectation value of the spin (Pauli)
operator (`i = inl 0` gives `S₀`, the intensity). -/
noncomputable def stokesS (i : Fin 1 ⊕ Fin 3) (χ : Fin 2 → ℂ) : ℂ := spinExpectation (σ i) χ

/-- The four Stokes parameters in explicit form (`a = χ₀`, `b = χ₁`). -/
lemma stokesS0_apply (χ : Fin 2 → ℂ) :
    stokesS (Sum.inl 0) χ = star (χ 0) * χ 0 + star (χ 1) * χ 1 := by
  simp [stokesS, spinExpectation, pauliMatrix, dotProduct, mulVec, Fin.sum_univ_two]

lemma stokesS1_apply (χ : Fin 2 → ℂ) :
    stokesS (Sum.inr 0) χ = star (χ 0) * χ 1 + star (χ 1) * χ 0 := by
  simp [stokesS, spinExpectation, pauliMatrix, dotProduct, mulVec, Fin.sum_univ_two]

lemma stokesS2_apply (χ : Fin 2 → ℂ) :
    stokesS (Sum.inr 1) χ = Complex.I * (star (χ 1) * χ 0 - star (χ 0) * χ 1) := by
  simp [stokesS, spinExpectation, pauliMatrix, dotProduct, mulVec, Fin.sum_univ_two]
  ring

lemma stokesS3_apply (χ : Fin 2 → ℂ) :
    stokesS (Sum.inr 2) χ = star (χ 0) * χ 0 - star (χ 1) * χ 1 := by
  simp [stokesS, spinExpectation, pauliMatrix, dotProduct, mulVec, Fin.sum_univ_two]
  ring

/-- **`S₀` is the intensity** `‖χ₀‖² + ‖χ₁‖²` — the spin expectation of the identity. -/
lemma stokesS0_eq_normSq (χ : Fin 2 → ℂ) :
    stokesS (Sum.inl 0) χ = ((Complex.normSq (χ 0) + Complex.normSq (χ 1) : ℝ) : ℂ) := by
  rw [stokesS0_apply]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  rfl


/-- **The Poincaré sphere**: `S₁² + S₂² + S₃² = S₀²` — the Stokes/spin vector lies on a sphere
of radius `S₀` (the intensity). The polarisation state is a point on the Poincaré sphere. -/
lemma poincare_sphere (χ : Fin 2 → ℂ) :
    stokesS (Sum.inr 0) χ ^ 2 + stokesS (Sum.inr 1) χ ^ 2 + stokesS (Sum.inr 2) χ ^ 2
      = stokesS (Sum.inl 0) χ ^ 2 := by
  rw [stokesS0_apply, stokesS1_apply, stokesS2_apply, stokesS3_apply]
  linear_combination (star (χ 1) * χ 0 - star (χ 0) * χ 1) ^ 2 * Complex.I_sq


/-- **The Jones (polarisation) vector is the spin part of the Dirac spinor**: `χ` is precisely
the 2-spinor of `restPositiveSpinor χ`. The Stokes/spin isomorphism is the polarisation content
of the Dirac spinor. -/
lemma jonesVector_eq_diracSpin (χ : Fin 2 → ℂ) (i : Fin 2) :
    restPositiveSpinor χ (Sum.inl i) = χ i := rfl

end Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism.poincare_sphere where
  formalizes @ "claim:the-stokes-spin-vector-lies-on-the-poincare-sphere-s1sq-plus-s2sq-plus-s3sq-equals-s0sq",
  supported_by @ "paper:saito-2024-stokes-spin-isomorphism"

zil attach Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism.stokesS0_eq_normSq where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism.stokesS0_apply",
  formalizes @ "claim:the-stokes-intensity-s0-is-the-spinor-norm-squared",
  requires @ "claim:the-stokes-spin-vector-lies-on-the-poincare-sphere-s1sq-plus-s2sq-plus-s3sq-equals-s0sq"

zil attach Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism.jonesVector_eq_diracSpin where
  formalizes @ "claim:the-jones-polarisation-vector-is-the-spin-two-spinor-of-the-dirac-spinor",
  requires @ "claim:the-stokes-intensity-s0-is-the-spinor-norm-squared"

zil_file_contract physlib.stokesSpinorIsomorphism where
  promises "The Stokes-spin isomorphism: the Stokes spin vector lies on the Poincare sphere with S1 squared plus S2 squared plus S3 squared equal to S0 squared, the intensity S0 is the spinor norm squared, and the Jones polarisation vector is the spin two-spinor of the Dirac spinor."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism.stokesS",
    "lean:Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism.spinExpectation"]
  forbids_substitutes ["a full polarisation-optics or Mueller-calculus development, only the Stokes-spinor identity"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism.poincare_sphere,
    Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism.stokesS0_eq_normSq,
    Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism.jonesVector_eq_diracSpin]

/- ZIL-END -/
