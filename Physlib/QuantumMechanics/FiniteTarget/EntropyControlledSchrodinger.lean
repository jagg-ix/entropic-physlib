/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.NagaoNielsenSchrodinger
public import QuantumInfo.Entropy.EntropicProperTime

/-!
# Entropy-controlled non-Hermitian Schrödinger system

Ties the Nagao–Nielsen irreversible generator `H_I` to an entropy-production
rate. The system includes the reversible generator `H_R`, the irreversible
generator `H_I`, and an entropy rate that equals `(2/ℏ)·⟨H_I⟩`.

Key facts:
* the norm-squared decay rate equals the negative entropy rate;
* the entropy rate is non-negative (so the norm is non-increasing);
* at `H_I = 0` the generator is reversible (`H_C = H_R`), the entropy rate
  vanishes, and the norm is preserved.

## References

- **Sergi & Giaquinta 2016** — *Linear Quantum Entropy and Non-Hermitian Hamiltonians*, Entropy 18(12), 451, doi:10.3390/e18120451, arXiv:1612.05917 [bib: `SergiGiaquinta2016`] (`entropic-physlib-inventory/entropy-v18-i12_20260602.bib`) — **direct source** for the `H_C = H_R − i·H_I` decomposition with `d‖ψ‖²/dt = −(2/ℏ)·⟨H_I⟩`; Eq. (1)–(2) of the paper match this module verbatim.
- **Nagao & Nielsen 2011** — *Formulation of Complex Action Theory* [bib: `Nagao2011`] — related work in the rescaled `E_n − iΓ_n/2` convention.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics.FiniteTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- A non-Hermitian Schrödinger system whose irreversible generator `H_I` is
tied to an entropy-production rate `(2/ℏ)·⟨H_I⟩`. -/
structure EntropyControlledSchrodingerSystem where
  /-- Reversible (Hermitian) generator. -/
  H_R : H →L[ℂ] H
  /-- Irreversible generator. -/
  H_I : H →L[ℂ] H
  /-- Reduced Planck constant. -/
  hbar : ℝ
  /-- `ℏ > 0`. -/
  hbar_pos : 0 < hbar
  /-- Expectation `⟨ψ|H_I|ψ⟩` of the irreversible generator. -/
  expectation_HI : H → ℝ
  /-- Entropy-production rate. -/
  entropyRate : H → ℝ
  /-- The entropy rate is `(2/ℏ)·⟨H_I⟩`. -/
  entropyRate_eq_expectation :
    ∀ ψ, entropyRate ψ = (2 / hbar) * expectation_HI ψ
  /-- The expectation is non-negative (positive-semidefinite `H_I`). -/
  expectation_nonneg :
    ∀ ψ, 0 ≤ expectation_HI ψ
  /-- A vanishing irreversible generator has vanishing expectation. -/
  zero_HI_zero_expectation :
    H_I = 0 → ∀ ψ, expectation_HI ψ = 0

namespace EntropyControlledSchrodingerSystem

/-- The complex Hamiltonian `H_C = H_R − i·H_I`. -/
def H_C (S : EntropyControlledSchrodingerSystem (H := H)) : H →L[ℂ] H :=
  complexHamiltonian S.H_R S.H_I

/-- The norm-squared decay rate `−(2/ℏ)·⟨H_I⟩`. -/
def normDecayRate (S : EntropyControlledSchrodingerSystem (H := H)) (ψ : H) : ℝ :=
  normSquaredDecayRate S.hbar (S.expectation_HI ψ)

theorem normDecayRate_eq_neg_entropyRate
    (S : EntropyControlledSchrodingerSystem (H := H)) (ψ : H) :
    S.normDecayRate ψ = - S.entropyRate ψ := by
  unfold normDecayRate normSquaredDecayRate
  rw [S.entropyRate_eq_expectation ψ]
  ring

theorem entropyRate_nonneg
    (S : EntropyControlledSchrodingerSystem (H := H)) (ψ : H) :
    0 ≤ S.entropyRate ψ := by
  rw [S.entropyRate_eq_expectation ψ]
  exact mul_nonneg (div_nonneg (by norm_num) S.hbar_pos.le) (S.expectation_nonneg ψ)

theorem normDecayRate_nonpos
    (S : EntropyControlledSchrodingerSystem (H := H)) (ψ : H) :
    S.normDecayRate ψ ≤ 0 := by
  rw [normDecayRate_eq_neg_entropyRate]
  exact neg_nonpos.mpr (entropyRate_nonneg S ψ)

theorem zero_HI_implies_unitary_generator
    (S : EntropyControlledSchrodingerSystem (H := H))
    (hzero : S.H_I = 0) :
    S.H_C = S.H_R := by
  unfold H_C
  rw [hzero]
  exact complexHamiltonian_at_H_I_zero S.H_R

theorem zero_HI_implies_zero_entropyRate
    (S : EntropyControlledSchrodingerSystem (H := H))
    (hzero : S.H_I = 0) (ψ : H) :
    S.entropyRate ψ = 0 := by
  rw [S.entropyRate_eq_expectation ψ, S.zero_HI_zero_expectation hzero ψ]
  ring

theorem zero_HI_frozen_reduction
    (S : EntropyControlledSchrodingerSystem (H := H))
    (hzero : S.H_I = 0) (ψ : H) :
    S.H_C = S.H_R
    ∧ S.entropyRate ψ = 0
    ∧ S.normDecayRate ψ = 0 := by
  refine ⟨zero_HI_implies_unitary_generator S hzero,
          zero_HI_implies_zero_entropyRate S hzero ψ, ?_⟩
  rw [normDecayRate_eq_neg_entropyRate, zero_HI_implies_zero_entropyRate S hzero ψ]
  ring

end EntropyControlledSchrodingerSystem

/-- A **finite entropic transition** for an entropy-controlled system: an
initial and final finite quantum state, a Hilbert-space vector at which the
entropy rate is read, and an elapsed external time `Δt`, related by the
entropy-production law `D(ρ₁‖ρ₀) = entropyRate ψ · Δt`. -/
structure EntropicTransition {d : Type*} [Fintype d] [DecidableEq d]
    (S : EntropyControlledSchrodingerSystem (H := H)) where
  /-- Initial state. -/
  ρ₀ : MState d
  /-- Final state. -/
  ρ₁ : MState d
  /-- Hilbert-space vector at which the entropy rate is evaluated. -/
  ψ : H
  /-- Elapsed external time. -/
  Δt : ℝ
  /-- Entropy-production relation: dimensionless gap `= entropyRate · Δt`. -/
  rate_relation :
    (QuantumInfo.Finite.entropicProperTime ρ₁ ρ₀).toReal = S.entropyRate ψ * Δt

end QuantumMechanics.FiniteTarget

end
