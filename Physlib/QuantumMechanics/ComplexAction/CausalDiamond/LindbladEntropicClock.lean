/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MisraJacobsonSynthesis
public import Physlib.QuantumMechanics.Lindblad.GKLSEntropicRate
public import Physlib.QuantumMechanics.FiniteTarget.QIFMasterEquationDerivations

/-!
# The GKLS Lindblad rate is the matrix realization of the synthesis's entropic clock

`CausalDiamond.MisraJacobsonSynthesis` classifies the irreversible **entropic clock** abstractly — the
generator `H_I` of `H_C = H_R − i H_I`, the conditional entropic rate `(1/ℏ)∑‖Lⱼψ‖² ≥ 0`, the Misra
`i[L,T] = I` time operator, and the diamond's negative temperature. The GKLS / Lindblad layer
(`Lindblad.GKLSEntropicRate`) gives the **matrix** form of exactly that clock:

* `gklsImaginaryHamiltonian L ℏ = (ℏ/2)·∑ⱼ Lⱼ† Lⱼ` *is* the imaginary Hamiltonian `H_I` built from the
  jump family — the entropic generator;
* `gklsEntropicRate L ρ = ∑ⱼ Tr(Lⱼ† Lⱼ ρ).re ≥ 0` is its entropy-production rate — the second law in the
  GKLS setting, the matrix counterpart of the conditional entropic rate.

`GKLSEntropicRate` only *asserts in prose* that feeding `gklsImaginaryHamiltonian` into the QIF
mixed-state rate `entropicRateOfDensity H_I ℏ ρ = (2/ℏ)·Tr(ρ H_I)` reproduces the GKLS rate. This file
**proves** that identity (`gkls_imaginaryHamiltonian_reproduces_rate` /
`gkls_imaginaryHamiltonian_reproduces_gklsRate`), then bundles it with the synthesis: the main result
`lindblad_realizes_synthesis_entropic_clock` **depends on `misra_jacobson_entropic_synthesis`** and
exhibits the Lindblad GKLS rate as the concrete matrix face of the irreversible entropic clock — on the
*same* modular state `ρ` whose modular flow is the reversible clock.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LindbladEntropicClock

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MisraJacobsonSynthesis
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.QuantumOrigins
open Physlib.Relativity.SemiClassical.CausalDiamondThermodynamics
open Physlib.QuantumMechanics.Lindblad
open _root_.QuantumMechanics.RelationalTime
open _root_.QuantumMechanics.FiniteTarget
open scoped MState Matrix

/-! ## §A — the concrete GKLS ↔ QIF entropic-rate identity (the theorem the prose only asserted) -/

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]

/-- **The GKLS imaginary Hamiltonian reproduces the GKLS rate through the QIF mixed-state rate.** Feeding
`H_I^GKLS = (ℏ/2)·∑ⱼ Lⱼ† Lⱼ` into the QIF entropic rate `entropicRateOfDensity H_I ℏ ρ = (2/ℏ)·Tr(ρ H_I)`
returns `∑ⱼ Tr(Lⱼ† Lⱼ ρ)` — the (complex) GKLS rate. The `(2/ℏ)` and `(ℏ/2)` cancel; cyclicity of the
trace moves `ρ` to the right. This is the identity `GKLSEntropicRate` states in prose but does not prove. -/
theorem gkls_imaginaryHamiltonian_reproduces_rate
    (L : ι → Matrix d d ℂ) (ρ : MState d) (ℏ : ℝ) (hℏ : (ℏ : ℂ) ≠ 0) :
    entropicRateOfDensity (gklsImaginaryHamiltonian L ℏ) ℏ ρ.m
      = ∑ j, ((L j)ᴴ * (L j) * ρ.m).trace := by
  unfold entropicRateOfDensity gklsImaginaryHamiltonian
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc]
  have hc : (2 / (ℏ : ℂ)) * ((ℏ : ℂ) / 2) = 1 := by field_simp
  rw [hc, one_mul, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Matrix.trace_mul_comm ρ.m ((L j)ᴴ * (L j))

/-- **The real part is exactly the GKLS entropic rate.** Taking the real part of the QIF rate fed the
GKLS imaginary Hamiltonian returns `gklsEntropicRate L ρ = ∑ⱼ Tr(Lⱼ† Lⱼ ρ).re`. -/
theorem gkls_imaginaryHamiltonian_reproduces_gklsRate
    (L : ι → Matrix d d ℂ) (ρ : MState d) (ℏ : ℝ) (hℏ : (ℏ : ℂ) ≠ 0) :
    (entropicRateOfDensity (gklsImaginaryHamiltonian L ℏ) ℏ ρ.m).re = gklsEntropicRate L ρ := by
  rw [gkls_imaginaryHamiltonian_reproduces_rate L ρ ℏ hℏ, gklsEntropicRate, Complex.re_sum]

/-! ## §B — the main result: the Lindblad GKLS rate realizes the synthesis's entropic clock -/

/-- **The Lindblad GKLS rate is the matrix realization of the synthesis's irreversible entropic clock.**
This theorem **depends on `misra_jacobson_entropic_synthesis`**: from the same data — the Nagao–Nielsen
parts `H_R, H_I`, the dissipative clock `P` with jumps `L` at `ψ`, the modular state `ρ` with flow `U`,
the modular `K` and commutant `D`, the Misra spectral profile `f` at `λ`, the Jacobson diamond data — plus
a Lindblad jump family `Lmat` acting on the *same* modular state `ρ`:

* **(entropic clock, irreversible — from the synthesis)** `P.conditionalEntropicRate L ψ ≥ 0` and `= 0`
  iff frozen;
* **(Misra time operator — from the synthesis)** `i[L, T] = I` for `T = i d/dλ`;
* **(Jacobson negative temperature — from the synthesis)** `diamondTemperature ℏ κ c kB < 0`;
* **(GKLS matrix realization — new)** the Lindblad rate on `ρ` is non-negative `0 ≤ gklsEntropicRate Lmat ρ`
  (the second law), and it is reproduced by the QIF rate of the GKLS imaginary Hamiltonian
  `(entropicRateOfDensity (gklsImaginaryHamiltonian Lmat ℏ) ℏ ρ.m).re = gklsEntropicRate Lmat ρ`.

So the Lindblad GKLS rate is the concrete matrix face of the irreversible entropic clock that the
synthesis classifies — entropy-producing on the very state `ρ` whose modular flow `U` is the reversible
clock (`Sᵥₙ(U ◃ ρ) = Sᵥₙ ρ`). -/
theorem lindblad_realizes_synthesis_entropic_clock
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [FiniteDimensional ℂ H]
    (H_R : H →L[ℂ] H) (P : DissipativeConditionalClock H) {ι : Type*} [Fintype ι]
    (L : ι → (H →L[ℂ] H)) (ψ : H)
    {dM : Type*} [Fintype dM] [DecidableEq dM] (ρ : MState dM) (U : 𝐔[dM])
    {mM : Type*} [Fintype mM] (K X D : Matrix mM mM ℂ) (hK : Kᴴ = K) (hKD : K * D = D * K)
    (f : ℝ → ℂ) (lam : ℝ) (hf : DifferentiableAt ℝ f lam)
    (ℏ κ c kB ξ Δ : ℝ) (hℏ : 0 < ℏ) (hκ : 0 < κ) (hc : 0 < c) (hkB : 0 < kB)
    {ιL : Type*} [Fintype ιL] (Lmat : ιL → Matrix dM dM ℂ) (hℏc : (ℏ : ℂ) ≠ 0) :
    (0 ≤ P.conditionalEntropicRate L ψ)
      ∧ (P.conditionalEntropicRate L ψ = 0 ↔ ∀ j, L j ψ = 0)
      ∧ (Complex.I * (Physlib.QuantumMechanics.RelationalTime.spectralLiouvillian
            (Physlib.QuantumMechanics.RelationalTime.ageOperator f) lam
          - Physlib.QuantumMechanics.RelationalTime.ageOperator
            (Physlib.QuantumMechanics.RelationalTime.spectralLiouvillian f) lam) = f lam)
      ∧ (diamondTemperature ℏ κ c kB < 0)
      ∧ (0 ≤ gklsEntropicRate Lmat ρ)
      ∧ ((entropicRateOfDensity (gklsImaginaryHamiltonian Lmat ℏ) ℏ ρ.m).re
          = gklsEntropicRate Lmat ρ) := by
  obtain ⟨_, _, h3, h4, _, hMisra, _, hTneg⟩ :=
    misra_jacobson_entropic_synthesis H_R P L ψ ρ U K X D hK hKD f lam hf
      ℏ κ c kB ξ Δ hℏ hκ hc hkB
  exact ⟨h3, h4, hMisra, hTneg, gklsEntropicRate_nonneg Lmat ρ,
    gkls_imaginaryHamiltonian_reproduces_gklsRate Lmat ρ ℏ hℏc⟩

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LindbladEntropicClock

end
