/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.MisraJacobsonSynthesis
public import Physlib.QuantumMechanics.Lindblad.GKLSEntropicRate
public import Physlib.QuantumMechanics.FiniteTarget.QIFMasterEquationDerivations
meta import Zil

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
open Physlib.QuantumMechanics.RelationalTime
open _root_.QuantumMechanics.FiniteTarget
open scoped MState Matrix


variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]

/-- **The GKLS imaginary Hamiltonian reproduces the GKLS rate through the QIF mixed-state rate.** Feeding
`H_I^GKLS = (ℏ/2)·∑ⱼ Lⱼ† Lⱼ` into the QIF entropic rate `entropicRateOfDensity H_I ℏ ρ = (2/ℏ)·Tr(ρ H_I)`
returns `∑ⱼ Tr(Lⱼ† Lⱼ ρ)` — the (complex) GKLS rate. The `(2/ℏ)` and `(ℏ/2)` cancel; cyclicity of the
trace moves `ρ` to the right. This is the identity `GKLSEntropicRate` states in prose but does not prove. -/
lemma gkls_imaginaryHamiltonian_reproduces_rate
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
lemma gkls_imaginaryHamiltonian_reproduces_gklsRate
    (L : ι → Matrix d d ℂ) (ρ : MState d) (ℏ : ℝ) (hℏ : (ℏ : ℂ) ≠ 0) :
    (entropicRateOfDensity (gklsImaginaryHamiltonian L ℏ) ℏ ρ.m).re = gklsEntropicRate L ρ := by
  rw [gkls_imaginaryHamiltonian_reproduces_rate L ρ ℏ hℏ, gklsEntropicRate, Complex.re_sum]


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
lemma lindblad_realizes_synthesis_entropic_clock
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

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LindbladEntropicClock.gkls_imaginaryHamiltonian_reproduces_rate where
  supported_by @ "lean:HermitianMat.trace_smul",
  formalizes @ "claim:the-qif-entropic-rate-of-density-driven-by-the-gkls-imaginary-hamiltonian-equals-the-sum-over-jumps-of-the-trace-of-l-dagger-l-rho-the-gkls-dissipation-rate"

zil attach Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LindbladEntropicClock.gkls_imaginaryHamiltonian_reproduces_gklsRate where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LindbladEntropicClock.gkls_imaginaryHamiltonian_reproduces_rate",
  supported_by @ "lean:misra_jacobson_entropic_synthesis",
  formalizes @ "claim:the-real-part-of-the-qif-entropic-rate-of-the-gkls-imaginary-hamiltonian-equals-the-gkls-entropic-rate-the-sum-of-real-trace-of-l-dagger-l-rho",
  requires @ "claim:the-qif-entropic-rate-of-density-driven-by-the-gkls-imaginary-hamiltonian-equals-the-sum-over-jumps-of-the-trace-of-l-dagger-l-rho-the-gkls-dissipation-rate"

zil attach Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LindbladEntropicClock.lindblad_realizes_synthesis_entropic_clock where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LindbladEntropicClock.gkls_imaginaryHamiltonian_reproduces_gklsRate",
  supported_by @ "lean:misra_jacobson_entropic_synthesis",
  formalizes @ "claim:the-lindblad-gkls-rate-is-the-concrete-matrix-realization-of-the-irreversible-entropic-clock-of-the-misra-jacobson-synthesis-on-the-same-modular-state-the-conditional-rate-is-non-negative-the-second-law-frozen-iff-no-jumps-the-misra-i-l-t-equals-i-time-operator-holds-the-diamond-temperature-is-negative-and-the-gkls-rate-is-non-negative-reproduced-by-the-qif-rate-of-the-gkls-imaginary-hamiltonian",
  requires @ "claim:the-real-part-of-the-qif-entropic-rate-of-the-gkls-imaginary-hamiltonian-equals-the-gkls-entropic-rate-the-sum-of-real-trace-of-l-dagger-l-rho"

zil_file_contract physlib.lindbladEntropicClock where
  promises "The GKLS Lindblad rate is the concrete matrix realization of the irreversible entropic clock that the Misra-Jacobson causal-diamond synthesis classifies abstractly. The QIF entropic rate driven by the GKLS imaginary Hamiltonian equals the sum over jumps of Tr(L-dagger L rho) (gkls_imaginaryHamiltonian_reproduces_rate), whose real part is the GKLS entropic rate (gkls_imaginaryHamiltonian_reproduces_gklsRate). The capstone assembles, on the same modular state, the synthesis's conditional entropic rate being non-negative (the second law) and zero iff frozen, the Misra i[L,T]=I time operator, the negative diamond temperature, and the new GKLS matrix face: the Lindblad rate is non-negative and reproduced by the QIF rate of the GKLS imaginary Hamiltonian (lindblad_realizes_synthesis_entropic_clock) -- the entropy-producing clock on the very state whose modular flow is the reversible clock."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.Lindblad.GKLSEntropicRate.gklsEntropicRate",
    "lean:Physlib.QuantumMechanics.Lindblad.GKLSEntropicRate.gklsImaginaryHamiltonian"]
  forbids_substitutes ["the Misra-Jacobson synthesis theorem itself and the modular / age-operator / diamond-temperature carriers it bundles, which are the cited inputs the capstone depends on",
    "any claim that this fixes a preferred physical clock, only the identity of the GKLS rate with the synthesis's entropic rate is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LindbladEntropicClock.gkls_imaginaryHamiltonian_reproduces_rate,
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LindbladEntropicClock.gkls_imaginaryHamiltonian_reproduces_gklsRate,
    Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LindbladEntropicClock.lindblad_realizes_synthesis_entropic_clock]

/- ZIL-END -/
