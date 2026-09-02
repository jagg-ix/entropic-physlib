/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap
public import Physlib.QuantumMechanics.Schrodinger.SpectralDynamics
meta import Zil

/-!
# Variational bounds for the Ipek--Caticha functional Schrödinger generator

This module gives the existing continuum-capable smeared generator a finite spectral interface and
then reuses the repository's Gibbs--Bogoliubov--Feynman carrier.  It proves two distinct statements:

* at positive inverse temperature, the Gibbs free energy is below every strictly positive normalized
  trial distribution's free energy;
* if `E₀` is a lower bound for every selected spectral value, then `E₀` is below every normalized
  spectral trial expectation -- the finite Rayleigh--Ritz bound.

The spectral interface is explicit and load-bearing: complex linearity of
`continuumSmearedSchrodingerGenerator` alone does not imply self-adjointness, diagonalizability, a
complete eigenbasis, or a lower-bounded spectrum.  No zero-temperature limit or continuum spectral
theorem is claimed here.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy

open IpekCatichaFunctionalSchrodinger

/-! ## Bounded Hilbert-space realization -/

/-- The existing smeared Ipek--Caticha generator, promoted from a bare linear map to a bounded
operator when its normal and tangential pieces are bounded operators on a Hilbert space. -/
noncomputable def boundedSmearedSchrodingerOperator {Hilb : Type*}
    [NormedAddCommGroup Hilb] [InnerProductSpace ℂ Hilb]
    (N Ni : ℝ) (Hperp Hi : Hilb →L[ℂ] Hilb) : Hilb →L[ℂ] Hilb :=
  (N : ℂ) • Hperp + (Ni : ℂ) • Hi

/-- Forgetting boundedness recovers the repository's original linear smeared generator exactly. -/
theorem boundedSmearedSchrodingerOperator_toLinearMap {Hilb : Type*}
    [NormedAddCommGroup Hilb] [InnerProductSpace ℂ Hilb]
    (N Ni : ℝ) (Hperp Hi : Hilb →L[ℂ] Hilb) :
    (boundedSmearedSchrodingerOperator N Ni Hperp Hi).toLinearMap =
      continuumSmearedSchrodingerGenerator N Ni Hperp.toLinearMap Hi.toLinearMap := by
  rfl

/-- Real lapse and shift preserve self-adjointness of the two bounded Caticha generator pieces. -/
theorem boundedSmearedSchrodingerOperator_isSelfAdjoint {Hilb : Type*}
    [NormedAddCommGroup Hilb] [InnerProductSpace ℂ Hilb]
    [CompleteSpace Hilb]
    (N Ni : ℝ) (Hperp Hi : Hilb →L[ℂ] Hilb)
    (hperp : IsSelfAdjoint Hperp) (hi : IsSelfAdjoint Hi) :
    IsSelfAdjoint (boundedSmearedSchrodingerOperator N Ni Hperp Hi) := by
  apply IsSelfAdjoint.add
  · exact IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) hperp
  · exact IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) hi

/-- **Bounded Stone evolution for the Caticha generator.**  In the finite-dimensional Hilbert
carrier already used by `SpectralDynamics`, self-adjoint normal and tangential pieces generate a
unitary one-parameter Schrödinger flow. -/
theorem boundedSmearedSchrodingerFlow_unitary {Hilb : Type*}
    [NormedAddCommGroup Hilb] [InnerProductSpace ℂ Hilb]
    [CompleteSpace Hilb] [FiniteDimensional ℂ Hilb]
    (N Ni : ℝ) (Hperp Hi : Hilb →L[ℂ] Hilb) (hbar : ℝ)
    (hperp : IsSelfAdjoint Hperp) (hi : IsSelfAdjoint Hi) (hbar_ne : hbar ≠ 0) :
    ∀ t : ℝ,
      Physlib.QuantumMechanics.Schrodinger.SpectralDynamics.selfAdjointSchrodingerFlow
          (boundedSmearedSchrodingerOperator N Ni Hperp Hi) hbar t ∈
        unitary (Hilb →L[ℂ] Hilb) :=
  Physlib.QuantumMechanics.Schrodinger.SpectralDynamics.selfAdjointSchrodingerFlow_mem_unitary_forall
      (boundedSmearedSchrodingerOperator N Ni Hperp Hi) hbar hbar_ne
      (boundedSmearedSchrodingerOperator_isSelfAdjoint N Ni Hperp Hi hperp hi)

/-- A finite family of genuine eigenmodes of the continuum Ipek--Caticha smeared generator.
The carrier records the generator data and its real spectral readout without asserting completeness. -/
structure FiniteSpectralCarrier (ι Ψ : Type*) [Fintype ι]
    [AddCommMonoid Ψ] [Module ℂ Ψ] where
  lapse : ℝ
  shift : ℝ
  normalGenerator : Ψ →ₗ[ℂ] Ψ
  tangentialGenerator : Ψ →ₗ[ℂ] Ψ
  mode : ι → Ψ
  energy : ι → ℝ
  eigenmode : ∀ i,
    continuumSmearedSchrodingerGenerator lapse shift normalGenerator tangentialGenerator (mode i) =
      (energy i : ℂ) • mode i

/-- The complete orthonormal eigenbasis supplied by the finite-dimensional spectral theorem for
the self-adjoint bounded Caticha generator. -/
noncomputable def boundedSmearedEigenvectorBasis {Hilb : Type*}
    [NormedAddCommGroup Hilb] [InnerProductSpace ℂ Hilb] [CompleteSpace Hilb]
    [FiniteDimensional ℂ Hilb]
    (n : ℕ) (hn : Module.finrank ℂ Hilb = n)
    (N Ni : ℝ) (Hperp Hi : Hilb →L[ℂ] Hilb)
    (hperp : IsSelfAdjoint Hperp) (hi : IsSelfAdjoint Hi) :
    OrthonormalBasis (Fin n) ℂ Hilb :=
  let hA : IsSelfAdjoint (boundedSmearedSchrodingerOperator N Ni Hperp Hi) :=
    boundedSmearedSchrodingerOperator_isSelfAdjoint N Ni Hperp Hi hperp hi
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA).eigenvectorBasis hn

/-- The real, multiplicity-counted Caticha energies paired with
`boundedSmearedEigenvectorBasis`. -/
noncomputable def boundedSmearedEigenvalues {Hilb : Type*}
    [NormedAddCommGroup Hilb] [InnerProductSpace ℂ Hilb] [CompleteSpace Hilb]
    [FiniteDimensional ℂ Hilb]
    (n : ℕ) (hn : Module.finrank ℂ Hilb = n)
    (N Ni : ℝ) (Hperp Hi : Hilb →L[ℂ] Hilb)
    (hperp : IsSelfAdjoint Hperp) (hi : IsSelfAdjoint Hi) : Fin n → ℝ :=
  let hA : IsSelfAdjoint (boundedSmearedSchrodingerOperator N Ni Hperp Hi) :=
    boundedSmearedSchrodingerOperator_isSelfAdjoint N Ni Hperp Hi hperp hi
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA).eigenvalues hn

/-- **Constructive finite Caticha spectral carrier.**  Self-adjoint bounded normal and tangential
generators determine the complete orthonormal spectral basis and its real eigenvalues; no external
eigenmode certificate is required. -/
noncomputable def selfAdjointFiniteSpectralCarrier {Hilb : Type*}
    [NormedAddCommGroup Hilb] [InnerProductSpace ℂ Hilb] [CompleteSpace Hilb]
    [FiniteDimensional ℂ Hilb]
    (n : ℕ) (hn : Module.finrank ℂ Hilb = n)
    (N Ni : ℝ) (Hperp Hi : Hilb →L[ℂ] Hilb)
    (hperp : IsSelfAdjoint Hperp) (hi : IsSelfAdjoint Hi) :
    FiniteSpectralCarrier (Fin n) Hilb where
  lapse := N
  shift := Ni
  normalGenerator := Hperp.toLinearMap
  tangentialGenerator := Hi.toLinearMap
  mode := boundedSmearedEigenvectorBasis n hn N Ni Hperp Hi hperp hi
  energy := boundedSmearedEigenvalues n hn N Ni Hperp Hi hperp hi
  eigenmode i := by
    rw [← boundedSmearedSchrodingerOperator_toLinearMap]
    let hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (boundedSmearedSchrodingerOperator_isSelfAdjoint N Ni Hperp Hi hperp hi)
    simpa [boundedSmearedEigenvectorBasis, boundedSmearedEigenvalues] using
      hsym.apply_eigenvectorBasis hn i

/-- The energy expectation of a probability distribution on a selected finite Caticha spectrum. -/
noncomputable def finiteSpectralTrialEnergy {ι Ψ : Type*} [Fintype ι]
    [AddCommMonoid Ψ] [Module ℂ Ψ]
    (C : FiniteSpectralCarrier ι Ψ) (p : ι → ℝ) : ℝ :=
  ∑ i, p i * C.energy i

/-- **Finite-temperature Caticha variational bound.**  Once the selected generator eigenvalues
form the energy input of a finite Gibbs system, its Gibbs free energy is below every positive,
normalized trial free energy.  This is the finite-temperature Rayleigh--Ritz/Bogoliubov bound. -/
theorem caticha_finiteTemperature_variational_bound {ι Ψ : Type*} [Fintype ι]
    [AddCommMonoid Ψ] [Module ℂ Ψ]
    (C : FiniteSpectralCarrier ι Ψ) (p : ι → ℝ) (β Z : ℝ)
    (hp : ∀ i, 0 < p i) (hβ : 0 < β) (hZ : 0 < Z)
    (hnorm : ∑ i, p i = 1)
    (hpartition : ∑ i, Real.exp (-(β * C.energy i)) = Z) :
    gibbsFreeEnergy Z β ≤ finiteTrialFreeEnergy p C.energy β :=
  finite_gibbs_variational_upper_bound p C.energy β Z hp hβ hZ hnorm hpartition

/-- **Sharp finite-temperature Caticha gap.**  The trial excess over the Gibbs value is exactly
the relative-entropy free-energy gap, rather than merely being nonnegative. -/
theorem caticha_trialFreeEnergy_gap_eq_relativeEntropy {ι Ψ : Type*} [Fintype ι]
    [AddCommMonoid Ψ] [Module ℂ Ψ]
    (C : FiniteSpectralCarrier ι Ψ) (p : ι → ℝ) (β Z : ℝ)
    (hp : ∀ i, 0 < p i) (hβ : 0 < β) (hZ : 0 < Z)
    (hnorm : ∑ i, p i = 1) :
    finiteTrialFreeEnergy p C.energy β - gibbsFreeEnergy Z β =
      freeEnergyGap p (fun i => Real.exp (-(β * C.energy i)) / Z) β :=
  trialFreeEnergy_sub_gibbs_eq_gap p C.energy β Z hp hZ hnorm hβ

/-- **Finite spectral Rayleigh--Ritz bound.**  If `E₀` is below every selected eigenvalue of the
Ipek--Caticha generator, then every normalized positive spectral trial state has expectation at
least `E₀`.  Equivalently, each trial expectation is an upper bound on the selected ground energy. -/
theorem caticha_rayleighRitz_ground_le_trialEnergy {ι Ψ : Type*} [Fintype ι]
    [AddCommMonoid Ψ] [Module ℂ Ψ]
    (C : FiniteSpectralCarrier ι Ψ) (p : ι → ℝ) (E₀ : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hnorm : ∑ i, p i = 1)
    (hground : ∀ i, E₀ ≤ C.energy i) :
    E₀ ≤ finiteSpectralTrialEnergy C p := by
  have hweighted : ∑ i, p i * E₀ ≤ ∑ i, p i * C.energy i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hground i) (hp i)
  calc
    E₀ = (∑ i, p i) * E₀ := by rw [hnorm, one_mul]
    _ = ∑ i, p i * E₀ := by rw [Finset.sum_mul]
    _ ≤ ∑ i, p i * C.energy i := hweighted
    _ = finiteSpectralTrialEnergy C p := rfl

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy

end

/- ZIL-BEGIN -/

open Zil

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy.caticha_finiteTemperature_variational_bound where
  formalizes @ "claim:the-finite-spectral-ipek-caticha-functional-generator-obeys-the-gibbs-bogoliubov-variational-bound",
  supported_by @ "paper:ipek-caticha-covariant-entropic-dynamics",
  caveat @ "claim:requires-an-explicit-finite-real-eigenspectrum-and-does-not-derive-self-adjointness-completeness-or-a-continuum-spectral-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy.boundedSmearedSchrodingerOperator_isSelfAdjoint where
  supported_by @ "lean:ContinuousLinearMap.adjoint",
  formalizes @ "claim:the-bounded-ipek-caticha-smeared-generator-is-self-adjoint-when-its-normal-and-tangential-generators-are-self-adjoint",
  caveat @ "claim:bounded-hilbert-operator-carrier-not-an-unbounded-functional-operator-domain-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy.boundedSmearedSchrodingerFlow_unitary where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy.boundedSmearedSchrodingerOperator_isSelfAdjoint",
  formalizes @ "claim:the-self-adjoint-bounded-ipek-caticha-generator-produces-unitary-schrodinger-evolution",
  requires @ "claim:the-bounded-ipek-caticha-smeared-generator-is-self-adjoint-when-its-normal-and-tangential-generators-are-self-adjoint",
  caveat @ "claim:uses-the-repositorys-bounded-finite-dimensional-stone-carrier"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy.selfAdjointFiniteSpectralCarrier where
  formalizes @ "claim:a-bounded-self-adjoint-ipek-caticha-generator-has-a-complete-orthonormal-real-eigenbasis",
  requires @ "claim:the-bounded-ipek-caticha-smeared-generator-is-self-adjoint-when-its-normal-and-tangential-generators-are-self-adjoint",
  caveat @ "claim:finite-dimensional-bounded-spectral-theorem-not-the-unbounded-continuum-functional-spectrum"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy.caticha_trialFreeEnergy_gap_eq_relativeEntropy where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap.trialFreeEnergy_sub_gibbs_eq_gap",
  formalizes @ "claim:the-caticha-finite-spectral-trial-free-energy-excess-is-the-scaled-relative-entropy",
  requires @ "claim:the-finite-spectral-ipek-caticha-functional-generator-obeys-the-gibbs-bogoliubov-variational-bound"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy.caticha_rayleighRitz_ground_le_trialEnergy where
  formalizes @ "claim:a-normalized-finite-spectral-trial-state-of-the-ipek-caticha-generator-has-energy-at-least-the-selected-ground-energy",
  supported_by @ "paper:rayleigh-ritz-variational-principle",
  caveat @ "claim:this-is-the-finite-spectral-rayleigh-ritz-inequality-not-a-proved-zero-temperature-limit-or-interacting-functional-spectrum"

zil_file_contract physlib.ipekCatichaVariationalEnergy where
  promises "The Ipek--Caticha smeared functional generator has an exact bounded Hilbert-operator realization; self-adjoint component generators yield a self-adjoint sum and unitary finite-dimensional Stone evolution.  Equipped with an explicit finite real eigenmode carrier, it obeys the finite-temperature Gibbs variational bound, has trial excess exactly equal to scaled relative entropy, and satisfies the finite spectral Rayleigh--Ritz ground-energy inequality."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaFunctionalSchrodinger.continuumSmearedSchrodingerGenerator",
    "lean:Physlib.QuantumMechanics.Schrodinger.SpectralDynamics.selfAdjointSchrodingerFlow_mem_unitary_forall",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.FiniteArakiRelativeEntropy.finite_gibbs_variational_upper_bound",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.VariationalFreeEnergyGap.trialFreeEnergy_sub_gibbs_eq_gap"]
  forbids_substitutes ["self-adjointness or spectral completeness inferred from complex linearity alone",
    "a continuum or zero-temperature Rayleigh--Ritz theorem without analytic domain and convergence data"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy.boundedSmearedSchrodingerOperator_isSelfAdjoint,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy.boundedSmearedSchrodingerFlow_unitary,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy.selfAdjointFiniteSpectralCarrier,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy.caticha_finiteTemperature_variational_bound,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy.caticha_trialFreeEnergy_gap_eq_relativeEntropy,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaVariationalEnergy.caticha_rayleighRitz_ground_le_trialEnergy]

/- ZIL-END -/
