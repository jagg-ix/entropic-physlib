/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.NonHermitian.Propagator
public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameModularGroup
public import Physlib.QuantumMechanics.Schrodinger.MadelungPolarDecomposition
public import Physlib.QFT.PathIntegral.FeynmanKac

/-!
# Spectral theorem dynamics bridge

This module extracts the Lean-checkable core of Paolo Facchi's *spettro e dinamica*
notes, chapters 3 and 5, in the bounded finite-dimensional setting already used by
Physlib's propagator infrastructure.

The paper-level statement is the spectral-theorem/Stone formula
`U(t) = exp(-i t A) = ∫ exp(-i t λ) dP_A(λ)` for a self-adjoint generator `A`.
Physlib does not yet contain the full unbounded projection-valued-measure functional
calculus.  What is available, and what is formalized here, is the bounded
operator-exponential specialization and the finite pure-point/eigencomponent
specialization:

* `selfAdjointSchrodingerFlow` is exactly the existing operator propagator
  `exp(t • (-i A / ℏ))`;
* it has identity at `0`, the one-parameter group law, and satisfies the operator
  Schrödinger equation;
* if `A` is self-adjoint and `ℏ ≠ 0`, every `U(t)` is unitary;
* on each spectral component/eigenline, the scalar factor is the reversible phase
  `exp(-i E t / ℏ)`, of norm `1`, and it solves the scalar Schrödinger equation;
* a finite pure-point spectrum evolves componentwise by these phases.

Thus the Facchi spectral-dynamics content is connected to the repository's existing
non-Hermitian-to-Hermitian reduction layer without duplicating the propagator or
phase equations.

The final bridge section connects this file to the rest of Physlib:

* finite Tomita/KMS modular flow via `QuantumMechanics.FiniteTarget.unitaryFlow`;
* Madelung polar form via `Schrodinger.MadelungWaveFunction`;
* Wick-rotated Feynman-Kac damping via `QFT.PathIntegral.feynman_kac_weight`.

## Reference

Paolo Facchi, *spettro e dinamica*, Chapters 3 and 5.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.NonHermitian.Propagator
open Physlib.QuantumMechanics.NonHermitian.WickRotation

namespace Physlib.QuantumMechanics.Schrodinger.SpectralDynamics

open BigOperators

variable {Hilb : Type*} [NormedAddCommGroup Hilb] [InnerProductSpace ℂ Hilb]
  [CompleteSpace Hilb] [FiniteDimensional ℂ Hilb]

/-! ## A. Bounded Stone/Schrödinger flow -/

/-- The bounded self-adjoint Schrödinger flow `U(t) = exp(-i t A / ℏ)`, implemented
by the repo's operator-level propagator.  The self-adjointness assumption is encoded in the theorems, not by the definition, matching the reusable propagator API. -/
def selfAdjointSchrodingerFlow (A : Hilb →L[ℂ] Hilb) (hbar : ℝ) (t : ℝ) :
    Hilb →L[ℂ] Hilb :=
  propagator A hbar t

/-- Facchi/Stone identity at zero time: `U(0)=1`. -/
@[simp] theorem selfAdjointSchrodingerFlow_zero (A : Hilb →L[ℂ] Hilb) (hbar : ℝ) :
    selfAdjointSchrodingerFlow A hbar 0 = 1 := by
  simpa [selfAdjointSchrodingerFlow] using propagator_zero A hbar

/-- Facchi/Stone one-parameter group law in the bounded setting:
`U(s+t)=U(s)U(t)`. -/
theorem selfAdjointSchrodingerFlow_add (A : Hilb →L[ℂ] Hilb) (hbar s t : ℝ) :
    selfAdjointSchrodingerFlow A hbar (s + t) =
      selfAdjointSchrodingerFlow A hbar s * selfAdjointSchrodingerFlow A hbar t := by
  simpa [selfAdjointSchrodingerFlow] using propagator_add A hbar s t

/-- Operator derivative form of the Schrödinger equation:
`dU/dt = (-i A/ℏ) U(t)`. -/
theorem hasDerivAt_selfAdjointSchrodingerFlow
    (A : Hilb →L[ℂ] Hilb) (hbar t : ℝ) :
    HasDerivAt (selfAdjointSchrodingerFlow A hbar)
      (schrodingerGenerator A hbar * selfAdjointSchrodingerFlow A hbar t) t := by
  exact hasDerivAt_propagator A hbar t

/-- Operator Schrödinger equation `iℏ dU/dt = A U(t)`.  This is the bounded version
of Facchi's equation `i dψ/dt = Hψ`, with explicit `ℏ`. -/
theorem selfAdjointSchrodinger_operator
    (A : Hilb →L[ℂ] Hilb) (hbar : ℝ) (hbar_ne_zero : hbar ≠ 0) (t : ℝ) :
    (Complex.I * (hbar : ℂ)) •
        (schrodingerGenerator A hbar * selfAdjointSchrodingerFlow A hbar t) =
      A * selfAdjointSchrodingerFlow A hbar t := by
  simpa [selfAdjointSchrodingerFlow] using
    nonHermitian_schrodinger_operator A hbar hbar_ne_zero t

/-- Stone-type unitarity specialization: if the bounded generator `A` is
self-adjoint and `ℏ ≠ 0`, then `exp(-i t A/ℏ)` is unitary for every real time. -/
theorem selfAdjointSchrodingerFlow_mem_unitary_forall
    (A : Hilb →L[ℂ] Hilb) (hbar : ℝ) (hbar_ne_zero : hbar ≠ 0)
    (hA : IsSelfAdjoint A) :
    ∀ t : ℝ, selfAdjointSchrodingerFlow A hbar t ∈ unitary (Hilb →L[ℂ] Hilb) := by
  have hskew : schrodingerGenerator A hbar ∈ skewAdjoint (Hilb →L[ℂ] Hilb) :=
    (schrodingerGenerator_mem_skewAdjoint_iff_isSelfAdjoint A hbar hbar_ne_zero).2 hA
  have hU : ∀ t : ℝ, propagator A hbar t ∈ unitary (Hilb →L[ℂ] Hilb) :=
    (propagator_mem_unitary_forall_iff_skewAdjoint A hbar).2 hskew
  intro t
  simpa [selfAdjointSchrodingerFlow] using hU t

/-! ## B. Scalar spectral phase on an eigencomponent -/

/-- The scalar spectral phase attached to an energy/eigenvalue `E`:
`exp(-i E t / ℏ)`.  This is the finite pure-point instance of Facchi's
`exp(-itλ)` inside the spectral integral. -/
def spectralPhase (E hbar t : ℝ) : ℂ :=
  reversiblePhase E hbar t

/-- The spectral phase is exactly the existing reversible phase from the
non-Hermitian-to-Hermitian reduction layer. -/
theorem spectralPhase_eq_reversiblePhase (E hbar t : ℝ) :
    spectralPhase E hbar t = reversiblePhase E hbar t := rfl

/-- At zero time, the spectral phase is `1`. -/
@[simp] theorem spectralPhase_zero (E hbar : ℝ) :
    spectralPhase E hbar 0 = 1 := by
  simp [spectralPhase, reversiblePhase]

/-- Scalar version of the one-parameter group law. -/
theorem spectralPhase_add (E hbar s t : ℝ) :
    spectralPhase E hbar (s + t) = spectralPhase E hbar s * spectralPhase E hbar t := by
  unfold spectralPhase reversiblePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The scalar spectral phase has unit norm. -/
theorem spectralPhase_norm (E hbar t : ℝ) :
    ‖spectralPhase E hbar t‖ = 1 := by
  simpa [spectralPhase] using norm_reversiblePhase E hbar t

/-- Multiplication by the spectral phase preserves the norm of a complex spectral
coefficient. -/
theorem spectralAmplitude_norm_preserved (E hbar t : ℝ) (c : ℂ) :
    ‖spectralPhase E hbar t * c‖ = ‖c‖ := by
  rw [norm_mul, spectralPhase_norm, one_mul]

/-- The Born weight of a scalar spectral coefficient is preserved by the unitary
spectral phase. -/
theorem spectralAmplitude_probability_preserved (E hbar t : ℝ) (c : ℂ) :
    ‖spectralPhase E hbar t * c‖ ^ 2 = ‖c‖ ^ 2 := by
  rw [spectralAmplitude_norm_preserved]

/-- Eigencomponent Schrödinger equation: the complex-time eigenfactor with
imaginary energy part set to zero solves `u' = E/(iℏ) u`. -/
theorem spectralPhase_solves_scalar_schrodinger (E hbar : ℝ) (t : ℂ) :
    HasDerivAt (evolutionFactorC E 0 hbar)
      ((E : ℂ) / (Complex.I * hbar) * evolutionFactorC E 0 hbar t) t := by
  simpa [complexEnergy_at_E_I_zero] using nonHermitian_schrodinger_eigen E 0 hbar t

/-- The scalar spectral phase is the zero-imaginary-energy specialization of the
repo's non-Hermitian eigen-evolution factor. -/
theorem spectralPhase_eq_evolutionFactor_at_H_I_zero (E hbar t : ℝ) :
    spectralPhase E hbar t = evolutionFactor E 0 hbar t := by
  simpa [spectralPhase] using (evolutionFactor_at_H_I_zero E hbar t).symm

/-! ## C. Finite pure-point spectral evolution -/

section FinitePurePoint

variable {ι : Type*}

/-- Finite pure-point spectral evolution: each spectral component `i` with
energy/eigenvalue `E i` is multiplied by the phase `exp(-i E_i t/ℏ)`.  This is the
finite diagonal form of `U(t)=∫ exp(-itλ)dP_A(λ)`. -/
def finiteSpectralEvolution (E : ι → ℝ) (hbar t : ℝ) (c : ι → ℂ) : ι → ℂ :=
  fun i => spectralPhase (E i) hbar t * c i

/-- At zero time finite spectral evolution is the identity on coefficients. -/
@[simp] theorem finiteSpectralEvolution_zero (E : ι → ℝ) (hbar : ℝ) (c : ι → ℂ) :
    finiteSpectralEvolution E hbar 0 c = c := by
  funext i
  simp [finiteSpectralEvolution]

/-- Componentwise form of the finite spectral group law. -/
theorem finiteSpectralEvolution_add_apply
    (E : ι → ℝ) (hbar s t : ℝ) (c : ι → ℂ) (i : ι) :
    finiteSpectralEvolution E hbar (s + t) c i =
      finiteSpectralEvolution E hbar s (finiteSpectralEvolution E hbar t c) i := by
  simp [finiteSpectralEvolution, spectralPhase_add, mul_assoc]

/-- Each coefficient norm is preserved by finite pure-point spectral evolution. -/
theorem finiteSpectralEvolution_component_norm
    (E : ι → ℝ) (hbar t : ℝ) (c : ι → ℂ) (i : ι) :
    ‖finiteSpectralEvolution E hbar t c i‖ = ‖c i‖ := by
  simpa [finiteSpectralEvolution] using spectralAmplitude_norm_preserved (E i) hbar t (c i)

/-- Each component Born weight is preserved by finite pure-point spectral evolution. -/
theorem finiteSpectralEvolution_component_probability
    (E : ι → ℝ) (hbar t : ℝ) (c : ι → ℂ) (i : ι) :
    ‖finiteSpectralEvolution E hbar t c i‖ ^ 2 = ‖c i‖ ^ 2 := by
  rw [finiteSpectralEvolution_component_norm]

/-- For a finite pure-point spectrum, the total Born weight of all spectral
coefficients is preserved. -/
theorem finiteSpectralEvolution_total_probability [Fintype ι]
    (E : ι → ℝ) (hbar t : ℝ) (c : ι → ℂ) :
    (∑ i, ‖finiteSpectralEvolution E hbar t c i‖ ^ 2) =
      ∑ i, ‖c i‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _hi
  rw [finiteSpectralEvolution_component_probability]

end FinitePurePoint

/-! ## D. Bridges to existing Physlib layers -/

/-- The Facchi/Schrödinger flow is the finite-dimensional modular/unitary flow
already used by the QIF/Tomita infrastructure, with generator rescaled by
`-1/ℏ`.  This avoids a second definition of one-parameter unitary flow. -/
theorem selfAdjointSchrodingerFlow_eq_unitaryFlow
    (A : Hilb →L[ℂ] Hilb) (hbar t : ℝ) :
    selfAdjointSchrodingerFlow A hbar t =
      QuantumMechanics.FiniteTarget.unitaryFlow ((-(1 : ℂ) / (hbar : ℂ)) • A) t := by
  unfold selfAdjointSchrodingerFlow propagator schrodingerGenerator
  unfold QuantumMechanics.FiniteTarget.unitaryFlow
  congr 1
  ext x
  simp only [ContinuousLinearMap.smul_apply]
  change t • ((-Complex.I / (hbar : ℂ)) • A x) =
    ((t : ℂ) * Complex.I) • ((-1 / (hbar : ℂ)) • A x)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) t ((-Complex.I / (hbar : ℂ)) • A x)]
  rw [smul_smul, smul_smul]
  congr 1
  simp
  ring

/-- The modular automorphism generated by the rescaled spectral Hamiltonian is
conjugation by the Facchi/Schrödinger flow. -/
theorem spectralFlow_modularGroup_ofGenerator_σ
    (A B : Hilb →L[ℂ] Hilb) (hbar t : ℝ) :
    (QuantumMechanics.FiniteTarget.ModularGroupData.ofGenerator
        ((-(1 : ℂ) / (hbar : ℂ)) • A)).σ t B =
      selfAdjointSchrodingerFlow A hbar t * B *
        selfAdjointSchrodingerFlow A hbar (-t) := by
  rw [QuantumMechanics.FiniteTarget.ModularGroupData.ofGenerator_σ,
    ← selfAdjointSchrodingerFlow_eq_unitaryFlow A hbar t,
    ← selfAdjointSchrodingerFlow_eq_unitaryFlow A hbar (-t)]

/-- Madelung representative for a stationary spectral component: constant amplitude
`R`, phase action `S(t)=-E t`, and Planck scale `ℏ`. -/
def spectralMadelungWaveFunction
    (R : ℝ) (hR : 0 ≤ R) (E hbar : ℝ) (hbar_pos : 0 < hbar) (t : ℝ) :
    _root_.Physlib.QuantumMechanics.Schrodinger.MadelungWaveFunction where
  amplitude := R
  amplitude_nonneg := hR
  phase := -E * t
  hbar := hbar
  hbar_pos := hbar_pos

/-- The Madelung phase `exp(iS/ℏ)` of a stationary spectral component is exactly
the spectral phase `exp(-iEt/ℏ)`. -/
theorem spectralMadelung_phaseFactor_eq_spectralPhase
    (R : ℝ) (hR : 0 ≤ R) (E hbar : ℝ) (hbar_pos : 0 < hbar) (t : ℝ) :
    Complex.exp (Complex.I *
        (((spectralMadelungWaveFunction R hR E hbar hbar_pos t).phase : ℂ) /
          ((spectralMadelungWaveFunction R hR E hbar hbar_pos t).hbar : ℂ))) =
      spectralPhase E hbar t := by
  rw [spectralPhase_eq_reversiblePhase]
  change Complex.exp (Complex.I * (((-E * t : ℝ) : ℂ) / (hbar : ℂ))) =
    reversiblePhase E hbar t
  rw [show Complex.I * (((-E * t : ℝ) : ℂ) / (hbar : ℂ)) =
      (((-E * t / hbar : ℝ) : ℂ) * Complex.I) by
        push_cast
        ring]
  exact madelung_phase_factor_eq_reversiblePhase E hbar t

/-- The Madelung norm identity specializes to norm preservation for a stationary
spectral component. -/
theorem spectralMadelung_norm_eq_amplitude
    (R : ℝ) (hR : 0 ≤ R) (E hbar : ℝ) (hbar_pos : 0 < hbar) (t : ℝ) :
    ‖(R : ℂ) * spectralPhase E hbar t‖ = R := by
  have hnorm :=
    _root_.Physlib.QuantumMechanics.Schrodinger.madelung_wf_norm
      (spectralMadelungWaveFunction R hR E hbar hbar_pos t)
  have hphase :=
    spectralMadelung_phaseFactor_eq_spectralPhase R hR E hbar hbar_pos t
  rw [← hphase]
  simpa [spectralMadelungWaveFunction] using hnorm

/-- Wick rotation of the spectral phase is the constant-potential
Feynman-Kac weight with potential `E/ℏ`. -/
theorem wickRotatedSpectralPhase_eq_feynmanKacWeight (E hbar τ : ℝ) :
    reversiblePhaseC E hbar (-Complex.I * (τ : ℂ)) =
      ((Physlib.QFT.PathIntegral.feynman_kac_weight
        (fun _ : Unit => E / hbar) τ () : ℝ) : ℂ) := by
  rw [reversiblePhase_wickRotation]
  simp [Physlib.QFT.PathIntegral.feynman_kac_weight]
  congr 1
  ring

/-- The Wick-rotated spectral/Feynman-Kac weight is also the existing entropic
damping correspondence when `S_I = ℏ · (E/ℏ) · τ`. -/
theorem spectralFeynmanKac_eq_entropic_damping
    (E hbar τ S_I : ℝ) (hbar_pos : 0 < hbar)
    (hSI : S_I = (E / hbar) * τ * hbar) :
    Real.exp (-(S_I / hbar)) =
      Physlib.QFT.PathIntegral.feynman_kac_weight (fun _ : Unit => E / hbar) τ () :=
  Physlib.QFT.PathIntegral.fk_euclidean_entropic_damping_correspondence
    (E / hbar) τ hbar hbar_pos S_I hSI

end Physlib.QuantumMechanics.Schrodinger.SpectralDynamics

end
