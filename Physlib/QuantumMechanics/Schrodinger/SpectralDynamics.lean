/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.NonHermitian.Propagator
public import Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic
public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameModularGroup
public import Physlib.QuantumMechanics.Schrodinger.MadelungPolarDecomposition
public import Physlib.QFT.PathIntegral.FeynmanKac
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

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

open BigOperators MeasureTheory
open ClassicalMechanics

variable {Hilb : Type*} [NormedAddCommGroup Hilb] [InnerProductSpace ℂ Hilb]
  [CompleteSpace Hilb] [FiniteDimensional ℂ Hilb]

/-! ## A. Bounded Stone/Schrödinger flow -/

/-- The bounded self-adjoint Schrödinger flow `U(t) = exp(-i t A / ℏ)`, implemented
by the repo's operator-level propagator.  The self-adjointness assumption is carried
by the theorems, not by the definition, matching the reusable propagator API. -/
def selfAdjointSchrodingerFlow (A : Hilb →L[ℂ] Hilb) (hbar : ℝ) (t : ℝ) :
    Hilb →L[ℂ] Hilb :=
  propagator A hbar t

/-- Facchi/Stone identity at zero time: `U(0)=1`. -/
@[simp] lemma selfAdjointSchrodingerFlow_zero (A : Hilb →L[ℂ] Hilb) (hbar : ℝ) :
    selfAdjointSchrodingerFlow A hbar 0 = 1 := by
  simpa [selfAdjointSchrodingerFlow] using propagator_zero A hbar

/-- Facchi/Stone one-parameter group law in the bounded setting:
`U(s+t)=U(s)U(t)`. -/
lemma selfAdjointSchrodingerFlow_add (A : Hilb →L[ℂ] Hilb) (hbar s t : ℝ) :
    selfAdjointSchrodingerFlow A hbar (s + t) =
      selfAdjointSchrodingerFlow A hbar s * selfAdjointSchrodingerFlow A hbar t := by
  simpa [selfAdjointSchrodingerFlow] using propagator_add A hbar s t

/-- Operator derivative form of the Schrödinger equation:
`dU/dt = (-i A/ℏ) U(t)`. -/
lemma hasDerivAt_selfAdjointSchrodingerFlow
    (A : Hilb →L[ℂ] Hilb) (hbar t : ℝ) :
    HasDerivAt (selfAdjointSchrodingerFlow A hbar)
      (schrodingerGenerator A hbar * selfAdjointSchrodingerFlow A hbar t) t := by
  exact hasDerivAt_propagator A hbar t

/-- Operator Schrödinger equation `iℏ dU/dt = A U(t)`.  This is the bounded version
of Facchi's equation `i dψ/dt = Hψ`, with explicit `ℏ`. -/
lemma selfAdjointSchrodinger_operator
    (A : Hilb →L[ℂ] Hilb) (hbar : ℝ) (hbar_ne_zero : hbar ≠ 0) (t : ℝ) :
    (Complex.I * (hbar : ℂ)) •
        (schrodingerGenerator A hbar * selfAdjointSchrodingerFlow A hbar t) =
      A * selfAdjointSchrodingerFlow A hbar t := by
  simpa [selfAdjointSchrodingerFlow] using
    nonHermitian_schrodinger_operator A hbar hbar_ne_zero t

/-- Stone-type unitarity specialization: if the bounded generator `A` is
self-adjoint and `ℏ ≠ 0`, then `exp(-i t A/ℏ)` is unitary for every real time. -/
lemma selfAdjointSchrodingerFlow_mem_unitary_forall
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
lemma spectralPhase_eq_reversiblePhase (E hbar t : ℝ) :
    spectralPhase E hbar t = reversiblePhase E hbar t := rfl

/-- At zero time, the spectral phase is `1`. -/
@[simp] lemma spectralPhase_zero (E hbar : ℝ) :
    spectralPhase E hbar 0 = 1 := by
  simp [spectralPhase, reversiblePhase]

/-- Scalar version of the one-parameter group law. -/
lemma spectralPhase_add (E hbar s t : ℝ) :
    spectralPhase E hbar (s + t) = spectralPhase E hbar s * spectralPhase E hbar t := by
  unfold spectralPhase reversiblePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The scalar spectral phase has unit norm. -/
lemma spectralPhase_norm (E hbar t : ℝ) :
    ‖spectralPhase E hbar t‖ = 1 := by
  simpa [spectralPhase] using norm_reversiblePhase E hbar t

/-- Multiplication by the spectral phase preserves the norm of a complex spectral
coefficient. -/
lemma spectralAmplitude_norm_preserved (E hbar t : ℝ) (c : ℂ) :
    ‖spectralPhase E hbar t * c‖ = ‖c‖ := by
  rw [norm_mul, spectralPhase_norm, one_mul]

/-- The Born weight of a scalar spectral coefficient is preserved by the unitary
spectral phase. -/
lemma spectralAmplitude_probability_preserved (E hbar t : ℝ) (c : ℂ) :
    ‖spectralPhase E hbar t * c‖ ^ 2 = ‖c‖ ^ 2 := by
  rw [spectralAmplitude_norm_preserved]

/-- Eigencomponent Schrödinger equation: the complex-time eigenfactor with
imaginary energy part set to zero solves `u' = E/(iℏ) u`. -/
lemma spectralPhase_solves_scalar_schrodinger (E hbar : ℝ) (t : ℂ) :
    HasDerivAt (evolutionFactorC E 0 hbar)
      ((E : ℂ) / (Complex.I * hbar) * evolutionFactorC E 0 hbar t) t := by
  simpa [complexEnergy_at_E_I_zero] using nonHermitian_schrodinger_eigen E 0 hbar t

/-- Real-time derivative form of the scalar spectral Schrödinger equation. -/
lemma hasDerivAt_spectralPhase (E hbar t : ℝ) :
    HasDerivAt (spectralPhase E hbar)
      ((E : ℂ) / (Complex.I * hbar) * spectralPhase E hbar t) t := by
  have ht : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have harg : HasDerivAt
      (fun s : ℝ => -Complex.I * (((E / hbar : ℝ) : ℂ)) * (s : ℂ))
      (-Complex.I * (((E / hbar : ℝ) : ℂ))) t := by
    simpa using ht.const_mul (-Complex.I * (((E / hbar : ℝ) : ℂ)))
  have hcoeff :
      -Complex.I * (((E / hbar : ℝ) : ℂ)) = (E : ℂ) / (Complex.I * hbar) := by
    simpa [complexEnergy] using schrodingerCoeff_eq E 0 hbar
  convert harg.cexp using 1
  · rfl
  · rw [hcoeff]
    unfold spectralPhase reversiblePhase
    rw [hcoeff]
    rw [mul_comm]

/-- The scalar spectral phase is the zero-imaginary-energy specialization of the
repo's non-Hermitian eigen-evolution factor. -/
lemma spectralPhase_eq_evolutionFactor_at_H_I_zero (E hbar t : ℝ) :
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

/-- The finite pure-point spectral projector associated to a Borel set of
energies, written on coefficient functions.  It keeps exactly those components
whose energy lies in `B`. -/
noncomputable def finiteSpectralProjector (E : ι → ℝ) (B : Set ℝ) (c : ι → ℂ) : ι → ℂ := by
  classical
  exact fun i => if E i ∈ B then c i else 0

/-- The finite pure-point spectral projector as a continuous linear operator on
coefficient functions. -/
noncomputable def finiteSpectralProjectorCLM [Fintype ι] (E : ι → ℝ) (B : Set ℝ) :
    (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := finiteSpectralProjector E B
      map_add' := by
        intro c d
        funext i
        by_cases hB : E i ∈ B <;> simp [finiteSpectralProjector, hB]
      map_smul' := by
        intro a c
        funext i
        by_cases hB : E i ∈ B <;> simp [finiteSpectralProjector, hB] }

/-- Applying the finite spectral projector operator is the coefficient-level
spectral projection. -/
@[simp] lemma finiteSpectralProjectorCLM_apply [Fintype ι]
    (E : ι → ℝ) (B : Set ℝ) (c : ι → ℂ) :
    finiteSpectralProjectorCLM E B c = finiteSpectralProjector E B c :=
  rfl

/-- The empty spectral projector is zero. -/
@[simp] lemma finiteSpectralProjector_empty (E : ι → ℝ) (c : ι → ℂ) :
    finiteSpectralProjector E ∅ c = 0 := by
  funext i
  simp [finiteSpectralProjector]

/-- The full spectral projector is the identity. -/
@[simp] lemma finiteSpectralProjector_univ (E : ι → ℝ) (c : ι → ℂ) :
    finiteSpectralProjector E Set.univ c = c := by
  funext i
  simp [finiteSpectralProjector]

/-- The empty finite spectral projector operator is zero. -/
@[simp] lemma finiteSpectralProjectorCLM_empty [Fintype ι] (E : ι → ℝ) :
    finiteSpectralProjectorCLM E ∅ = 0 := by
  ext c i
  simp

/-- The full finite spectral projector operator is the identity. -/
@[simp] lemma finiteSpectralProjectorCLM_univ [Fintype ι] (E : ι → ℝ) :
    finiteSpectralProjectorCLM E Set.univ = 1 := by
  ext c i
  simp

/-- Applying two finite spectral projectors is the projector onto the
intersection of their energy sets. -/
lemma finiteSpectralProjector_comp (E : ι → ℝ) (B C : Set ℝ) (c : ι → ℂ) :
    finiteSpectralProjector E B (finiteSpectralProjector E C c) =
      finiteSpectralProjector E (B ∩ C) c := by
  funext i
  by_cases hB : E i ∈ B <;> by_cases hC : E i ∈ C <;>
    simp [finiteSpectralProjector, hB, hC]

/-- Finite spectral projectors are idempotent. -/
lemma finiteSpectralProjector_idempotent (E : ι → ℝ) (B : Set ℝ) (c : ι → ℂ) :
    finiteSpectralProjector E B (finiteSpectralProjector E B c) =
      finiteSpectralProjector E B c := by
  rw [finiteSpectralProjector_comp]
  simp

/-- Finite spectral projector operators multiply by intersecting energy sets. -/
lemma finiteSpectralProjectorCLM_comp [Fintype ι]
    (E : ι → ℝ) (B C : Set ℝ) :
    finiteSpectralProjectorCLM E B ∘L finiteSpectralProjectorCLM E C =
      finiteSpectralProjectorCLM E (B ∩ C) := by
  ext c i
  simp [finiteSpectralProjector_comp]

/-- Finite spectral projector operators are idempotent. -/
lemma finiteSpectralProjectorCLM_idempotent [Fintype ι]
    (E : ι → ℝ) (B : Set ℝ) :
    finiteSpectralProjectorCLM E B ∘L finiteSpectralProjectorCLM E B =
      finiteSpectralProjectorCLM E B := by
  rw [finiteSpectralProjectorCLM_comp]
  simp

/-- Projectors for disjoint energy sets have zero composite. -/
lemma finiteSpectralProjector_comp_of_disjoint (E : ι → ℝ) {B C : Set ℝ}
    (hBC : Disjoint B C) (c : ι → ℂ) :
    finiteSpectralProjector E B (finiteSpectralProjector E C c) = 0 := by
  funext i
  by_cases hB : E i ∈ B
  · by_cases hC : E i ∈ C
    · exact (hBC.le_bot ⟨hB, hC⟩).elim
    · simp [finiteSpectralProjector, hB, hC]
  · simp [finiteSpectralProjector, hB]

/-- Disjoint finite spectral projector operators have zero composite. -/
lemma finiteSpectralProjectorCLM_comp_of_disjoint [Fintype ι]
    (E : ι → ℝ) {B C : Set ℝ} (hBC : Disjoint B C) :
    finiteSpectralProjectorCLM E B ∘L finiteSpectralProjectorCLM E C = 0 := by
  ext c i
  simpa using congrFun (finiteSpectralProjector_comp_of_disjoint E hBC c) i

/-- A spectral projector commutes with finite pure-point Schrödinger evolution. -/
lemma finiteSpectralProjector_evolution_commute
    (E : ι → ℝ) (B : Set ℝ) (hbar t : ℝ) (c : ι → ℂ) :
    finiteSpectralProjector E B (finiteSpectralEvolution E hbar t c) =
      finiteSpectralEvolution E hbar t (finiteSpectralProjector E B c) := by
  funext i
  by_cases hB : E i ∈ B <;> simp [finiteSpectralProjector, finiteSpectralEvolution, hB]

/-- Finite Stone/SNAG spectral representation: the componentwise unitary
evolution is the finite sum of spectral phases times the finite energy
projectors.  The sum runs over the image of `E`, so degenerate eigenspaces are
grouped by their common energy value. -/
lemma finiteSpectralEvolution_eq_projector_sum [Fintype ι]
    (E : ι → ℝ) (hbar t : ℝ) (c : ι → ℂ) :
    (∑ e ∈ Finset.univ.image E,
        spectralPhase e hbar t • finiteSpectralProjectorCLM E {e}) c =
      finiteSpectralEvolution E hbar t c := by
  classical
  funext i
  rw [sum_apply]
  simp [finiteSpectralProjectorCLM, finiteSpectralProjector, finiteSpectralEvolution]

/-- A finite spectral projector over a disjoint union is the sum of the two
projectors. -/
lemma finiteSpectralProjector_union_of_disjoint (E : ι → ℝ) {B C : Set ℝ}
    (hBC : Disjoint B C) (c : ι → ℂ) :
    finiteSpectralProjector E (B ∪ C) c =
      finiteSpectralProjector E B c + finiteSpectralProjector E C c := by
  funext i
  by_cases hB : E i ∈ B
  · have hC : ¬ E i ∈ C := fun hC => (hBC.le_bot ⟨hB, hC⟩).elim
    simp [finiteSpectralProjector, hB, hC]
  · by_cases hC : E i ∈ C <;> simp [finiteSpectralProjector, hB, hC]

/-- Operator form of finite additivity for disjoint energy projectors. -/
lemma finiteSpectralProjectorCLM_union_of_disjoint [Fintype ι]
    (E : ι → ℝ) {B C : Set ℝ} (hBC : Disjoint B C) :
    finiteSpectralProjectorCLM E (B ∪ C) =
      finiteSpectralProjectorCLM E B + finiteSpectralProjectorCLM E C := by
  ext c i
  simp [finiteSpectralProjector_union_of_disjoint E hBC c]

/-- The diagonal finite spectral measure of a coefficient vector, evaluated on
an energy set.  It is the finite pure-point measure
`μ_c(B) = Σ_{E_i ∈ B} |c_i|²`. -/
noncomputable def finiteSpectralDiagonalMeasure [Fintype ι]
    (E : ι → ℝ) (c : ι → ℂ) (B : Set ℝ) : ℝ := by
  classical
  exact ∑ i, if E i ∈ B then ‖c i‖ ^ 2 else 0

/-- The finite atomic spectral measure associated to a pure-point coefficient
vector.  It is the positive measure
`μ_c = Σ_i |c_i|² δ_{E_i}` on the real energy axis. -/
noncomputable def finiteSpectralAtomicMeasure [Fintype ι]
    (E : ι → ℝ) (c : ι → ℂ) : Measure ℝ :=
  ∑ i : ι, (ENNReal.ofReal (‖c i‖ ^ 2)) • Measure.dirac (E i)

/-- Evaluation of the finite atomic spectral measure on a measurable energy set. -/
lemma finiteSpectralAtomicMeasure_apply [Fintype ι]
    (E : ι → ℝ) (c : ι → ℂ) (B : Set ℝ) (hB : MeasurableSet B) :
    finiteSpectralAtomicMeasure E c B =
      ∑ i : ι, ENNReal.ofReal (‖c i‖ ^ 2) * B.indicator 1 (E i) := by
  classical
  simp [finiteSpectralAtomicMeasure, hB]

/-- On measurable sets, the real-valued diagonal spectral set function is the
real part of the finite atomic spectral measure. -/
lemma finiteSpectralAtomicMeasure_toReal_apply [Fintype ι]
    (E : ι → ℝ) (c : ι → ℂ) (B : Set ℝ) (hB : MeasurableSet B) :
    (finiteSpectralAtomicMeasure E c B).toReal =
      finiteSpectralDiagonalMeasure E c B := by
  classical
  rw [finiteSpectralAtomicMeasure_apply E c B hB]
  rw [ENNReal.toReal_sum]
  · unfold finiteSpectralDiagonalMeasure
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases h : E i ∈ B
    · simp [h]
    · simp [h]
  · intro i _hi
    by_cases h : E i ∈ B <;> simp [h]

/-- The total mass of the finite atomic spectral measure is the total Born
weight of the coefficient vector. -/
lemma finiteSpectralAtomicMeasure_univ [Fintype ι]
    (E : ι → ℝ) (c : ι → ℂ) :
    finiteSpectralAtomicMeasure E c Set.univ =
      ENNReal.ofReal (∑ i, ‖c i‖ ^ 2) := by
  classical
  rw [finiteSpectralAtomicMeasure_apply E c Set.univ MeasurableSet.univ]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · simp
  · intro i _hi
    exact sq_nonneg ‖c i‖

/-- Integrating against the finite atomic spectral measure is the weighted finite
sum over eigenvalues. -/
lemma finiteSpectralAtomicMeasure_integral [Fintype ι]
    (E : ι → ℝ) (c : ι → ℂ) (f : ℝ → ℂ) :
    ∫ x : ℝ, f x ∂finiteSpectralAtomicMeasure E c =
      ∑ i : ι, (ENNReal.ofReal (‖c i‖ ^ 2)).toReal • f (E i) := by
  classical
  rw [finiteSpectralAtomicMeasure]
  rw [integral_finsetSum_measure]
  · simp
  · intro i _hi
    exact (integrable_dirac (a := E i) (f := f) (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- The spectral-phase integral over the finite atomic spectral measure is the
finite pure-point Fourier sum.  This is the concrete finite-dimensional diagonal
instance of the Stone/SNAG spectral formula. -/
lemma finiteSpectralAtomicMeasure_integral_spectralPhase [Fintype ι]
    (E : ι → ℝ) (c : ι → ℂ) (hbar t : ℝ) :
    ∫ x : ℝ, spectralPhase x hbar t ∂finiteSpectralAtomicMeasure E c =
      ∑ i : ι, spectralPhase (E i) hbar t * ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
  rw [finiteSpectralAtomicMeasure_integral]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [ENNReal.toReal_ofReal (sq_nonneg ‖c i‖)]
  simp [mul_comm]

/-- The empty set has zero finite diagonal spectral measure. -/
@[simp] lemma finiteSpectralDiagonalMeasure_empty [Fintype ι]
    (E : ι → ℝ) (c : ι → ℂ) :
    finiteSpectralDiagonalMeasure E c ∅ = 0 := by
  simp [finiteSpectralDiagonalMeasure]

/-- The finite diagonal spectral measure is non-negative on every set. -/
lemma finiteSpectralDiagonalMeasure_nonneg [Fintype ι]
    (E : ι → ℝ) (c : ι → ℂ) (B : Set ℝ) :
    0 ≤ finiteSpectralDiagonalMeasure E c B := by
  unfold finiteSpectralDiagonalMeasure
  exact Finset.sum_nonneg fun i _hi => by
    by_cases hB : E i ∈ B <;> simp [hB]

/-- The total mass of the finite diagonal spectral measure is the total Born
weight of the coefficient vector. -/
@[simp] lemma finiteSpectralDiagonalMeasure_univ [Fintype ι]
    (E : ι → ℝ) (c : ι → ℂ) :
    finiteSpectralDiagonalMeasure E c Set.univ = ∑ i, ‖c i‖ ^ 2 := by
  simp [finiteSpectralDiagonalMeasure]

/-- The finite diagonal spectral measure is additive on disjoint unions. -/
lemma finiteSpectralDiagonalMeasure_union_of_disjoint [Fintype ι]
    (E : ι → ℝ) (c : ι → ℂ) {B C : Set ℝ} (hBC : Disjoint B C) :
    finiteSpectralDiagonalMeasure E c (B ∪ C) =
      finiteSpectralDiagonalMeasure E c B + finiteSpectralDiagonalMeasure E c C := by
  classical
  unfold finiteSpectralDiagonalMeasure
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hB : E i ∈ B
  · have hC : ¬ E i ∈ C := fun hC => (hBC.le_bot ⟨hB, hC⟩).elim
    simp [hB, hC]
  · by_cases hC : E i ∈ C <;> simp [hB, hC]

/-- Projecting onto an energy set changes the total Born weight to the diagonal
spectral measure of that set. -/
lemma finiteSpectralProjector_total_probability_eq_diagonalMeasure [Fintype ι]
    (E : ι → ℝ) (B : Set ℝ) (c : ι → ℂ) :
    finiteSpectralDiagonalMeasure E (finiteSpectralProjector E B c) Set.univ =
      finiteSpectralDiagonalMeasure E c B := by
  classical
  unfold finiteSpectralDiagonalMeasure finiteSpectralProjector
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hB : E i ∈ B <;> simp [hB]

/-- Diagonal matrix element of the finite spectral evolution as a finite
Fourier transform of the pure-point spectral weights. -/
lemma finiteSpectralAutocorrelation_eq_fourier_sum [Fintype ι]
    (E : ι → ℝ) (hbar t : ℝ) (c : ι → ℂ) :
    (∑ i, (starRingEnd ℂ) (c i) * finiteSpectralEvolution E hbar t c i) =
      ∑ i, spectralPhase (E i) hbar t * ((starRingEnd ℂ) (c i) * c i) := by
  apply Finset.sum_congr rfl
  intro i _hi
  simp [finiteSpectralEvolution]
  ring

/-- At zero time finite spectral evolution is the identity on coefficients. -/
@[simp] lemma finiteSpectralEvolution_zero (E : ι → ℝ) (hbar : ℝ) (c : ι → ℂ) :
    finiteSpectralEvolution E hbar 0 c = c := by
  funext i
  simp [finiteSpectralEvolution]

/-- Componentwise form of the finite spectral group law. -/
lemma finiteSpectralEvolution_add_apply
    (E : ι → ℝ) (hbar s t : ℝ) (c : ι → ℂ) (i : ι) :
    finiteSpectralEvolution E hbar (s + t) c i =
      finiteSpectralEvolution E hbar s (finiteSpectralEvolution E hbar t c) i := by
  simp [finiteSpectralEvolution, spectralPhase_add, mul_assoc]

/-- Each coefficient norm is preserved by finite pure-point spectral evolution. -/
lemma finiteSpectralEvolution_component_norm
    (E : ι → ℝ) (hbar t : ℝ) (c : ι → ℂ) (i : ι) :
    ‖finiteSpectralEvolution E hbar t c i‖ = ‖c i‖ := by
  simpa [finiteSpectralEvolution] using spectralAmplitude_norm_preserved (E i) hbar t (c i)

/-- Each component Born weight is preserved by finite pure-point spectral evolution. -/
lemma finiteSpectralEvolution_component_probability
    (E : ι → ℝ) (hbar t : ℝ) (c : ι → ℂ) (i : ι) :
    ‖finiteSpectralEvolution E hbar t c i‖ ^ 2 = ‖c i‖ ^ 2 := by
  rw [finiteSpectralEvolution_component_norm]

/-- For a finite pure-point spectrum, the total Born weight of all spectral
coefficients is preserved. -/
lemma finiteSpectralEvolution_total_probability [Fintype ι]
    (E : ι → ℝ) (hbar t : ℝ) (c : ι → ℂ) :
    (∑ i, ‖finiteSpectralEvolution E hbar t c i‖ ^ 2) =
      ∑ i, ‖c i‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _hi
  rw [finiteSpectralEvolution_component_probability]

/-- Finite pure-point evolution preserves every diagonal spectral measure. -/
lemma finiteSpectralDiagonalMeasure_evolution_invariant [Fintype ι]
    (E : ι → ℝ) (hbar t : ℝ) (c : ι → ℂ) (B : Set ℝ) :
    finiteSpectralDiagonalMeasure E (finiteSpectralEvolution E hbar t c) B =
      finiteSpectralDiagonalMeasure E c B := by
  classical
  unfold finiteSpectralDiagonalMeasure
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hB : E i ∈ B <;> simp [hB, finiteSpectralEvolution_component_probability]

end FinitePurePoint

/-! ## D. Bridges to existing Physlib layers -/

/-- The Facchi/Schrödinger flow is the finite-dimensional modular/unitary flow
already used by the QIF/Tomita infrastructure, with generator rescaled by
`-1/ℏ`.  This avoids a second definition of one-parameter unitary flow. -/
lemma selfAdjointSchrodingerFlow_eq_unitaryFlow
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
lemma spectralFlow_modularGroup_ofGenerator_σ
    (A B : Hilb →L[ℂ] Hilb) (hbar t : ℝ) :
    (QuantumMechanics.FiniteTarget.ModularGroupData.ofGenerator
        ((-(1 : ℂ) / (hbar : ℂ)) • A)).σ t B =
      selfAdjointSchrodingerFlow A hbar t * B *
        selfAdjointSchrodingerFlow A hbar (-t) := by
  rw [QuantumMechanics.FiniteTarget.ModularGroupData.ofGenerator_σ,
    ← selfAdjointSchrodingerFlow_eq_unitaryFlow A hbar t,
    ← selfAdjointSchrodingerFlow_eq_unitaryFlow A hbar (-t)]

/-- Madelung carrier for a stationary spectral component: constant amplitude
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
lemma spectralMadelung_phaseFactor_eq_spectralPhase
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
lemma spectralMadelung_norm_eq_amplitude
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
lemma wickRotatedSpectralPhase_eq_feynmanKacWeight (E hbar τ : ℝ) :
    reversiblePhaseC E hbar (-Complex.I * (τ : ℂ)) =
      ((Physlib.QFT.PathIntegral.feynman_kac_weight
        (fun _ : Unit => E / hbar) τ () : ℝ) : ℂ) := by
  rw [reversiblePhase_wickRotation]
  simp [Physlib.QFT.PathIntegral.feynman_kac_weight]
  congr 1
  ring

/-- The Wick-rotated spectral/Feynman-Kac weight is also the existing entropic
damping correspondence when `S_I = ℏ · (E/ℏ) · τ`. -/
lemma spectralFeynmanKac_eq_entropic_damping
    (E hbar τ S_I : ℝ) (hbar_pos : 0 < hbar)
    (hSI : S_I = (E / hbar) * τ * hbar) :
    Real.exp (-(S_I / hbar)) =
      Physlib.QFT.PathIntegral.feynman_kac_weight (fun _ : Unit => E / hbar) τ () :=
  Physlib.QFT.PathIntegral.fk_euclidean_entropic_damping_correspondence
    (E / hbar) τ hbar hbar_pos S_I hSI

/-! ## E. Finite random-process spectra and oscillator filters -/

/-! ## E.1. Finite spectral representation of covariance -/

/-- The discrete spectral character `exp(i omega k)` used in the finite
Fourier representation of a stationary covariance sequence. -/
def spectralCharacter (omega : ℝ) (k : ℤ) : ℂ :=
  Complex.exp (Complex.I * (omega : ℂ) * (k : ℂ))

/-- At zero lag the spectral character is `1`. -/
@[simp] lemma spectralCharacter_zero_lag (omega : ℝ) :
    spectralCharacter omega 0 = 1 := by
  simp [spectralCharacter]

/-- The finite pure-point covariance associated to spectral frequencies `freq`
and real spectral weights `power`:

`C[k] = sum_j power_j * exp(i freq_j k)`.

This is the finite atomic version of the discrete Wiener-Khinchin inverse
formula. -/
def finiteSpectralCovariance {idx : Type*} [Fintype idx]
    (freq : idx → ℝ) (power : idx → ℝ) (k : ℤ) : ℂ :=
  ∑ j : idx, (power j : ℂ) * spectralCharacter (freq j) k

/-- At zero lag, finite spectral covariance is total spectral power. -/
@[simp] lemma finiteSpectralCovariance_zero {idx : Type*} [Fintype idx]
    (freq : idx → ℝ) (power : idx → ℝ) :
    finiteSpectralCovariance freq power 0 = ((∑ j : idx, power j) : ℂ) := by
  simp [finiteSpectralCovariance]

/-- Finite spectral covariance is additive in the spectral power weights. -/
lemma finiteSpectralCovariance_add_power {idx : Type*} [Fintype idx]
    (freq : idx → ℝ) (p q : idx → ℝ) (k : ℤ) :
    finiteSpectralCovariance freq (fun j => p j + q j) k =
      finiteSpectralCovariance freq p k + finiteSpectralCovariance freq q k := by
  simp [finiteSpectralCovariance, add_mul, Finset.sum_add_distrib]

/-- Scaling all spectral weights scales the finite covariance. -/
lemma finiteSpectralCovariance_smul_power {idx : Type*} [Fintype idx]
    (freq : idx → ℝ) (a : ℝ) (p : idx → ℝ) (k : ℤ) :
    finiteSpectralCovariance freq (fun j => a * p j) k =
      (a : ℂ) * finiteSpectralCovariance freq p k := by
  simp [finiteSpectralCovariance, Finset.mul_sum, mul_assoc]

/-! ## E.2. White noise and transfer spectra -/

/-- The flat power spectral density of discrete white noise with variance
`sigma2`, normalized as `sigma2 / (2*pi)`. -/
def whiteNoiseSpectrum (sigma2 : ℝ) : ℝ :=
  sigma2 / (2 * Real.pi)

/-- White-noise spectral density is nonnegative when the variance is
nonnegative. -/
lemma whiteNoiseSpectrum_nonneg {sigma2 : ℝ} (hsigma : 0 ≤ sigma2) :
    0 ≤ whiteNoiseSpectrum sigma2 := by
  exact div_nonneg hsigma (mul_nonneg zero_le_two (le_of_lt Real.pi_pos))

/-- Output spectral power of a linear filter with complex transfer value `H`:
input power times `|H|^2`. -/
def outputSpectrum (inputPower : ℝ) (H : ℂ) : ℝ :=
  inputPower * Complex.normSq H

/-- Output spectral power is nonnegative when the input power is nonnegative. -/
lemma outputSpectrum_nonneg {inputPower : ℝ} (hinput : 0 ≤ inputPower) (H : ℂ) :
    0 ≤ outputSpectrum inputPower H := by
  exact mul_nonneg hinput (Complex.normSq_nonneg H)

/-- Output spectral power for white noise through transfer value `H`. -/
def whiteNoiseOutputSpectrum (sigma2 : ℝ) (H : ℂ) : ℝ :=
  outputSpectrum (whiteNoiseSpectrum sigma2) H

/-- White-noise output power is nonnegative for nonnegative variance. -/
lemma whiteNoiseOutputSpectrum_nonneg {sigma2 : ℝ} (hsigma : 0 ≤ sigma2) (H : ℂ) :
    0 ≤ whiteNoiseOutputSpectrum sigma2 H := by
  exact outputSpectrum_nonneg (whiteNoiseSpectrum_nonneg hsigma) H

/-! ## E.3. AR, MA, and ARMA spectra -/

/-- The discrete lag phase `exp(-i omega n)` used by transfer functions in
Z-transform convention. -/
def discreteLagPhase (omega : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (-(Complex.I * (omega : ℂ) * (n : ℂ)))

/-- Zero lag has unit phase. -/
@[simp] lemma discreteLagPhase_zero (omega : ℝ) :
    discreteLagPhase omega 0 = 1 := by
  simp [discreteLagPhase]

/-- The AR(1) denominator `1 - a exp(-i omega)`. -/
def ar1Denominator (a omega : ℝ) : ℂ :=
  1 - (a : ℂ) * discreteLagPhase omega 1

/-- The AR(1) transfer function `1 / (1 - a exp(-i omega))`. -/
def ar1Transfer (a omega : ℝ) : ℂ :=
  (ar1Denominator a omega)⁻¹

/-- AR(1) transfer inverts its denominator away from poles. -/
lemma ar1Denominator_mul_transfer {a omega : ℝ}
    (hden : ar1Denominator a omega ≠ 0) :
    ar1Denominator a omega * ar1Transfer a omega = 1 := by
  simp [ar1Transfer, hden]

/-- The AR(1) spectrum `sigma2/(2*pi) * |1/(1-ae^{-i omega})|^2`. -/
def ar1PowerSpectrum (sigma2 a omega : ℝ) : ℝ :=
  whiteNoiseOutputSpectrum sigma2 (ar1Transfer a omega)

/-- The AR(1) spectrum is white-noise power multiplied by transfer power. -/
lemma ar1PowerSpectrum_eq_whiteNoise_mul_transfer (sigma2 a omega : ℝ) :
    ar1PowerSpectrum sigma2 a omega =
      whiteNoiseSpectrum sigma2 * Complex.normSq (ar1Transfer a omega) := by
  rfl

/-- The moving-average transfer `sum_j b_j exp(-i omega lag_j)`. -/
def movingAverageTransfer {idx : Type*} [Fintype idx]
    (b : idx → ℝ) (lag : idx → ℕ) (omega : ℝ) : ℂ :=
  ∑ j : idx, (b j : ℂ) * discreteLagPhase omega (lag j)

/-- The MA spectrum `sigma2/(2*pi) * |B(e^{i omega})|^2`. -/
def movingAveragePowerSpectrum {idx : Type*} [Fintype idx]
    (sigma2 : ℝ) (b : idx → ℝ) (lag : idx → ℕ) (omega : ℝ) : ℝ :=
  whiteNoiseOutputSpectrum sigma2 (movingAverageTransfer b lag omega)

/-- The moving-average spectrum is white-noise power multiplied by the squared
modulus of the feed-forward transfer. -/
lemma movingAveragePowerSpectrum_eq_whiteNoise_mul_transfer
    {idx : Type*} [Fintype idx]
    (sigma2 : ℝ) (b : idx → ℝ) (lag : idx → ℕ) (omega : ℝ) :
    movingAveragePowerSpectrum sigma2 b lag omega =
      whiteNoiseSpectrum sigma2 * Complex.normSq (movingAverageTransfer b lag omega) := by
  rfl

/-- The autoregressive denominator `1 - sum_i a_i exp(-i omega lag_i)`. -/
def autoregressiveDenominator {idx : Type*} [Fintype idx]
    (a : idx → ℝ) (lag : idx → ℕ) (omega : ℝ) : ℂ :=
  1 - ∑ i : idx, (a i : ℂ) * discreteLagPhase omega (lag i)

/-- The ARMA transfer `B(e^{i omega}) / A(e^{i omega})`. -/
def armaTransfer {ar ma : Type*} [Fintype ar] [Fintype ma]
    (a : ar → ℝ) (arLag : ar → ℕ) (b : ma → ℝ) (maLag : ma → ℕ)
    (omega : ℝ) : ℂ :=
  movingAverageTransfer b maLag omega / autoregressiveDenominator a arLag omega

/-- The ARMA spectrum from white noise through the ARMA transfer. -/
def armaPowerSpectrum {ar ma : Type*} [Fintype ar] [Fintype ma]
    (sigma2 : ℝ) (a : ar → ℝ) (arLag : ar → ℕ)
    (b : ma → ℝ) (maLag : ma → ℕ) (omega : ℝ) : ℝ :=
  whiteNoiseOutputSpectrum sigma2 (armaTransfer a arLag b maLag omega)

/-- The ARMA spectrum is white-noise power multiplied by ARMA transfer power. -/
lemma armaPowerSpectrum_eq_whiteNoise_mul_transfer
    {ar ma : Type*} [Fintype ar] [Fintype ma]
    (sigma2 : ℝ) (a : ar → ℝ) (arLag : ar → ℕ)
    (b : ma → ℝ) (maLag : ma → ℕ) (omega : ℝ) :
    armaPowerSpectrum sigma2 a arLag b maLag omega =
      whiteNoiseSpectrum sigma2 *
        Complex.normSq (armaTransfer a arLag b maLag omega) := by
  rfl

/-- The discrete integrator transfer `1 / (1 - exp(-i omega))` for random
walks and ARIMA(1,1,0). -/
def discreteIntegratorTransfer (omega : ℝ) : ℂ :=
  (1 - discreteLagPhase omega 1)⁻¹

/-! ## E.4. Damped oscillator transfer spectrum -/

/-- Frequency-domain denominator of the driven damped oscillator,
`k - m omega^2 + i gamma omega`. -/
def dampedOscillatorDenominator
    (S : DampedHarmonicOscillator) (omega : ℝ) : ℂ :=
  ((S.k - S.m * omega ^ 2 : ℝ) : ℂ) + ((S.γ * omega : ℝ) : ℂ) * Complex.I

/-- Frequency-domain transfer function of the driven damped oscillator. -/
def dampedOscillatorTransfer
    (S : DampedHarmonicOscillator) (omega : ℝ) : ℂ :=
  (dampedOscillatorDenominator S omega)⁻¹

/-- White-noise output spectrum of the damped oscillator filter. -/
def dampedOscillatorNoiseSpectrum
    (sigma2 : ℝ) (S : DampedHarmonicOscillator) (omega : ℝ) : ℝ :=
  whiteNoiseOutputSpectrum sigma2 (dampedOscillatorTransfer S omega)

/-- The damped oscillator spectrum is white-noise power multiplied by oscillator
transfer power. -/
lemma dampedOscillatorNoiseSpectrum_eq_whiteNoise_mul_transfer
    (sigma2 : ℝ) (S : DampedHarmonicOscillator) (omega : ℝ) :
    dampedOscillatorNoiseSpectrum sigma2 S omega =
      whiteNoiseSpectrum sigma2 * Complex.normSq (dampedOscillatorTransfer S omega) := by
  rfl

/-- The damped oscillator white-noise output spectrum is nonnegative for
nonnegative input variance. -/
lemma dampedOscillatorNoiseSpectrum_nonneg
    {sigma2 : ℝ} (hsigma : 0 ≤ sigma2)
    (S : DampedHarmonicOscillator) (omega : ℝ) :
    0 ≤ dampedOscillatorNoiseSpectrum sigma2 S omega := by
  exact whiteNoiseOutputSpectrum_nonneg hsigma (dampedOscillatorTransfer S omega)

/-- At the inherited natural frequency, the real part of the damped oscillator
denominator vanishes. -/
lemma dampedOscillatorDenominator_re_at_naturalFrequency
    (S : DampedHarmonicOscillator) :
    (dampedOscillatorDenominator S S.ω).re = 0 := by
  have homega : S.ω ^ 2 = S.k / S.m :=
    HarmonicOscillator.ω_sq S.toHarmonicOscillator
  simp [dampedOscillatorDenominator, homega]
  field_simp [S.m_ne_zero]
  ring

/-- At the inherited natural frequency the damped oscillator denominator is
purely imaginary, equal to `i gamma omega`. -/
lemma dampedOscillatorDenominator_at_naturalFrequency
    (S : DampedHarmonicOscillator) :
    dampedOscillatorDenominator S S.ω = ((S.γ * S.ω : ℝ) : ℂ) * Complex.I := by
  have homega : S.ω ^ 2 = S.k / S.m :=
    HarmonicOscillator.ω_sq S.toHarmonicOscillator
  have hreal : S.k - S.m * S.ω ^ 2 = 0 := by
    rw [homega]
    field_simp [S.m_ne_zero]
    ring
  simp [dampedOscillatorDenominator, hreal]

/-! ## F. Infinite-well wave packets, phase space, and Gibbs weights

This section records the pure-point core of E. E. Perepelkin et al.,
*Exact time-dependent solution of the Schrödinger equation, its generalization to the phase
space and relation to the Gibbs distribution* (arXiv:2112.15212v1).  It deliberately reuses the
spectral flow above and the repository's canonical-ensemble implementation.  It includes both
the finite approximation layer and the paper's convergent, normalized infinite Jacobi-theta
wavefunction, with its exact Parseval normalization and modewise spectral evolution.
-/

section InfiniteWell

variable {X ι : Type*}

/-! ### F.1. The paper's shifted Jacobi theta series -/

/-- A summand of the shifted theta series in paper Eq. (1.3), written with the half-integer
mode `n + 1/2`. -/
noncomputable def perepelkinThetaTerm (n : ℤ) (z tau : ℂ) : ℂ :=
  Complex.exp
    (Complex.I * (Real.pi : ℂ) * ((n : ℂ) + 1 / 2) ^ 2 * tau +
      2 * Complex.I * (Real.pi : ℂ) * ((n : ℂ) + 1 / 2) * (z + 1 / 2))

/-- The Gaussian factor obtained by completing the square in the half-integer theta series. -/
noncomputable def perepelkinThetaPrefactor (z tau : ℂ) : ℂ :=
  Complex.exp
    (Complex.I * (Real.pi : ℂ) * (1 / 2 : ℂ) ^ 2 * tau +
      2 * Complex.I * (Real.pi : ℂ) * (1 / 2 : ℂ) * (z + 1 / 2))

/-- The paper's theta convention, defined by its convergent half-integer lattice series. -/
noncomputable def perepelkinTheta (z tau : ℂ) : ℂ :=
  ∑' n : ℤ, perepelkinThetaTerm n z tau

/-- Completing the square identifies every paper summand with a standard Jacobi-theta
summand.  This is the termwise bridge to Mathlib's analytic theta implementation. -/
lemma perepelkinThetaTerm_eq_jacobiTheta₂_term (n : ℤ) (z tau : ℂ) :
    perepelkinThetaTerm n z tau =
      perepelkinThetaPrefactor z tau *
        jacobiTheta₂_term n (z + 1 / 2 + (1 / 2 : ℂ) * tau) tau := by
  rw [perepelkinThetaTerm, perepelkinThetaPrefactor, jacobiTheta₂_term,
    ← Complex.exp_add]
  congr 1
  ring

/-- Paper Eq. (1.3) in its displayed odd-integer form. -/
lemma perepelkinThetaTerm_eq_odd_integer_form (n : ℤ) (z tau : ℂ) :
    perepelkinThetaTerm n z tau =
      Complex.exp
        (Complex.I * (Real.pi : ℂ) * tau / 4 * (2 * (n : ℂ) + 1) ^ 2 +
          Complex.I * (Real.pi : ℂ) / 2 * (2 * z + 1) * (2 * (n : ℂ) + 1)) := by
  rw [perepelkinThetaTerm]
  congr 1
  ring

/-- For positive imaginary modular parameter, the paper's theta series is absolutely
summable.  This discharges the convergence premise by reusing Mathlib's Jacobi-theta bound. -/
lemma summable_perepelkinThetaTerm (z : ℂ) {tau : ℂ} (htau : 0 < tau.im) :
    Summable (fun n : ℤ => perepelkinThetaTerm n z tau) := by
  have htheta : Summable
      (fun n : ℤ => jacobiTheta₂_term n (z + 1 / 2 + (1 / 2 : ℂ) * tau) tau) :=
    (summable_jacobiTheta₂_term_iff _ _).2 htau
  refine (htheta.mul_left (perepelkinThetaPrefactor z tau)).congr ?_
  intro n
  exact (perepelkinThetaTerm_eq_jacobiTheta₂_term n z tau).symm

/-- The convergent lattice series has sum `perepelkinTheta`. -/
lemma hasSum_perepelkinThetaTerm (z : ℂ) {tau : ℂ} (htau : 0 < tau.im) :
    HasSum (fun n : ℤ => perepelkinThetaTerm n z tau) (perepelkinTheta z tau) := by
  exact (summable_perepelkinThetaTerm z htau).hasSum

/-- Closed Jacobi-theta form of the paper's shifted lattice series. -/
lemma perepelkinTheta_eq_jacobiTheta₂ (z tau : ℂ) :
    perepelkinTheta z tau =
      perepelkinThetaPrefactor z tau *
        jacobiTheta₂ (z + 1 / 2 + (1 / 2 : ℂ) * tau) tau := by
  unfold perepelkinTheta jacobiTheta₂
  rw [tsum_congr (fun n => perepelkinThetaTerm_eq_jacobiTheta₂_term n z tau),
    tsum_mul_left]

/-- Shifting the spatial theta coordinate by one changes the sign of each half-integer
mode.  This is the termwise analytic core of the infinite-well boundary condition. -/
lemma perepelkinThetaTerm_add_one (n : ℤ) (z tau : ℂ) :
    perepelkinThetaTerm n (z + 1) tau = -perepelkinThetaTerm n z tau := by
  rw [perepelkinThetaTerm, perepelkinThetaTerm]
  rw [show
      Complex.I * (Real.pi : ℂ) * ((n : ℂ) + 1 / 2) ^ 2 * tau +
          2 * Complex.I * (Real.pi : ℂ) * ((n : ℂ) + 1 / 2) * (z + 1 + 1 / 2) =
        (Complex.I * (Real.pi : ℂ) * ((n : ℂ) + 1 / 2) ^ 2 * tau +
          2 * Complex.I * (Real.pi : ℂ) * ((n : ℂ) + 1 / 2) * (z + 1 / 2)) +
          (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I by ring,
    Complex.exp_add, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I n, Complex.exp_pi_mul_I]
  ring

/-- The shifted theta series is anti-periodic with spatial period one. -/
lemma perepelkinTheta_antiperiodic (tau : ℂ) :
    Function.Antiperiodic (fun z : ℂ => perepelkinTheta z tau) 1 := by
  intro z
  unfold perepelkinTheta
  rw [← tsum_neg]
  exact tsum_congr fun n => perepelkinThetaTerm_add_one n z tau

/-- Genuine antiperiodicity closes after two spatial shifts.  This is the
standard doubled-period consequence, not an amplitude-damped sign twist. -/
lemma perepelkinTheta_periodic_two (tau : ℂ) :
    Function.Periodic (fun z : ℂ => perepelkinTheta z tau) 2 := by
  simpa using (perepelkinTheta_antiperiodic tau).periodic_two_mul

/-- Reflecting a half-integer mode by `n ↦ -n-1` turns the summand at `-z` into the
negative of the original summand. -/
lemma perepelkinThetaTerm_reflect (n : ℤ) (z tau : ℂ) :
    perepelkinThetaTerm (-n - 1) (-z) tau = -perepelkinThetaTerm n z tau := by
  rw [perepelkinThetaTerm, perepelkinThetaTerm]
  rw [show
      Complex.I * (Real.pi : ℂ) * ((((-n - 1 : ℤ) : ℂ)) + 1 / 2) ^ 2 * tau +
          2 * Complex.I * (Real.pi : ℂ) * ((((-n - 1 : ℤ) : ℂ)) + 1 / 2) *
            (-z + 1 / 2) =
        (Complex.I * (Real.pi : ℂ) * ((n : ℂ) + 1 / 2) ^ 2 * tau +
          2 * Complex.I * (Real.pi : ℂ) * ((n : ℂ) + 1 / 2) * (z + 1 / 2)) +
          ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I by push_cast; ring,
    sub_eq_add_neg, Complex.exp_add, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I (-n), Complex.exp_neg_pi_mul_I]
  ring

/-- The paper's shifted theta convention is odd in its spatial coordinate. -/
lemma perepelkinTheta_neg (z tau : ℂ) :
    perepelkinTheta (-z) tau = -perepelkinTheta z tau := by
  let reflect : ℤ ≃ ℤ :=
    { toFun := fun n => -n - 1
      invFun := fun n => -n - 1
      left_inv := by intro n; simp
      right_inv := by intro n; simp }
  calc
    perepelkinTheta (-z) tau = ∑' n : ℤ, perepelkinThetaTerm n (-z) tau := rfl
    _ = ∑' n : ℤ, perepelkinThetaTerm (reflect n) (-z) tau :=
      ((reflect.tsum_eq (fun n : ℤ => perepelkinThetaTerm n (-z) tau))).symm
    _ = ∑' n : ℤ, -perepelkinThetaTerm n z tau := by
      apply tsum_congr
      intro n
      exact perepelkinThetaTerm_reflect n z tau
    _ = -perepelkinTheta z tau := by rw [tsum_neg]; rfl

/-- The shifted theta vanishes at the origin. -/
@[simp] lemma perepelkinTheta_zero (tau : ℂ) : perepelkinTheta 0 tau = 0 := by
  have h := perepelkinTheta_neg (0 : ℂ) tau
  simpa only [neg_zero, eq_neg_iff_add_eq_zero, add_self_eq_zero] using h

/-- The odd, anti-periodic shifted theta vanishes at every integer spatial coordinate.
These are the Dirichlet lattice boundary nodes used by the paper's infinite-well solution. -/
lemma perepelkinTheta_intCast_zero (k : ℤ) (tau : ℂ) :
    perepelkinTheta (k : ℂ) tau = 0 := by
  have h := (perepelkinTheta_antiperiodic tau).int_mul_eq_of_eq_zero
    (perepelkinTheta_zero tau) k
  simpa using h

/-! ### F.2. Exact finite spectral evolution -/

/-- Reconstruction of a finite pure-point wave packet from spatial modes and the existing
componentwise Schrödinger evolution. -/
def finiteSpectralWavePacket [Fintype ι]
    (E : ι → ℝ) (mode : ι → X → ℂ) (hbar t : ℝ) (c : ι → ℂ) (x : X) : ℂ :=
  ∑ i, finiteSpectralEvolution E hbar t c i * mode i x

/-- The unit-period Fourier mode used to express a spectrum whose phases close after one
rescaled time period.  It is the same exponential character mechanism used elsewhere in
Physlib's torus-character orthogonality layer, specialized here without creating an import
cycle through the larger complex-action graph. -/
noncomputable def unitPeriodSpectralMode (q : ℤ) (u : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (q : ℂ) * u)

@[simp] lemma norm_unitPeriodSpectralMode (q : ℤ) (u : ℝ) :
    ‖unitPeriodSpectralMode q u‖ = 1 := by
  rw [unitPeriodSpectralMode, Complex.norm_exp]
  simp

/-- Distinct integer spectral frequencies are orthogonal over one rescaled time period. -/
lemma unitPeriodSpectralMode_orthogonal (a b : ℤ) :
    (∫ u in (0 : ℝ)..1,
      unitPeriodSpectralMode a u * (starRingEnd ℂ) (unitPeriodSpectralMode b u)) =
      if a = b then 1 else 0 := by
  have hpoint : ∀ u : ℝ,
      unitPeriodSpectralMode a u * (starRingEnd ℂ) (unitPeriodSpectralMode b u) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a - b : ℤ) : ℂ) * u) := by
    intro u
    rw [unitPeriodSpectralMode, unitPeriodSpectralMode, ← Complex.exp_conj,
      ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]
    push_cast
    ring
  rw [intervalIntegral.integral_congr (fun u _ => hpoint u)]
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab]
    have hcoeff : (2 * (Real.pi : ℂ) * Complex.I * (((a - b : ℤ) : ℂ))) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
      · exact Complex.I_ne_zero
      · exact_mod_cast sub_ne_zero.mpr hab
    rw [integral_exp_mul_complex hcoeff]
    have hexp :
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((a - b : ℤ) : ℂ))) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (((a - b : ℤ) : ℂ)) =
          (((a - b : ℤ) : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I (a - b)
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, hexp, sub_self, zero_div]

/-- A finite packet with integer frequencies after rescaling time to a unit period. -/
noncomputable def finiteUnitPeriodWavePacket [Fintype ι]
    (frequency : ι → ℤ) (amplitude : ι → ℂ) (u : ℝ) : ℂ :=
  ∑ i, amplitude i * unitPeriodSpectralMode (frequency i) u

/-- The complex-valued Born kernel `conj ψ · ψ`; it is the canonical complex coercion of
the real squared norm and is convenient for exact Fourier integration. -/
noncomputable def finiteUnitPeriodBornKernel [Fintype ι]
    (frequency : ι → ℤ) (amplitude : ι → ℂ) (u : ℝ) : ℂ :=
  (starRingEnd ℂ) (finiteUnitPeriodWavePacket frequency amplitude u) *
    finiteUnitPeriodWavePacket frequency amplitude u

lemma finiteUnitPeriodBornKernel_eq_normSq [Fintype ι]
    (frequency : ι → ℤ) (amplitude : ι → ℂ) (u : ℝ) :
    finiteUnitPeriodBornKernel frequency amplitude u =
      (Complex.normSq (finiteUnitPeriodWavePacket frequency amplitude u) : ℂ) := by
  exact (Complex.normSq_eq_conj_mul_self).symm

/-- A cross term of two distinct spectral frequencies averages to zero over one period;
equal frequencies retain the coefficient inner product. -/
lemma integral_unitPeriodSpectralCrossTerm (a b : ℤ) (ca cb : ℂ) :
    (∫ u in (0 : ℝ)..1,
      (starRingEnd ℂ) (ca * unitPeriodSpectralMode a u) *
        (cb * unitPeriodSpectralMode b u)) =
      (starRingEnd ℂ) ca * cb * (if b = a then 1 else 0) := by
  have hpoint : ∀ u : ℝ,
      (starRingEnd ℂ) (ca * unitPeriodSpectralMode a u) *
          (cb * unitPeriodSpectralMode b u) =
        ((starRingEnd ℂ) ca * cb) *
          (unitPeriodSpectralMode b u *
            (starRingEnd ℂ) (unitPeriodSpectralMode a u)) := by
    intro u
    simp only [map_mul]
    ring
  rw [intervalIntegral.integral_congr (fun u _ => hpoint u),
    intervalIntegral.integral_const_mul,
    unitPeriodSpectralMode_orthogonal b a]

/-- Exact finite-spectrum dephasing: if the integer frequencies are nondegenerate, the
one-period average of the Born density contains only the diagonal mode weights. -/
lemma integral_finiteUnitPeriodBornKernel [Fintype ι] [DecidableEq ι]
    (frequency : ι → ℤ) (amplitude : ι → ℂ) (hfrequency : Function.Injective frequency) :
    (∫ u in (0 : ℝ)..1, finiteUnitPeriodBornKernel frequency amplitude u) =
      ∑ i, (Complex.normSq (amplitude i) : ℂ) := by
  have hpoint : ∀ u : ℝ,
      finiteUnitPeriodBornKernel frequency amplitude u =
        ∑ i, ∑ j,
          (starRingEnd ℂ) (amplitude i * unitPeriodSpectralMode (frequency i) u) *
            (amplitude j * unitPeriodSpectralMode (frequency j) u) := by
    intro u
    unfold finiteUnitPeriodBornKernel finiteUnitPeriodWavePacket
    simp only [map_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
  have hinterm (i j : ι) : IntervalIntegrable
      (fun u : ℝ =>
        (starRingEnd ℂ) (amplitude i * unitPeriodSpectralMode (frequency i) u) *
          (amplitude j * unitPeriodSpectralMode (frequency j) u)) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold unitPeriodSpectralMode
    fun_prop
  have hinsum (i : ι) : IntervalIntegrable
      (fun u : ℝ => ∑ j,
        (starRingEnd ℂ) (amplitude i * unitPeriodSpectralMode (frequency i) u) *
          (amplitude j * unitPeriodSpectralMode (frequency j) u)) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold unitPeriodSpectralMode
    fun_prop
  rw [intervalIntegral.integral_congr (fun u _ => hpoint u)]
  rw [intervalIntegral.integral_finsetSum (fun i _hi => hinsum i)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [integral_unitPeriodSpectralCrossTerm]
    rw [Finset.sum_eq_single i]
    · simp [Complex.normSq_eq_conj_mul_self]
    · intro j _hj hji
      simp [show frequency j ≠ frequency i from fun h => hji (hfrequency h)]
    · simp
  · intro j _hj
    exact hinterm i j

/-- An absolutely convergent infinite packet with integer frequencies on the unit period. -/
noncomputable def infiniteUnitPeriodWavePacket {κ : Type*}
    (frequency : κ → ℤ) (amplitude : κ → ℂ) (u : ℝ) : ℂ :=
  ∑' i, amplitude i * unitPeriodSpectralMode (frequency i) u

/-- The Born kernel of an infinite unit-period packet. -/
noncomputable def infiniteUnitPeriodBornKernel {κ : Type*}
    (frequency : κ → ℤ) (amplitude : κ → ℂ) (u : ℝ) : ℂ :=
  (starRingEnd ℂ) (infiniteUnitPeriodWavePacket frequency amplitude u) *
    infiniteUnitPeriodWavePacket frequency amplitude u

lemma infiniteUnitPeriodBornKernel_eq_normSq {κ : Type*}
    (frequency : κ → ℤ) (amplitude : κ → ℂ) (u : ℝ) :
    infiniteUnitPeriodBornKernel frequency amplitude u =
      (Complex.normSq (infiniteUnitPeriodWavePacket frequency amplitude u) : ℂ) := by
  exact (Complex.normSq_eq_conj_mul_self).symm

/-- Infinite Parseval/dephasing theorem for an absolutely convergent packet with distinct
integer frequencies.  This is the countable counterpart of
`integral_finiteUnitPeriodBornKernel` and is the normalization engine for the paper's exact
theta wavefunction. -/
lemma integral_infiniteUnitPeriodBornKernel {κ : Type*} [Countable κ] [DecidableEq κ]
    (frequency : κ → ℤ) (amplitude : κ → ℂ)
    (hamplitude : Summable fun i => ‖amplitude i‖)
    (hfrequency : Function.Injective frequency) :
    (∫ u in (0 : ℝ)..1, infiniteUnitPeriodBornKernel frequency amplitude u) =
      ∑' i, (Complex.normSq (amplitude i) : ℂ) := by
  let term : κ → ℝ → ℂ := fun i u => amplitude i * unitPeriodSpectralMode (frequency i) u
  have hterm_norm (u : ℝ) : Summable fun i => ‖term i u‖ := by
    simpa [term, norm_mul] using hamplitude
  have hterm (u : ℝ) : Summable fun i => term i u := (hterm_norm u).of_norm
  let cross : κ × κ → C(ℝ, ℂ) := fun p =>
    ⟨fun u => (starRingEnd ℂ) (term p.1 u) * term p.2 u, by
      unfold term unitPeriodSpectralMode
      fun_prop⟩
  have hcross_bound (p : κ × κ) :
      ‖(cross p).restrict
        (⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ ≤
        ‖amplitude p.1‖ * ‖amplitude p.2‖ := by
    apply (ContinuousMap.norm_le
      (f := (cross p).restrict
        (⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
    intro u
    simp [cross, term]
  have hamp_pair : Summable fun p : κ × κ => ‖amplitude p.1‖ * ‖amplitude p.2‖ :=
    hamplitude.mul_of_nonneg hamplitude (fun i => norm_nonneg _) (fun i => norm_nonneg _)
  have hcross_sum : Summable fun p : κ × κ =>
      ‖(cross p).restrict
        (⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ :=
    hamp_pair.of_nonneg_of_le (fun _ => norm_nonneg _) hcross_bound
  have hkernel (u : ℝ) :
      (∑' p : κ × κ, cross p u) =
        infiniteUnitPeriodBornKernel frequency amplitude u := by
    have hconj_norm : Summable fun i => ‖(starRingEnd ℂ) (term i u)‖ := by
      simpa using hterm_norm u
    rw [infiniteUnitPeriodBornKernel, infiniteUnitPeriodWavePacket,
      Complex.conj_tsum]
    exact (tsum_mul_tsum_of_summable_norm hconj_norm (hterm_norm u)).symm
  have hintegral := intervalIntegral.hasSum_intervalIntegral_of_summable_norm hcross_sum
  have hintegral' : HasSum (fun p : κ × κ => ∫ u in (0 : ℝ)..1, cross p u)
      (∫ u in (0 : ℝ)..1, infiniteUnitPeriodBornKernel frequency amplitude u) := by
    have heq : (∫ u in (0 : ℝ)..1, ∑' p : κ × κ, cross p u) =
        ∫ u in (0 : ℝ)..1, infiniteUnitPeriodBornKernel frequency amplitude u := by
      apply intervalIntegral.integral_congr
      intro u _hu
      exact hkernel u
    rw [← heq]
    exact hintegral
  rw [← hintegral'.tsum_eq]
  simp_rw [show ∀ p : κ × κ,
      (∫ u in (0 : ℝ)..1, cross p u) =
        (starRingEnd ℂ) (amplitude p.1) * amplitude p.2 *
          (if frequency p.2 = frequency p.1 then 1 else 0) by
    intro p
    exact integral_unitPeriodSpectralCrossTerm
      (frequency p.1) (frequency p.2) (amplitude p.1) (amplitude p.2)]
  have hdiag : Summable fun p : κ × κ =>
      (starRingEnd ℂ) (amplitude p.1) * amplitude p.2 *
        (if frequency p.2 = frequency p.1 then 1 else 0) := by
    refine hamp_pair.of_norm_bounded ?_
    intro p
    by_cases hp : frequency p.2 = frequency p.1
    · simp [hp]
    · simpa [hp] using mul_nonneg (norm_nonneg (amplitude p.1)) (norm_nonneg (amplitude p.2))
  rw [hdiag.tsum_prod]
  apply tsum_congr
  intro i
  rw [tsum_eq_single i]
  · simp [Complex.normSq_eq_conj_mul_self]
  · intro j hji
    simp [show frequency j ≠ frequency i from fun h => hji (hfrequency h)]

/-! ### F.3. The normalized infinite-mode theta wavefunction -/

/-- The time-dependent modular parameter in Theorem 1 of arXiv:2112.15212v1.
Its imaginary part is the positive thermal parameter `beta`; the real part carries the
Schrödinger evolution. -/
noncomputable def perepelkinTau
    (hbar mass width : ℝ) (mu : ℕ) (beta t : ℝ) : ℂ :=
  ((-(2 * Real.pi * hbar * (mu : ℝ) ^ 2 * t / (mass * width ^ 2)) : ℝ) : ℂ) +
    Complex.I * (beta : ℂ)

@[simp] lemma perepelkinTau_im
    (hbar mass width : ℝ) (mu : ℕ) (beta t : ℝ) :
    (perepelkinTau hbar mass width mu beta t).im = beta := by
  let a : ℝ := -(2 * Real.pi * hbar * (mu : ℝ) ^ 2 * t / (mass * width ^ 2))
  change (((a : ℂ) + Complex.I * (beta : ℂ)).im = beta)
  simp

/-- The exact, unnormalized infinite-mode theta packet of paper Theorem 1. -/
noncomputable def perepelkinThetaWavePacket
    (hbar mass width : ℝ) (mu : ℕ) (beta x t : ℝ) : ℂ :=
  perepelkinTheta (((mu : ℝ) * x / width : ℝ) : ℂ)
    (perepelkinTau hbar mass width mu beta t)

/-- Coefficient of the `n`th integer Fourier character after extracting the common
half-integer spatial phase from the paper's theta series. -/
noncomputable def perepelkinSpectralAmplitude
    (hbar mass width : ℝ) (mu : ℕ) (beta t : ℝ) (n : ℤ) : ℂ :=
  perepelkinThetaTerm n 0 (perepelkinTau hbar mass width mu beta t)

/-- The common half-integer spatial phase omitted by the integer Fourier packet. -/
noncomputable def perepelkinCommonSpatialPhase (mu : ℕ) (u : ℝ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi : ℂ) * (mu : ℂ) * (u : ℂ))

@[simp] lemma norm_perepelkinCommonSpatialPhase (mu : ℕ) (u : ℝ) :
    ‖perepelkinCommonSpatialPhase mu u‖ = 1 := by
  rw [perepelkinCommonSpatialPhase, Complex.norm_exp]
  simp

/-- Termwise Fourier decomposition of the paper's shifted theta convention. -/
lemma perepelkinThetaTerm_spatial_decomposition
    (hbar mass width : ℝ) (mu : ℕ) (beta t u : ℝ) (n : ℤ) :
    perepelkinThetaTerm n (((mu : ℝ) * u : ℝ) : ℂ)
        (perepelkinTau hbar mass width mu beta t) =
      perepelkinCommonSpatialPhase mu u *
        (perepelkinSpectralAmplitude hbar mass width mu beta t n *
          unitPeriodSpectralMode ((mu : ℤ) * n) u) := by
  rw [perepelkinThetaTerm, perepelkinSpectralAmplitude, perepelkinThetaTerm,
    perepelkinCommonSpatialPhase, unitPeriodSpectralMode, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The theta packet is a common unit phase times an absolutely convergent integer-frequency
packet.  This is the bridge from the paper's analytic formula to the reusable Parseval layer. -/
lemma perepelkinTheta_eq_infiniteUnitPeriodWavePacket
    (hbar mass width : ℝ) (mu : ℕ) (beta t u : ℝ) :
    perepelkinTheta (((mu : ℝ) * u : ℝ) : ℂ)
        (perepelkinTau hbar mass width mu beta t) =
      perepelkinCommonSpatialPhase mu u *
        infiniteUnitPeriodWavePacket (fun n : ℤ => (mu : ℤ) * n)
          (perepelkinSpectralAmplitude hbar mass width mu beta t) u := by
  unfold perepelkinTheta infiniteUnitPeriodWavePacket
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  exact perepelkinThetaTerm_spatial_decomposition hbar mass width mu beta t u n

/-- The positive Gaussian weight appearing in the paper's normalization `N(beta)`. -/
noncomputable def perepelkinSpectralWeight (beta : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-2 * Real.pi * beta * ((n : ℝ) + 1 / 2) ^ 2)

/-- The real part of the Schrödinger phase drops out of each coefficient norm. -/
lemma norm_perepelkinSpectralAmplitude
    (hbar mass width : ℝ) (mu : ℕ) (beta t : ℝ) (n : ℤ) :
    ‖perepelkinSpectralAmplitude hbar mass width mu beta t n‖ =
      Real.exp (-Real.pi * beta * ((n : ℝ) + 1 / 2) ^ 2) := by
  let q : ℝ := (n : ℝ) + 1 / 2
  let a : ℝ := -(2 * Real.pi * hbar * (mu : ℝ) ^ 2 * t / (mass * width ^ 2))
  have hm : ((n : ℂ) + 1 / 2) = (q : ℂ) := by
    simp [q]
  have htau : perepelkinTau hbar mass width mu beta t =
      (a : ℂ) + Complex.I * (beta : ℂ) := rfl
  rw [perepelkinSpectralAmplitude, perepelkinThetaTerm, hm, htau, Complex.norm_exp]
  congr 1
  norm_num [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im, pow_two, q]
  ring

/-- The squared coefficient norm is exactly the Gaussian normalization weight and is
independent of time, mass, width, `hbar`, and the state label `mu`. -/
lemma normSq_perepelkinSpectralAmplitude
    (hbar mass width : ℝ) (mu : ℕ) (beta t : ℝ) (n : ℤ) :
    Complex.normSq (perepelkinSpectralAmplitude hbar mass width mu beta t n) =
      perepelkinSpectralWeight beta n := by
  rw [Complex.normSq_eq_norm_sq, norm_perepelkinSpectralAmplitude,
    perepelkinSpectralWeight, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Energy carried by the half-integer theta mode.  It is chosen so that the real part of
`perepelkinTau` is precisely the repository's phase `exp (-i E t / hbar)`. -/
noncomputable def perepelkinModeEnergy
    (hbar mass width : ℝ) (mu : ℕ) (n : ℤ) : ℝ :=
  2 * Real.pi ^ 2 * hbar ^ 2 * (mu : ℝ) ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 /
    (mass * width ^ 2)

/-- Every infinite theta coefficient is exactly an existing `spectralPhase` evolution of
its initial coefficient.  Thus the analytic infinite packet uses the same Schrödinger
mechanism as the repository's finite pure-point dynamics. -/
lemma perepelkinSpectralAmplitude_eq_spectralPhase
    {hbar mass width : ℝ} (hhbar : hbar ≠ 0) (hmass : mass ≠ 0) (hwidth : width ≠ 0)
    (mu : ℕ) (beta t : ℝ) (n : ℤ) :
    perepelkinSpectralAmplitude hbar mass width mu beta t n =
      spectralPhase (perepelkinModeEnergy hbar mass width mu n) hbar t *
        perepelkinSpectralAmplitude hbar mass width mu beta 0 n := by
  rw [perepelkinSpectralAmplitude, perepelkinSpectralAmplitude,
    perepelkinThetaTerm, perepelkinThetaTerm, spectralPhase, reversiblePhase,
    perepelkinModeEnergy, ← Complex.exp_add]
  congr 1
  simp only [perepelkinTau, mul_zero, neg_zero, zero_div, zero_add]
  push_cast
  field_simp
  ring

/-- Modewise time-dependent Schrödinger equation for every coefficient in the infinite
theta packet.  No new evolution law is introduced: this is inherited from
`hasDerivAt_spectralPhase`. -/
lemma hasDerivAt_perepelkinSpectralAmplitude
    {hbar mass width : ℝ} (hhbar : hbar ≠ 0) (hmass : mass ≠ 0) (hwidth : width ≠ 0)
    (mu : ℕ) (beta t : ℝ) (n : ℤ) :
    HasDerivAt
      (fun s : ℝ => perepelkinSpectralAmplitude hbar mass width mu beta s n)
      (((perepelkinModeEnergy hbar mass width mu n : ℝ) : ℂ) /
          (Complex.I * hbar) *
        perepelkinSpectralAmplitude hbar mass width mu beta t n) t := by
  have hphase :=
    (hasDerivAt_spectralPhase (perepelkinModeEnergy hbar mass width mu n) hbar t).mul_const
      (perepelkinSpectralAmplitude hbar mass width mu beta 0 n)
  have hfun :
      (fun s : ℝ => perepelkinSpectralAmplitude hbar mass width mu beta s n) =
        (fun s : ℝ => spectralPhase (perepelkinModeEnergy hbar mass width mu n) hbar s *
          perepelkinSpectralAmplitude hbar mass width mu beta 0 n) := by
    funext s
    exact perepelkinSpectralAmplitude_eq_spectralPhase hhbar hmass hwidth mu beta s n
  rw [hfun]
  have hamp_t :=
    perepelkinSpectralAmplitude_eq_spectralPhase hhbar hmass hwidth mu beta t n
  rw [hamp_t]
  simpa only [mul_assoc] using hphase

/-- Positive thermal parameter gives absolute summability of the spectral amplitudes. -/
lemma summable_norm_perepelkinSpectralAmplitude
    (hbar mass width : ℝ) (mu : ℕ) {beta : ℝ} (hbeta : 0 < beta) (t : ℝ) :
    Summable (fun n : ℤ =>
      ‖perepelkinSpectralAmplitude hbar mass width mu beta t n‖) := by
  have hs := (summable_perepelkinThetaTerm (0 : ℂ)
    (tau := perepelkinTau hbar mass width mu beta t) (by simpa using hbeta)).norm
  simpa [perepelkinSpectralAmplitude] using hs

/-- The Gaussian normalization weights form a summable real series for `beta > 0`. -/
lemma summable_perepelkinSpectralWeight {beta : ℝ} (hbeta : 0 < beta) :
    Summable (perepelkinSpectralWeight beta) := by
  have hs := summable_norm_perepelkinSpectralAmplitude
    (1 : ℝ) 1 1 1 (beta := 2 * beta) (by positivity) 0
  refine hs.congr ?_
  intro n
  rw [norm_perepelkinSpectralAmplitude, perepelkinSpectralWeight]
  congr 1
  ring

/-- Paper Eq. (1.2): `N(beta) = width * sum exp(-2 pi beta (n+1/2)^2)`. -/
noncomputable def perepelkinNormalization (width beta : ℝ) : ℝ :=
  width * ∑' n : ℤ, perepelkinSpectralWeight beta n

/-- The paper's normalization constant is strictly positive on a positive-width well at
positive thermal parameter. -/
lemma perepelkinNormalization_pos {width beta : ℝ}
    (hwidth : 0 < width) (hbeta : 0 < beta) :
    0 < perepelkinNormalization width beta := by
  unfold perepelkinNormalization
  apply mul_pos hwidth
  exact (summable_perepelkinSpectralWeight hbeta).tsum_pos
    (fun n => (Real.exp_pos _).le) 0 (Real.exp_pos _)

/-- Parseval normalization of the unnormalized theta packet on the rescaled unit well. -/
lemma integral_normSq_perepelkinTheta_unit
    (hbar mass width : ℝ) {mu : ℕ} (hmu : 0 < mu)
    {beta : ℝ} (hbeta : 0 < beta) (t : ℝ) :
    (∫ u in (0 : ℝ)..1,
      (Complex.normSq
        (perepelkinTheta (((mu : ℝ) * u : ℝ) : ℂ)
          (perepelkinTau hbar mass width mu beta t)) : ℂ)) =
      ((∑' n : ℤ, perepelkinSpectralWeight beta n : ℝ) : ℂ) := by
  let frequency : ℤ → ℤ := fun n => (mu : ℤ) * n
  let amplitude : ℤ → ℂ := perepelkinSpectralAmplitude hbar mass width mu beta t
  have hmu0 : (mu : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmu)
  have hfrequency : Function.Injective frequency := by
    intro a b hab
    exact mul_left_cancel₀ hmu0 hab
  have hamplitude : Summable fun n => ‖amplitude n‖ := by
    simpa [amplitude] using
      summable_norm_perepelkinSpectralAmplitude hbar mass width mu hbeta t
  have hparseval := integral_infiniteUnitPeriodBornKernel frequency amplitude
    hamplitude hfrequency
  have hpoint (u : ℝ) :
      (Complex.normSq
        (perepelkinTheta (((mu : ℝ) * u : ℝ) : ℂ)
          (perepelkinTau hbar mass width mu beta t)) : ℂ) =
        infiniteUnitPeriodBornKernel frequency amplitude u := by
    rw [perepelkinTheta_eq_infiniteUnitPeriodWavePacket,
      infiniteUnitPeriodBornKernel_eq_normSq]
    simp only [Complex.ofReal_inj]
    rw [Complex.normSq_eq_norm_sq, norm_mul, norm_perepelkinCommonSpatialPhase,
      one_mul, ← Complex.normSq_eq_norm_sq]
  rw [intervalIntegral.integral_congr (fun u _hu => hpoint u), hparseval]
  simp_rw [amplitude, normSq_perepelkinSpectralAmplitude]
  exact (Complex.ofReal_tsum (perepelkinSpectralWeight beta)).symm

/-- The unnormalized theta packet has squared norm exactly `N(beta)` on the physical well. -/
lemma integral_normSq_perepelkinThetaWavePacket
    (hbar mass : ℝ) {width : ℝ} (hwidth : 0 < width)
    {mu : ℕ} (hmu : 0 < mu) {beta : ℝ} (hbeta : 0 < beta) (t : ℝ) :
    (∫ x in (0 : ℝ)..width,
      (Complex.normSq
        (perepelkinThetaWavePacket hbar mass width mu beta x t) : ℂ)) =
      (perepelkinNormalization width beta : ℂ) := by
  let f : ℝ → ℂ := fun u =>
    (Complex.normSq
      (perepelkinTheta (((mu : ℝ) * u : ℝ) : ℂ)
        (perepelkinTau hbar mass width mu beta t)) : ℂ)
  have hscale := intervalIntegral.integral_comp_div
    (f := f) (a := (0 : ℝ)) (b := width) hwidth.ne'
  have hunit := integral_normSq_perepelkinTheta_unit
    hbar mass width hmu hbeta t
  have hscale' :
      (∫ x in (0 : ℝ)..width, f (x / width)) =
        (width : ℂ) * ∫ u in (0 : ℝ)..1, f u := by
    simpa [hwidth.ne', smul_eq_mul] using hscale
  rw [hunit] at hscale'
  simpa [f, perepelkinThetaWavePacket, perepelkinNormalization, hwidth.ne',
    div_eq_mul_inv, mul_assoc] using hscale'

/-- The full normalized infinite-mode wavefunction from paper Theorem 1. -/
noncomputable def perepelkinWaveFunction
    (hbar mass width : ℝ) (mu : ℕ) (beta x t : ℝ) : ℂ :=
  ((Real.sqrt (perepelkinNormalization width beta))⁻¹ : ℂ) *
    perepelkinThetaWavePacket hbar mass width mu beta x t

/-- Pointwise Born density of the normalized wavefunction. -/
lemma normSq_perepelkinWaveFunction
    (hbar mass width : ℝ) (mu : ℕ) {beta : ℝ} (x t : ℝ)
    (hN : 0 < perepelkinNormalization width beta) :
    Complex.normSq (perepelkinWaveFunction hbar mass width mu beta x t) =
      (perepelkinNormalization width beta)⁻¹ *
        Complex.normSq (perepelkinThetaWavePacket hbar mass width mu beta x t) := by
  rw [perepelkinWaveFunction, Complex.normSq_mul, Complex.normSq_inv,
    Complex.normSq_ofReal, Real.mul_self_sqrt hN.le]

/-- Paper Theorem 1 normalization: the full infinite-mode wavefunction has unit Born mass
on the well at every time. -/
lemma integral_normSq_perepelkinWaveFunction
    (hbar mass : ℝ) {width : ℝ} (hwidth : 0 < width)
    {mu : ℕ} (hmu : 0 < mu) {beta : ℝ} (hbeta : 0 < beta) (t : ℝ) :
    (∫ x in (0 : ℝ)..width,
      (Complex.normSq
        (perepelkinWaveFunction hbar mass width mu beta x t) : ℂ)) = 1 := by
  have hN : 0 < perepelkinNormalization width beta :=
    perepelkinNormalization_pos hwidth hbeta
  have hpoint (x : ℝ) :
      (Complex.normSq
        (perepelkinWaveFunction hbar mass width mu beta x t) : ℂ) =
        ((perepelkinNormalization width beta)⁻¹ : ℂ) *
          (Complex.normSq
            (perepelkinThetaWavePacket hbar mass width mu beta x t) : ℂ) := by
    rw [normSq_perepelkinWaveFunction hbar mass width mu x t hN]
    norm_cast
  rw [intervalIntegral.integral_congr (fun x _hx => hpoint x),
    intervalIntegral.integral_const_mul,
    integral_normSq_perepelkinThetaWavePacket hbar mass hwidth hmu hbeta t]
  simp [hN.ne']

/-- The exact theta series converges whenever the paper's thermal parameter is positive. -/
lemma summable_perepelkinWaveFunction_series
    (hbar mass width : ℝ) (mu : ℕ) {beta : ℝ} (hbeta : 0 < beta) (x t : ℝ) :
    Summable (fun n : ℤ =>
      perepelkinThetaTerm n (((mu : ℝ) * x / width : ℝ) : ℂ)
        (perepelkinTau hbar mass width mu beta t)) := by
  apply summable_perepelkinThetaTerm
  simpa using hbeta

/-- The unnormalized and normalized packets obey the left Dirichlet boundary condition. -/
@[simp] lemma perepelkinWaveFunction_zero
    (hbar mass width : ℝ) (mu : ℕ) (beta t : ℝ) :
    perepelkinWaveFunction hbar mass width mu beta 0 t = 0 := by
  simp [perepelkinWaveFunction, perepelkinThetaWavePacket]

/-- The normalized packet obeys the right Dirichlet boundary condition for nonzero width. -/
@[simp] lemma perepelkinWaveFunction_width
    (hbar mass width : ℝ) (mu : ℕ) (beta t : ℝ) (hwidth : width ≠ 0) :
    perepelkinWaveFunction hbar mass width mu beta width t = 0 := by
  rw [perepelkinWaveFunction, perepelkinThetaWavePacket]
  have harg : (mu : ℝ) * width / width = mu := by field_simp
  rw [harg]
  have hz :
      perepelkinTheta (((mu : ℝ) : ℂ)) (perepelkinTau hbar mass width mu beta t) = 0 := by
    have hcast : ((Int.ofNat mu : ℤ) : ℂ) = (((mu : ℝ) : ℂ)) := by norm_num
    rw [← hcast]
    exact perepelkinTheta_intCast_zero (Int.ofNat mu)
      (perepelkinTau hbar mass width mu beta t)
  rw [hz, mul_zero]

/-- At zero time the reconstructed packet is its initial spectral expansion. -/
@[simp] lemma finiteSpectralWavePacket_zero [Fintype ι]
    (E : ι → ℝ) (mode : ι → X → ℂ) (hbar : ℝ) (c : ι → ℂ) (x : X) :
    finiteSpectralWavePacket E mode hbar 0 c x = ∑ i, c i * mode i x := by
  simp [finiteSpectralWavePacket, finiteSpectralEvolution]

/-- Exact time composition of a finite wave packet: evolving coefficients by `t` and then by
`s` is the same packet as evolving once by `s+t`. -/
lemma finiteSpectralWavePacket_add [Fintype ι]
    (E : ι → ℝ) (mode : ι → X → ℂ) (hbar s t : ℝ) (c : ι → ℂ) (x : X) :
    finiteSpectralWavePacket E mode hbar (s + t) c x =
      finiteSpectralWavePacket E mode hbar s (finiteSpectralEvolution E hbar t c) x := by
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [finiteSpectralEvolution, spectralPhase_add]
  ring

/-- The reconstructed finite packet satisfies the time-dependent Schrödinger equation
mode by mode.  The right-hand side is the spectral Hamiltonian action on the packet. -/
lemma hasDerivAt_finiteSpectralWavePacket [Fintype ι]
    (E : ι → ℝ) (mode : ι → X → ℂ) (hbar t : ℝ) (c : ι → ℂ) (x : X) :
    HasDerivAt (fun s : ℝ => finiteSpectralWavePacket E mode hbar s c x)
      (∑ i, ((E i : ℂ) / (Complex.I * hbar)) *
        (finiteSpectralEvolution E hbar t c i * mode i x)) t := by
  unfold finiteSpectralWavePacket
  apply HasDerivAt.fun_sum
  intro i _hi
  have hi := ((hasDerivAt_spectralPhase (E i) hbar t).mul_const (c i)).mul_const (mode i x)
  simpa only [finiteSpectralEvolution, mul_assoc] using hi

/-- The one-dimensional infinite-well spectrum
`E_n = π² ℏ² (n+1)² / (2 m L²)`, indexed from `n = 0`. -/
def infiniteWellEnergy (hbar mass width : ℝ) (n : ℕ) : ℝ :=
  Real.pi ^ 2 * hbar ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2 / (2 * mass * width ^ 2)

/-- For positive mass, nonzero `ℏ`, and nonzero well width, the infinite-well energies are
strictly increasing with the mode number. -/
lemma infiniteWellEnergy_strictMono (hbar mass width : ℝ)
    (hhbar : hbar ≠ 0) (hmass : 0 < mass) (hwidth : width ≠ 0) :
    StrictMono (infiniteWellEnergy hbar mass width) := by
  intro n k hnk
  have hcoeff : 0 < Real.pi ^ 2 * hbar ^ 2 / (2 * mass * width ^ 2) := by
    positivity
  have hcast : (((n + 1 : ℕ) : ℝ)) < (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.add_lt_add_right hnk 1
  have hsquare : (((n + 1 : ℕ) : ℝ) ^ 2) < (((k + 1 : ℕ) : ℝ) ^ 2) := by
    exact (sq_lt_sq₀ (by positivity) (by positivity)).2 hcast
  rw [show infiniteWellEnergy hbar mass width n =
      (Real.pi ^ 2 * hbar ^ 2 / (2 * mass * width ^ 2)) *
        (((n + 1 : ℕ) : ℝ) ^ 2) by unfold infiniteWellEnergy; ring,
    show infiniteWellEnergy hbar mass width k =
      (Real.pi ^ 2 * hbar ^ 2 / (2 * mass * width ^ 2)) *
        (((k + 1 : ℕ) : ℝ) ^ 2) by unfold infiniteWellEnergy; ring]
  exact mul_lt_mul_of_pos_left hsquare hcoeff

/-- A spectral phase closes after `period` whenever its accumulated phase is an integer
multiple of `2π`. -/
lemma spectralPhase_eq_one_of_integer_period (E hbar period : ℝ) (q : ℤ)
    (hphase : E / hbar * period = 2 * Real.pi * q) :
    spectralPhase E hbar period = 1 := by
  have hphaseC : (((E / hbar * period : ℝ) : ℂ)) =
      2 * (Real.pi : ℂ) * (q : ℂ) := by
    exact_mod_cast hphase
  unfold spectralPhase reversiblePhase
  rw [show -Complex.I * (((E / hbar : ℝ) : ℂ)) * (period : ℂ) =
      ((-q : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
    calc
      -Complex.I * (((E / hbar : ℝ) : ℂ)) * (period : ℂ) =
          -Complex.I * (((E / hbar * period : ℝ) : ℂ)) := by push_cast; ring
      _ = -Complex.I * (2 * (Real.pi : ℂ) * (q : ℂ)) := by rw [hphaseC]
      _ = ((-q : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I (-q)

/-- The full revival period `4mL²/(πℏ)` of the one-dimensional infinite well. -/
def infiniteWellRevivalPeriod (hbar mass width : ℝ) : ℝ :=
  4 * mass * width ^ 2 / (Real.pi * hbar)

/-- Every infinite-well energy accumulates an integer multiple of `2π` over one revival
period. -/
lemma infiniteWellEnergy_revival_phase (hbar mass width : ℝ) (n : ℕ)
    (hhbar : hbar ≠ 0) (hmass : mass ≠ 0) (hwidth : width ≠ 0) :
    infiniteWellEnergy hbar mass width n / hbar *
        infiniteWellRevivalPeriod hbar mass width =
      2 * Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2) := by
  unfold infiniteWellEnergy infiniteWellRevivalPeriod
  field_simp [hhbar, hmass, hwidth, Real.pi_ne_zero]
  ring

/-- Every finite-cutoff infinite-well spectral phase revives exactly after the common revival
period. -/
lemma infiniteWell_spectralPhase_revival (hbar mass width : ℝ) (n : ℕ)
    (hhbar : hbar ≠ 0) (hmass : mass ≠ 0) (hwidth : width ≠ 0) :
    spectralPhase (infiniteWellEnergy hbar mass width n) hbar
        (infiniteWellRevivalPeriod hbar mass width) = 1 := by
  apply spectralPhase_eq_one_of_integer_period _ _ _
    (Int.ofNat ((n + 1) ^ 2))
  simpa using infiniteWellEnergy_revival_phase hbar mass width n hhbar hmass hwidth

/-- A finite cutoff of the paper's infinite-well packet, reconstructed through the shared
spectral-evolution mechanism rather than a second Schrödinger propagator. -/
def finiteInfiniteWellWavePacket {N : ℕ}
    (mode : Fin N → X → ℂ) (hbar mass width t : ℝ) (c : Fin N → ℂ) (x : X) : ℂ :=
  finiteSpectralWavePacket
    (fun n : Fin N => infiniteWellEnergy hbar mass width n.val) mode hbar t c x

/-- The finite-cutoff packet is exactly periodic with the full infinite-well revival period. -/
lemma finiteInfiniteWellWavePacket_revival {N : ℕ}
    (mode : Fin N → X → ℂ) (hbar mass width t : ℝ) (c : Fin N → ℂ) (x : X)
    (hhbar : hbar ≠ 0) (hmass : mass ≠ 0) (hwidth : width ≠ 0) :
    finiteInfiniteWellWavePacket mode hbar mass width
        (t + infiniteWellRevivalPeriod hbar mass width) c x =
      finiteInfiniteWellWavePacket mode hbar mass width t c x := by
  unfold finiteInfiniteWellWavePacket finiteSpectralWavePacket finiteSpectralEvolution
  apply Finset.sum_congr rfl
  intro n _hn
  rw [spectralPhase_add,
    infiniteWell_spectralPhase_revival hbar mass width n.val hhbar hmass hwidth]
  ring

/-- The finite cutoff of the infinite-well spectrum as the repository's native discrete
canonical ensemble. -/
noncomputable def finiteInfiniteWellCanonicalEnsemble {N : ℕ}
    [MeasurableSpace (Fin N)] [MeasurableSingletonClass (Fin N)]
    (hbar mass width : ℝ) : CanonicalEnsemble (Fin N) :=
  CanonicalEnsemble.ofFiniteEnergy
    (fun n : Fin N => infiniteWellEnergy hbar mass width n.val)

/-- Theorem 8's freezing statement for every nonempty finite cutoff: as inverse temperature
goes to infinity, the Gibbs mean converges to the well's ground-state energy. -/
lemma finiteInfiniteWell_meanEnergy_tendsto_ground (N : ℕ)
    [MeasurableSpace (Fin (N + 1))] [MeasurableSingletonClass (Fin (N + 1))]
    (hbar mass width : ℝ) (hhbar : hbar ≠ 0) (hmass : 0 < mass) (hwidth : width ≠ 0) :
    Filter.Tendsto
      (finiteInfiniteWellCanonicalEnsemble (N := N + 1) hbar mass width).meanEnergyBetaReal
      Filter.atTop (nhds (infiniteWellEnergy hbar mass width 0)) := by
  apply CanonicalEnsemble.tendsto_meanEnergyBetaReal_atTop_of_unique_min
    (finiteInfiniteWellCanonicalEnsemble (N := N + 1) hbar mass width) (0 : Fin (N + 1))
  intro j hj
  change infiniteWellEnergy hbar mass width 0 <
    infiniteWellEnergy hbar mass width j.val
  apply infiniteWellEnergy_strictMono hbar mass width hhbar hmass hwidth
  have hjval : j.val ≠ 0 := by
    intro hjzero
    apply hj
    apply Fin.ext
    simpa using hjzero
  exact Nat.pos_of_ne_zero hjval

/-- The finite-cutoff infinite-well Gibbs entropy vanishes as `β → +∞`: the canonical
state freezes onto the unique ground mode. -/
lemma finiteInfiniteWell_shannonEntropy_tendsto_zero (N : ℕ)
    [MeasurableSpace (Fin (N + 1))] [MeasurableSingletonClass (Fin (N + 1))]
    (hbar mass width : ℝ) (hhbar : hbar ≠ 0) (hmass : 0 < mass) (hwidth : width ≠ 0) :
    Filter.Tendsto
      (finiteInfiniteWellCanonicalEnsemble
        (N := N + 1) hbar mass width).shannonEntropyBetaReal
      Filter.atTop (nhds 0) := by
  apply CanonicalEnsemble.tendsto_shannonEntropyBetaReal_atTop_of_unique_min
    (finiteInfiniteWellCanonicalEnsemble (N := N + 1) hbar mass width) (0 : Fin (N + 1))
  intro j hj
  change infiniteWellEnergy hbar mass width 0 <
    infiniteWellEnergy hbar mass width j.val
  apply infiniteWellEnergy_strictMono hbar mass width hhbar hmass hwidth
  have hjval : j.val ≠ 0 := by
    intro hjzero
    apply hj
    apply Fin.ext
    simpa using hjzero
  exact Nat.pos_of_ne_zero hjval

/-- The finite infinite-well packet inherits exact time composition from spectral dynamics. -/
lemma finiteInfiniteWellWavePacket_add {N : ℕ}
    (mode : Fin N → X → ℂ) (hbar mass width s t : ℝ) (c : Fin N → ℂ) (x : X) :
    finiteInfiniteWellWavePacket mode hbar mass width (s + t) c x =
      finiteInfiniteWellWavePacket mode hbar mass width s
        (finiteSpectralEvolution
          (fun n : Fin N => infiniteWellEnergy hbar mass width n.val) hbar t c) x := by
  exact finiteSpectralWavePacket_add _ _ hbar s t c x

/-- For every nonempty finite infinite-well cutoff, the paper's Gibbs mean-energy identity
`U(β) = -∂β log Z(β)` follows from the shared canonical-ensemble implementation. -/
lemma finiteInfiniteWell_meanEnergy_eq_neg_deriv_log_partition {N : ℕ}
    [MeasurableSpace (Fin N)] [MeasurableSingletonClass (Fin N)] [Nonempty (Fin N)]
    (hbar mass width beta : ℝ) :
    (finiteInfiniteWellCanonicalEnsemble (N := N) hbar mass width).meanEnergyBetaReal beta =
      -deriv (fun b : ℝ => Real.log
        ((finiteInfiniteWellCanonicalEnsemble (N := N)
          hbar mass width).mathematicalPartitionFunctionBetaReal b)) beta := by
  exact CanonicalEnsemble.meanEnergyBetaReal_eq_neg_deriv_log_partition
    (finiteInfiniteWellCanonicalEnsemble (N := N) hbar mass width) beta

/-! ### F.1. Pure-state Wigner kernel -/

/-- The off-diagonal pure-state kernel whose momentum Fourier transform is the Wigner
distribution (paper Eq. (2.1)).  Keeping this kernel separate lets later Fourier-normalization
choices reuse the same phase-space input. -/
def pureStateWignerKernel (psi : ℝ → ℂ) (x y : ℝ) : ℂ :=
  (starRingEnd ℂ) (psi (x - y / 2)) * psi (x + y / 2)

/-- The ordinary pure-state Wigner distribution: the momentum Fourier transform of
`pureStateWignerKernel`, with explicit `ℏ` and the standard `1/(2πℏ)` normalization. -/
noncomputable def pureStateWignerDistribution
    (psi : ℝ → ℂ) (hbar x p : ℝ) : ℂ :=
  (((1 / (2 * Real.pi * hbar) : ℝ) : ℂ)) *
    ∫ y : ℝ, pureStateWignerKernel psi x y *
      Complex.exp (-Complex.I * (((p * y / hbar : ℝ) : ℂ)))

/-- On the zero-displacement diagonal the Wigner kernel is exactly the Born probability
density, before the momentum Fourier transform. -/
@[simp] lemma pureStateWignerKernel_zero (psi : ℝ → ℂ) (x : ℝ) :
    pureStateWignerKernel psi x 0 = (Complex.normSq (psi x) : ℂ) := by
  simp [pureStateWignerKernel, Complex.normSq_eq_conj_mul_self]

/-- Hermitian symmetry of the pure-state Wigner kernel under reversal of relative position. -/
lemma pureStateWignerKernel_star_neg (psi : ℝ → ℂ) (x y : ℝ) :
    (starRingEnd ℂ) (pureStateWignerKernel psi x (-y)) =
      pureStateWignerKernel psi x y := by
  simp only [pureStateWignerKernel, map_mul, starRingEnd_self_apply]
  rw [mul_comm]
  congr 2 <;> ring_nf

/-- A spatial eigenmode with its scalar spectral phase attached. -/
def spectralModeWaveFunction (E hbar t : ℝ) (psi : ℝ → ℂ) (x : ℝ) : ℂ :=
  spectralPhase E hbar t * psi x

/-- The Wigner kernel of one energy eigenmode is stationary: its global unitary phase cancels
between the bra and ket factors. -/
lemma pureStateWignerKernel_spectralModeWaveFunction
    (E hbar t : ℝ) (psi : ℝ → ℂ) (x y : ℝ) :
    pureStateWignerKernel (spectralModeWaveFunction E hbar t psi) x y =
      pureStateWignerKernel psi x y := by
  have hphase :
      (starRingEnd ℂ) (spectralPhase E hbar t) * spectralPhase E hbar t = 1 := by
    rw [Complex.conj_mul']
    simp [spectralPhase_norm]
  simp only [pureStateWignerKernel, spectralModeWaveFunction, map_mul]
  calc
    ((starRingEnd ℂ) (spectralPhase E hbar t) *
          (starRingEnd ℂ) (psi (x - y / 2))) *
        (spectralPhase E hbar t * psi (x + y / 2)) =
        ((starRingEnd ℂ) (spectralPhase E hbar t) * spectralPhase E hbar t) *
          ((starRingEnd ℂ) (psi (x - y / 2)) * psi (x + y / 2)) := by ring
    _ = pureStateWignerKernel psi x y := by simp [hphase, pureStateWignerKernel]

/-- Consequently the full Wigner distribution of a single energy eigenmode is stationary. -/
lemma pureStateWignerDistribution_spectralModeWaveFunction
    (E hbar t : ℝ) (psi : ℝ → ℂ) (x p : ℝ) :
    pureStateWignerDistribution (spectralModeWaveFunction E hbar t psi) hbar x p =
      pureStateWignerDistribution psi hbar x p := by
  simp only [pureStateWignerDistribution]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [pureStateWignerKernel_spectralModeWaveFunction]

end InfiniteWell

end Physlib.QuantumMechanics.Schrodinger.SpectralDynamics

end
