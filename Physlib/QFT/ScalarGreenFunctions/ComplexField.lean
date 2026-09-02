/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.ScalarGreenFunctions.FreeTheory
public import Physlib.QFT.PathIntegral.MeasureExpectation

/-!
# Complex scalar Green functions

This file formalizes Rivers, Section 1.7, at the existing measure-theoretic
path-integral level. A complex scalar and its conjugate are coupled to
independent sources `Jstar` and `J`, and mixed Green functions are indexed by
two multisets: particle and antiparticle insertions.

The construction is compatible with the free Gaussian functional in
`FreeTheory.lean` and with the determinant doubling proved in
`ExternalField.lean`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.ScalarGreenFunctions

open scoped BigOperators
open Physlib.QFT.PathIntegral

variable {α X : Type*} [MeasurableSpace α]

/-- Product of complex-scalar and conjugate-scalar insertions. -/
def chargedFieldMonomial
    (field : α → X → ℂ) (particles antiparticles : Multiset X) : α → ℂ :=
  fun φ =>
    (particles.map (field φ)).prod *
      (antiparticles.map (fun x => star (field φ x))).prod

@[simp] lemma chargedFieldMonomial_empty
    (field : α → X → ℂ) :
    chargedFieldMonomial field 0 0 = fun _ => 1 := by
  funext φ
  simp [chargedFieldMonomial]

/-- Unnormalised mixed charged Green function. -/
def unnormalizedChargedGreenFunction
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ)
    (particles antiparticles : Multiset X) : ℂ :=
  m.unnormalizedExpectation
    (chargedFieldMonomial field particles antiparticles)

/-- Normalised mixed charged Green function. -/
def chargedGreenFunction
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ)
    (particles antiparticles : Multiset X) : ℂ :=
  m.normalizedExpectation
    (chargedFieldMonomial field particles antiparticles)

/-- The zero-leg unnormalised charged Green function is the partition. -/
lemma unnormalizedChargedGreenFunction_empty
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ) :
    unnormalizedChargedGreenFunction m field 0 0 = m.partition := by
  unfold unnormalizedChargedGreenFunction
    MeasurePathIntegralModel.unnormalizedExpectation
    MeasurePathIntegralModel.partition
  simp [chargedFieldMonomial]

@[simp] lemma chargedGreenFunction_empty
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ)
    (hZ : m.partition ≠ 0) :
    chargedGreenFunction m field 0 0 = 1 := by
  change unnormalizedChargedGreenFunction m field 0 0 / m.partition = 1
  rw [unnormalizedChargedGreenFunction_empty]
  exact div_self hZ

section FiniteSources

variable [Fintype X]

/-- Complex scalar source pairing
`Σ_x (Jstar(x) A(x) + J(x) Astar(x))`. -/
def complexScalarSourcePairing
    (field : α → X → ℂ) (J Jstar : X → ℂ) (φ : α) : ℂ :=
  ∑ x, (Jstar x * field φ x + J x * star (field φ x))

@[simp] lemma complexScalarSourcePairing_zero
    (field : α → X → ℂ) (φ : α) :
    complexScalarSourcePairing field (fun _ => 0) (fun _ => 0) φ = 0 := by
  simp [complexScalarSourcePairing]

lemma complexScalarSourcePairing_add_particleSource
    (field : α → X → ℂ) (J₁ J₂ Jstar : X → ℂ) (φ : α) :
    complexScalarSourcePairing field (fun x => J₁ x + J₂ x) Jstar φ =
      complexScalarSourcePairing field J₁ Jstar φ +
        complexScalarSourcePairing field J₂ (fun _ => 0) φ := by
  unfold complexScalarSourcePairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

lemma complexScalarSourcePairing_add_antiparticleSource
    (field : α → X → ℂ) (J Jstar₁ Jstar₂ : X → ℂ) (φ : α) :
    complexScalarSourcePairing field J (fun x => Jstar₁ x + Jstar₂ x) φ =
      complexScalarSourcePairing field J Jstar₁ φ +
        complexScalarSourcePairing field (fun _ => 0) Jstar₂ φ := by
  unfold complexScalarSourcePairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Interacting complex-scalar generating functional `Z[J,Jstar]`. -/
def complexScalarGeneratingFunctional
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ)
    (J Jstar : X → ℂ) : ℂ :=
  m.sourceCoupledPartition (complexScalarSourcePairing field J Jstar)

/-- Connected complex-scalar generating functional. -/
def complexScalarConnectedGeneratingFunctional
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ)
    (J Jstar : X → ℂ) : ℂ :=
  Complex.log (complexScalarGeneratingFunctional m field J Jstar)

@[simp] lemma complexScalarGeneratingFunctional_zero
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ) :
    complexScalarGeneratingFunctional m field (fun _ => 0) (fun _ => 0) =
      m.partition := by
  unfold complexScalarGeneratingFunctional
  have hpair :
      complexScalarSourcePairing field (fun _ => 0) (fun _ => 0) =
        fun _ => 0 := by
    funext φ
    exact complexScalarSourcePairing_zero field φ
  rw [hpair, m.sourceCoupledPartition_zero]

@[simp] lemma complexScalarConnectedGeneratingFunctional_zero
    (m : MeasurePathIntegralModel α) (field : α → X → ℂ) :
    complexScalarConnectedGeneratingFunctional m field
        (fun _ => 0) (fun _ => 0) = Complex.log m.partition := by
  simp [complexScalarConnectedGeneratingFunctional]

end FiniteSources

/-- Complex scalar density `Astar A`, a real nonnegative quantity. -/
def complexScalarDensity (A : ℂ) : ℝ :=
  Complex.normSq A

lemma complexScalarDensity_nonneg (A : ℂ) :
    0 ≤ complexScalarDensity A :=
  Complex.normSq_nonneg A

/-- Quartic interaction depending only on `Astar A`. -/
def complexScalarQuarticPotential (g : ℝ) (A : ℂ) : ℝ :=
  g * complexScalarDensity A ^ 2 / 4

lemma complexScalarQuarticPotential_nonneg
    (g : ℝ) (A : ℂ) (hg : 0 ≤ g) :
    0 ≤ complexScalarQuarticPotential g A := by
  unfold complexScalarQuarticPotential
  positivity

end Physlib.QFT.ScalarGreenFunctions

end
