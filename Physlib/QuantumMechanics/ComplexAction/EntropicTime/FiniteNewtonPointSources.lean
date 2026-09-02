/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux

/-!
# Finite Newton point sources

This module extends the translated isolated Newton kernel to a finite family of point sources.
It uses only the linear structure already present on distributions:

* the point-mass distribution is the finite sum `∑ i, M i • δ_(x i)`;
* the potential distribution is the finite sum of the translated inverse-radius kernels;
* the distributional Laplacian is
  `Δᵈ Φ = ∑ i, (4π G M i) • δ_(x i) = (4πG) • ρ`.

The complete source configuration and its potential are covariant under a common spatial
translation. The final entropic-screen bridge uses the total mass `∑ i, M i` in the existing
holographic bit identities.

No enclosing-surface flux theorem is asserted here. In particular, linear superposition of
distributional sources does not by itself prove that an arbitrary screen encloses every source,
nor does it turn the Dirac source distribution into a smooth rest-dust field or an exact nonlinear
Einstein solution.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources

open scoped Space
open Physlib
open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HorizonNagaoContourBitEinstein
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa

/-! ## A. Finite source and potential distributions -/

/-- The distributional mass density of finitely many point sources. -/
def finitePointMassDistribution3 {ι : Type*} [Fintype ι]
    (M : ι → ℝ) (x : ι → Space 3) : (Space 3) →d[ℝ] ℝ :=
  ∑ i, M i • Physlib.Distribution.diracDelta ℝ (x i)

/-- The finite superposition of translated isolated Newton potential distributions. -/
def finiteNewtonPotentialDistribution3 {ι : Type*} [Fintype ι]
    (G : ℝ) (M : ι → ℝ) (x : ι → Space 3) : (Space 3) →d[ℝ] ℝ :=
  ∑ i, isolatedNewtonPotentialDistribution3At G (M i) (x i)

/-- The total mass of a finite point-source configuration. -/
def finiteTotalMass {ι : Type*} [Fintype ι] (M : ι → ℝ) : ℝ :=
  ∑ i, M i

/-! ## B. The finite distributional Poisson law -/

/-- The Laplacian of the finite potential is the sum of its individual Dirac sources. -/
lemma finiteNewtonPotentialDistribution3_laplacian_expanded
    {ι : Type*} [Fintype ι] (G : ℝ) (M : ι → ℝ) (x : ι → Space 3) :
    Δᵈ (finiteNewtonPotentialDistribution3 G M x) =
      ∑ i, (4 * Real.pi * G * M i) • Physlib.Distribution.diracDelta ℝ (x i) := by
  rw [finiteNewtonPotentialDistribution3, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact isolatedNewtonPotentialDistribution3At_laplacian G (M i) (x i)

/-- Factored finite-source Poisson law `Δᵈ Φ = (4πG) • ρ`. -/
lemma finiteNewtonPotentialDistribution3_laplacian
    {ι : Type*} [Fintype ι] (G : ℝ) (M : ι → ℝ) (x : ι → Space 3) :
    Δᵈ (finiteNewtonPotentialDistribution3 G M x) =
      (4 * Real.pi * G) • finitePointMassDistribution3 M x := by
  rw [finiteNewtonPotentialDistribution3_laplacian_expanded,
    finitePointMassDistribution3, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul]

/-! ## C. Translation covariance of the complete configuration -/

/-- A common translation of every source point in a finite configuration. -/
def translatePointConfiguration3 {ι : Type*}
    (a : EuclideanSpace ℝ (Fin 3)) (x : ι → Space 3) : ι → Space 3 :=
  fun i => a +ᵥ x i

/-- Translating an isolated potential translates its source point by the same vector. -/
lemma isolatedNewtonPotentialDistribution3At_translate
    (a : EuclideanSpace ℝ (Fin 3)) (G M : ℝ) (x₀ : Space 3) :
    Space.distTranslate a (isolatedNewtonPotentialDistribution3At G M x₀) =
      isolatedNewtonPotentialDistribution3At G M (a +ᵥ x₀) := by
  rw [isolatedNewtonPotentialDistribution3At, isolatedNewtonPotentialDistribution3At,
    Space.distTranslate_add]
  congr 1

/-- The finite point-mass distribution is covariant under a common source translation. -/
lemma finitePointMassDistribution3_translate
    {ι : Type*} [Fintype ι] (a : EuclideanSpace ℝ (Fin 3))
    (M : ι → ℝ) (x : ι → Space 3) :
    Space.distTranslate a (finitePointMassDistribution3 M x) =
      finitePointMassDistribution3 M (translatePointConfiguration3 a x) := by
  rw [finitePointMassDistribution3, finitePointMassDistribution3, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, Space.distTranslate_diracDelta]
  rfl

/-- The finite Newton potential is covariant under a common source translation. -/
lemma finiteNewtonPotentialDistribution3_translate
    {ι : Type*} [Fintype ι] (a : EuclideanSpace ℝ (Fin 3))
    (G : ℝ) (M : ι → ℝ) (x : ι → Space 3) :
    Space.distTranslate a (finiteNewtonPotentialDistribution3 G M x) =
      finiteNewtonPotentialDistribution3 G M (translatePointConfiguration3 a x) := by
  rw [finiteNewtonPotentialDistribution3, finiteNewtonPotentialDistribution3, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact isolatedNewtonPotentialDistribution3At_translate a G (M i) (x i)

/-! ## D. Finite sources and the entropic screen -/

/--
For a finite point-source configuration and a positive-radius holographic screen, the finite
distributional Poisson law and its expanded Dirac form coexist with the established screen
identities evaluated at the total mass.

This statement does not assert that the chosen screen geometrically encloses the sources and
therefore does not identify a surface flux with the total Dirac coefficient.
-/
lemma finiteNewtonPointSources_bitCount_gravity_chain
    {ι : Type*} [Fintype ι] (S_R G ℏ c N R : ℝ)
    (M : ι → ℝ) (x : ι → Space 3)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : 0 < R)
    (hbits : N = holographicBits (sphereArea R) G ℏ c) :
    Δᵈ (finiteNewtonPotentialDistribution3 G M x) =
        (4 * Real.pi * G) • finitePointMassDistribution3 M x
      ∧ Δᵈ (finiteNewtonPotentialDistribution3 G M x) =
        ∑ i, (4 * Real.pi * G * M i) • Physlib.Distribution.diracDelta ℝ (x i)
      ∧ G * finiteTotalMass M / R ^ 2 =
        4 * Real.pi * finiteTotalMass M * c ^ 3 / (ℏ * N)
      ∧ ‖nnPathWeight S_R (horizonImaginaryAction G c (sphereArea R)) ℏ‖ =
        Real.exp (-(N / 4))
      ∧ 8 * Real.pi * G / c ^ 4 =
        8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  have hGravity :=
    bitCount_governs_gravity S_R G (finiteTotalMass M) ℏ c N R
      hℏ hc hG hR.ne' hbits
  exact ⟨finiteNewtonPotentialDistribution3_laplacian G M x,
    finiteNewtonPotentialDistribution3_laplacian_expanded G M x,
    hGravity.2.1, hGravity.1, hGravity.2.2⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources

end
