/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources

/-!
# Finite point sources in the distributional weak-field Einstein `00` equation

This module applies the scalar distributional Einstein-Poisson equivalence to the finite Newton
point-source construction.  For

`ρ = ∑ i, Mᵢ δ_(xᵢ)`

and the corresponding finite superposition of inverse-radius potential distributions, it proves

`G₀₀^(1)[Φ] = (8πG/c⁴) T₀₀[ρ]`.

The result is then included in the established total-mass holographic-screen chain.  This is a
static scalar linearized `00` statement.  It is not a smooth rest-dust solution, a full
distribution-valued Einstein tensor, or an exact nonlinear multi-body spacetime.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourcesEinstein00

open scoped Space
open Physlib
open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.DistributionalWeakFieldEinstein00
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSources
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HorizonNagaoContourBitEinstein
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa

/-! ## A. Finite-source distributional Einstein `00` equation -/

/-- The finite Newton potential and finite Dirac mass density satisfy the scalar linearized EFE. -/
lemma finiteNewtonPointSources_distributionalEinstein00
    {ι : Type*} [Fintype ι] (G c : ℝ) (M : ι → ℝ) (x : ι → Space 3)
    (hc : c ≠ 0) :
    DistributionalWeakFieldEinstein00Equation3 G c
      (finiteNewtonPotentialDistribution3 G M x)
      (finitePointMassDistribution3 M x) :=
  distributionalWeakFieldEinstein00Equation3_of_poisson G c
    (finiteNewtonPotentialDistribution3 G M x)
    (finitePointMassDistribution3 M x) hc
    (finiteNewtonPotentialDistribution3_laplacian G M x)

/-- A common source translation preserves the finite-source scalar linearized EFE. -/
lemma finiteNewtonPointSources_distributionalEinstein00_translate
    {ι : Type*} [Fintype ι] (a : EuclideanSpace ℝ (Fin 3))
    (G c : ℝ) (M : ι → ℝ) (x : ι → Space 3) (hc : c ≠ 0) :
    DistributionalWeakFieldEinstein00Equation3 G c
      (finiteNewtonPotentialDistribution3 G M (translatePointConfiguration3 a x))
      (finitePointMassDistribution3 M (translatePointConfiguration3 a x)) := by
  rw [← finiteNewtonPotentialDistribution3_translate,
    ← finitePointMassDistribution3_translate]
  exact (finiteNewtonPointSources_distributionalEinstein00 G c M x hc).translate a

/-! ## B. Distributional Einstein-to-entropic-screen chain -/

/--
The finite-source scalar linearized Einstein equation, both forms of its Poisson source law, and
the total-mass entropic-screen identities coexist in one audited chain.

The screen identities are evaluated at `∑ i, M i`; the theorem does not claim that the selected
screen encloses the source configuration or satisfies an arbitrary-surface flux law.
-/
lemma finiteNewtonPointSources_distributionalEinstein00_bitCount_chain
    {ι : Type*} [Fintype ι] (S_R G ℏ c N R : ℝ)
    (M : ι → ℝ) (x : ι → Space 3)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : 0 < R)
    (hbits : N = holographicBits (sphereArea R) G ℏ c) :
    DistributionalWeakFieldEinstein00Equation3 G c
        (finiteNewtonPotentialDistribution3 G M x)
        (finitePointMassDistribution3 M x)
      ∧ Δᵈ (finiteNewtonPotentialDistribution3 G M x) =
        (4 * Real.pi * G) • finitePointMassDistribution3 M x
      ∧ Δᵈ (finiteNewtonPotentialDistribution3 G M x) =
        ∑ i, (4 * Real.pi * G * M i) • Physlib.Distribution.diracDelta ℝ (x i)
      ∧ G * finiteTotalMass M / R ^ 2 =
        4 * Real.pi * finiteTotalMass M * c ^ 3 / (ℏ * N)
      ∧ ‖nnPathWeight S_R (horizonImaginaryAction G c (sphereArea R)) ℏ‖ =
        Real.exp (-(N / 4))
      ∧ 8 * Real.pi * G / c ^ 4 =
        8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  exact ⟨finiteNewtonPointSources_distributionalEinstein00 G c M x hc,
    finiteNewtonPointSources_bitCount_gravity_chain S_R G ℏ c N R M x
      hℏ hc hG hR hbits⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.FiniteNewtonPointSourcesEinstein00

end
