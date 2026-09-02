/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPoissonField3

public import
  Physlib.QuantumMechanics.ComplexAction.LeviCivita.Tensor

/-!
# Static Poisson fields through the three-dimensional Hodge star

This module equips the Cartesian static-potential carrier with the degree-one/degree-two Hodge
star on its oriented Euclidean spatial slice.  It reuses physlib's public three-dimensional
Levi-Civita tensor and its proved antisymmetry/contraction API.

For the spatial one-form `dΦ`,

`(⋆dΦ)ᵢⱼ = εᵢⱼₖ ∂ₖΦ`.

The coefficient of its exterior derivative is therefore

`(d⋆dΦ)₀₁₂ = ∂₀(⋆dΦ)₁₂ + ∂₁(⋆dΦ)₂₀ + ∂₂(⋆dΦ)₀₁ = ∇²Φ`.

Consequently the existing Poisson law is equivalently a sourced `d⋆dΦ` identity, and the same
potential jet, density, and Newton coupling feed the existing static linearized Einstein equation.

This is a component theorem on an oriented Cartesian Euclidean three-space.  It does not assert a
general curved-manifold Hodge theorem, a Lorentzian Hodge convention, or that Poisson's equation
alone yields an exact nonlinear Einstein spacetime.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock

open Matrix
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionLieAlgebra
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.Tensor
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

/-- The Euclidean three-dimensional Hodge star from one-forms to two-forms. -/
def hodgeStarOneForm3 (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ∑ k, (leviCivita3 i j k : ℝ) * v k

/-- The Euclidean three-dimensional Hodge star from two-forms to one-forms. -/
def hodgeStarTwoForm3 (ω : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  fun k => (1 / 2 : ℝ) * ∑ i, ∑ j, (leviCivita3 i j k : ℝ) * ω i j

/-- The Hodge star of a one-form is antisymmetric. -/
theorem hodgeStarOneForm3_antisymm (v : Fin 3 → ℝ) :
    ∀ i j, hodgeStarOneForm3 v i j = -hodgeStarOneForm3 v j i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hodgeStarOneForm3, Fin.sum_univ_three, leviCivita3]

/-- With the standard `1/2` normalization, the second Hodge star recovers the original one-form. -/
theorem hodgeStarTwoForm3_hodgeStarOneForm3 (v : Fin 3 → ℝ) :
    hodgeStarTwoForm3 (hodgeStarOneForm3 v) = v := by
  funext k
  fin_cases k <;>
    simp [hodgeStarTwoForm3, hodgeStarOneForm3, Fin.sum_univ_three, leviCivita3] <;>
    ring

namespace StaticPotentialJet3

/-- The spatial two-form `⋆dΦ` selected by the jet gradient. -/
def gradientHodgeFlux2 (J : StaticPotentialJet3) : Matrix (Fin 3) (Fin 3) ℝ :=
  hodgeStarOneForm3 J.gradient

/--
The oriented spatial Hodge-flux components are the three Cartesian gradient components:
`(⋆dΦ)₁₂ = ∂₀Φ`, `(⋆dΦ)₂₀ = ∂₁Φ`, and `(⋆dΦ)₀₁ = ∂₂Φ`.
-/
theorem gradientHodgeFlux2_components (J : StaticPotentialJet3) :
    J.gradientHodgeFlux2 1 2 = J.gradient 0
      ∧ J.gradientHodgeFlux2 2 0 = J.gradient 1
      ∧ J.gradientHodgeFlux2 0 1 = J.gradient 2 := by
  simp [gradientHodgeFlux2, hodgeStarOneForm3, Fin.sum_univ_three, leviCivita3]

/-- Applying the complementary Hodge star to the gradient flux recovers `dΦ`. -/
theorem gradientHodgeFlux2_recovers_gradient (J : StaticPotentialJet3) :
    hodgeStarTwoForm3 J.gradientHodgeFlux2 = J.gradient := by
  exact hodgeStarTwoForm3_hodgeStarOneForm3 J.gradient

/--
The derivative in spatial direction `i` of `⋆dΦ`, represented by applying the Hodge star to row
`i` of the jet Hessian.
-/
def gradientHodgeFluxDerivative3
    (J : StaticPotentialJet3) (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  hodgeStarOneForm3 (J.hessian i)

/-- The oriented three-form coefficient `(d⋆dΦ)₀₁₂`. -/
def hodgeFluxDivergence3 (J : StaticPotentialJet3) : ℝ :=
  J.gradientHodgeFluxDerivative3 0 1 2
    + J.gradientHodgeFluxDerivative3 1 2 0
    + J.gradientHodgeFluxDerivative3 2 0 1

/-- The `d⋆dΦ` coefficient is exactly the existing Cartesian Laplacian. -/
theorem hodgeFluxDivergence3_eq_laplacian (J : StaticPotentialJet3) :
    J.hodgeFluxDivergence3 = J.laplacian := by
  simp [hodgeFluxDivergence3, gradientHodgeFluxDerivative3, hodgeStarOneForm3,
    Fin.sum_univ_three, leviCivita3, laplacian]

/-- Poisson's equation is equivalently the sourced static `d⋆dΦ` equation. -/
theorem satisfiesPoisson_iff_hodgeFluxDivergence3
    (J : StaticPotentialJet3) (G ρ : ℝ) :
    J.SatisfiesPoisson G ρ ↔
      J.hodgeFluxDivergence3 = 4 * Real.pi * G * ρ := by
  rw [hodgeFluxDivergence3_eq_laplacian]
  rfl

end StaticPotentialJet3

namespace StaticPoissonField3

/-- Every point of a bundled static Poisson field satisfies the sourced `d⋆dΦ` equation. -/
theorem hodgeFluxDivergence3_at
    (F : StaticPoissonField3) (x : StaticPotentialSpace3) :
    (F.jetAt x).hodgeFluxDivergence3 =
      4 * Real.pi * F.newtonConstant * F.density x := by
  exact (StaticPotentialJet3.satisfiesPoisson_iff_hodgeFluxDivergence3
    (F.jetAt x) F.newtonConstant (F.density x)).1
    (F.jetAt_satisfiesPoisson x)

/--
At each point, the sourced Hodge-flux identity and the static linearized Einstein equation use the
same potential jet, density, and stored Newton coupling.
-/
theorem hodgeFluxDivergence3_and_einsteinFieldEquation_at
    (F : StaticPoissonField3) (c : ℝ) (hc : c ≠ 0) (x : StaticPotentialSpace3) :
    (F.jetAt x).hodgeFluxDivergence3 =
        4 * Real.pi * F.newtonConstant * F.density x
      ∧ einsteinFieldEquation
          ((F.jetAt x).ricci4 c) ((F.jetAt x).scalar4 c) minkowskiMetric4
          (restDustStressEnergy4 (F.density x) c)
          (8 * Real.pi * F.newtonConstant / c ^ 4) := by
  exact ⟨F.hodgeFluxDivergence3_at x, F.einsteinFieldEquation_at c hc x⟩

end StaticPoissonField3

end Physlib.QuantumMechanics.ComplexAction.ComptonClock

end
