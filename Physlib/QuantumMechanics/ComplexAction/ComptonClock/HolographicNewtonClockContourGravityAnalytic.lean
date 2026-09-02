/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity

public import
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3Analytic

/-!
# Analytic-potential capstone for the holographic clock/contour/gravity bridge

This module specializes the typed-jet capstone to a genuine `C²` potential
`Φ : (Fin 3 → ℝ) → ℝ`.  The gradient and Hessian supplied to the weak-field geometry are therefore
the Cartesian components of the first and second Fréchet derivatives at a selected point, and
Hessian symmetry follows from Schwarz's theorem rather than from an independent data-field
assumption.

The physical scope remains the same as the underlying capstone: this is a local, static,
linearized `Fin 4` carrier.  Smoothness of `Φ` does not promote it to an exact nonlinear Einstein
solution, and the complex imaginary-sector equation remains an explicit independent hypothesis.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity

open MeasureTheory
open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.ComptonClock
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

/-!
## C² potential specialization
-/

/--
The complete holographic-Newton/clock/contour/static-gravity chain at a point of a `C²` potential.

Unlike the raw component and typed-jet versions, the gradient and symmetric Hessian here are
actually derived from one potential.  The conclusion explicitly exposes the analytic Cartesian
first derivatives and Laplacian while reusing the jet adapters for the connection, curvature, and
Einstein carriers.
-/
theorem holographicNewton_comptonNagaoLeviCivita_C2Potential_chain
    (Φ : StaticPotentialSpace3 → ℝ) (x : StaticPotentialSpace3)
    (hΦ : ContDiffAt ℝ 2 Φ x)
    (G ℏ c N ρ m η θ ε : ℝ)
    (Λ S : Matrix (Fin 4) (Fin 4) ℝ)
    (hℏ : 0 < ℏ) (hc : 0 < c) (hm : 0 < m) (hη : 0 < η)
    (hG : G ≠ 0) (hε : 0 < ε)
    (hN : N = holographicBits
      (sphereArea (entropicProperDistance m c ℏ η)) G ℏ c)
    (hWeak : weakFieldRicci00 (laplacianAt3 Φ x) c =
      4 * Real.pi * G * ρ / c ^ 2)
    (hImaginary : Λ = (8 * Real.pi * G / c ^ 4) • S) :
    G = sphereArea (entropicProperDistance m c ℏ η) * c ^ 3 / (ℏ * N)
    ∧ 8 * Real.pi * G / c ^ 4 =
        8 * Real.pi * (sphereArea (entropicProperDistance m c ℏ η) / N) / (ℏ * c)
    ∧ (StaticPotentialJet3.ofFunctionAt Φ x hΦ).SatisfiesPoisson G ρ
    ∧ deBroglieFrequency (einsteinEnergy m c (m * c * Real.sinh θ)) ℏ =
        Real.cosh θ * comptonFrequency m c ℏ
    ∧ energyMomentumComplex m c (m * c * Real.sinh θ) =
        Complex.exp (massShellContourAngle θ * Complex.I) *
          (massShellContourRadius m c θ : ℂ)
    ∧ (∫ s : ℝ,
        deltaEpsC ε (Complex.exp (massShellContourAngle θ * Complex.I) * s) *
          Complex.exp (massShellContourAngle θ * Complex.I)) = 1
    ∧ ((StaticPotentialJet3.ofFunctionAt Φ x hΦ).leviCivita4 c 1 0 0 =
          firstSpatialDerivativeAt3 Φ x 0 / c ^ 2
      ∧ (StaticPotentialJet3.ofFunctionAt Φ x hΦ).leviCivita4 c 2 0 0 =
          firstSpatialDerivativeAt3 Φ x 1 / c ^ 2
      ∧ (StaticPotentialJet3.ofFunctionAt Φ x hΦ).leviCivita4 c 3 0 0 =
          firstSpatialDerivativeAt3 Φ x 2 / c ^ 2)
    ∧ (StaticPotentialJet3.ofFunctionAt Φ x hΦ).leviCivita4 c =
        weakFieldLinearizedConnection4Spatial
          (firstSpatialDerivativeAt3 Φ x 0)
          (firstSpatialDerivativeAt3 Φ x 1)
          (firstSpatialDerivativeAt3 Φ x 2) c
    ∧ ricciMatrixFromConnection (fun _ => 0)
        ((StaticPotentialJet3.ofFunctionAt Φ x hΦ).leviCivitaDeriv4 c) =
      !![laplacianAt3 Φ x / c ^ 2, 0, 0, 0;
         0, laplacianAt3 Φ x / c ^ 2, 0, 0;
         0, 0, laplacianAt3 Φ x / c ^ 2, 0;
         0, 0, 0, laplacianAt3 Φ x / c ^ 2]
    ∧ einsteinFieldEquation
        ((StaticPotentialJet3.ofFunctionAt Φ x hΦ).ricci4 c)
        ((StaticPotentialJet3.ofFunctionAt Φ x hΦ).scalar4 c)
        minkowskiMetric4 (restDustStressEnergy4 ρ c) (8 * Real.pi * G / c ^ 4)
    ∧ complexEinsteinFieldEquation
        ((StaticPotentialJet3.ofFunctionAt Φ x hΦ).einstein4 c) Λ
        (restDustStressEnergy4 ρ c) S (8 * Real.pi * G / c ^ 4) := by
  have hWeakJet :
      weakFieldRicci00 (StaticPotentialJet3.ofFunctionAt Φ x hΦ).laplacian c =
        4 * Real.pi * G * ρ / c ^ 2 := by
    simpa only [StaticPotentialJet3.laplacian_ofFunctionAt] using hWeak
  simpa only [StaticPotentialJet3.gradient_ofFunctionAt,
    StaticPotentialJet3.laplacian_ofFunctionAt] using
    holographicNewton_comptonNagaoLeviCivita_staticPotentialJet3_chain
      (StaticPotentialJet3.ofFunctionAt Φ x hΦ)
      G ℏ c N ρ m η θ ε Λ S hℏ hc hm hη hG hε hN hWeakJet hImaginary

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity

end
