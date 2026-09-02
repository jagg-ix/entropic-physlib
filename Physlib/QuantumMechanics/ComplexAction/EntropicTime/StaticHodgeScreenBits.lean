/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
public import
  Physlib.QuantumMechanics.ComplexAction.ComptonClock.HomogeneousDensityPoissonField3

public import
  Physlib.QuantumMechanics.ComplexAction.EntropicTime.HorizonNagaoContourBitEinstein

/-!
# From a local static Hodge source to a holographic spherical screen

The static Cartesian formalization already proves the local differential-form identity

`d⋆dΦ = ∇²Φ = 4πGρ`

and connects the same potential jet to the linearized Einstein equation.  The entropic-time
formalization separately proves that a spherical screen bit count controls the Newton acceleration,
the Nagao–Nielsen horizon weight, and the Einstein coupling.  This module closes the missing
homogeneous spherical specialization between those two developments.

For the explicit constant-density quadratic potential

`Φ(x) = (2πGρ/3) |x|²`,

the outward radial derivative on a sphere of radius `R` is constant.  Multiplying this constant
normal component by `sphereArea R` gives an algebraic spherical Hodge flux and proves

`flux = 4πG M(R)`,

where `M(R) = 4πρR³/3`.  At nonzero radius, the same boundary derivative is `G M(R)/R²`, so the
existing holographic-bit theorem rewrites it as `4πM(R)c³/(ℏN)`.

This is the exact homogeneous/isotropic specialization of the proved Cartesian Hodge law.  The
quantity called a spherical flux below is defined as the constant boundary normal component times
the sphere area.  No general Stokes theorem, arbitrary surface integral, isolated-source exterior
solution, asymptotic flatness statement, or nonlinear Einstein solution is asserted.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits

open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.ComptonClock
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HorizonNagaoContourBitEinstein
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa

/-! ## A. Homogeneous mass and the radial Hodge-flux density -/

/-- The mass assigned to a radius-`R` Euclidean ball with constant density `ρ`. -/
def homogeneousBallMass3 (ρ R : ℝ) : ℝ :=
  4 * Real.pi * ρ * R ^ 3 / 3

/--
The constant outward radial derivative of the homogeneous quadratic potential on the sphere of
radius `R`.
-/
def homogeneousSphereRadialPotentialDerivative3 (G ρ R : ℝ) : ℝ :=
  2 * homogeneousDensityPotentialCoefficient G ρ * R

/-- The radial derivative has the explicit constant-density form `(4πGρ/3)R`. -/
lemma homogeneousSphereRadialPotentialDerivative3_eq
    (G ρ R : ℝ) :
    homogeneousSphereRadialPotentialDerivative3 G ρ R =
      4 * Real.pi * G * ρ * R / 3 := by
  unfold homogeneousSphereRadialPotentialDerivative3 homogeneousDensityPotentialCoefficient
  ring

/--
At nonzero radius, the boundary radial derivative is Newton's acceleration magnitude
`G M(R)/R²` for the mass enclosed by the homogeneous sphere.
-/
lemma homogeneousSphereRadialPotentialDerivative3_eq_newtonAcceleration
    (G ρ R : ℝ) (hR : R ≠ 0) :
    homogeneousSphereRadialPotentialDerivative3 G ρ R =
      G * homogeneousBallMass3 ρ R / R ^ 2 := by
  rw [homogeneousSphereRadialPotentialDerivative3_eq]
  unfold homogeneousBallMass3
  field_simp

/-! ## B. The spherical Hodge flux and Gauss identity -/

/--
The homogeneous spherical Hodge flux: the constant outward normal component of `dΦ` multiplied by
the sphere area.
-/
def homogeneousSphereHodgeFlux3 (G ρ R : ℝ) : ℝ :=
  sphereArea R * homogeneousSphereRadialPotentialDerivative3 G ρ R

/--
For the homogeneous model, the boundary Hodge flux is exactly `4πG` times the enclosed mass.
This is an algebraic spherical specialization, not a general divergence theorem.
-/
lemma homogeneousSphereHodgeFlux3_eq_fourPiG_mass
    (G ρ R : ℝ) :
    homogeneousSphereHodgeFlux3 G ρ R =
      4 * Real.pi * G * homogeneousBallMass3 ρ R := by
  unfold homogeneousSphereHodgeFlux3 sphereArea
  rw [homogeneousSphereRadialPotentialDerivative3_eq]
  unfold homogeneousBallMass3
  ring

/--
At a holographic screen, the same radial Hodge-flux density is the bit-count form of universal
free fall.
-/
lemma homogeneousSphereRadialPotentialDerivative3_bitForm
    (G ρ ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c) :
    homogeneousSphereRadialPotentialDerivative3 G ρ R =
      4 * Real.pi * homogeneousBallMass3 ρ R * c ^ 3 / (ℏ * N) := by
  rw [homogeneousSphereRadialPotentialDerivative3_eq_newtonAcceleration G ρ R hR]
  exact FreeFallUniversalityFisherMass.freeFall_acceleration_bitForm
    G (homogeneousBallMass3 ρ R) ℏ c N R hℏ hc hG hR hbits

/-! ## C. Local Hodge source, screen bits, contour, and Einstein equation -/

/--
The complete local-to-screen chain for the explicit homogeneous field.

One stored Newton coupling `G` and one screen bit count `N` simultaneously provide:

1. the local sourced Hodge identity `d⋆dΦ = 4πGρ`;
2. the spherical flux law `flux = 4πG M(R)`;
3. the boundary acceleration in bit form;
4. the horizon Nagao–Nielsen modulus `e^{-N/4}`;
5. the Einstein coupling in area-per-bit form; and
6. the pointwise static linearized Einstein equation for the same field and density.

The result composes existing proved carriers.  It does not promote the homogeneous quadratic model
to an isolated body or an exact nonlinear spacetime.
-/
lemma homogeneousHodgeScreen_bitCount_gravity_chain
    (S_R G ρ ℏ c N R : ℝ) (x : StaticPotentialSpace3)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c) :
    ((homogeneousDensityPoissonField3 G ρ).jetAt x).hodgeFluxDivergence3 =
        4 * Real.pi * G * ρ
      ∧ homogeneousSphereHodgeFlux3 G ρ R =
        4 * Real.pi * G * homogeneousBallMass3 ρ R
      ∧ homogeneousSphereRadialPotentialDerivative3 G ρ R =
        4 * Real.pi * homogeneousBallMass3 ρ R * c ^ 3 / (ℏ * N)
      ∧ ‖nnPathWeight S_R (horizonImaginaryAction G c (sphereArea R)) ℏ‖ =
        Real.exp (-(N / 4))
      ∧ 8 * Real.pi * G / c ^ 4 =
        8 * Real.pi * (sphereArea R / N) / (ℏ * c)
      ∧ einsteinFieldEquation
          (((homogeneousDensityPoissonField3 G ρ).jetAt x).ricci4 c)
          (((homogeneousDensityPoissonField3 G ρ).jetAt x).scalar4 c)
          minkowskiMetric4 (restDustStressEnergy4 ρ c)
          (8 * Real.pi * G / c ^ 4) := by
  have hLocalAndEFE :=
    (homogeneousDensityPoissonField3 G ρ).hodgeFluxDivergence3_and_einsteinFieldEquation_at
      c hc x
  have hGravity :=
    bitCount_governs_gravity S_R G (homogeneousBallMass3 ρ R) ℏ c N R
      hℏ hc hG hR hbits
  refine ⟨?_, homogeneousSphereHodgeFlux3_eq_fourPiG_mass G ρ R,
    homogeneousSphereRadialPotentialDerivative3_bitForm G ρ ℏ c N R
      hℏ hc hG hR hbits,
    hGravity.1, hGravity.2.2, ?_⟩
  · simpa using hLocalAndEFE.1
  · simpa using hLocalAndEFE.2

/-! ## D. Inference-variance coupling on the homogeneous Hodge screen -/

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

/-- The independently counted Compton screen fixes `G = ℏcσ₀⁴` and the existing
homogeneous theorem carries that same coupling through local Hodge divergence,
spherical flux, boundary acceleration, horizon damping, Einstein coupling, and the
pointwise static linearized Einstein equation. -/
@[zil_level bridge_theorem]
lemma comptonCellInference_homogeneousHodgeScreen_gravity_chain
    (S_R ρ ℏ c σ₀ η : ℝ) (x : StaticPotentialSpace3)
    (hℏ : 0 < ℏ) (hc : 0 < c) (hσ : 0 < σ₀) (hη : 0 < η) :
    let m := inferenceMass σ₀
    let R := entropicProperDistance m c ℏ η
    let N := comptonCellBits m c ℏ η
    let G := ℏ * c * σ₀ ^ 4
    G = sphereArea R * c ^ 3 / (ℏ * N)
      ∧ ((homogeneousDensityPoissonField3 G ρ).jetAt x).hodgeFluxDivergence3 =
          4 * Real.pi * G * ρ
      ∧ homogeneousSphereHodgeFlux3 G ρ R =
          4 * Real.pi * G * homogeneousBallMass3 ρ R
      ∧ homogeneousSphereRadialPotentialDerivative3 G ρ R =
          4 * Real.pi * homogeneousBallMass3 ρ R * c ^ 3 / (ℏ * N)
      ∧ ‖nnPathWeight S_R (horizonImaginaryAction G c (sphereArea R)) ℏ‖ =
          Real.exp (-(N / 4))
      ∧ 8 * Real.pi * G / c ^ 4 =
          8 * Real.pi * (sphereArea R / N) / (ℏ * c)
      ∧ einsteinFieldEquation
          (((homogeneousDensityPoissonField3 G ρ).jetAt x).ricci4 c)
          (((homogeneousDensityPoissonField3 G ρ).jetAt x).scalar4 c)
          minkowskiMetric4 (restDustStressEnergy4 ρ c)
          (8 * Real.pi * G / c ^ 4) := by
  dsimp only
  have hm : 0 < inferenceMass σ₀ := by rw [inferenceMass]; positivity
  have hR : 0 < entropicProperDistance (inferenceMass σ₀) c ℏ η :=
    entropicProperDistance_pos _ _ _ _ hm hc hℏ hη
  have hG : ℏ * c * σ₀ ^ 4 ≠ 0 := by positivity
  have hlog : Real.log (schmidtNumber η) ≠ 0 :=
    ne_of_gt (Real.log_pos (schmidtNumber_gt_one η hη))
  have hArea :=
    (newtonG_from_positionVariance σ₀ c ℏ η hσ.ne' hc.ne' hℏ.ne' hlog).symm
  have hbits :=
    (holographicBits_eq_comptonCellBits_of_inferenceVariance
      c ℏ σ₀ η hσ.ne' hc.ne' hℏ.ne').symm
  exact ⟨hArea, homogeneousHodgeScreen_bitCount_gravity_chain
    S_R (ℏ * c * σ₀ ^ 4) ρ ℏ c
      (comptonCellBits (inferenceMass σ₀) c ℏ η)
      (entropicProperDistance (inferenceMass σ₀) c ℏ η) x
      hℏ.ne' hc.ne' hG hR.ne' hbits⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits

end
