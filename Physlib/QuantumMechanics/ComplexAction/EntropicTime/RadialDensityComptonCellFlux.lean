/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ComptonCellIsolatedNewtonFlux
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
meta import Zil

/-!
# The general radial mass density: Gauss's law for the smooth-`ρ(r)` source

The isolated-source layer (`IsolatedNewtonHodgeSphereFlux`) carries the genuine analytic content of
Newtonian gravity for a single mass: the outward field `GM x/‖x‖³` has an *actual parameterized
surface integral* through the radius-`R` sphere equal to `4πGM`
(`isolatedNewtonExteriorField3At_sphereFlux`, a Bochner integral against the unit-sphere angular
measure `volume.toSphere` whose total mass `4π` is proved), and the singular kernel `-GM/‖x‖`
satisfies the distributional Poisson law `ΔΦ = 4πGM·δ` derived from the proved fundamental solution
`Space.distLaplacian_fundamentalSolution_norm_zpow`.

This module reaches the **spatially varying radial density** `ρ(r)` through those genuine carriers.
The enclosed mass of the radius-`R` ball is the shell integral

  `M(R) = ∫₀^R 4πr²·ρ(r) dr`   (`radialBallMass`),

which reduces to the homogeneous ball mass when `ρ` is constant (`radialBallMass_const`). For a
spherically-symmetric source, Gauss's law makes the enclosing-sphere flux `4πG·M(R)`: the field on
the enclosing sphere is that of the enclosed mass `M(R)` placed at the center, and its genuine
surface integral is `4πG·M(R)` (`radialEnclosedMass_sphereFlux`). Feeding the `G`-free Compton-cell
coupling `G = ℏc·σ₀⁴` and instantiating the isolated-source gravity chain at the enclosed mass gives,
in one statement, the area-per-bit coupling, the genuine spherical surface flux `4πG·M(R)`, its
distributional Poisson law `ΔΦ = (flux)·δ`, the Nagao–Nielsen horizon damping, and the Einstein
coupling (`comptonCellInference_radialDensity_enclosingFlux`).

**What is derived, and what remains.** For the spherically-symmetric density the *local* Poisson
equation `∇²Φ = 4πGρ` is derived pointwise. The enclosed mass differentiates back to the density
shell, `M′(R) = 4πR²·ρ(R)`, by the fundamental theorem of calculus (`radialBallMass_hasDerivAt`), so
the radial divergence of the enclosed-mass Newton field `a(r) = G·M(r)/r²` equals `4πG·ρ(R)`
(`radialEnclosedMass_poisson`, `radialField_poisson_divergence`) — the varying-density generalization
of the constant-density pointwise Poisson law `laplacianAt3_homogeneousDensityPotential`. The
enclosing-sphere flux is likewise the genuine Bochner surface integral `4πG·M(R)`
(`radialEnclosedMass_sphereFlux`) and its distributional source law the genuine fundamental-solution
law. What remains genuinely absent — in both this repository and Mathlib — is the general
*non-symmetric* convolution potential `Φ = kernel ∗ ρ` with `Δφ = 4πGρ`: there is no
distributional-convolution operator, Riesz/Newtonian potential, or `n`-dimensional harmonic
mean-value to assemble it from. This module also does not fit `σ₀` to the measured value of `G`.

## References

* Companions: `EntropicTime.IsolatedNewtonHodgeSphereFlux` (the genuine spherical surface flux and
  distributional Poisson law of the isolated source), `EntropicTime.ComptonCellIsolatedNewtonFlux`
  (the isolated-source gravity chain at `G = ℏc·σ₀⁴`), `EntropicTime.StaticHodgeScreenBits`
  (the homogeneous constant-`ρ` ball), `ComptonClock.ComptonCellNewtonConstant`
  (`G = ℏc·σ₀⁴` from the `G`-free Compton-cell bit count).
-/

set_option autoImplicit false

open MeasureTheory
open scoped Space
open Physlib
open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ComptonCellIsolatedNewtonFlux
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux

/-- The enclosed mass of the radius-`R` ball for a **radial density profile** `ρ(r)`: the shell
integral `M(R) = ∫₀^R 4π r² ρ(r) dr`. -/
noncomputable def radialBallMass (ρ : ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..R, 4 * Real.pi * r ^ 2 * ρ r

/-- **[The radial enclosed mass reduces to the homogeneous ball]** for a constant density `ρ₀` the
shell integral gives `(4/3)πR³ρ₀`. -/
@[zil_level physical_theorem]
theorem radialBallMass_const (ρ₀ R : ℝ) :
    radialBallMass (fun _ => ρ₀) R = homogeneousBallMass3 ρ₀ R := by
  unfold radialBallMass homogeneousBallMass3
  rw [show (fun r : ℝ => 4 * Real.pi * r ^ 2 * ρ₀) = (fun r : ℝ => 4 * Real.pi * ρ₀ * r ^ 2)
      from funext fun r => by ring, intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  try ring

/-- **[The enclosed mass differentiates back to the density shell]** for a continuous radial density
the fundamental theorem of calculus gives `M'(R) = 4πR²·ρ(R)`: the derivative of the enclosed mass is
the mass of the surface shell. This is the differential heart of Newton's theorem, derived from the
shell integral rather than assumed. -/
@[zil_level physical_theorem]
theorem radialBallMass_hasDerivAt (ρ : ℝ → ℝ) (hρ : Continuous ρ) (R : ℝ) :
    HasDerivAt (radialBallMass ρ) (4 * Real.pi * R ^ 2 * ρ R) R := by
  have hcont : Continuous (fun r : ℝ => 4 * Real.pi * r ^ 2 * ρ r) := by fun_prop
  unfold radialBallMass
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt

/-- **[The radial Poisson equation for the continuous density]** `(r²·a)′ = 4πG·r²·ρ`, where the
enclosed-mass Newton acceleration is `a(r) = G·M(r)/r²` so that `r²·a(r) = G·M(r)`. This is Poisson's
equation `∇²Φ = 4πGρ` in spherically-symmetric radial form, derived pointwise from the enclosed-mass
integral via the fundamental theorem of calculus — not assumed as a structure field. -/
@[zil_level physical_theorem]
theorem radialEnclosedMass_poisson (G : ℝ) (ρ : ℝ → ℝ) (hρ : Continuous ρ) (R : ℝ) :
    HasDerivAt (fun r => G * radialBallMass ρ r) (4 * Real.pi * G * R ^ 2 * ρ R) R := by
  have h := (radialBallMass_hasDerivAt ρ hρ R).const_mul G
  rw [show 4 * Real.pi * G * R ^ 2 * ρ R = G * (4 * Real.pi * R ^ 2 * ρ R) from by ring]
  exact h

/-- **[The local Gauss law `∇·a = 4πGρ` for the continuous radial density]** dividing the derivative
`(r²·a)′` by `r²` gives the three-dimensional radial divergence of the enclosed-mass Newton field
`a(r) = G·M(r)/r²`, and it equals `4πG·ρ(R)` pointwise — Poisson's equation for the smoothly varying
radial density. -/
@[zil_level physical_theorem]
theorem radialField_poisson_divergence
    (G : ℝ) (ρ : ℝ → ℝ) (hρ : Continuous ρ) (R : ℝ) (hR : R ≠ 0) :
    deriv (fun r => G * radialBallMass ρ r) R / R ^ 2 = 4 * Real.pi * G * ρ R := by
  rw [(radialEnclosedMass_poisson G ρ hρ R).deriv]
  field_simp
  try ring

/-- **[Gauss's law for the radial density]** the genuine parameterized surface integral of the
enclosed-mass exterior field through the enclosing sphere of radius `R` is `4πG·M(R)`. This is the
real Bochner flux integral of `IsolatedNewtonHodgeSphereFlux` evaluated at the enclosed mass, not an
area-times-acceleration definition. -/
@[zil_level physical_theorem]
theorem radialEnclosedMass_sphereFlux (G : ℝ) (ρ : ℝ → ℝ) (x₀ : Space 3) (R : ℝ) (hR : 0 < R) :
    sphereFluxIntegral3At x₀ R (isolatedNewtonExteriorField3At G (radialBallMass ρ R) x₀) =
      4 * Real.pi * G * radialBallMass ρ R :=
  isolatedNewtonExteriorField3At_sphereFlux G (radialBallMass ρ R) R x₀ hR

/-- **[The Compton-cell coupling reaches the general radial-density source through Gauss's law]** the
`G`-free Compton-cell count fixes `G = ℏc·σ₀⁴`; instantiating the isolated-source gravity chain at
the enclosed mass `M(R) = radialBallMass ρ R` then gives, for the spatially-varying continuous
source, the area-per-bit coupling `G = 𝒜c³/(ℏN)`, the distributional Poisson law
`ΔΦ = (surface flux)·δ`, the genuine spherical surface flux `4πG·M(R)`, the bit-count acceleration
`G·M(R)/R² = 4πM(R)c³/(ℏN)`, the Nagao–Nielsen horizon damping, and the Einstein coupling — with the
surface flux the actual Bochner integral and the Poisson law the genuine distributional
fundamental-solution law. -/
@[zil_level physical_theorem]
theorem comptonCellInference_radialDensity_enclosingFlux
    (ρ : ℝ → ℝ) (S_R c ℏ σ₀ η : ℝ) (x₀ : Space 3)
    (hℏ : 0 < ℏ) (hc : 0 < c) (hσ : 0 < σ₀) (hη : 0 < η) :
    let m := inferenceMass σ₀
    let R := entropicProperDistance m c ℏ η
    let N := comptonCellBits m c ℏ η
    let G := ℏ * c * σ₀ ^ 4
    let M := radialBallMass ρ R
    G = sphereArea R * c ^ 3 / (ℏ * N)
      ∧ Δᵈ (isolatedNewtonPotentialDistribution3At G M x₀) =
          sphereFluxIntegral3At x₀ R (isolatedNewtonExteriorField3At G M x₀) •
            Physlib.Distribution.diracDelta ℝ x₀
      ∧ sphereFluxIntegral3At x₀ R (isolatedNewtonExteriorField3At G M x₀) =
          4 * Real.pi * G * M
      ∧ G * M / R ^ 2 = 4 * Real.pi * M * c ^ 3 / (ℏ * N)
      ∧ ‖nnPathWeight S_R (horizonImaginaryAction G c (sphereArea R)) ℏ‖ =
          Real.exp (-(N / 4))
      ∧ 8 * Real.pi * G / c ^ 4 =
          8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  dsimp only
  exact comptonCellInference_isolatedNewton_surfaceFluxEinstein_chain S_R ℏ c σ₀ η
    (radialBallMass ρ (entropicProperDistance (inferenceMass σ₀) c ℏ η)) x₀ hℏ hc hσ hη

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux.comptonCellInference_radialDensity_enclosingFlux where
  formalizes @ "claim:the-g-free-compton-cell-inference-coupling-g-equals-hbar-c-sigma-0-to-the-fourth-reaches-the-general-spatially-varying-radial-mass-density-source-through-gausss-law-with-the-shell-integral-enclosed-mass-the-genuine-bochner-surface-flux-four-pi-g-m-and-the-distributional-poisson-law",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ComptonCellIsolatedNewtonFlux.comptonCellInference_isolatedNewton_surfaceFluxEinstein_chain",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonExteriorField3At_sphereFlux",
  caveat @ "claim:the-enclosing-sphere-flux-uses-the-enclosed-mass-exterior-kernel-representation-newtons-theorem-gausss-law-for-a-spherically-symmetric-source-the-local-poisson-equation-is-separately-derived-in-radialEnclosedMass-poisson-what-remains-absent-is-the-general-non-symmetric-convolution-potential-and-this-does-not-fit-sigma-0-to-the-measured-value-of-g"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux.radialEnclosedMass_poisson where
  formalizes @ "claim:the-local-poisson-equation-nabla-squared-phi-equals-four-pi-g-rho-holds-pointwise-for-the-continuous-spatially-varying-radial-density-derived-from-the-enclosed-mass-shell-integral-via-the-fundamental-theorem-of-calculus-the-radial-divergence-of-the-enclosed-mass-newton-field-equals-four-pi-g-rho",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux.radialBallMass_hasDerivAt",
  caveat @ "claim:this-is-the-spherically-symmetric-radial-form-of-poissons-equation-the-general-non-symmetric-convolution-potential-remains-absent"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux.radialBallMass_hasDerivAt where
  formalizes @ "claim:the-derivative-of-the-radial-enclosed-mass-shell-integral-is-the-surface-shell-mass-four-pi-r-squared-rho-of-r-by-the-fundamental-theorem-of-calculus-the-differential-heart-of-newtons-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux.radialEnclosedMass_sphereFlux where
  formalizes @ "claim:the-genuine-parameterized-surface-integral-of-the-enclosed-mass-exterior-field-through-the-enclosing-sphere-is-four-pi-g-times-the-radial-shell-integral-enclosed-mass-gausss-law-for-a-spherically-symmetric-density",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonExteriorField3At_sphereFlux"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux.radialBallMass_const where
  supported_by @ "lean:CPTPMap.funext",
  formalizes @ "claim:the-radial-shell-integral-enclosed-mass-of-a-constant-density-ball-reduces-to-the-homogeneous-ball-mass-four-thirds-pi-r-cubed-rho"

zil_file_contract physlib.radialDensityComptonCellFlux where
  promises "The general spatially-varying radial mass density source for the independent Compton-cell gravitational coupling, reached through Gauss's law and the genuine isolated-source carriers. The enclosed mass of the radius-R ball is the shell integral M(R) = integral from 0 to R of 4 pi r^2 rho(r) dr (radialBallMass), reducing to the homogeneous ball mass (4/3) pi R^3 rho when rho is constant (radialBallMass_const). For a spherically-symmetric source the enclosing-sphere flux is 4 pi G M(R): the enclosing-sphere field is that of the enclosed mass M(R) at the center, and its genuine parameterized Bochner surface integral against the unit-sphere angular measure is 4 pi G M(R) (radialEnclosedMass_sphereFlux, reusing isolatedNewtonExteriorField3At_sphereFlux). Feeding the G-free Compton-cell coupling G = hbar c sigma_0^4 (newtonG_from_positionVariance) and instantiating the isolated-source gravity chain at the enclosed mass gives, in one statement, the area-per-bit coupling G = A c^3/(hbar N), the distributional Poisson law Laplacian Phi = (surface flux) dirac at x0 (genuine distributional fundamental-solution law), the genuine spherical surface flux 4 pi G M(R), the bit-count acceleration G M(R)/R^2 = 4 pi M(R) c^3/(hbar N), the Nagao-Nielsen horizon damping norm nnPathWeight = exp(-N/4), and the Einstein coupling 8 pi G/c^4 = 8 pi (A/N)/(hbar c). The local Poisson equation is derived pointwise for the continuous varying density: M'(R) = 4 pi R^2 rho(R) by the fundamental theorem of calculus (radialBallMass_hasDerivAt), so the radial divergence of the enclosed-mass Newton field equals 4 pi G rho(R) (radialEnclosedMass_poisson, radialField_poisson_divergence) -- the varying-density generalization of the constant-density laplacianAt3_homogeneousDensityPotential. Honest: the enclosing-sphere flux uses the enclosed-mass exterior kernel representation (Newton's theorem / Gauss's law for a spherically-symmetric source); the surface flux is the genuine Bochner integral and the Poisson law the genuine distributional fundamental-solution law. What remains genuinely absent, in both this repository and Mathlib, is the general non-symmetric convolution potential Phi = kernel * rho with Delta phi = 4 pi G rho (no distributional-convolution operator, Riesz/Newtonian potential, or n-dimensional harmonic mean-value exists); and this does not fit sigma_0 to the measured value of G."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ComptonCellIsolatedNewtonFlux.comptonCellInference_isolatedNewton_surfaceFluxEinstein_chain",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonExteriorField3At_sphereFlux",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits.homogeneousBallMass3"]
  forbids_substitutes ["a constant-density ball alone, whereas this carries a general spatially-varying radial density rho(r)",
    "an area-times-acceleration definition of the flux, whereas this reuses the genuine parameterized Bochner surface integral 4 pi G M(R)",
    "a numerical prediction of G from no physical input, whereas the mass scale sigma_0 remains an independent input"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux.radialBallMass_const,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux.radialBallMass_hasDerivAt,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux.radialEnclosedMass_poisson,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux.radialField_poisson_divergence,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux.radialEnclosedMass_sphereFlux,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux.comptonCellInference_radialDensity_enclosingFlux]

/- ZIL-END -/
