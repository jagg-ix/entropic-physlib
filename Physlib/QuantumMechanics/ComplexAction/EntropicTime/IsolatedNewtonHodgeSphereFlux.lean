/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.StaticHodgeScreenBits
public import Physlib.SpaceAndTime.Space.Integrals.RadialAngularMeasure
public import Physlib.SpaceAndTime.Space.Norm.Basic
public import Physlib.SpaceAndTime.Space.Translations

/-!
# Isolated Newton field: spherical Hodge flux and distributional source

This module advances the static Hodge-screen development from the homogeneous interior model to the
isolated Newton kernel.  It reuses two existing analytic carriers:

* `volume.toSphere`, Physlib's angular measure on the unit sphere, to define an actual Bochner
  surface integral through the radius-`R` sphere;
* `Space.distLaplacian_fundamentalSolution_norm_zpow`, the proved distributional fundamental
  solution of the Laplacian.

For the exterior potential `Φ(r) = -GM/r`, the outward derivative is `GM/r²`.  Its radial vector
field has sphere flux

`∫_{S_R²} ∇Φ · n dA = 4πGM`,

and the singular kernel satisfies

`ΔΦ = 4πGM δ₀`

as a distribution.  Thus the surface flux and the Dirac-source coefficient are the same proved
quantity.  The final bridge reuses the holographic bit count to express the boundary field,
Nagao–Nielsen horizon modulus, and Einstein coupling.

The final sections translate the complete construction to an arbitrary source point. The surface
remains a round sphere centered on that source and parameterized by the unit sphere. The result
does not establish a general Stokes theorem for arbitrary surfaces or vector fields, and the
distributional point source is not inserted into the existing smooth rest-dust linearized Einstein
carrier.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux

open MeasureTheory
open scoped Space
open Physlib
open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.HorizonNagaoContourBitEinstein
open Physlib.QuantumMechanics.ComplexAction.NonHermitianComplexAction.EntropicDampingEquivalence
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa

/-! ## A. Parameterized spherical surface integrals -/

/-- The unit two-sphere in the repository's three-dimensional Euclidean `Space`. -/
abbrev UnitSphere3 :=
  Metric.sphere (0 : Space 3) 1

/--
The scalar surface integral over the radius-`R` sphere, parameterized by the unit sphere.
The factor `R²` is the surface-area Jacobian.
-/
def sphereSurfaceIntegral3 (R : ℝ) (f : UnitSphere3 → ℝ) : ℝ :=
  ∫ n, R ^ 2 * f n ∂(volume (α := Space 3)).toSphere

/--
The outward flux of a vector field through the radius-`R` sphere, using the unit normal supplied by
the unit-sphere parameter `n`.
-/
def sphereFluxIntegral3 (R : ℝ) (F : Space 3 → Space 3) : ℝ :=
  sphereSurfaceIntegral3 R fun n => inner ℝ (F (R • n.1)) n.1

/-- The total angular measure of the unit two-sphere is `4π`. -/
lemma unitSphere3_measureReal_univ :
    (volume (α := Space 3)).toSphere.real Set.univ = 4 * Real.pi := by
  rw [Measure.toSphere_real_apply_univ, Space.finrank_eq_dim,
    Space.volume_metricBall_three_real]
  ring

/-- Integrating a constant scalar normal component gives the sphere area times that component. -/
lemma sphereSurfaceIntegral3_const (R a : ℝ) :
    sphereSurfaceIntegral3 R (fun _ => a) = sphereArea R * a := by
  rw [sphereSurfaceIntegral3, integral_const, unitSphere3_measureReal_univ]
  simp [sphereArea]
  ring

/-! ## B. The isolated exterior Newton field -/

/-- The radial isolated-source Newton potential profile `-GM/r`. -/
def isolatedNewtonPotentialRadial (G M r : ℝ) : ℝ :=
  -(G * M) * r⁻¹

/-- Away from the source, the outward derivative of `-GM/r` is `GM/r²`. -/
lemma isolatedNewtonPotentialRadial_hasDerivAt
    (G M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (isolatedNewtonPotentialRadial G M) (G * M / r ^ 2) r := by
  change HasDerivAt (fun y => -(G * M) * y⁻¹) (G * M / r ^ 2) r
  have h := (hasDerivAt_inv hr).const_mul (-(G * M))
  apply h.congr_deriv
  rw [div_eq_mul_inv]
  ring

/-- The radial gradient field `GM x/‖x‖³` of the isolated Newton potential away from the origin. -/
def isolatedNewtonExteriorField3 (G M : ℝ) (x : Space 3) : Space 3 :=
  (G * M / ‖x‖ ^ 3) • x

/--
On a positive-radius sphere, the isolated exterior field is the constant radial vector
`(GM/R²)n`.
-/
lemma isolatedNewtonExteriorField3_on_sphere
    (G M R : ℝ) (hR : 0 < R) (n : UnitSphere3) :
    isolatedNewtonExteriorField3 G M (R • n.1) =
      (G * M / R ^ 2) • n.1 := by
  have hn : ‖(n.1 : Space 3)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp n.2
  simp [isolatedNewtonExteriorField3, norm_smul, hn, abs_of_pos hR, smul_smul]
  field_simp

/-- The actual parameterized surface flux of the isolated field is `4πGM`. -/
lemma isolatedNewtonExteriorField3_sphereFlux
    (G M R : ℝ) (hR : 0 < R) :
    sphereFluxIntegral3 R (isolatedNewtonExteriorField3 G M) =
      4 * Real.pi * G * M := by
  unfold sphereFluxIntegral3
  have hIntegrand :
      (fun n : UnitSphere3 =>
        inner ℝ (isolatedNewtonExteriorField3 G M (R • n.1)) n.1) =
        fun _ => G * M / R ^ 2 := by
    funext n
    rw [isolatedNewtonExteriorField3_on_sphere G M R hR n]
    simp [real_inner_smul_left, mem_sphere_zero_iff_norm.mp n.2]
  rw [hIntegrand, sphereSurfaceIntegral3_const]
  unfold sphereArea
  field_simp [hR.ne']

/-! ## C. The distributional point source -/

/--
The distribution defined by the isolated Newton kernel `-GM/‖x‖` in three dimensions.
-/
def isolatedNewtonPotentialDistribution3 (G M : ℝ) :
    (Space 3) →d[ℝ] ℝ :=
  (-(G * M)) •
    Space.distOfFunction
      (fun x : Space 3 => ‖x‖ ^ (- ((3 : ℤ) - 2)))
      (Space.IsDistBounded.pow _ (by omega))

/-- The isolated Newton kernel satisfies `ΔΦ = 4πGM δ₀` distributionally. -/
lemma isolatedNewtonPotentialDistribution3_laplacian
    (G M : ℝ) :
    Δᵈ (isolatedNewtonPotentialDistribution3 G M) =
      (4 * Real.pi * G * M) •
        Physlib.Distribution.diracDelta ℝ (0 : Space 3) := by
  unfold isolatedNewtonPotentialDistribution3
  rw [map_smul]
  have hFundamental :
      Δᵈ (Space.distOfFunction
        (fun x : Space 3 => ‖x‖ ^ (- ((3 : ℤ) - 2)))
        (Space.IsDistBounded.pow _ (by omega))) =
        (- ((3 : ℝ) - 2) * 3 *
          (volume (α := Space 3)).real (Metric.ball 0 1)) •
            Physlib.Distribution.diracDelta ℝ (0 : Space 3) := by
    simpa using
      (Space.distLaplacian_fundamentalSolution_norm_zpow (d := 3))
  rw [hFundamental]
  rw [Space.volume_metricBall_three_real]
  simp only [smul_smul]
  ring_nf

/--
The distributional source coefficient equals the actual surface flux through every positive-radius
sphere.
-/
lemma isolatedNewton_laplacian_eq_sphereFlux_smul_dirac
    (G M R : ℝ) (hR : 0 < R) :
    Δᵈ (isolatedNewtonPotentialDistribution3 G M) =
      sphereFluxIntegral3 R (isolatedNewtonExteriorField3 G M) •
        Physlib.Distribution.diracDelta ℝ (0 : Space 3) := by
  rw [isolatedNewtonPotentialDistribution3_laplacian,
    isolatedNewtonExteriorField3_sphereFlux G M R hR]

/-! ## D. Isolated source, screen bits, and entropic gravity -/

/--
For one isolated source and one positive-radius holographic screen, the same data give:

1. the distributional point-source law;
2. its equality with the actual spherical surface flux;
3. the boundary field in holographic-bit form;
4. the Nagao–Nielsen horizon modulus; and
5. the area-per-bit Einstein coupling.

This links the isolated Newton kernel to the entropic-time screen without asserting a smooth
pointwise Einstein equation at the singular source.
-/
lemma isolatedNewton_surfaceFlux_bitCount_gravity_chain
    (S_R G M ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : 0 < R)
    (hbits : N = holographicBits (sphereArea R) G ℏ c) :
    Δᵈ (isolatedNewtonPotentialDistribution3 G M) =
        sphereFluxIntegral3 R (isolatedNewtonExteriorField3 G M) •
          Physlib.Distribution.diracDelta ℝ (0 : Space 3)
      ∧ sphereFluxIntegral3 R (isolatedNewtonExteriorField3 G M) =
        4 * Real.pi * G * M
      ∧ G * M / R ^ 2 = 4 * Real.pi * M * c ^ 3 / (ℏ * N)
      ∧ ‖nnPathWeight S_R (horizonImaginaryAction G c (sphereArea R)) ℏ‖ =
        Real.exp (-(N / 4))
      ∧ 8 * Real.pi * G / c ^ 4 =
        8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  have hGravity :=
    bitCount_governs_gravity S_R G M ℏ c N R hℏ hc hG hR.ne' hbits
  exact ⟨isolatedNewton_laplacian_eq_sphereFlux_smul_dirac G M R hR,
    isolatedNewtonExteriorField3_sphereFlux G M R hR,
    hGravity.2.1, hGravity.1, hGravity.2.2⟩

/-! ## E. Translation to an arbitrary source point -/

/--
The outward flux through the radius-`R` sphere centered at `x₀`, parameterized by the same unit
sphere and using its unit normal.
-/
def sphereFluxIntegral3At (x₀ : Space 3) (R : ℝ) (F : Space 3 → Space 3) : ℝ :=
  sphereSurfaceIntegral3 R fun n => inner ℝ (F (x₀ + R • n.1)) n.1

/-- The isolated Newton exterior field sourced at `x₀`. -/
def isolatedNewtonExteriorField3At (G M : ℝ) (x₀ x : Space 3) : Space 3 :=
  isolatedNewtonExteriorField3 G M (x - x₀)

/--
On a sphere centered at its source, the translated field reduces to the origin-centered field.
-/
lemma isolatedNewtonExteriorField3At_on_centered_sphere
    (G M R : ℝ) (x₀ : Space 3) (n : UnitSphere3) :
    isolatedNewtonExteriorField3At G M x₀ (x₀ + R • n.1) =
      isolatedNewtonExteriorField3 G M (R • n.1) := by
  simp [isolatedNewtonExteriorField3At]

/-- Translating the source does not change its flux through a sphere centered on that source. -/
lemma isolatedNewtonExteriorField3At_sphereFlux
    (G M R : ℝ) (x₀ : Space 3) (hR : 0 < R) :
    sphereFluxIntegral3At x₀ R (isolatedNewtonExteriorField3At G M x₀) =
      4 * Real.pi * G * M := by
  rw [sphereFluxIntegral3At]
  simp_rw [isolatedNewtonExteriorField3At_on_centered_sphere]
  exact isolatedNewtonExteriorField3_sphereFlux G M R hR

/-- The inverse-radius Newton distribution translated from the origin to the source point `x₀`. -/
def isolatedNewtonPotentialDistribution3At (G M : ℝ) (x₀ : Space 3) :
    (Space 3) →d[ℝ] ℝ :=
  Space.distTranslate (Space.basis.repr x₀) (isolatedNewtonPotentialDistribution3 G M)

/-- The translated inverse-radius kernel has Dirac source at the translated source point. -/
lemma isolatedNewtonPotentialDistribution3At_laplacian
    (G M : ℝ) (x₀ : Space 3) :
    Δᵈ (isolatedNewtonPotentialDistribution3At G M x₀) =
      (4 * Real.pi * G * M) • Physlib.Distribution.diracDelta ℝ x₀ := by
  have hx₀ : Space.basis.repr x₀ +ᵥ (0 : Space 3) = x₀ := by
    ext i
    simp
  rw [isolatedNewtonPotentialDistribution3At, Space.distLaplacian_distTranslate,
    isolatedNewtonPotentialDistribution3_laplacian, map_smul,
    Space.distTranslate_diracDelta, hx₀]

/--
For every positive radius, the translated distributional source coefficient is the actual flux
through the round sphere centered at the same source point.
-/
lemma isolatedNewtonAt_laplacian_eq_sphereFlux_smul_dirac
    (G M R : ℝ) (x₀ : Space 3) (hR : 0 < R) :
    Δᵈ (isolatedNewtonPotentialDistribution3At G M x₀) =
      sphereFluxIntegral3At x₀ R (isolatedNewtonExteriorField3At G M x₀) •
        Physlib.Distribution.diracDelta ℝ x₀ := by
  rw [isolatedNewtonPotentialDistribution3At_laplacian,
    isolatedNewtonExteriorField3At_sphereFlux G M R x₀ hR]

/-! ## F. Translated isolated source and entropic screen -/

/--
The arbitrary-center isolated-source chain: translated distributional point-source law, centered
sphere flux, holographic boundary acceleration, Nagao–Nielsen modulus, and area-per-bit Einstein
coupling all use the same source mass, Newton coupling, screen radius, and bit count.

This is translation covariance of the Newtonian distributional carrier. It does not make the
source smooth and does not promote the result to a nonlinear Einstein point-mass solution.
-/
lemma isolatedNewtonAt_surfaceFlux_bitCount_gravity_chain
    (S_R G M ℏ c N R : ℝ) (x₀ : Space 3)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : 0 < R)
    (hbits : N = holographicBits (sphereArea R) G ℏ c) :
    Δᵈ (isolatedNewtonPotentialDistribution3At G M x₀) =
        sphereFluxIntegral3At x₀ R (isolatedNewtonExteriorField3At G M x₀) •
          Physlib.Distribution.diracDelta ℝ x₀
      ∧ sphereFluxIntegral3At x₀ R (isolatedNewtonExteriorField3At G M x₀) =
        4 * Real.pi * G * M
      ∧ G * M / R ^ 2 = 4 * Real.pi * M * c ^ 3 / (ℏ * N)
      ∧ ‖nnPathWeight S_R (horizonImaginaryAction G c (sphereArea R)) ℏ‖ =
        Real.exp (-(N / 4))
      ∧ 8 * Real.pi * G / c ^ 4 =
        8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  have hGravity :=
    bitCount_governs_gravity S_R G M ℏ c N R hℏ hc hG hR.ne' hbits
  exact ⟨isolatedNewtonAt_laplacian_eq_sphereFlux_smul_dirac G M R x₀ hR,
    isolatedNewtonExteriorField3At_sphereFlux G M R x₀ hR,
    hGravity.2.1, hGravity.1, hGravity.2.2⟩

/-! ## G. Inference-variance coupling for an isolated translated source -/

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ComptonCellNewtonConstant
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicMassNewtonianDynamics
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

/-- The `G`-free Compton-cell count at the inference mass fixes the coupling of
the translated isolated Newton distribution.  The existing analytic theorem then
identifies its Dirac coefficient with the actual centered-sphere flux and carries
the same coupling through acceleration, horizon damping, and Einstein `κ`.

This remains a singular weak-field point source and a round sphere centered at that
source; it is not an arbitrary-surface Stokes theorem or nonlinear point-mass
spacetime. -/
@[zil_level bridge_theorem]
lemma comptonCellInference_isolatedNewtonAt_surfaceFlux_gravity_chain
    (S_R M ℏ c σ₀ η : ℝ) (x₀ : Space 3)
    (hℏ : 0 < ℏ) (hc : 0 < c) (hσ : 0 < σ₀) (hη : 0 < η) :
    let m := inferenceMass σ₀
    let R := entropicProperDistance m c ℏ η
    let N := comptonCellBits m c ℏ η
    let G := ℏ * c * σ₀ ^ 4
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
  exact ⟨hArea, isolatedNewtonAt_surfaceFlux_bitCount_gravity_chain
    S_R (ℏ * c * σ₀ ^ 4) M ℏ c
      (comptonCellBits (inferenceMass σ₀) c ℏ η)
      (entropicProperDistance (inferenceMass σ₀) c ℏ η) x₀
      hℏ.ne' hc.ne' hG hR hbits⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux

end
