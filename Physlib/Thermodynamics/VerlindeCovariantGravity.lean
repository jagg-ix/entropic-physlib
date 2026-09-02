/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux
public import Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicciFromMetric
public import Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein
public import Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral
public import Physlib.Relativity.SemiClassical.SchwarzschildEntropicRate
public import Physlib.Mathematics.LovelockRund.PoincareStokes
meta import Zil

/-!
# Covariant Verlinde bridge: screens, Poisson flux, redshift, and Komar mass

This module closes the geometric middle of the repository's entropic-gravity chain without
redefining its endpoints.

* The translated Newton potential `-GM/‖x-x₀‖` has the existing isolated Newton field as its
  Fréchet gradient.  Its acceleration is the negative gradient, and its equipotential level set at
  radius `R` is exactly `Metric.sphere x₀ R`.
* The Mathlib-backed box divergence theorem turns a pointwise Poisson equation into the oriented
  integral flux law for a general three-dimensional density.  The existing radial-density carrier
  supplies the smooth spherical specialization.
* For the exact Schwarzschild metric `f(r)=1-2GM/r`, the static Killing norm defines
  `φ=(1/2)log(-ξ²)`.  Its redshifted unit-normal derivative is `GM/r²`, so
  `F=-m exp(φ) n·∇φ` is Newton's inverse-square force.
* Integrating that derivative on a round static screen gives the genuine Bochner surface integral
  `4πGM`, hence the Komar mass `M` in geometrized units.  A separate general pointwise theorem
  derives `□ξ=-Ric(ξ)` from the covariantly differentiated Killing equation and the repository's
  connection-built Ricci commutator.

The Schwarzschild results are exact on the static exterior (`f>0`) and use `c=1`; they are not an
arbitrary-stationary-spacetime Komar theorem.  The Killing identity is local and second-order: its
input is the covariantly differentiated Killing equation for a nondegenerate symmetric metric.
The formerly supplied divergence and wave contractions are now proved from that one tensor
equation.  No Einstein equation, equation of state, or empirical value of `G` is introduced.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics.VerlindeCovariantGravity

open Set MeasureTheory
open scoped Space
open Physlib
open Physlib.Thermodynamics
open Physlib.Mathematics.LovelockRund
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.RadialDensityComptonCellFlux
open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci
open Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ConnectionCovariantHessian
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral
open Physlib.Relativity.SemiClassical

/-! ## A. Newton acceleration and equipotential screens -/

/-- The translated three-dimensional Newton potential `Φ(x)=-GM/‖x-x₀‖`. -/
def newtonPotential3At (G M : ℝ) (x₀ x : Space 3) : ℝ :=
  isolatedNewtonPotentialRadial G M ‖x - x₀‖

/-- The level set of the translated Newton potential at radial value `Φ(R)`. -/
def newtonEquipotentialScreen (G M : ℝ) (x₀ : Space 3) (R : ℝ) : Set (Space 3) :=
  {x | newtonPotential3At G M x₀ x = isolatedNewtonPotentialRadial G M R}

/-- **A14, screen identification.** For a nonzero source coupling, the potential level set at
`Φ(R)` is exactly the round screen centered at the source. -/
@[zil_level physical_theorem]
lemma newtonEquipotentialScreen_eq_sphere
    (G M R : ℝ) (x₀ : Space 3) (hGM : G * M ≠ 0) :
    newtonEquipotentialScreen G M x₀ R = Metric.sphere x₀ R := by
  ext x
  simp only [newtonEquipotentialScreen, Set.mem_setOf_eq, Metric.mem_sphere]
  change -(G * M) * ‖x - x₀‖⁻¹ = -(G * M) * R⁻¹ ↔ dist x x₀ = R
  constructor
  · intro h
    have hi : ‖x - x₀‖⁻¹ = R⁻¹ :=
      mul_left_cancel₀ (neg_ne_zero.mpr hGM) h
    have hn : ‖x - x₀‖ = R := inv_injective hi
    simpa [dist_eq_norm] using hn
  · intro h
    have hn : ‖x - x₀‖ = R := by simpa [dist_eq_norm] using h
    rw [hn]

/-- The physical Newton acceleration: minus the outward gradient field of the potential. -/
def newtonAccelerationField3At (G M : ℝ) (x₀ x : Space 3) : Space 3 :=
  -isolatedNewtonExteriorField3At G M x₀ x

/-- **A14, actual gradient.** Away from the source, the Fréchet derivative of the translated
potential is the inner-product covector represented by the existing isolated exterior field. -/
@[zil_level physical_theorem]
lemma newtonPotential3At_hasFDerivAt
    (G M : ℝ) (x₀ x : Space 3) (hx : x ≠ x₀) :
    HasFDerivAt (newtonPotential3At G M x₀)
      (innerSL ℝ (isolatedNewtonExteriorField3At G M x₀ x)) x := by
  have hsub : HasFDerivAt (fun y : Space 3 => y - x₀)
      (ContinuousLinearMap.id ℝ (Space 3)) x := hasFDerivAt_sub_const x₀
  have hnormSq := hsub.norm_sq
  have hnormSq_ne : ‖x - x₀‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))
  have hnorm := hnormSq.sqrt hnormSq_ne
  rw [show (fun y : Space 3 => Real.sqrt (‖y - x₀‖ ^ 2)) =
      (fun y : Space 3 => ‖y - x₀‖) by
        funext y
        simp] at hnorm
  have hcomp := (isolatedNewtonPotentialRadial_hasDerivAt G M ‖x - x₀‖
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))).hasFDerivAt.comp x hnorm
  have hfun :
      (isolatedNewtonPotentialRadial G M ∘ fun y : Space 3 => ‖y - x₀‖) =
        newtonPotential3At G M x₀ := by
    funext y
    rfl
  rw [hfun] at hcomp
  refine hcomp.congr_fderiv ?_
  ext y
  simp [isolatedNewtonExteriorField3At, isolatedNewtonExteriorField3]
  field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)]

/-- **A14, `a=-∇Φ`.** The Riesz vector representing the potential derivative is the negative of
the physical acceleration field. -/
@[zil_level physical_theorem]
lemma newtonAccelerationField3At_eq_neg_gradient
    (G M : ℝ) (x₀ x : Space 3) (hx : x ≠ x₀) :
    fderiv ℝ (newtonPotential3At G M x₀) x =
      innerSL ℝ (-newtonAccelerationField3At G M x₀ x) := by
  rw [(newtonPotential3At_hasFDerivAt G M x₀ x hx).fderiv]
  simp [newtonAccelerationField3At]

/-- On a positive-radius screen the acceleration is the inward normal vector with magnitude
`GM/R²`. -/
@[zil_level physical_theorem]
lemma newtonAccelerationField3At_on_centered_sphere
    (G M R : ℝ) (x₀ : Space 3) (hR : 0 < R) (n : UnitSphere3) :
    newtonAccelerationField3At G M x₀ (x₀ + R • n.1) =
      -(G * M / R ^ 2) • n.1 := by
  rw [newtonAccelerationField3At,
    isolatedNewtonExteriorField3At_on_centered_sphere,
    isolatedNewtonExteriorField3_on_sphere G M R hR n]
  simp

/-! ## B. Pointwise Poisson equation to integral Gauss flux -/

/-- **A15, integral Poisson–Gauss law.** On a three-dimensional coordinate box, any sufficiently
regular field satisfying `div field = 4πGρ` has oriented boundary flux equal to the volume integral
of `4πGρ`.  This uses the actual Mathlib Bochner divergence theorem; the boundary expression is not
defined to equal the volume integral. -/
@[zil_level physical_theorem]
lemma poisson_box_integral_flux
    (G : ℝ) (ρ : BoxPoint 2 → ℝ)
    (a b : BoxPoint 2) (hle : a ≤ b)
    (field : BoxPoint 2 → BoxVector 2 ℝ)
    (fieldDeriv : BoxPoint 2 → BoxPoint 2 →L[ℝ] BoxVector 2 ℝ)
    (singular : Set (BoxPoint 2)) (hsingular : singular.Countable)
    (hcontinuous : ContinuousOn field (Icc a b))
    (hderiv : ∀ x ∈
      (Set.pi Set.univ fun i => Ioo (a i) (b i)) \ singular,
        HasFDerivAt field (fieldDeriv x) x)
    (hintegrable : IntegrableOn (boxDivergence fieldDeriv) (Icc a b))
    (hpoisson : ∀ x ∈ Icc a b,
      boxDivergence fieldDeriv x = 4 * Real.pi * G * ρ x) :
    ∑ i : Fin 3,
        ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            field (i.insertNth (b i) x) i) -
          ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            field (i.insertNth (a i) x) i) =
      ∫ x in Icc a b, 4 * Real.pi * G * ρ x := by
  rw [← boxDivergenceTheorem a b hle field fieldDeriv singular hsingular
    hcontinuous hderiv hintegrable]
  exact setIntegral_congr_fun measurableSet_Icc hpoisson

/-- The existing smooth radial-density local Poisson law and genuine spherical Bochner flux law,
assembled as the spherical specialization of A15. -/
@[zil_level physical_theorem]
lemma radialDensity_poisson_and_integralFlux
    (G : ℝ) (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    (x₀ : Space 3) (R : ℝ) (hR : 0 < R) :
    deriv (fun r => G * radialBallMass ρ r) R / R ^ 2 = 4 * Real.pi * G * ρ R
      ∧ sphereFluxIntegral3At x₀ R
          (isolatedNewtonExteriorField3At G (radialBallMass ρ R) x₀) =
        4 * Real.pi * G * radialBallMass ρ R :=
  ⟨radialField_poisson_divergence G ρ hρ R hR.ne',
    radialEnclosedMass_sphereFlux G ρ x₀ R hR⟩

/-! ## C. Static Killing redshift and the covariant screen force -/

/-- The squared norm `ξ²=g(∂ₜ,∂ₜ)=-f` of the static Schwarzschild Killing field. -/
def timelikeKillingNormSq (μ r : ℝ) : ℝ := -schwF μ r

/-- The Verlinde redshift potential `φ=(1/2)log(-ξ²)` for the static Killing field. -/
def killingRedshiftPotential (μ r : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (-timelikeKillingNormSq μ r)

/-- The Schwarzschild profile has derivative `f'(r)=2μ/r²`. -/
lemma schwF_hasDerivAt (μ r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (schwF μ) (schwDf μ r) r := by
  have hquot := (hasDerivAt_const r (2 * μ)).div (hasDerivAt_id r) hr
  have h := (hasDerivAt_const r 1).sub hquot
  have hfun : ((fun _ : ℝ => 1) - (fun _ : ℝ => 2 * μ) / id) = schwF μ := by
    funext y
    simp [schwF]
  rw [hfun] at h
  apply h.congr_deriv
  unfold schwDf
  simp
  ring

/-- **A16, redshift definition from geometry.** The potential is literally half the logarithm of
minus the squared static Killing norm, equivalently `(1/2)log f`. -/
@[zil_level physical_theorem]
lemma killingRedshiftPotential_eq (μ r : ℝ) :
    killingRedshiftPotential μ r = (1 / 2 : ℝ) * Real.log (schwF μ r) := by
  simp [killingRedshiftPotential, timelikeKillingNormSq]

/-- The radial derivative of the exact Schwarzschild redshift potential. -/
@[zil_level physical_theorem]
lemma killingRedshiftPotential_hasDerivAt
    (μ r : ℝ) (hr : r ≠ 0) (hf : schwF μ r ≠ 0) :
    HasDerivAt (killingRedshiftPotential μ)
      (μ / (r ^ 2 * schwF μ r)) r := by
  rw [show killingRedshiftPotential μ =
      fun y => (1 / 2 : ℝ) * Real.log (schwF μ y) by
        funext y
        simp [killingRedshiftPotential, timelikeKillingNormSq]]
  have h := ((schwF_hasDerivAt μ r hr).log hf).const_mul (1 / 2 : ℝ)
  apply h.congr_deriv
  unfold schwDf
  field_simp

/-- The gravitational redshift factor `exp φ`. -/
def redshiftFactor (μ r : ℝ) : ℝ :=
  Real.exp (killingRedshiftPotential μ r)

/-- In the static exterior, `exp φ=√f`. -/
lemma redshiftFactor_eq_sqrt
    (μ r : ℝ) (hf : 0 < schwF μ r) :
    redshiftFactor μ r = Real.sqrt (schwF μ r) := by
  unfold redshiftFactor killingRedshiftPotential timelikeKillingNormSq
  simp only [neg_neg]
  rw [show (1 / 2 : ℝ) * Real.log (schwF μ r) =
      Real.log (Real.sqrt (schwF μ r)) by
        rw [Real.log_sqrt hf.le]
        ring]
  exact Real.exp_log (Real.sqrt_pos.2 hf)

/-- The redshifted unit-normal derivative `exp(φ) n·∇φ`.  The second `√f` is the radial unit-normal
factor of the spatial Schwarzschild metric `g_rr=f⁻¹`. -/
def redshiftedNormalGradient (μ r : ℝ) : ℝ :=
  redshiftFactor μ r * Real.sqrt (schwF μ r) *
    deriv (killingRedshiftPotential μ) r

/-- The exact cancellation `exp(φ) n·∇φ=μ/r²` in the static Schwarzschild exterior. -/
@[zil_level physical_theorem]
lemma redshiftedNormalGradient_eq
    (μ r : ℝ) (hr : r ≠ 0) (hf : 0 < schwF μ r) :
    redshiftedNormalGradient μ r = μ / r ^ 2 := by
  rw [redshiftedNormalGradient, redshiftFactor_eq_sqrt μ r hf,
    (killingRedshiftPotential_hasDerivAt μ r hr hf.ne').deriv]
  rw [show Real.sqrt (schwF μ r) * Real.sqrt (schwF μ r) = schwF μ r by
    exact Real.mul_self_sqrt hf.le]
  field_simp

/-- The inward scalar force `F=-m exp(φ) n·∇φ`. -/
def covariantScreenForce (m μ r : ℝ) : ℝ :=
  -m * redshiftedNormalGradient μ r

/-- **A16, force law.** With the Schwarzschild mass parameter `μ=GM`, the covariant redshift-force
formula reduces exactly to the inward Newton force `-GMm/r²`. -/
@[zil_level physical_theorem]
lemma covariantScreenForce_eq_newton
    (G M m r : ℝ) (hr : r ≠ 0) (hf : 0 < schwF (G * M) r) :
    covariantScreenForce m (G * M) r = -(G * M * m) / r ^ 2 := by
  rw [covariantScreenForce, redshiftedNormalGradient_eq (G * M) r hr hf]
  ring

/-! ## D. Komar screen mass and the Killing identity -/

/-- The genuine parameterized surface integral of `exp(φ)n·∇φ` on the static round screen. -/
def komarScreenFlux (G M R : ℝ) : ℝ :=
  sphereSurfaceIntegral3 R (fun _ => redshiftedNormalGradient (G * M) R)

/-- **A17, Komar surface flux.** The redshifted normal derivative integrates to `4πGM`. -/
@[zil_level physical_theorem]
lemma komarScreenFlux_eq
    (G M R : ℝ) (hR : 0 < R) (hf : 0 < schwF (G * M) R) :
    komarScreenFlux G M R = 4 * Real.pi * G * M := by
  rw [komarScreenFlux, sphereSurfaceIntegral3_const,
    redshiftedNormalGradient_eq (G * M) R hR.ne' hf]
  unfold sphereArea
  field_simp

/-- The Komar mass `M_K=(4πG)⁻¹∮exp(φ)n·∇φ dA` on the exact static spherical screen. -/
def komarScreenMass (G M R : ℝ) : ℝ :=
  komarScreenFlux G M R / (4 * Real.pi * G)

/-- **A17, Komar mass.** Every positive-radius static exterior screen recovers the source mass. -/
@[zil_level physical_theorem]
lemma komarScreenMass_eq
    (G M R : ℝ) (hG : G ≠ 0) (hR : 0 < R)
    (hf : 0 < schwF (G * M) R) :
    komarScreenMass G M R = M := by
  rw [komarScreenMass, komarScreenFlux_eq G M R hR hf]
  field_simp [hG, Real.pi_ne_zero]

/-- The covariant Killing equation
`∇_μ ξ_ν + ∇_ν ξ_μ=0` at one point, with the vector index lowered by the
metric. -/
def KillingEquationAt {ι : Type*} [Fintype ι]
    (g : Matrix ι ι ℝ) (nablaV : ι → ι → ℝ) : Prop :=
  ∀ μ ν,
    (∑ ρ, g ν ρ * nablaV μ ρ) +
      ∑ ρ, g μ ρ * nablaV ν ρ = 0

/-- For a metric-compatible torsion-free connection, the coordinate metric
Lie derivative is exactly the symmetrized metric-lowered covariant derivative
of the vector field. -/
lemma metricLieDerivative_apply_eq_covariantKilling
    {ι : Type*} [Fintype ι]
    (g : Matrix ι ι ℝ) (dg Γ : ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (dV : ι → ι → ℝ)
    (hg : Matrix.transpose g = g)
    (hΓ : IsTorsionFree Γ) (hcompat : IsMetricCompatible Γ dg g)
    (μ ν : ι) :
    metricLieDerivative g dg V dV μ ν =
      (∑ ρ, g ν ρ * covariantDerivVectorAt Γ V dV μ ρ) +
        ∑ ρ, g μ ρ * covariantDerivVectorAt Γ V dV ν ρ := by
  have hmetric (s : ι) :
      dg s μ ν =
        (∑ ρ, (Γ ρ) s μ * g ρ ν) + ∑ ρ, (Γ ρ) s ν * g μ ρ := by
    have hs := congrFun (congrFun (hcompat s) μ) ν
    simp only [metricCovariantDeriv, Matrix.zero_apply] at hs
    linarith
  have hconn₁ :
      (∑ s, V s * ∑ ρ, (Γ ρ) s μ * g ρ ν) =
        ∑ ρ, g ν ρ * ∑ s, (Γ ρ) μ s * V s := by
    calc
      (∑ s, V s * ∑ ρ, (Γ ρ) s μ * g ρ ν) =
          ∑ s, ∑ ρ, V s * ((Γ ρ) s μ * g ρ ν) := by
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.mul_sum]
      _ = ∑ ρ, ∑ s, V s * ((Γ ρ) s μ * g ρ ν) := Finset.sum_comm
      _ = ∑ ρ, ∑ s, g ν ρ * ((Γ ρ) μ s * V s) := by
            apply Finset.sum_congr rfl
            intro ρ _
            apply Finset.sum_congr rfl
            intro s _
            have hΓs : (Γ ρ) s μ = (Γ ρ) μ s := by
              simpa [Matrix.transpose_apply] using
                congrFun (congrFun (hΓ ρ) μ) s
            have hgs : g ρ ν = g ν ρ := by
              simpa [Matrix.transpose_apply] using congrFun (congrFun hg ν) ρ
            rw [hΓs, hgs]
            ring
      _ = ∑ ρ, g ν ρ * ∑ s, (Γ ρ) μ s * V s := by
            apply Finset.sum_congr rfl
            intro ρ _
            rw [Finset.mul_sum]
  have hconn₂ :
      (∑ s, V s * ∑ ρ, (Γ ρ) s ν * g μ ρ) =
        ∑ ρ, g μ ρ * ∑ s, (Γ ρ) ν s * V s := by
    calc
      (∑ s, V s * ∑ ρ, (Γ ρ) s ν * g μ ρ) =
          ∑ s, ∑ ρ, V s * ((Γ ρ) s ν * g μ ρ) := by
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.mul_sum]
      _ = ∑ ρ, ∑ s, V s * ((Γ ρ) s ν * g μ ρ) := Finset.sum_comm
      _ = ∑ ρ, ∑ s, g μ ρ * ((Γ ρ) ν s * V s) := by
            apply Finset.sum_congr rfl
            intro ρ _
            apply Finset.sum_congr rfl
            intro s _
            have hΓs : (Γ ρ) s ν = (Γ ρ) ν s := by
              simpa [Matrix.transpose_apply] using
                congrFun (congrFun (hΓ ρ) ν) s
            rw [hΓs]
            ring
      _ = ∑ ρ, g μ ρ * ∑ s, (Γ ρ) ν s * V s := by
            apply Finset.sum_congr rfl
            intro ρ _
            rw [Finset.mul_sum]
  unfold metricLieDerivative covariantDerivVectorAt
  simp only [Matrix.of_apply]
  simp_rw [hmetric, mul_add, Finset.sum_add_distrib]
  rw [hconn₁, hconn₂]
  ring

/-- The repository's Lie-derivative Killing predicate and the covariant
Killing equation are equivalent for a Levi-Civita connection. -/
@[zil_level bridge_theorem]
lemma isKillingVector_iff_killingEquationAt
    {ι : Type*} [Fintype ι]
    (g : Matrix ι ι ℝ) (dg Γ : ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (dV : ι → ι → ℝ)
    (hg : Matrix.transpose g = g)
    (hΓ : IsTorsionFree Γ) (hcompat : IsMetricCompatible Γ dg g) :
    IsKillingVector g dg V dV ↔
      KillingEquationAt g (covariantDerivVectorAt Γ V dV) := by
  constructor
  · intro h μ ν
    have hz : metricLieDerivative g dg V dV μ ν = 0 := by
      rw [h]
      rfl
    rw [metricLieDerivative_apply_eq_covariantKilling
      g dg Γ V dV hg hΓ hcompat μ ν] at hz
    exact hz
  · intro h
    unfold IsKillingVector
    ext μ ν
    rw [metricLieDerivative_apply_eq_covariantKilling
      g dg Γ V dV hg hΓ hcompat μ ν]
    simpa using h μ ν

/-- The covariantly differentiated Killing equation
`∇_κ(∇_μ ξ_ν + ∇_ν ξ_μ)=0` at one point.  Metric compatibility has already
lowered the vector index, so the equation is expressed entirely through the
metric and the second covariant derivative of the contravariant field. -/
def DifferentiatedKillingEquationAt {ι : Type*} [Fintype ι]
    (g : Matrix ι ι ℝ) (nabla2V : ι → ι → ι → ℝ) : Prop :=
  ∀ κ μ ν,
    (∑ ρ, g ν ρ * nabla2V κ μ ρ) +
      ∑ ρ, g μ ρ * nabla2V κ ν ρ = 0

/-- Pointwise second-jet data for a genuine Killing field on a pseudo-Riemannian
metric.  Unlike the earlier carrier, this structure does not assume either the
vanishing derivative of the divergence or the contracted wave equation.  Both
are consequences of `differentiatedKilling`, proved below. -/
structure KillingSecondJetAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g gInv : Matrix ι ι ℝ)
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (dV : ι → ι → ℝ) (ddV : ι → ι → ι → ℝ) : Prop where
  metricSymmetric : Matrix.transpose g = g
  inverseLeft : gInv * g = 1
  inverseRight : g * gInv = 1
  torsionFree : IsTorsionFree Γ
  secondPartialsCommute : ∀ μ ν ρ, ddV μ ν ρ = ddV ν μ ρ
  killing : KillingEquationAt g (covariantDerivVectorAt Γ V dV)
  differentiatedKilling : DifferentiatedKillingEquationAt g
    (covariantSecondDerivVectorAt Γ dΓ V dV ddV)

/-- An actual chart metric, inverse metric, and `C²` vector field construct
the local Killing second jet.  The first-order field condition is supplied in
the repository's established Lie-derivative form; Levi-Civita metric
compatibility converts it to `KillingEquationAt`.  Smoothness supplies the
commuting coordinate second partials. -/
@[zil_level bridge_theorem]
lemma killingSecondJetAt_of_metricLieDerivative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g gInv : CoordinateVector ι → Matrix ι ι ℝ)
    (V : CoordinateVector ι → ι → ℝ)
    (hg : ∀ x, Matrix.transpose (g x) = g x)
    (hgi : ∀ x, Matrix.transpose (gInv x) = gInv x)
    (hinvLeft : ∀ x, gInv x * g x = 1)
    (hinvRight : ∀ x, g x * gInv x = 1)
    (hV : ∀ ρ, ContDiff ℝ 2 (fun x => V x ρ))
    (hKilling : ∀ x, IsKillingVector (g x)
      (metricFirstJet (frechetCoordinatePartial (ι := ι)) g x)
      (V x) (vectorFirstJet (frechetCoordinatePartial (ι := ι)) V x))
    (hDifferentiated : ∀ x,
      DifferentiatedKillingEquationAt (g x)
        (leviCivitaSecondDerivVectorField
          (frechetCoordinatePartial (ι := ι)) g gInv V x))
    (x : CoordinateVector ι) :
    KillingSecondJetAt (g x) (gInv x)
      (leviCivitaConnectionField
        (frechetCoordinatePartial (ι := ι)) g gInv x)
      (connectionFirstJet (frechetCoordinatePartial (ι := ι))
        (leviCivitaConnectionField
          (frechetCoordinatePartial (ι := ι)) g gInv) x)
      (V x) (vectorFirstJet (frechetCoordinatePartial (ι := ι)) V x)
      (vectorSecondJet (frechetCoordinatePartial (ι := ι)) V x) := by
  let D := frechetCoordinatePartial (ι := ι)
  let dg := metricFirstJet D g x
  let Γ := leviCivitaConnectionField D g gInv x
  have hdg : ∀ κ, Matrix.transpose (dg κ) = dg κ :=
    metricFirstJet_transpose_eq D g hg x
  have htor : IsTorsionFree Γ := by
    simpa [Γ, dg, leviCivitaConnectionField] using
      christoffelFromMetric_isTorsionFree (gInv x) dg hdg
  have hcompat : IsMetricCompatible Γ dg (g x) := by
    simpa [Γ, dg, leviCivitaConnectionField] using
      christoffelFromMetric_isMetricCompatible dg (hg x) (hgi x)
        (hinvLeft x) hdg
  refine
    { metricSymmetric := hg x
      inverseLeft := hinvLeft x
      inverseRight := hinvRight x
      torsionFree := htor
      secondPartialsCommute := ?_
      killing := ?_
      differentiatedKilling := ?_ }
  · exact (vectorSecondPartialsCommute_frechet_of_contDiff V hV) x
  · exact (isKillingVector_iff_killingEquationAt
      (g x) dg Γ (V x) (vectorFirstJet D V x)
      (hg x) htor hcompat).mp (by
        simpa [D, dg] using hKilling x)
  · simpa [D, Γ, leviCivitaSecondDerivVectorField,
      leviCivitaConnectionField] using hDifferentiated x

/-- A two-sided inverse of a symmetric metric is symmetric. -/
lemma inverseMetric_transpose_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g gInv : Matrix ι ι ℝ) (hg : Matrix.transpose g = g)
    (hRight : g * gInv = 1) : Matrix.transpose gInv = gInv := by
  have ht := congrArg Matrix.transpose hRight
  simp only [Matrix.transpose_mul, Matrix.transpose_one, hg] at ht
  calc
    Matrix.transpose gInv = Matrix.transpose gInv * 1 := by rw [Matrix.mul_one]
    _ = Matrix.transpose gInv * (g * gInv) := by rw [hRight]
    _ = (Matrix.transpose gInv * g) * gInv := by rw [Matrix.mul_assoc]
    _ = 1 * gInv := by rw [ht]
    _ = gInv := Matrix.one_mul _

/-- Contracting a covector with a metric and its left inverse returns the
original component. -/
lemma inverseMetric_contract
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g gInv : Matrix ι ι ℝ) (hInv : gInv * g = 1)
    (v : ι → ℝ) (i : ι) :
    (∑ j, gInv i j * ∑ k, g j k * v k) = v i := by
  calc
    (∑ j, gInv i j * ∑ k, g j k * v k) =
        ∑ j, ∑ k, gInv i j * (g j k * v k) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
    _ = ∑ k, ∑ j, gInv i j * (g j k * v k) := Finset.sum_comm
    _ = ∑ k, (∑ j, gInv i j * g j k) * v k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ k, (gInv * g) i k * v k := by
          simp only [Matrix.mul_apply]
    _ = ∑ k, (1 : Matrix ι ι ℝ) i k * v k := by rw [hInv]
    _ = v i := by simp [Matrix.one_apply]

/-- Reorder a triple finite contraction so that the last index is outermost. -/
lemma sum_sum_mul_sum_reorder
    {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (b : ι → ℝ) (T : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, a i j * ∑ k, b k * T i j k) =
      ∑ k, b k * ∑ i, ∑ j, a i j * T i j k := by
  calc
    (∑ i, ∑ j, a i j * ∑ k, b k * T i j k) =
        ∑ i, ∑ j, ∑ k, a i j * (b k * T i j k) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
    _ =
        ∑ i, ∑ k, ∑ j, a i j * (b k * T i j k) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, a i j * (b k * T i j k) := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, b k * (a i j * T i j k) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ k, b k * ∑ i, ∑ j, a i j * T i j k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]

/-- A Killing field is divergence-free.  This is the trace of
`∇_μ ξ_ν + ∇_ν ξ_μ=0`, derived using the inverse metric. -/
@[zil_level bridge_theorem]
lemma killingSecondJet_divergenceZero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g gInv : Matrix ι ι ℝ)
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (dV : ι → ι → ℝ) (ddV : ι → ι → ι → ℝ)
    (hK : KillingSecondJetAt g gInv Γ dΓ V dV ddV) :
    ∑ μ, covariantDerivVectorAt Γ V dV μ μ = 0 := by
  let N := covariantDerivVectorAt Γ V dV
  have hgi : Matrix.transpose gInv = gInv :=
    inverseMetric_transpose_eq g gInv hK.metricSymmetric hK.inverseRight
  have hweighted :
      (∑ μ, ∑ ν, gInv μ ν *
        ((∑ ρ, g ν ρ * N μ ρ) + ∑ ρ, g μ ρ * N ν ρ)) = 0 := by
    apply Finset.sum_eq_zero
    intro μ _
    apply Finset.sum_eq_zero
    intro ν _
    rw [hK.killing μ ν, mul_zero]
  have hfirst :
      (∑ μ, ∑ ν, gInv μ ν * ∑ ρ, g ν ρ * N μ ρ) =
        ∑ μ, N μ μ := by
    apply Finset.sum_congr rfl
    intro μ _
    exact inverseMetric_contract g gInv hK.inverseLeft (fun ρ => N μ ρ) μ
  have hsecond :
      (∑ μ, ∑ ν, gInv μ ν * ∑ ρ, g μ ρ * N ν ρ) =
        ∑ ν, N ν ν := by
    calc
      (∑ μ, ∑ ν, gInv μ ν * ∑ ρ, g μ ρ * N ν ρ) =
          ∑ ν, ∑ μ, gInv μ ν * ∑ ρ, g μ ρ * N ν ρ := Finset.sum_comm
      _ = ∑ ν, ∑ μ, gInv ν μ * ∑ ρ, g μ ρ * N ν ρ := by
            apply Finset.sum_congr rfl
            intro ν _
            apply Finset.sum_congr rfl
            intro μ _
            rw [show gInv μ ν = gInv ν μ by
              simpa [Matrix.transpose_apply] using congrFun (congrFun hgi ν) μ]
      _ = ∑ ν, N ν ν := by
            apply Finset.sum_congr rfl
            intro ν _
            exact inverseMetric_contract g gInv hK.inverseLeft (fun ρ => N ν ρ) ν
  rw [show (∑ μ, ∑ ν, gInv μ ν *
      ((∑ ρ, g ν ρ * N μ ρ) + ∑ ρ, g μ ρ * N ν ρ)) =
      (∑ μ, ∑ ν, gInv μ ν * ∑ ρ, g ν ρ * N μ ρ) +
      ∑ μ, ∑ ν, gInv μ ν * ∑ ρ, g μ ρ * N ν ρ by
        simp_rw [mul_add, Finset.sum_add_distrib]] at hweighted
  rw [hfirst, hsecond] at hweighted
  linarith

/-- The differentiated Killing equation implies
`∇_κ(∇_μ ξ^μ)=0`; this is derived by contracting the two Killing
indices with the inverse metric. -/
@[zil_level bridge_theorem]
lemma killingSecondJet_divergenceDerivativeZero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g gInv : Matrix ι ι ℝ)
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (dV : ι → ι → ℝ) (ddV : ι → ι → ι → ℝ)
    (hK : KillingSecondJetAt g gInv Γ dΓ V dV ddV) (κ : ι) :
    ∑ μ, covariantSecondDerivVectorAt Γ dΓ V dV ddV κ μ μ = 0 := by
  let N := covariantSecondDerivVectorAt Γ dΓ V dV ddV
  have hgi : Matrix.transpose gInv = gInv :=
    inverseMetric_transpose_eq g gInv hK.metricSymmetric hK.inverseRight
  have hweighted :
      (∑ μ, ∑ ν, gInv μ ν *
        ((∑ ρ, g ν ρ * N κ μ ρ) + ∑ ρ, g μ ρ * N κ ν ρ)) = 0 := by
    apply Finset.sum_eq_zero
    intro μ _
    apply Finset.sum_eq_zero
    intro ν _
    rw [hK.differentiatedKilling κ μ ν, mul_zero]
  have hfirst :
      (∑ μ, ∑ ν, gInv μ ν * ∑ ρ, g ν ρ * N κ μ ρ) =
        ∑ μ, N κ μ μ := by
    apply Finset.sum_congr rfl
    intro μ _
    exact inverseMetric_contract g gInv hK.inverseLeft (fun ρ => N κ μ ρ) μ
  have hsecond :
      (∑ μ, ∑ ν, gInv μ ν * ∑ ρ, g μ ρ * N κ ν ρ) =
        ∑ ν, N κ ν ν := by
    calc
      (∑ μ, ∑ ν, gInv μ ν * ∑ ρ, g μ ρ * N κ ν ρ) =
          ∑ ν, ∑ μ, gInv μ ν * ∑ ρ, g μ ρ * N κ ν ρ := Finset.sum_comm
      _ = ∑ ν, ∑ μ, gInv ν μ * ∑ ρ, g μ ρ * N κ ν ρ := by
            apply Finset.sum_congr rfl
            intro ν _
            apply Finset.sum_congr rfl
            intro μ _
            rw [show gInv μ ν = gInv ν μ by
              simpa [Matrix.transpose_apply] using congrFun (congrFun hgi ν) μ]
      _ = ∑ ν, N κ ν ν := by
            apply Finset.sum_congr rfl
            intro ν _
            exact inverseMetric_contract g gInv hK.inverseLeft (fun ρ => N κ ν ρ) ν
  rw [show (∑ μ, ∑ ν, gInv μ ν *
      ((∑ ρ, g ν ρ * N κ μ ρ) + ∑ ρ, g μ ρ * N κ ν ρ)) =
      (∑ μ, ∑ ν, gInv μ ν * ∑ ρ, g ν ρ * N κ μ ρ) +
      ∑ μ, ∑ ν, gInv μ ν * ∑ ρ, g μ ρ * N κ ν ρ by
        simp_rw [mul_add, Finset.sum_add_distrib]] at hweighted
  rw [hfirst, hsecond] at hweighted
  linarith

/-- The other contraction of the differentiated Killing equation gives
`□ξ^ν = -g^{νβ}∇_μ∇_βξ^μ`. -/
@[zil_level bridge_theorem]
lemma killingSecondJet_wave_eq_neg_contraction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g gInv : Matrix ι ι ℝ)
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (dV : ι → ι → ℝ) (ddV : ι → ι → ι → ℝ)
    (hK : KillingSecondJetAt g gInv Γ dΓ V dV ddV) (ν : ι) :
    covariantVectorWaveAt gInv
        (covariantSecondDerivVectorAt Γ dΓ V dV ddV) ν =
      -∑ β, gInv ν β *
        ∑ μ, covariantSecondDerivVectorAt Γ dΓ V dV ddV μ β μ := by
  let N := covariantSecondDerivVectorAt Γ dΓ V dV ddV
  have hlower (β : ι) :
      (∑ ρ, g β ρ * covariantVectorWaveAt gInv N ρ) +
        ∑ μ, N μ β μ = 0 := by
    have hweighted :
        (∑ μ, ∑ α, gInv μ α *
          ((∑ ρ, g β ρ * N μ α ρ) + ∑ ρ, g α ρ * N μ β ρ)) = 0 := by
      apply Finset.sum_eq_zero
      intro μ _
      apply Finset.sum_eq_zero
      intro α _
      rw [hK.differentiatedKilling μ α β, mul_zero]
    have hfirst :
        (∑ μ, ∑ α, gInv μ α * ∑ ρ, g β ρ * N μ α ρ) =
          ∑ ρ, g β ρ * covariantVectorWaveAt gInv N ρ := by
      simpa only [covariantVectorWaveAt] using
        sum_sum_mul_sum_reorder gInv (fun ρ => g β ρ) N
    have hsecond :
        (∑ μ, ∑ α, gInv μ α * ∑ ρ, g α ρ * N μ β ρ) =
          ∑ μ, N μ β μ := by
      apply Finset.sum_congr rfl
      intro μ _
      exact inverseMetric_contract g gInv hK.inverseLeft (fun ρ => N μ β ρ) μ
    rw [show (∑ μ, ∑ α, gInv μ α *
        ((∑ ρ, g β ρ * N μ α ρ) + ∑ ρ, g α ρ * N μ β ρ)) =
        (∑ μ, ∑ α, gInv μ α * ∑ ρ, g β ρ * N μ α ρ) +
        ∑ μ, ∑ α, gInv μ α * ∑ ρ, g α ρ * N μ β ρ by
          simp_rw [mul_add, Finset.sum_add_distrib]] at hweighted
    rw [hfirst, hsecond] at hweighted
    exact hweighted
  have hraised :
      (∑ β, gInv ν β *
        ((∑ ρ, g β ρ * covariantVectorWaveAt gInv N ρ) + ∑ μ, N μ β μ)) = 0 := by
    apply Finset.sum_eq_zero
    intro β _
    rw [hlower β, mul_zero]
  have hwave := inverseMetric_contract g gInv hK.inverseLeft
    (covariantVectorWaveAt gInv N) ν
  rw [show (∑ β, gInv ν β *
      ((∑ ρ, g β ρ * covariantVectorWaveAt gInv N ρ) + ∑ μ, N μ β μ)) =
      (∑ β, gInv ν β * ∑ ρ, g β ρ * covariantVectorWaveAt gInv N ρ) +
      ∑ β, gInv ν β * ∑ μ, N μ β μ by
        simp_rw [mul_add, Finset.sum_add_distrib]] at hraised
  rw [hwave] at hraised
  linarith

/-- **A17, Killing identity.** The connection-built Ricci commutator plus the differentiated
Killing equation gives `□ξ=-Ric♯(ξ)` pointwise.  Ricci is the existing contraction of
`riemannFromConnection`, not a supplied curvature placeholder. -/
@[zil_level bridge_theorem]
lemma generalKilling_wave_eq_neg_raisedRicci
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g gInv : Matrix ι ι ℝ)
    (Γ : ι → Matrix ι ι ℝ) (dΓ : ι → ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (dV : ι → ι → ℝ) (ddV : ι → ι → ι → ℝ)
    (hK : KillingSecondJetAt g gInv Γ dΓ V dV ddV) (ν : ι) :
    covariantVectorWaveAt gInv
        (covariantSecondDerivVectorAt Γ dΓ V dV ddV) ν =
      -raisedRicciActionAt gInv Γ dΓ V ν := by
  have hContract (α : ι) :=
    covariantSecondDerivVectorAt_commutator_contraction_eq_ricciAction
      Γ dΓ V dV ddV hK.torsionFree hK.secondPartialsCommute α
  have hFirst (α : ι) :
      (∑ μ, covariantSecondDerivVectorAt Γ dΓ V dV ddV μ α μ) =
        ricciActionAt Γ dΓ V α := by
    rw [← hContract α, Finset.sum_sub_distrib,
      killingSecondJet_divergenceDerivativeZero g gInv Γ dΓ V dV ddV hK α]
    ring
  rw [killingSecondJet_wave_eq_neg_contraction g gInv Γ dΓ V dV ddV hK ν]
  unfold raisedRicciActionAt
  simp_rw [hFirst]

/-- **Field-realized general Killing identity.** A `C²` Killing vector field
for the metric-built Levi-Civita connection, together with its covariantly
differentiated Killing equation, satisfies `□ξ = -Ric♯(ξ)` at every chart
point.  All connection, connection-derivative, vector-derivative, and
mixed-partial data are constructed from the actual metric and vector fields. -/
@[zil_level bridge_theorem]
lemma contDiffMetricKilling_wave_eq_neg_raisedRicci_onChart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g gInv : CoordinateVector ι → Matrix ι ι ℝ)
    (V : CoordinateVector ι → ι → ℝ)
    (hg : ∀ x, Matrix.transpose (g x) = g x)
    (hgi : ∀ x, Matrix.transpose (gInv x) = gInv x)
    (hinvLeft : ∀ x, gInv x * g x = 1)
    (hinvRight : ∀ x, g x * gInv x = 1)
    (hV : ∀ ρ, ContDiff ℝ 2 (fun x => V x ρ))
    (hKilling : ∀ x, IsKillingVector (g x)
      (metricFirstJet (frechetCoordinatePartial (ι := ι)) g x)
      (V x) (vectorFirstJet (frechetCoordinatePartial (ι := ι)) V x))
    (hDifferentiated : ∀ x,
      DifferentiatedKillingEquationAt (g x)
        (leviCivitaSecondDerivVectorField
          (frechetCoordinatePartial (ι := ι)) g gInv V x))
    (x : CoordinateVector ι) (ν : ι) :
    covariantVectorWaveAt (gInv x)
        (leviCivitaSecondDerivVectorField
          (frechetCoordinatePartial (ι := ι)) g gInv V x) ν =
      -raisedRicciActionAt (gInv x)
        (leviCivitaConnectionField
          (frechetCoordinatePartial (ι := ι)) g gInv x)
        (connectionFirstJet (frechetCoordinatePartial (ι := ι))
          (leviCivitaConnectionField
            (frechetCoordinatePartial (ι := ι)) g gInv) x)
        (V x) ν := by
  exact generalKilling_wave_eq_neg_raisedRicci
    (g x) (gInv x)
    (leviCivitaConnectionField
      (frechetCoordinatePartial (ι := ι)) g gInv x)
    (connectionFirstJet (frechetCoordinatePartial (ι := ι))
      (leviCivitaConnectionField
        (frechetCoordinatePartial (ι := ι)) g gInv) x)
    (V x) (vectorFirstJet (frechetCoordinatePartial (ι := ι)) V x)
    (vectorSecondJet (frechetCoordinatePartial (ι := ι)) V x)
    (killingSecondJetAt_of_metricLieDerivative
      g gInv V hg hgi hinvLeft hinvRight hV hKilling hDifferentiated x) ν

/-! ## E. Einstein matter source and the horizon limit -/

/-- **Dimension-generic trace reversal, derived from the Einstein equation.**
In every finite dimension `D ≠ 2`, tracing
`Ric - (scalarR/2)g = κT` and using `scalarR = tr(g⁻¹ Ric)` gives
`Ric = κ(T - tr(g⁻¹T)/(D-2) g)`.  The denominator and the exclusion of
dimension two are therefore derived visibly rather than hidden in the
four-dimensional specialization. -/
@[zil_level bridge_theorem]
lemma einsteinFieldEquation_traceReversedRicci
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ric g gInv T : Matrix ι ι ℝ) (scalarR κ : ℝ)
    (hdim : (Fintype.card ι : ℝ) ≠ 2)
    (hinv : gInv * g = 1)
    (hscalar : metricTrace gInv Ric = scalarR)
    (hEFE : einsteinFieldEquation Ric scalarR g T κ) :
    Ric = κ • traceReversedMatter gInv g T := by
  have htrace := congrArg (metricTrace gInv) hEFE
  have hscalar_eq :
      scalarR = -(2 * κ * metricTrace gInv T) /
        ((Fintype.card ι : ℝ) - 2) := by
    have hscalar' := hscalar
    unfold metricTrace at hscalar'
    unfold einsteinFieldEquation einsteinTensor at htrace
    simp only [metricTrace, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.trace_sub, Matrix.trace_smul, hinv, Matrix.trace_one,
      smul_eq_mul] at htrace
    rw [hscalar'] at htrace
    apply (eq_div_iff (sub_ne_zero.mpr hdim)).2
    unfold metricTrace
    linear_combination -2 * htrace
  unfold einsteinFieldEquation einsteinTensor at hEFE
  unfold traceReversedMatter
  rw [hscalar_eq] at hEFE
  ext i j
  have hij := congrFun (congrFun hEFE i) j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hij ⊢
  linear_combination hij

/-- **Four-dimensional trace reversal, derived from the Einstein equation.**
If `scalarR` is the metric trace of the connection-built Ricci tensor, then
`Ric - (scalarR/2)g = κT` implies
`Ric = κ(T - (tr_g T/2)g)`.  This reuses the repository's general
`traceReversedMatter`; it does not supply the trace-reversed equation as a
separate field-equation premise. -/
@[zil_level bridge_theorem]
lemma einsteinFieldEquation_traceReversedRicci4
    (Ric g gInv T : Matrix (Fin 4) (Fin 4) ℝ) (scalarR κ : ℝ)
    (hinv : gInv * g = 1)
    (hscalar : metricTrace gInv Ric = scalarR)
    (hEFE : einsteinFieldEquation Ric scalarR g T κ) :
    Ric = κ • traceReversedMatter gInv g T := by
  exact einsteinFieldEquation_traceReversedRicci
    Ric g gInv T scalarR κ (by norm_num) hinv hscalar hEFE

/-- The raised trace-reversed stress tensor acting on a vector,
`g^{να}(T_{σα} - tr_g(T)/(D-2) g_{σα})V^σ`.  The index order
matches the existing `raisedRicciActionAt` exactly. -/
noncomputable def raisedTraceReversedMatterActionAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (gInv g T : Matrix ι ι ℝ)
    (V : ι → ℝ) (ν : ι) : ℝ :=
  ∑ α, gInv ν α *
    ∑ σ, traceReversedMatter gInv g T σ α * V σ

/-- In dimension `D ≠ 2`, the Einstein equation turns the connection-built
raised Ricci action into the raised trace-reversed matter action.  This is the
dimension-generic local source conversion needed by the Komar/Killing
identity. -/
@[zil_level bridge_theorem]
lemma raisedRicciActionAt_eq_einsteinMatterSource
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g gInv T : Matrix ι ι ℝ)
    (Γ : ι → Matrix ι ι ℝ)
    (dΓ : ι → ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (scalarR κ : ℝ)
    (hdim : (Fintype.card ι : ℝ) ≠ 2)
    (hinv : gInv * g = 1)
    (hscalar : metricTrace gInv (ricciFromConnection Γ dΓ) = scalarR)
    (hEFE : einsteinFieldEquation
      (ricciFromConnection Γ dΓ) scalarR g T κ)
    (ν : ι) :
    raisedRicciActionAt gInv Γ dΓ V ν =
      κ * raisedTraceReversedMatterActionAt gInv g T V ν := by
  have hRic := einsteinFieldEquation_traceReversedRicci
    (ricciFromConnection Γ dΓ) g gInv T scalarR κ hdim hinv hscalar hEFE
  unfold raisedRicciActionAt ricciActionAt
    raisedTraceReversedMatterActionAt
  rw [hRic]
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ α, gInv ν α *
        ∑ σ, κ * traceReversedMatter gInv g T σ α * V σ) =
        ∑ α, κ * (gInv ν α *
          ∑ σ, traceReversedMatter gInv g T σ α * V σ) := by
          apply Finset.sum_congr rfl
          intro α _
          rw [Finset.mul_sum]
          rw [show κ * (gInv ν α *
              ∑ σ, traceReversedMatter gInv g T σ α * V σ) =
              gInv ν α * (κ *
                ∑ σ, traceReversedMatter gInv g T σ α * V σ) by ring,
            Finset.mul_sum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro σ _
          ring
    _ = κ * ∑ α, gInv ν α *
        ∑ σ, traceReversedMatter gInv g T σ α * V σ := by
          rw [Finset.mul_sum]

/-- Four-dimensional specialization of the dimension-generic raised matter
source conversion. -/
@[zil_level bridge_theorem]
lemma raisedRicciActionAt_eq_einsteinMatterSource4
    (g gInv T : Matrix (Fin 4) (Fin 4) ℝ)
    (Γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ)
    (dΓ : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Fin 4 → ℝ) (scalarR κ : ℝ)
    (hinv : gInv * g = 1)
    (hscalar : metricTrace gInv (ricciFromConnection Γ dΓ) = scalarR)
    (hEFE : einsteinFieldEquation
      (ricciFromConnection Γ dΓ) scalarR g T κ)
    (ν : Fin 4) :
    raisedRicciActionAt gInv Γ dΓ V ν =
      κ * raisedTraceReversedMatterActionAt gInv g T V ν :=
  raisedRicciActionAt_eq_einsteinMatterSource
    g gInv T Γ dΓ V scalarR κ (by norm_num) hinv hscalar hEFE ν

/-- **Dimension-generic matter-sourced Killing equation.**  Combining the
geometric Killing identity with the trace reversal derived above yields
`□ξ = -κ (T - tr_g(T)/(D-2)g)♯(ξ)` in every finite dimension other
than two. -/
@[zil_level physical_theorem]
lemma killing_wave_eq_traceReversedMatterSource
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g gInv T : Matrix ι ι ℝ)
    (Γ : ι → Matrix ι ι ℝ)
    (dΓ : ι → ι → Matrix ι ι ℝ)
    (V : ι → ℝ) (dV : ι → ι → ℝ)
    (ddV : ι → ι → ι → ℝ)
    (scalarR κ : ℝ)
    (hdim : (Fintype.card ι : ℝ) ≠ 2)
    (hinv : gInv * g = 1)
    (hscalar : metricTrace gInv (ricciFromConnection Γ dΓ) = scalarR)
    (hEFE : einsteinFieldEquation
      (ricciFromConnection Γ dΓ) scalarR g T κ)
    (hK : KillingSecondJetAt g gInv Γ dΓ V dV ddV)
    (ν : ι) :
    covariantVectorWaveAt gInv
        (covariantSecondDerivVectorAt Γ dΓ V dV ddV) ν =
      -κ * raisedTraceReversedMatterActionAt gInv g T V ν := by
  rw [generalKilling_wave_eq_neg_raisedRicci
      g gInv Γ dΓ V dV ddV hK ν,
    raisedRicciActionAt_eq_einsteinMatterSource
      g gInv T Γ dΓ V scalarR κ hdim hinv hscalar hEFE ν]
  ring

/-- **Matter-sourced Killing equation in four dimensions.**  A genuine local
Killing second jet obeys `□ξ = -Ric♯(ξ)` by the preceding geometric theorem;
the Einstein equation now derives the right-hand side as
`-κ (T - ½ tr_g(T)g)♯(ξ)`.  Thus the Ricci/stress step in the covariant
Verlinde--Komar chain is a theorem, not a supplied identification. -/
@[zil_level physical_theorem]
lemma killing_wave_eq_traceReversedMatterSource4
    (g gInv T : Matrix (Fin 4) (Fin 4) ℝ)
    (Γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ)
    (dΓ : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Fin 4 → ℝ) (dV : Fin 4 → Fin 4 → ℝ)
    (ddV : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (scalarR κ : ℝ)
    (hinv : gInv * g = 1)
    (hscalar : metricTrace gInv (ricciFromConnection Γ dΓ) = scalarR)
    (hEFE : einsteinFieldEquation
      (ricciFromConnection Γ dΓ) scalarR g T κ)
    (hK : KillingSecondJetAt g gInv Γ dΓ V dV ddV)
    (ν : Fin 4) :
    covariantVectorWaveAt gInv
        (covariantSecondDerivVectorAt Γ dΓ V dV ddV) ν =
      -κ * raisedTraceReversedMatterActionAt gInv g T V ν := by
  exact killing_wave_eq_traceReversedMatterSource
    g gInv T Γ dΓ V dV ddV scalarR κ (by norm_num)
      hinv hscalar hEFE hK ν

/-- **Integrated stationary Einstein--Killing source law on a coordinate
box.**  Suppose a four-current realizes one fixed component of the covariant
Killing wave operator as its ordinary box divergence.  The genuine Bochner
divergence theorem and the local matter-sourced Killing identity then imply
that its oriented boundary flux equals the volume integral of
`-κ (T - ½ tr_g(T)g)♯(ξ)`.

The premise `hdivWave` is deliberately explicit: converting a covariant
divergence into an ordinary coordinate divergence requires the appropriate
metric volume-density current.  This theorem proves the integration and
Einstein-source conversion once that analytic current is supplied; it does
not define the boundary term to be the volume term. -/
@[zil_level physical_theorem]
lemma killingEinstein_box_flux_eq_matterSource4
    (a b : BoxPoint 3) (hle : a ≤ b)
    (current : BoxPoint 3 → BoxVector 3 ℝ)
    (currentDeriv : BoxPoint 3 → BoxPoint 3 →L[ℝ] BoxVector 3 ℝ)
    (singular : Set (BoxPoint 3)) (hsingular : singular.Countable)
    (hcontinuous : ContinuousOn current (Icc a b))
    (hderiv : ∀ x ∈
      (Set.pi Set.univ fun i => Ioo (a i) (b i)) \ singular,
        HasFDerivAt current (currentDeriv x) x)
    (hintegrable : IntegrableOn (boxDivergence currentDeriv) (Icc a b))
    (g gInv T : BoxPoint 3 → Matrix (Fin 4) (Fin 4) ℝ)
    (Γ : BoxPoint 3 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ)
    (dΓ : BoxPoint 3 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ)
    (V : BoxPoint 3 → Fin 4 → ℝ)
    (dV : BoxPoint 3 → Fin 4 → Fin 4 → ℝ)
    (ddV : BoxPoint 3 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (scalarR : BoxPoint 3 → ℝ) (κ : ℝ) (ν : Fin 4)
    (hinv : ∀ x ∈ Icc a b, gInv x * g x = 1)
    (hscalar : ∀ x ∈ Icc a b,
      metricTrace (gInv x) (ricciFromConnection (Γ x) (dΓ x)) = scalarR x)
    (hEFE : ∀ x ∈ Icc a b, einsteinFieldEquation
      (ricciFromConnection (Γ x) (dΓ x)) (scalarR x) (g x) (T x) κ)
    (hK : ∀ x ∈ Icc a b,
      KillingSecondJetAt (g x) (gInv x) (Γ x) (dΓ x)
        (V x) (dV x) (ddV x))
    (hdivWave : ∀ x ∈ Icc a b,
      boxDivergence currentDeriv x =
        covariantVectorWaveAt (gInv x)
          (covariantSecondDerivVectorAt
            (Γ x) (dΓ x) (V x) (dV x) (ddV x)) ν) :
    ∑ i : Fin 4,
        ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            current (i.insertNth (b i) x) i) -
          ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            current (i.insertNth (a i) x) i) =
      ∫ x in Icc a b,
        -κ * raisedTraceReversedMatterActionAt
          (gInv x) (g x) (T x) (V x) ν := by
  rw [← boxDivergenceTheorem a b hle current currentDeriv singular
    hsingular hcontinuous hderiv hintegrable]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  rw [hdivWave x hx,
    killing_wave_eq_traceReversedMatterSource4
      (g x) (gInv x) (T x) (Γ x) (dΓ x) (V x) (dV x) (ddV x)
      (scalarR x) κ (hinv x hx) (hscalar x hx) (hEFE x hx) (hK x hx) ν]

/-- **The exact redshifted screen acceleration tends to the Schwarzschild
surface gravity at the horizon.**  The logarithmic redshift potential itself
is singular at `r=2GM`, so the honest geometric statement is the one-sided
exterior limit.  On every exterior point the lapse factors cancel to `GM/r²`;
continuity then gives `1/(4GM)`, exactly the existing
`schwarzschildSurfaceGravity G M 1`. -/
@[zil_level physical_theorem]
lemma redshiftedNormalGradient_tendsto_horizon_surfaceGravity
    (G M : ℝ) (hG : 0 < G) (hM : 0 < M) :
    Filter.Tendsto (redshiftedNormalGradient (G * M))
      (nhdsWithin (2 * G * M) (Set.Ioi (2 * G * M)))
      (nhds (schwarzschildSurfaceGravity G M 1)) := by
  have hR : 2 * G * M ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hG.ne') hM.ne'
  have heq :
      ∀ᶠ r in nhdsWithin (2 * G * M) (Set.Ioi (2 * G * M)),
        redshiftedNormalGradient (G * M) r = G * M / r ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrpos : 0 < r :=
      lt_trans (by positivity : 0 < 2 * G * M) hr
    have hr0 : r ≠ 0 := ne_of_gt hrpos
    have hnum : 2 * (G * M) < r := by
      simpa [mul_assoc] using hr
    have hratio : 2 * (G * M) / r < 1 :=
      (div_lt_one hrpos).2 hnum
    have hf : 0 < schwF (G * M) r := by
      unfold schwF
      linarith
    exact redshiftedNormalGradient_eq (G * M) r hr0 hf
  have hcont : ContinuousAt
      (fun r : ℝ => G * M / r ^ 2) (2 * G * M) :=
    continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hR)
  have hlim : Filter.Tendsto (fun r : ℝ => G * M / r ^ 2)
      (nhdsWithin (2 * G * M) (Set.Ioi (2 * G * M)))
      (nhds (G * M / (2 * G * M) ^ 2)) :=
    hcont.tendsto.mono_left inf_le_left
  have hvalue : G * M / (2 * G * M) ^ 2 =
      schwarzschildSurfaceGravity G M 1 := by
    unfold schwarzschildSurfaceGravity
    field_simp [hG.ne', hM.ne']
    ring
  rw [← hvalue]
  exact hlim.congr' (Filter.Eventually.mono heq fun _ h => h.symm)

/-- A16–A17 capstone for the exact static spherical exterior: the Killing-norm potential,
redshifted force, surface flux, and Komar mass are one chain. -/
@[zil_level physical_theorem]
lemma schwarzschild_redshift_force_komar_chain
    (G M m R : ℝ) (hG : G ≠ 0) (hR : 0 < R)
    (hf : 0 < schwF (G * M) R) :
    killingRedshiftPotential (G * M) R =
        (1 / 2 : ℝ) * Real.log (-timelikeKillingNormSq (G * M) R)
      ∧ covariantScreenForce m (G * M) R = -(G * M * m) / R ^ 2
      ∧ komarScreenFlux G M R = 4 * Real.pi * G * M
      ∧ komarScreenMass G M R = M :=
  ⟨rfl, covariantScreenForce_eq_newton G M m R hR.ne' hf,
    komarScreenFlux_eq G M R hR hf, komarScreenMass_eq G M R hG hR hf⟩

end Physlib.Thermodynamics.VerlindeCovariantGravity

end

/- ZIL-BEGIN -/

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.newtonAccelerationField3At_eq_neg_gradient where
  formalizes @ "claim:a-three-dimensional-newton-acceleration-is-the-negative-frechet-gradient-of-the-translated-potential-minus-g-m-over-distance-away-from-the-source",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonPotentialRadial_hasDerivAt",
  caveat @ "claim:the-identity-is-the-euclidean-exterior-point-source-law-away-from-the-source-it-is-not-a-general-curved-spacetime-acceleration-law"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.newtonEquipotentialScreen_eq_sphere where
  formalizes @ "claim:the-level-sets-of-the-translated-newton-potential-are-exactly-the-round-screens-centered-at-the-source-when-g-times-m-is-nonzero",
  supported_by @ "lean:Physlib.Thermodynamics.VerlindeCovariantGravity.newtonPotential3At_hasFDerivAt"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.poisson_box_integral_flux where
  formalizes @ "claim:the-pointwise-poisson-equation-divergence-field-equals-four-pi-g-rho-integrates-to-the-oriented-boundary-flux-equals-the-volume-integral-of-four-pi-g-rho-on-a-three-dimensional-coordinate-box",
  supported_by @ "lean:Physlib.Mathematics.LovelockRund.boxDivergenceTheorem",
  caveat @ "claim:this-is-the-general-box-divergence-theorem-under-explicit-continuity-differentiability-and-integrability-hypotheses-spherical-radial-and-point-source-specializations-are-proved-separately"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.covariantScreenForce_eq_newton where
  formalizes @ "claim:for-the-exact-static-schwarzschild-exterior-the-killing-redshift-potential-phi-equals-one-half-log-minus-xi-squared-and-the-covariant-force-minus-m-exp-phi-times-the-unit-normal-gradient-of-phi-equals-minus-g-m-m-over-r-squared",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci.metric",
  caveat @ "claim:this-is-the-exact-static-spherical-exterior-in-geometrized-units-c-equals-one-not-an-arbitrary-stationary-spacetime-force-theorem"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.komarScreenMass_eq where
  formalizes @ "claim:the-genuine-spherical-bochner-integral-of-the-schwarzschild-redshifted-normal-gradient-is-four-pi-g-m-so-the-komar-screen-mass-one-over-four-pi-g-times-that-integral-equals-m",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.sphereSurfaceIntegral3_const",
  caveat @ "claim:this-is-the-round-static-schwarzschild-exterior-screen-with-positive-f-and-nonzero-g-not-the-full-komar-theorem-for-an-arbitrary-stationary-asymptotically-flat-manifold"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.generalKilling_wave_eq_neg_raisedRicci where
  formalizes @ "claim:for-a-nondegenerate-symmetric-metric-the-full-covariantly-differentiated-killing-equation-together-with-the-torsion-free-connection-built-ricci-commutator-implies-the-general-pointwise-killing-wave-identity-box-xi-equals-minus-raised-ricci-acting-on-xi",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.covariantSecondDerivVectorAt_commutator_contraction_eq_ricciAction",
  caveat @ "claim:this-is-the-general-local-second-jet-identity-the-input-is-the-covariantly-differentiated-killing-tensor-equation-of-a-c-two-killing-field-not-a-global-existence-theorem-for-a-killing-field"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.isKillingVector_iff_killingEquationAt where
  formalizes @ "claim:for-a-torsion-free-metric-compatible-connection-the-repository-lie-derivative-definition-of-a-killing-vector-is-equivalent-to-the-covariant-killing-equation-nabla-mu-xi-nu-plus-nabla-nu-xi-mu-equals-zero",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.IsKillingVector",
  caveat @ "claim:this-is-a-pointwise-coordinate-equivalence-under-explicit-metric-symmetry-torsion-freedom-and-metric-compatibility"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.contDiffMetricKilling_wave_eq_neg_raisedRicci_onChart where
  formalizes @ "claim:an-actual-c-two-coordinate-killing-vector-field-for-the-metric-built-levi-civita-connection-satisfies-box-xi-equals-minus-raised-ricci-xi-at-every-chart-point-with-all-jets-and-curvature-constructed-from-the-fields",
  supported_by @ "lean:Physlib.Thermodynamics.VerlindeCovariantGravity.generalKilling_wave_eq_neg_raisedRicci",
  caveat @ "claim:the-covariantly-differentiated-killing-equation-is-an-explicit-field-hypothesis-the-theorem-constructs-all-coordinate-jets-and-mixed-partial-regularity-but-is-not-yet-an-atlas-global-killing-field-existence-result"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.einsteinFieldEquation_traceReversedRicci where
  formalizes @ "claim:in-every-finite-dimension-other-than-two-the-einstein-equation-and-scalar-curvature-trace-identity-derive-ricci-equals-kappa-times-t-minus-its-metric-trace-over-d-minus-two-times-the-metric",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral.traceReversedMatter",
  caveat @ "claim:this-is-a-dimension-generic-algebraic-consequence-of-the-supplied-einstein-equation-dimension-two-is-excluded-because-the-trace-reversal-denominator-vanishes-and-kappa-remains-a-physical-input"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.einsteinFieldEquation_traceReversedRicci4 where
  formalizes @ "claim:in-four-dimensions-the-einstein-equation-and-the-definition-of-scalar-curvature-as-the-metric-trace-of-ricci-derive-ricci-equals-kappa-times-the-trace-reversed-stress-tensor",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral.traceReversedMatter",
  caveat @ "claim:this-is-an-exact-algebraic-consequence-of-the-supplied-einstein-field-equation-and-metric-inverse-law-it-does-not-derive-the-einstein-equation-or-calibrate-kappa"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.raisedRicciActionAt_eq_einsteinMatterSource where
  formalizes @ "claim:in-finite-dimension-different-from-two-the-einstein-equation-converts-the-raised-connection-ricci-action-on-a-vector-into-kappa-times-the-raised-trace-reversed-matter-action",
  supported_by @ "lean:Physlib.Thermodynamics.VerlindeCovariantGravity.einsteinFieldEquation_traceReversedRicci",
  caveat @ "claim:this-is-the-local-source-conversion-for-an-existing-connection-and-einstein-solution-not-an-existence-or-uniqueness-theorem-for-that-solution"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.killing_wave_eq_traceReversedMatterSource where
  formalizes @ "claim:in-every-finite-dimension-other-than-two-a-genuine-killing-second-jet-and-the-einstein-equation-imply-box-xi-equals-minus-kappa-times-the-raised-d-dimensional-trace-reversed-matter-tensor-acting-on-xi",
  supported_by @ "lean:Physlib.Thermodynamics.VerlindeCovariantGravity.generalKilling_wave_eq_neg_raisedRicci",
  caveat @ "claim:this-is-a-local-geometric-field-equation-under-explicit-killing-and-einstein-premises-not-a-global-stationary-spacetime-existence-result"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.killing_wave_eq_traceReversedMatterSource4 where
  formalizes @ "claim:in-four-dimensions-the-general-killing-wave-identity-and-the-einstein-equation-derive-box-xi-equals-minus-kappa-times-the-raised-trace-reversed-matter-tensor-acting-on-xi",
  supported_by @ "lean:Physlib.Thermodynamics.VerlindeCovariantGravity.generalKilling_wave_eq_neg_raisedRicci",
  caveat @ "claim:this-is-a-local-second-jet-stationary-source-equation-under-the-einstein-and-killing-premises-not-a-global-komar-volume-integral-or-a-derivation-of-einstein-gravity"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.killingEinstein_box_flux_eq_matterSource4 where
  formalizes @ "claim:on-a-four-dimensional-coordinate-box-a-current-realizing-one-component-of-the-covariant-killing-wave-has-oriented-boundary-flux-equal-to-the-volume-integral-of-minus-kappa-times-the-raised-trace-reversed-einstein-matter-source",
  supported_by @ "lean:Physlib.Mathematics.LovelockRund.boxDivergenceTheorem",
  caveat @ "claim:the-current-must-explicitly-realize-the-covariant-wave-as-an-ordinary-coordinate-divergence-this-is-a-genuine-box-divergence-integral-theorem-but-not-yet-a-global-manifold-komar-stokes-theorem"

zil attach Physlib.Thermodynamics.VerlindeCovariantGravity.redshiftedNormalGradient_tendsto_horizon_surfaceGravity where
  formalizes @ "claim:the-exact-schwarzschild-redshifted-unit-normal-gradient-tends-from-the-static-exterior-to-the-schwarzschild-surface-gravity-at-the-horizon",
  supported_by @ "lean:Physlib.Relativity.SemiClassical.schwarzschildSurfaceGravity",
  caveat @ "claim:the-logarithmic-redshift-potential-is-singular-at-the-horizon-so-the-proved-statement-is-the-one-sided-exterior-limit-in-units-c-equals-one"

zil_file_contract physlib.verlindeCovariantGravity where
  promises "The missing covariant middle of the Verlinde gravity chain. A14 is closed by an actual three-dimensional Frechet derivative: the translated potential Phi(x) = -GM/norm(x-x0) has the repository's isolated exterior field as its Riesz gradient, the physical acceleration is its negative, and the Phi(R) level set is exactly the round metric sphere centered at x0. A15 is closed in two complementary analytic carriers: the Mathlib-backed Bochner divergence theorem on a three-dimensional coordinate box proves that the pointwise Poisson law div field = 4 pi G rho implies the oriented integral boundary flux law, while the existing continuous radial-density shell mass supplies the pointwise radial Poisson equation and genuine spherical surface integral. A16 is closed on the exact Schwarzschild metric: the static Killing norm xi squared = -f defines phi = one half log(-xi squared), exp phi = sqrt f, and the spatial unit-normal factor sqrt f gives exp(phi) n dot grad(phi) = GM/r squared, hence F = -m exp(phi) n dot grad(phi) = -GMm/r squared. A17 integrates that quantity against the genuine parameterized sphere measure to obtain 4 pi GM and Komar mass M. Independently, the general local Killing theorem takes a symmetric nondegenerate metric and the full covariantly differentiated Killing tensor equation, derives both the differentiated zero-divergence and wave contractions from metric inversion, and composes them with the existing connection-built Ricci commutator to prove box xi = -Ric-sharp(xi). In every finite dimension other than two, tracing the Einstein equation derives the D-dimensional trace reversal rather than assuming it, and the Killing identity becomes box xi equals minus kappa times trace-reversed matter acting on xi. In four dimensions the existing box divergence theorem then upgrades any analytic current realizing that covariant wave component to an actual oriented-boundary-flux equals volume-source integral. The exact redshifted exterior acceleration also converges one-sidedly at the horizon to the existing Schwarzschild surface gravity. The established metric-Lie-derivative IsKillingVector predicate is proved equivalent to the covariant Killing equation under Levi-Civita conditions, and an actual C-two metric/vector field constructs all connection and vector jets needed by the identity. Honest scope: the redshift and Komar results are exact for the static round Schwarzschild exterior with c=1, not an arbitrary stationary asymptotically flat manifold; the field-realized Killing theorem still takes the covariantly differentiated Killing equation explicitly and is not a global atlas-level existence theorem for Killing fields; the integrated source theorem requires an explicit coordinate current realizing the covariant divergence and is not yet a global manifold Stokes theorem; the matter source theorem takes the Einstein equation as a physical premise; and none of these identities fixes the empirical value of G or derives Einstein's equation without its stated physical premises."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IsolatedNewtonHodgeSphereFlux.isolatedNewtonExteriorField3At",
    "lean:Physlib.Mathematics.LovelockRund.boxDivergenceTheorem",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildRicci.metric",
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.IsKillingVector",
    "lean:Physlib.QuantumMechanics.ComplexAction.Electromagnetic.CoordinateMaxwellEinstein.covariantSecondDerivVectorAt_commutator_contraction_eq_ricciAction",
    "lean:Physlib.QuantumMechanics.ComplexAction.EddingtonAffineFirstIntegral.traceReversedMatter",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinFieldEquation",
    "lean:Physlib.Relativity.SemiClassical.schwarzschildSurfaceGravity"]
  forbids_substitutes ["a radial derivative presented as a three-dimensional gradient whereas the Frechet derivative is proved here",
    "a boundary flux defined to equal a volume integral whereas the actual Bochner divergence and sphere integrals are used",
    "an arbitrary-stationary Komar theorem whereas this module proves the exact static spherical Schwarzschild exterior case",
    "a Killing curvature identity supplied as a premise whereas the Ricci term is derived from the connection-built commutator",
    "a trace-reversed matter source supplied independently whereas it is derived from the four-dimensional Einstein equation",
    "a boundary source integral defined by equality whereas the existing Bochner divergence theorem is applied to an explicit current",
    "evaluation of the singular logarithmic redshift potential at the horizon whereas the exterior one-sided limit is proved"]
  witnessed_by [Physlib.Thermodynamics.VerlindeCovariantGravity.newtonEquipotentialScreen_eq_sphere,
    Physlib.Thermodynamics.VerlindeCovariantGravity.newtonPotential3At_hasFDerivAt,
    Physlib.Thermodynamics.VerlindeCovariantGravity.newtonAccelerationField3At_eq_neg_gradient,
    Physlib.Thermodynamics.VerlindeCovariantGravity.poisson_box_integral_flux,
    Physlib.Thermodynamics.VerlindeCovariantGravity.radialDensity_poisson_and_integralFlux,
    Physlib.Thermodynamics.VerlindeCovariantGravity.killingRedshiftPotential_hasDerivAt,
    Physlib.Thermodynamics.VerlindeCovariantGravity.redshiftedNormalGradient_eq,
    Physlib.Thermodynamics.VerlindeCovariantGravity.covariantScreenForce_eq_newton,
    Physlib.Thermodynamics.VerlindeCovariantGravity.komarScreenFlux_eq,
    Physlib.Thermodynamics.VerlindeCovariantGravity.komarScreenMass_eq,
    Physlib.Thermodynamics.VerlindeCovariantGravity.isKillingVector_iff_killingEquationAt,
    Physlib.Thermodynamics.VerlindeCovariantGravity.killingSecondJetAt_of_metricLieDerivative,
    Physlib.Thermodynamics.VerlindeCovariantGravity.killingSecondJet_divergenceZero,
    Physlib.Thermodynamics.VerlindeCovariantGravity.killingSecondJet_divergenceDerivativeZero,
    Physlib.Thermodynamics.VerlindeCovariantGravity.killingSecondJet_wave_eq_neg_contraction,
    Physlib.Thermodynamics.VerlindeCovariantGravity.generalKilling_wave_eq_neg_raisedRicci,
    Physlib.Thermodynamics.VerlindeCovariantGravity.contDiffMetricKilling_wave_eq_neg_raisedRicci_onChart,
    Physlib.Thermodynamics.VerlindeCovariantGravity.einsteinFieldEquation_traceReversedRicci,
    Physlib.Thermodynamics.VerlindeCovariantGravity.einsteinFieldEquation_traceReversedRicci4,
    Physlib.Thermodynamics.VerlindeCovariantGravity.raisedRicciActionAt_eq_einsteinMatterSource,
    Physlib.Thermodynamics.VerlindeCovariantGravity.raisedRicciActionAt_eq_einsteinMatterSource4,
    Physlib.Thermodynamics.VerlindeCovariantGravity.killing_wave_eq_traceReversedMatterSource,
    Physlib.Thermodynamics.VerlindeCovariantGravity.killing_wave_eq_traceReversedMatterSource4,
    Physlib.Thermodynamics.VerlindeCovariantGravity.killingEinstein_box_flux_eq_matterSource4,
    Physlib.Thermodynamics.VerlindeCovariantGravity.redshiftedNormalGradient_tendsto_horizon_surfaceGravity,
    Physlib.Thermodynamics.VerlindeCovariantGravity.schwarzschild_redshift_force_komar_chain]

/- ZIL-END -/
