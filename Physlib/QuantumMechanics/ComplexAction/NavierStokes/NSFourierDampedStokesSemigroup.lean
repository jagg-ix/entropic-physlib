/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.PathIntegral.DampedHeatSemigroup
public import
  Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy
public import Mathlib.Analysis.ODE.ExistUnique


/-!
# Finite Fourier entropically damped Stokes semigroup

This module lifts the scalar damped Stokes mode in
`QFT.PathIntegral.DampedHeatSemigroup` to the repository's existing finite
Fourier/Galerkin Navier--Stokes carrier.  For fixed frequencies `kᵢ`, viscosity
`ν`, and non-negative entropic damping `λ`, the diagonal operators

`T(t) aᵢ = exp (-(ν kᵢ² + λ)t) aᵢ`

form a real `C₀` contraction semigroup on `Fin N → ℝ`.  Its infinitesimal
generator is the diagonal multiplier `-(ν kᵢ² + λ)`, and its Laplace resolvent
is componentwise the already formalized Euclidean propagator
`(β + ν kᵢ² + λ)⁻¹`.

The operator is then applied without replacement or duplication to
`NSFieldFourier`.  The existing kinetic energy and enstrophy satisfy the exact
finite-Galerkin balance

`E'(t) = -2ν Ω(t) - 2λ E(t)`,

and non-negative time, viscosity, and damping make the kinetic energy
non-increasing.

This is a finite-dimensional diagonal Stokes/Galerkin result.  It does not
construct the full heat semigroup on an infinite-dimensional function space,
include the pressure projection or nonlinear triadic term, or prove
Navier--Stokes existence or regularity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup

open Filter Set
open Physlib.QFT.PathIntegral
open NSFieldFourierSobolevHierarchy

/-! ## A. Diagonal finite Fourier evolution -/

/-- The damping rate of one finite Fourier mode. -/
def stokesGalerkinRate {N : ℕ} (freq : Fin N → ℕ) (nu lam : ℝ) (i : Fin N) : ℝ :=
  nu * (freq i : ℝ) ^ 2 + lam

/-- The diagonal finite Fourier Stokes evolution. -/
def stokesGalerkinOperator {N : ℕ} (freq : Fin N → ℕ) (nu lam t : ℝ) :
    (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.piMap fun i =>
    dampedHeatOperator (nu * (freq i : ℝ) ^ 2) lam t

@[simp]
lemma stokesGalerkinOperator_apply {N : ℕ} (freq : Fin N → ℕ)
    (nu lam t : ℝ) (a : Fin N → ℝ) (i : Fin N) :
    stokesGalerkinOperator freq nu lam t a i =
      damped_heat_propagator t (nu * (freq i : ℝ) ^ 2) lam * a i := by
  rfl

@[simp]
lemma stokesGalerkinOperator_zero {N : ℕ} (freq : Fin N → ℕ) (nu lam : ℝ) :
    stokesGalerkinOperator freq nu lam 0 =
      ContinuousLinearMap.id ℝ (Fin N → ℝ) := by
  apply ContinuousLinearMap.ext
  intro a
  funext i
  simp [damped_heat_propagator]

lemma stokesGalerkinOperator_add {N : ℕ} (freq : Fin N → ℕ)
    (nu lam s t : ℝ) :
    stokesGalerkinOperator freq nu lam (s + t) =
      (stokesGalerkinOperator freq nu lam s).comp
        (stokesGalerkinOperator freq nu lam t) := by
  apply ContinuousLinearMap.ext
  intro a
  funext i
  simp only [stokesGalerkinOperator_apply, ContinuousLinearMap.comp_apply]
  unfold damped_heat_propagator
  rw [show -(nu * (freq i : ℝ) ^ 2 + lam) * (s + t) =
      (-(nu * (freq i : ℝ) ^ 2 + lam) * s) +
        (-(nu * (freq i : ℝ) ^ 2 + lam) * t) by ring, Real.exp_add]
  ring

lemma stokesGalerkinOperator_continuous {N : ℕ} (freq : Fin N → ℕ)
    (nu lam : ℝ) (a : Fin N → ℝ) :
    Continuous (fun t => stokesGalerkinOperator freq nu lam t a) := by
  exact continuous_pi fun i =>
    dampedHeatOperator_continuous
      (nu * (freq i : ℝ) ^ 2) lam (a i)

lemma stokesGalerkinOperator_norm_le_one {N : ℕ} (freq : Fin N → ℕ)
    (nu lam t : ℝ) (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (ht : 0 ≤ t) :
    ‖stokesGalerkinOperator freq nu lam t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg a)]
  intro i
  rw [stokesGalerkinOperator_apply, norm_mul]
  have hcoeff :
      ‖damped_heat_propagator t (nu * (freq i : ℝ) ^ 2) lam‖ ≤ 1 := by
    rw [Real.norm_eq_abs,
      abs_of_pos (damped_heat_propagator_pos t (nu * (freq i : ℝ) ^ 2) lam)]
    exact damped_heat_propagator_le_one
      t (nu * (freq i : ℝ) ^ 2) lam ht
      (mul_nonneg hnu (sq_nonneg _)) hl
  calc
    ‖damped_heat_propagator t (nu * (freq i : ℝ) ^ 2) lam‖ * ‖a i‖
        ≤ 1 * ‖a i‖ := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
    _ = ‖a i‖ := one_mul _
    _ ≤ ‖a‖ := norm_le_pi_norm a i

def stokesGalerkinC0ContractionSemigroup {N : ℕ} (freq : Fin N → ℕ)
    (nu lam : ℝ) (hnu : 0 ≤ nu) (hl : 0 ≤ lam) :
    RealC0ContractionSemigroup (Fin N → ℝ) where
  operator := stokesGalerkinOperator freq nu lam
  operator_zero := stokesGalerkinOperator_zero freq nu lam
  operator_add := fun s t _ _ => stokesGalerkinOperator_add freq nu lam s t
  strong_continuous := fun a =>
    (stokesGalerkinOperator_continuous freq nu lam a).continuousOn
  contraction := fun t ht =>
    stokesGalerkinOperator_norm_le_one freq nu lam t hnu hl ht

/-! ## B. Infinitesimal generator -/

/-- The diagonal finite Fourier Stokes generator. -/
def stokesGalerkinGenerator {N : ℕ} (freq : Fin N → ℕ) (nu lam : ℝ) :
    (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.piMap fun i =>
    dampedHeatGenerator (nu * (freq i : ℝ) ^ 2) lam

@[simp]
lemma stokesGalerkinGenerator_apply {N : ℕ} (freq : Fin N → ℕ)
    (nu lam : ℝ) (a : Fin N → ℝ) (i : Fin N) :
    stokesGalerkinGenerator freq nu lam a i =
      -(nu * (freq i : ℝ) ^ 2 + lam) * a i := by
  rfl

lemma stokesGalerkin_hasInfinitesimalGenerator {N : ℕ} (freq : Fin N → ℕ)
    (nu lam : ℝ) (hnu : 0 ≤ nu) (hl : 0 ≤ lam) :
    (stokesGalerkinC0ContractionSemigroup freq nu lam hnu hl).HasInfinitesimalGenerator
      (stokesGalerkinGenerator freq nu lam) := by
  intro a
  refine tendsto_pi_nhds.mpr fun i => ?_
  change Tendsto
    (fun t => t⁻¹ •
      (dampedHeatOperator (nu * (freq i : ℝ) ^ 2) lam t (a i) - a i))
    (nhdsWithin 0 (Ioi 0))
    (nhds (dampedHeatGenerator (nu * (freq i : ℝ) ^ 2) lam (a i)))
  exact
    dampedHeat_hasInfinitesimalGenerator
      (nu * (freq i : ℝ) ^ 2) lam
      (mul_nonneg hnu (sq_nonneg _)) hl (a i)

/-! ## C. Finite-mode Laplace resolvent -/

/-- The diagonal Laplace resolvent, defined modewise by the scalar
Hille--Yosida integral already proved in `DampedHeatSemigroup`. -/
def stokesGalerkinLaplaceResolvent {N : ℕ} (freq : Fin N → ℕ)
    (beta nu lam : ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.piMap fun i =>
    dampedHeatLaplaceResolvent beta (nu * (freq i : ℝ) ^ 2) lam

@[simp]
lemma stokesGalerkinLaplaceResolvent_apply {N : ℕ} (freq : Fin N → ℕ)
    (beta nu lam : ℝ) (a : Fin N → ℝ) (i : Fin N) :
    stokesGalerkinLaplaceResolvent freq beta nu lam a i =
      dampedHeatLaplaceResolvent beta (nu * (freq i : ℝ) ^ 2) lam (a i) := by
  rfl

/-- Every component of the finite-mode Laplace resolvent is the existing
Euclidean propagator denominator times that Fourier amplitude. -/
lemma stokesGalerkinLaplaceResolvent_apply_eq_euclideanPropagator
    {N : ℕ} (freq : Fin N → ℕ) (beta nu lam : ℝ)
    (hbeta : 0 < beta) (hnu : 0 ≤ nu) (hl : 0 ≤ lam)
    (a : Fin N → ℝ) (i : Fin N) :
    stokesGalerkinLaplaceResolvent freq beta nu lam a i =
      euclidean_propagator beta (nu * (freq i : ℝ) ^ 2) lam * a i := by
  rw [stokesGalerkinLaplaceResolvent_apply,
    dampedHeatLaplaceResolvent_eq_euclideanPropagator
      beta (nu * (freq i : ℝ) ^ 2) lam hbeta
      (mul_nonneg hnu (sq_nonneg _)) hl]
  rfl

/-- The diagonal resolvent solves `(βI - A)R(β)a = a` on every finite
Fourier mode. -/
lemma stokesGalerkin_resolvent_equation
    {N : ℕ} (freq : Fin N → ℕ) (beta nu lam : ℝ)
    (hbeta : 0 < beta) (hnu : 0 ≤ nu) (hl : 0 ≤ lam)
    (a : Fin N → ℝ) (i : Fin N) :
    beta * stokesGalerkinLaplaceResolvent freq beta nu lam a i -
        stokesGalerkinGenerator freq nu lam
          (stokesGalerkinLaplaceResolvent freq beta nu lam a) i =
      a i := by
  change
    beta * stokesGalerkinLaplaceResolvent freq beta nu lam a i -
      (-(nu * (freq i : ℝ) ^ 2 + lam) *
        stokesGalerkinLaplaceResolvent freq beta nu lam a i) = a i
  rw [stokesGalerkinLaplaceResolvent_apply_eq_euclideanPropagator
    freq beta nu lam hbeta hnu hl a i]
  unfold euclidean_propagator
  have hden : beta + nu * (freq i : ℝ) ^ 2 + lam ≠ 0 := by
    have : 0 < beta + nu * (freq i : ℝ) ^ 2 + lam := by
      positivity
    exact this.ne'
  field_simp
  ring

/-! ## D. Evolution of the repository Fourier/Sobolev carrier -/

/-- Evolve the amplitudes of an existing finite Fourier field while retaining
its mode count and wavenumbers. -/
def dampedStokesEvolution
    (v : NSFieldFourier) (nu lam t : ℝ) : NSFieldFourier where
  N := v.N
  freq := v.freq
  amp := stokesGalerkinOperator v.freq nu lam t v.amp

@[simp]
lemma dampedStokesEvolution_N
    (v : NSFieldFourier) (nu lam t : ℝ) :
    (dampedStokesEvolution v nu lam t).N = v.N := rfl

@[simp]
lemma dampedStokesEvolution_freq
    (v : NSFieldFourier) (nu lam t : ℝ) :
    (dampedStokesEvolution v nu lam t).freq = v.freq := rfl

@[simp]
lemma dampedStokesEvolution_amp
    (v : NSFieldFourier) (nu lam t : ℝ) (i : Fin v.N) :
    (dampedStokesEvolution v nu lam t).amp i =
      damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam * v.amp i := by
  rfl

/-- Each evolved Fourier amplitude solves its diagonal Stokes decay ODE. -/
lemma dampedStokesEvolution_amp_hasDerivAt
    (v : NSFieldFourier) (nu lam t : ℝ) (i : Fin v.N) :
    HasDerivAt
      (fun s => (dampedStokesEvolution v nu lam s).amp i)
      (-(nu * (v.freq i : ℝ) ^ 2 + lam) *
        (dampedStokesEvolution v nu lam t).amp i) t := by
  have h :=
    ((damping_satisfies_decay_ODE
      (nu * (v.freq i : ℝ) ^ 2 + lam) t).mul_const (v.amp i))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · rw [dampedStokesEvolution_amp]
    unfold damped_heat_propagator
    congr 2
  · rw [dampedStokesEvolution_amp]
    unfold damped_heat_propagator
    ring

/-- The exact finite-Galerkin kinetic-energy balance:
`E'(t) = -2ν Ω(t) - 2λ E(t)`. -/
lemma dampedStokesEvolution_kineticEnergy_hasDerivAt
    (v : NSFieldFourier) (nu lam t : ℝ) :
    HasDerivAt
      (fun s => NSFieldFourier.kineticEnergy
        (dampedStokesEvolution v nu lam s))
      (-2 * nu * NSFieldFourier.enstrophy
          (dampedStokesEvolution v nu lam t) -
        2 * lam * NSFieldFourier.kineticEnergy
          (dampedStokesEvolution v nu lam t)) t := by
  change HasDerivAt
    (fun s => ∑ i : Fin v.N,
      (damped_heat_propagator s (nu * (v.freq i : ℝ) ^ 2) lam *
        v.amp i) ^ 2)
    (-2 * nu *
        (∑ i : Fin v.N, (v.freq i : ℝ) ^ 2 *
          (damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam *
            v.amp i) ^ 2) -
      2 * lam *
        (∑ i : Fin v.N,
          (damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam *
            v.amp i) ^ 2)) t
  have hsum : HasDerivAt
      (fun s => ∑ i : Fin v.N,
        (damped_heat_propagator s (nu * (v.freq i : ℝ) ^ 2) lam *
          v.amp i) ^ 2)
      (∑ i : Fin v.N,
        2 *
          (damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam *
            v.amp i) *
        (-(nu * (v.freq i : ℝ) ^ 2 + lam) *
          (damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam *
            v.amp i))) t := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hamp :
        HasDerivAt
          (fun s =>
            damped_heat_propagator s (nu * (v.freq i : ℝ) ^ 2) lam *
              v.amp i)
          (-(nu * (v.freq i : ℝ) ^ 2 + lam) *
            (damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam *
              v.amp i)) t := by
      simpa only [dampedStokesEvolution_amp] using
        dampedStokesEvolution_amp_hasDerivAt v nu lam t i
    have hprod := hamp.mul hamp
    refine
      (hprod.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => by
          change
            (damped_heat_propagator s (nu * (v.freq i : ℝ) ^ 2) lam *
              v.amp i) ^ 2 =
            (damped_heat_propagator s (nu * (v.freq i : ℝ) ^ 2) lam *
              v.amp i) *
            (damped_heat_propagator s (nu * (v.freq i : ℝ) ^ 2) lam *
              v.amp i)
          ring)).congr_deriv ?_
    ring
  have hderiv_eq :
      -2 * nu *
          (∑ i : Fin v.N, (v.freq i : ℝ) ^ 2 *
            (damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam *
              v.amp i) ^ 2) -
        2 * lam *
          (∑ i : Fin v.N,
            (damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam *
              v.amp i) ^ 2) =
      ∑ i : Fin v.N,
        2 *
          (damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam *
            v.amp i) *
        (-(nu * (v.freq i : ℝ) ^ 2 + lam) *
          (damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam *
            v.amp i)) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hderiv_eq]
  exact hsum

set_option backward.isDefEq.respectTransparency false in
/-- Non-negative viscosity, damping, and time make the existing finite
Fourier kinetic energy non-increasing. -/
lemma dampedStokesEvolution_kineticEnergy_le
    (v : NSFieldFourier) (nu lam t : ℝ)
    (hnu : 0 ≤ nu) (hl : 0 ≤ lam) (ht : 0 ≤ t) :
    NSFieldFourier.kineticEnergy (dampedStokesEvolution v nu lam t) ≤
      NSFieldFourier.kineticEnergy v := by
  unfold NSFieldFourier.kineticEnergy
  apply Finset.sum_le_sum
  intro i _
  rw [dampedStokesEvolution_amp, mul_pow]
  have hprop_nonneg :
      0 ≤ damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam :=
    (damped_heat_propagator_pos _ _ _).le
  have hprop_le :
      damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam ≤ 1 :=
    damped_heat_propagator_le_one t (nu * (v.freq i : ℝ) ^ 2) lam
      ht (mul_nonneg hnu (sq_nonneg _)) hl
  have hsq :
      damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg
      (damped_heat_propagator t (nu * (v.freq i : ℝ) ^ 2) lam - 1)]
  nlinarith [sq_nonneg (v.amp i)]

/-! ## E. Pressure-projected nonlinear Galerkin extension -/

/-- Finite-dimensional Leray/Galerkin data for the nonlinear term. The
idempotent map is the pressure-eliminating projection and `convection` is the
triadic `(u·∇)u` coefficient map. Energy neutrality records the analytic
divergence-free cancellation proved pointwise for the repository field
carrier in `FluidDynamics.NavierStokes.KineticEnergyTransport`. -/
structure PressureProjectedNonlinearData (N : ℕ) where
  /-- Finite-mode Leray projector. -/
  leray : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)
  /-- The pressure projection is idempotent. -/
  leray_idempotent : leray.comp leray = leray
  /-- Unprojected nonlinear convection coefficients. -/
  convection : (Fin N → ℝ) → (Fin N → ℝ)
  /-- The finite-mode convection vector field is continuously
  differentiable, as holds for the quadratic triadic polynomial. -/
  convection_contDiff : ContDiff ℝ 1 convection
  /-- Projected convection is energy-neutral on the incompressible carrier. -/
  energy_neutral : ∀ a, ∑ i, a i * leray (convection a) i = 0

namespace PressureProjectedNonlinearData

/-- The pressure-projected nonlinear convection term lies in the range of
the Leray projector. -/
lemma leray_projected_convection
    {N : ℕ} (D : PressureProjectedNonlinearData N) (a : Fin N → ℝ) :
    D.leray (D.leray (D.convection a)) = D.leray (D.convection a) := by
  have h := LinearMap.congr_fun D.leray_idempotent (D.convection a)
  exact h

/-- The entropically damped, pressure-projected nonlinear Galerkin vector
field. This is the diagonal Stokes generator plus the Leray projection of the
quadratic convection term. -/
def nonlinearGalerkinRHS
    {N : ℕ} (D : PressureProjectedNonlinearData N)
    (freq : Fin N → ℕ) (nu lam : ℝ) (a : Fin N → ℝ) : Fin N → ℝ :=
  fun i => -(stokesGalerkinRate freq nu lam i) * a i -
    D.leray (D.convection a) i

/-- The pressure-projected finite Galerkin vector field is continuously
differentiable. This is the analytic hypothesis required by the actual
Picard--Lindelöf local-existence theorem below. -/
lemma nonlinearGalerkinRHS_contDiff
    {N : ℕ} (D : PressureProjectedNonlinearData N)
    (freq : Fin N → ℕ) (nu lam : ℝ) :
    ContDiff ℝ 1 (D.nonlinearGalerkinRHS freq nu lam) := by
  let L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
    ⟨D.leray, D.leray.continuous_of_finiteDimensional⟩
  change ContDiff ℝ 1 (fun a i =>
    -(stokesGalerkinRate freq nu lam i) * a i - L (D.convection a) i)
  rw [contDiff_pi]
  intro i
  have hprojected : ContDiff ℝ 1 (fun a => L (D.convection a)) :=
    L.contDiff.comp D.convection_contDiff
  have hlinear : ContDiff ℝ 1 (fun a : Fin N → ℝ =>
      -(stokesGalerkinRate freq nu lam i) * a i) := by
    fun_prop
  exact hlinear.sub ((contDiff_pi.mp hprojected) i)

/-- Actual local existence for the nonlinear pressure-projected Galerkin
ODE. Unlike the diagonal semigroup formula, the solution is supplied by
Mathlib's Picard--Lindelöf theorem for the continuously differentiable
finite-dimensional vector field. -/
lemma exists_local_nonlinearGalerkin_solution
    {N : ℕ} (D : PressureProjectedNonlinearData N)
    (freq : Fin N → ℕ) (nu lam : ℝ) (a₀ : Fin N → ℝ) (t₀ : ℝ) :
    ∃ u : ℝ → (Fin N → ℝ), u t₀ = a₀ ∧ ∃ ε > 0,
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt u (D.nonlinearGalerkinRHS freq nu lam (u t)) t := by
  exact (D.nonlinearGalerkinRHS_contDiff freq nu lam).contDiffAt
    |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

/-- Squared finite-Galerkin kinetic energy. -/
noncomputable def galerkinEnergy {N : ℕ} (a : Fin N → ℝ) : ℝ :=
  ∑ i, a i ^ 2

/-- Exact nonlinear Galerkin energy balance at vector-field level. The Leray
projected quadratic term cancels, leaving precisely viscous enstrophy and
entropic damping. This does not assert infinite-dimensional existence. -/
lemma energy_pair_nonlinearGalerkinRHS
    {N : ℕ} (D : PressureProjectedNonlinearData N)
    (freq : Fin N → ℕ) (nu lam : ℝ) (a : Fin N → ℝ) :
    ∑ i, a i * D.nonlinearGalerkinRHS freq nu lam a i =
      -nu * (∑ i, (freq i : ℝ) ^ 2 * a i ^ 2) -
        lam * (∑ i, a i ^ 2) := by
  rw [show (∑ i, a i * D.nonlinearGalerkinRHS freq nu lam a i) =
      (∑ i, (-(nu * (freq i : ℝ) ^ 2) * a i ^ 2 - lam * a i ^ 2)) -
        (∑ i, a i * D.leray (D.convection a) i) by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [nonlinearGalerkinRHS, stokesGalerkinRate]
    ring]
  rw [D.energy_neutral, sub_zero]
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  ring

/-- Along every local nonlinear Galerkin solution, the kinetic energy has
the exact viscous-plus-entropic derivative. The pressure-projected quadratic
term disappears by incompressibility. -/
lemma nonlinearGalerkin_energy_hasDerivAt
    {N : ℕ} (D : PressureProjectedNonlinearData N)
    (freq : Fin N → ℕ) (nu lam t : ℝ)
    (u : ℝ → (Fin N → ℝ))
    (hu : HasDerivAt u (D.nonlinearGalerkinRHS freq nu lam (u t)) t) :
    HasDerivAt (fun s => galerkinEnergy (u s))
      (-2 * nu * (∑ i, (freq i : ℝ) ^ 2 * (u t i) ^ 2) -
        2 * lam * galerkinEnergy (u t)) t := by
  have hsum : HasDerivAt (fun s => ∑ i, (u s i) ^ 2)
      (∑ i, (u t i * D.nonlinearGalerkinRHS freq nu lam (u t) i +
        u t i * D.nonlinearGalerkinRHS freq nu lam (u t) i)) t := by
    apply HasDerivAt.fun_sum
    intro i _
    have hi := hasDerivAt_pi.mp hu i
    simpa [pow_two, mul_comm] using hi.inner ℝ hi
  have hderiv :
      (∑ i, (u t i * D.nonlinearGalerkinRHS freq nu lam (u t) i +
        u t i * D.nonlinearGalerkinRHS freq nu lam (u t) i)) =
        -2 * nu * (∑ i, (freq i : ℝ) ^ 2 * (u t i) ^ 2) -
          2 * lam * galerkinEnergy (u t) := by
    calc
      (∑ i, (u t i * D.nonlinearGalerkinRHS freq nu lam (u t) i +
        u t i * D.nonlinearGalerkinRHS freq nu lam (u t) i)) =
          2 * (∑ i, u t i * D.nonlinearGalerkinRHS freq nu lam (u t) i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 2 * (-nu * (∑ i, (freq i : ℝ) ^ 2 * (u t i) ^ 2) -
          lam * (∑ i, (u t i) ^ 2)) := by
        rw [D.energy_pair_nonlinearGalerkinRHS]
      _ = -2 * nu * (∑ i, (freq i : ℝ) ^ 2 * (u t i) ^ 2) -
          2 * lam * galerkinEnergy (u t) := by
        simp only [galerkinEnergy]
        ring
  exact hsum.congr_deriv hderiv

/-- Finite-Galerkin kinetic energy is nonnegative. -/
lemma galerkinEnergy_nonneg
    {N : ℕ} (a : Fin N → ℝ) :
    0 ≤ galerkinEnergy a := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (a i)

/-- With nonnegative viscosity and entropic damping, the exact Galerkin
energy is nonincreasing throughout every interval on which the nonlinear
pressure-projected solution exists. -/
lemma nonlinearGalerkin_energy_antitoneOn
    {N : ℕ} (D : PressureProjectedNonlinearData N)
    (freq : Fin N → ℕ) (nu lam a b : ℝ)
    (u : ℝ → (Fin N → ℝ))
    (hnu : 0 ≤ nu) (hlam : 0 ≤ lam)
    (hu : ∀ t ∈ Set.Ioo a b,
      HasDerivAt u (D.nonlinearGalerkinRHS freq nu lam (u t)) t) :
    AntitoneOn (fun t => galerkinEnergy (u t)) (Set.Ioo a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo a b)
  · intro t ht
    exact (D.nonlinearGalerkin_energy_hasDerivAt freq nu lam t u
      (hu t ht)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    exact (D.nonlinearGalerkin_energy_hasDerivAt freq nu lam t u
      (hu t ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(D.nonlinearGalerkin_energy_hasDerivAt freq nu lam t u
      (hu t ht)).deriv]
    have hfreq : 0 ≤ ∑ i, (freq i : ℝ) ^ 2 * (u t i) ^ 2 := by
      exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have henergy : 0 ≤ galerkinEnergy (u t) := galerkinEnergy_nonneg (u t)
    nlinarith

/-- A genuine local nonlinear pressure-projected Galerkin solution together
with its energy-dissipation law. This is the finite-dimensional nonlinear
existence statement; it deliberately makes no global or infinite-mode claim. -/
lemma exists_local_nonlinearGalerkin_energy_dissipating_solution
    {N : ℕ} (D : PressureProjectedNonlinearData N)
    (freq : Fin N → ℕ) (nu lam : ℝ) (a₀ : Fin N → ℝ) (t₀ : ℝ)
    (hnu : 0 ≤ nu) (hlam : 0 ≤ lam) :
    ∃ u : ℝ → (Fin N → ℝ), u t₀ = a₀ ∧ ∃ ε > 0,
      (∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt u (D.nonlinearGalerkinRHS freq nu lam (u t)) t) ∧
      AntitoneOn (fun t => galerkinEnergy (u t))
        (Set.Ioo (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨u, hu₀, ε, hε, hu⟩ :=
    D.exists_local_nonlinearGalerkin_solution freq nu lam a₀ t₀
  refine ⟨u, hu₀, ε, hε, hu, ?_⟩
  exact D.nonlinearGalerkin_energy_antitoneOn freq nu lam
    (t₀ - ε) (t₀ + ε) u hnu hlam hu

end PressureProjectedNonlinearData

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFourierDampedStokesSemigroup

end
