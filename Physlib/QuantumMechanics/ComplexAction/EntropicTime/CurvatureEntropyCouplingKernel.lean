/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSEnstrophyRateCoadjoint
public import Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.GravitationalFluidComplexNoether
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuasifreeGravFluidNoether
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy
public import Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberYoneda
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ZerothLaw
public import Physlib.Thermodynamics.SecondLaw
public import Physlib.SpaceAndTime.TolmanEhrenfestDissipation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Curvature-entropy coupling kernel

This module collects curvature/entropy coupling material under standard physlib-facing
names and connects it to the existing complex-action spine.  It contains three
algebraic kernels:

* a curvature/entropy coupling scale `Lambda = lambda0(1 + alpha/(R + eps) + gamma phi^2)`, its inverse
  `1/(8 pi Lambda)`, and the local entropy-production rate obtained by multiplying that inverse scale by
  a Tolman-style local temperature;
* a resonance time step `Delta tau = h/(m0 c^2) sqrt(spectralTerm)` and the corresponding entropy
  increment over one step;
* a dimensional exclusion/resonance layer: integer/fractional exclusion branches,
  half-step decoherence contraction, scalar purity, wavelet coordinates, and
  projector probability.

Here those kernels are connected to existing physlib results: the curvature input can be the
`Hopf.DualSphereFiberDecomposition.dualSphereDefect`, the zero-vortex-stretching slice is the
coadjoint enstrophy dissipation, and the imaginary part of the gravitational-fluid complex Noether charge
is half the Navier-Stokes enstrophy rate.  The final section also links the same kernel to the Fourier
Sobolev hierarchy, causal-diamond zeroth-law temperature uniformity, the Verch quasifree gravitational
Noether horizon, and Yoneda faithfulness of the field algebra.  -/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.CurvatureEntropyCouplingKernel

open Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSEnstrophyRateCoadjoint
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.VorticityCoadjointEnstrophy
open Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.GravitationalFluidComplexNoether
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.QuasifreeGravFluidNoether
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Noether
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ZerothLaw
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.EquivalencePrinciple
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellQuasifree
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.WeylCCRSpacetime
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy
open Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberYoneda
open Physlib.Thermodynamics.SecondLaw
open Physlib.SpaceTime
open Physlib.Relativity.SemiClassical
open CategoryTheory

/-! ## Curvature/entropy coupling scale and Tolman-style local rate -/

/-- The curvature/entropy effective coupling scale
`Lambda = lambda0 * (1 + alpha/(ricci + eps) + gamma * phi^2)`. -/
noncomputable def curvatureEntropyCoupling (lambda0 alpha eps gamma ricci phi : ℝ) : ℝ :=
  lambda0 * (1 + alpha / (ricci + eps) + gamma * phi ^ 2)

/-- The inverse gravitational scale associated to the curvature/entropy coupling, `1/(8*pi*Lambda)`. -/
noncomputable def curvatureEntropyInverseScale (lambda0 alpha eps gamma ricci phi : ℝ) : ℝ :=
  1 / (8 * Real.pi * curvatureEntropyCoupling lambda0 alpha eps gamma ricci phi)

/-- Turning off feedback terms leaves the bare coupling. -/
lemma curvatureEntropyCoupling_no_feedback (lambda0 eps ricci phi : ℝ) :
    curvatureEntropyCoupling lambda0 0 eps 0 ricci phi = lambda0 := by
  unfold curvatureEntropyCoupling
  ring

/-- The scalar-field contribution `lambda0 * gamma * phi^2` is non-negative when the coefficients are. -/
lemma curvatureEntropyCoupling_field_term_nonneg (lambda0 gamma phi : ℝ)
    (hlambda0 : 0 ≤ lambda0) (hgamma : 0 ≤ gamma) :
    0 ≤ lambda0 * gamma * phi ^ 2 := by
  exact mul_nonneg (mul_nonneg hlambda0 hgamma) (sq_nonneg phi)

/-- The curvature/entropy coupling is positive under the physical sign assumptions. -/
lemma curvatureEntropyCoupling_pos (lambda0 alpha eps gamma ricci phi : ℝ)
    (hlambda0 : 0 < lambda0) (halpha : 0 ≤ alpha) (heps : 0 < eps)
    (hgamma : 0 ≤ gamma) (hricci : 0 ≤ ricci) :
    0 < curvatureEntropyCoupling lambda0 alpha eps gamma ricci phi := by
  have hden : 0 < ricci + eps := add_pos_of_nonneg_of_pos hricci heps
  have hfrac : 0 ≤ alpha / (ricci + eps) := div_nonneg halpha hden.le
  have hfield : 0 ≤ gamma * phi ^ 2 := mul_nonneg hgamma (sq_nonneg phi)
  have hbracket : 0 < 1 + alpha / (ricci + eps) + gamma * phi ^ 2 := by linarith
  unfold curvatureEntropyCoupling
  exact mul_pos hlambda0 hbracket

/-- The inverse curvature/entropy scale is positive under the same sign assumptions. -/
lemma curvatureEntropyInverseScale_pos (lambda0 alpha eps gamma ricci phi : ℝ)
    (hlambda0 : 0 < lambda0) (halpha : 0 ≤ alpha) (heps : 0 < eps)
    (hgamma : 0 ≤ gamma) (hricci : 0 ≤ ricci) :
    0 < curvatureEntropyInverseScale lambda0 alpha eps gamma ricci phi := by
  have hLam : 0 < curvatureEntropyCoupling lambda0 alpha eps gamma ricci phi :=
    curvatureEntropyCoupling_pos lambda0 alpha eps gamma ricci phi hlambda0 halpha heps hgamma hricci
  have h8pi : 0 < 8 * Real.pi := by positivity
  have hden : 0 < 8 * Real.pi * curvatureEntropyCoupling lambda0 alpha eps gamma ricci phi :=
    mul_pos h8pi hLam
  unfold curvatureEntropyInverseScale
  exact one_div_pos.mpr hden

/-- Formal Ricci sensitivity of the curvature/entropy coupling kernel. -/
noncomputable def curvatureEntropyCoupling_curvatureSensitivity (lambda0 alpha eps _gamma ricci _phi : ℝ) : ℝ :=
  -lambda0 * alpha / (ricci + eps) ^ 2

/-- Formal scalar-field sensitivity of the curvature/entropy coupling kernel. -/
noncomputable def curvatureEntropyCoupling_fieldSensitivity (lambda0 _alpha _eps gamma _ricci phi : ℝ) : ℝ :=
  2 * lambda0 * gamma * phi

/-- The Ricci sensitivity is non-positive for non-negative `lambda0` and `alpha`. -/
lemma curvatureEntropyCoupling_curvatureSensitivity_nonpos (lambda0 alpha eps gamma ricci phi : ℝ)
    (hlambda0 : 0 ≤ lambda0) (halpha : 0 ≤ alpha) :
    curvatureEntropyCoupling_curvatureSensitivity lambda0 alpha eps gamma ricci phi ≤ 0 := by
  have hnum : -lambda0 * alpha ≤ 0 := by
    have hmul : 0 ≤ lambda0 * alpha := mul_nonneg hlambda0 halpha
    linarith
  have hden : 0 ≤ (ricci + eps) ^ 2 := sq_nonneg _
  unfold curvatureEntropyCoupling_curvatureSensitivity
  exact div_nonpos_of_nonpos_of_nonneg hnum hden

/-- The scalar-field sensitivity is non-negative on the non-negative scalar branch. -/
lemma curvatureEntropyCoupling_fieldSensitivity_nonneg (lambda0 alpha eps gamma ricci phi : ℝ)
    (hlambda0 : 0 ≤ lambda0) (hgamma : 0 ≤ gamma) (hphi : 0 ≤ phi) :
    0 ≤ curvatureEntropyCoupling_fieldSensitivity lambda0 alpha eps gamma ricci phi := by
  unfold curvatureEntropyCoupling_fieldSensitivity
  positivity

/-- Flat inverse-temperature scale `T_infty = 1/(k_B beta_infty)`. -/
noncomputable def flatTemperature (kB betaInf : ℝ) : ℝ :=
  1 / (kB * betaInf)

/-- Tolman-style local temperature `T_loc = T_infty / redshift`. -/
noncomputable def tolmanLocalTemperature (kB betaInf redshift : ℝ) : ℝ :=
  flatTemperature kB betaInf / redshift

/-- The local temperature is positive for positive inverse-temperature data and positive redshift. -/
lemma tolmanLocalTemperature_pos (kB betaInf redshift : ℝ)
    (hkB : 0 < kB) (hbeta : 0 < betaInf) (hredshift : 0 < redshift) :
    0 < tolmanLocalTemperature kB betaInf redshift := by
  have hprod : 0 < kB * betaInf := mul_pos hkB hbeta
  have hflat : 0 < flatTemperature kB betaInf := by
    unfold flatTemperature
    exact one_div_pos.mpr hprod
  unfold tolmanLocalTemperature
  exact div_pos hflat hredshift

/-- The scalar redshifted temperature used in this kernel is the pointwise
`TolmanScaling`/Tolman-Ehrenfest temperature when the scalar redshift is the
lapse value `N(x)`. -/
lemma tolmanLocalTemperature_eq_tolmanEhrenfestTemperature
    {sd : ℕ} (L : Lapse sd) (kB betaInf : ℝ) (x : SpaceTime sd) :
    tolmanLocalTemperature kB betaInf (L.N x) =
      (tolmanEhrenfestTemperature L (flatTemperature kB betaInf)).localValue x :=
  rfl

/-- The local entropy-production rate: inverse curvature/entropy scale times Tolman-style local temperature. -/
noncomputable def localEntropyProductionRate
    (kB betaInf redshift lambda0 alpha eps gamma ricci phi : ℝ) : ℝ :=
  curvatureEntropyInverseScale lambda0 alpha eps gamma ricci phi
    * tolmanLocalTemperature kB betaInf redshift

/-- The residual backreaction multiplier used by the coupled entropy-production rate. -/
noncomputable def residualBackreactionFactor (residual gain : ℝ) : ℝ :=
  1 + gain * residual

/-- The coupled entropy-production rate is the local rate multiplied by the residual backreaction factor. -/
noncomputable def backreactionCoupledEntropyProductionRate
    (kB betaInf redshift lambda0 alpha eps gamma ricci phi residual gain : ℝ) : ℝ :=
  localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi
    * residualBackreactionFactor residual gain

/-- The residual backreaction multiplier is non-negative under non-negative residual and gain. -/
lemma residualBackreactionFactor_nonneg (residual gain : ℝ)
    (hresidual : 0 ≤ residual) (hgain : 0 ≤ gain) :
    0 ≤ residualBackreactionFactor residual gain := by
  unfold residualBackreactionFactor
  have hmul : 0 ≤ gain * residual := mul_nonneg hgain hresidual
  linarith

/-- The local entropy rate is non-negative under the physical sign assumptions. -/
lemma localEntropyProductionRate_nonneg
    (kB betaInf redshift lambda0 alpha eps gamma ricci phi : ℝ)
    (hkB : 0 < kB) (hbeta : 0 < betaInf) (hredshift : 0 < redshift)
    (hlambda0 : 0 < lambda0) (halpha : 0 ≤ alpha) (heps : 0 < eps)
    (hgamma : 0 ≤ gamma) (hricci : 0 ≤ ricci) :
    0 ≤ localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi := by
  have hscale : 0 ≤ curvatureEntropyInverseScale lambda0 alpha eps gamma ricci phi :=
    (curvatureEntropyInverseScale_pos lambda0 alpha eps gamma ricci phi
      hlambda0 halpha heps hgamma hricci).le
  have htemp : 0 ≤ tolmanLocalTemperature kB betaInf redshift :=
    (tolmanLocalTemperature_pos kB betaInf redshift hkB hbeta hredshift).le
  unfold localEntropyProductionRate
  exact mul_nonneg hscale htemp

/-- The coupled entropy rate is non-negative when the local rate and backreaction factor are. -/
lemma backreactionCoupledEntropyProductionRate_nonneg
    (kB betaInf redshift lambda0 alpha eps gamma ricci phi residual gain : ℝ)
    (hkB : 0 < kB) (hbeta : 0 < betaInf) (hredshift : 0 < redshift)
    (hlambda0 : 0 < lambda0) (halpha : 0 ≤ alpha) (heps : 0 < eps)
    (hgamma : 0 ≤ gamma) (hricci : 0 ≤ ricci)
    (hresidual : 0 ≤ residual) (hgain : 0 ≤ gain) :
    0 ≤ backreactionCoupledEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi residual gain := by
  unfold backreactionCoupledEntropyProductionRate
  exact mul_nonneg
    (localEntropyProductionRate_nonneg kB betaInf redshift lambda0 alpha eps gamma ricci phi
      hkB hbeta hredshift hlambda0 halpha heps hgamma hricci)
    (residualBackreactionFactor_nonneg residual gain hresidual hgain)

/-- The local rate is exactly the inverse curvature/entropy scale times the flat temperature over redshift. -/
lemma localEntropyProductionRate_eq_inverseScale_mul_flat_over_redshift
    (kB betaInf redshift lambda0 alpha eps gamma ricci phi : ℝ) :
    localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi =
      curvatureEntropyInverseScale lambda0 alpha eps gamma ricci phi
        * (flatTemperature kB betaInf / redshift) := rfl

/-- The local entropy-production rate can be read through the repo's
Tolman-Ehrenfest carrier instead of a standalone scalar redshift formula. -/
lemma localEntropyProductionRate_eq_inverseScale_mul_tolmanEhrenfestTemperature
    {sd : ℕ} (L : Lapse sd) (kB betaInf lambda0 alpha eps gamma ricci phi : ℝ)
    (x : SpaceTime sd) :
    localEntropyProductionRate kB betaInf (L.N x) lambda0 alpha eps gamma ricci phi =
      curvatureEntropyInverseScale lambda0 alpha eps gamma ricci phi
        * (tolmanEhrenfestTemperature L (flatTemperature kB betaInf)).localValue x :=
  rfl

/-- Redshifting the local entropy-production rate by the lapse reconstructs the
asymptotic flat-temperature factor, reusing the same Tolman-Ehrenfest law as the
rest of `Physlib.SpaceTime`. -/
lemma localEntropyProductionRate_mul_lapse_eq_inverseScale_mul_flatTemperature
    {sd : ℕ} (L : Lapse sd) (kB betaInf lambda0 alpha eps gamma ricci phi : ℝ)
    (x : SpaceTime sd) :
    localEntropyProductionRate kB betaInf (L.N x) lambda0 alpha eps gamma ricci phi * L.N x =
      curvatureEntropyInverseScale lambda0 alpha eps gamma ricci phi * flatTemperature kB betaInf := by
  unfold localEntropyProductionRate tolmanLocalTemperature
  field_simp [(L.N_pos x).ne']

/-! ## Coupling to the existing dual-sphere defect -/

/-- The curvature/entropy coupling with its curvature input supplied by physlib's dual-sphere defect density. -/
noncomputable def curvatureEntropyCouplingFromDefect
    (lambda0 alpha eps gamma gradXiSq gradEtaSq crossSq curvSq lam phi : ℝ) : ℝ :=
  curvatureEntropyCoupling lambda0 alpha eps gamma
    (dualSphereDefect gradXiSq gradEtaSq crossSq curvSq lam) phi

/-- The defect-fed curvature/entropy coupling is positive when the defect terms are non-negative. -/
lemma curvatureEntropyCouplingFromDefect_pos
    (lambda0 alpha eps gamma gradXiSq gradEtaSq crossSq curvSq lam phi : ℝ)
    (hlambda0 : 0 < lambda0) (halpha : 0 ≤ alpha) (heps : 0 < eps)
    (hgamma : 0 ≤ gamma) (hgradXi : 0 ≤ gradXiSq) (hgradEta : 0 ≤ gradEtaSq)
    (hcross : 0 ≤ crossSq) (hcurv : 0 ≤ curvSq) (hlam : 0 ≤ lam) :
    0 < curvatureEntropyCouplingFromDefect
      lambda0 alpha eps gamma gradXiSq gradEtaSq crossSq curvSq lam phi := by
  unfold curvatureEntropyCouplingFromDefect
  exact curvatureEntropyCoupling_pos lambda0 alpha eps gamma
    (dualSphereDefect gradXiSq gradEtaSq crossSq curvSq lam) phi
    hlambda0 halpha heps hgamma
    (dualSphereDefect_nonneg gradXiSq gradEtaSq crossSq curvSq lam
      hgradXi hgradEta hcross hcurv hlam)

/-- On a 2D-collapsed dual-sphere leaf, the defect-fed coupling reduces to the zero-defect coupling. -/
lemma curvatureEntropyCouplingFromDefect_2D_collapse
    (lambda0 alpha eps gamma gradXiSq gradEtaSq curvSq lam phi : ℝ) (xi eta : Fin 3 → ℝ)
    (hg1 : gradXiSq = 0) (hg2 : gradEtaSq = 0) (hC : curvSq = 0)
    (hcol : xi 1 * eta 2 = xi 2 * eta 1
      ∧ xi 2 * eta 0 = xi 0 * eta 2
      ∧ xi 0 * eta 1 = xi 1 * eta 0) :
    curvatureEntropyCouplingFromDefect lambda0 alpha eps gamma
        gradXiSq gradEtaSq (crossSphereDefect xi eta) curvSq lam phi =
      curvatureEntropyCoupling lambda0 alpha eps gamma 0 phi := by
  unfold curvatureEntropyCouplingFromDefect
  rw [dualSphereDefect_2D_collapse gradXiSq gradEtaSq curvSq lam xi eta hg1 hg2 hC hcol]

/-! ## Resonance time step and entropy increment -/

/-- Mass associated to an angular frequency, `m = hbar * omega / c^2`. -/
noncomputable def frequencyMass (hbar omega cLight : ℝ) : ℝ :=
  hbar * omega / cLight ^ 2

/-- The frequency-derived mass is non-negative under non-negative `hbar` and `omega`. -/
lemma frequencyMass_nonneg (hbar omega cLight : ℝ)
    (hhbar : 0 ≤ hbar) (homega : 0 ≤ omega) :
    0 ≤ frequencyMass hbar omega cLight := by
  unfold frequencyMass
  exact div_nonneg (mul_nonneg hhbar homega) (sq_nonneg cLight)

/-- Resonance time step `Delta tau = h/(m0*c^2) * sqrt(spectralTerm)`. -/
noncomputable def resonanceTimeStep (h m0 cLight spectralTerm : ℝ) : ℝ :=
  (h / (m0 * cLight ^ 2)) * Real.sqrt spectralTerm

/-- The resonance time step is non-negative when its prefactor is non-negative. -/
lemma resonanceTimeStep_nonneg (h m0 cLight spectralTerm : ℝ)
    (hcoef : 0 ≤ h / (m0 * cLight ^ 2)) :
    0 ≤ resonanceTimeStep h m0 cLight spectralTerm := by
  unfold resonanceTimeStep
  exact mul_nonneg hcoef (Real.sqrt_nonneg spectralTerm)

/-- Squaring the resonance step recovers the spectral term times the squared prefactor. -/
lemma resonanceTimeStep_sq (h m0 cLight spectralTerm : ℝ) (hspectral : 0 ≤ spectralTerm) :
    resonanceTimeStep h m0 cLight spectralTerm ^ 2 =
      (h / (m0 * cLight ^ 2)) ^ 2 * spectralTerm := by
  unfold resonanceTimeStep
  rw [mul_pow, Real.sq_sqrt hspectral]

/-- Entropy increment over one resonance step. -/
noncomputable def entropyIncrementOverResonanceStep
    (rate h m0 cLight spectralTerm : ℝ) : ℝ :=
  rate * resonanceTimeStep h m0 cLight spectralTerm

/-- The entropy increment over one resonance step is non-negative under non-negative rate and step data. -/
lemma entropyIncrementOverResonanceStep_nonneg (rate h m0 cLight spectralTerm : ℝ)
    (hrate : 0 ≤ rate) (hcoef : 0 ≤ h / (m0 * cLight ^ 2)) :
    0 ≤ entropyIncrementOverResonanceStep rate h m0 cLight spectralTerm := by
  unfold entropyIncrementOverResonanceStep
  exact mul_nonneg hrate (resonanceTimeStep_nonneg h m0 cLight spectralTerm hcoef)

/-- If an entropy derivative is the local entropy-production rate, the entropy arrow is non-negative. -/
lemma secondLaw_from_local_rate_identification
    (entropy : ℝ → ℝ) (kB betaInf redshift lambda0 alpha eps gamma ricci phi : ℝ)
    (hkB : 0 < kB) (hbeta : 0 < betaInf) (hredshift : 0 < redshift)
    (hlambda0 : 0 < lambda0) (halpha : 0 ≤ alpha) (heps : 0 < eps)
    (hgamma : 0 ≤ gamma) (hricci : 0 ≤ ricci)
    (hrate : ∀ t, deriv entropy t =
      localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi) :
    ∀ t, 0 ≤ deriv entropy t := by
  intro t
  rw [hrate t]
  exact localEntropyProductionRate_nonneg kB betaInf redshift lambda0 alpha eps gamma ricci phi
    hkB hbeta hredshift hlambda0 halpha heps hgamma hricci

/-- The curvature local rate over one resonance step feeds the time-free
second-law theorem from `Thermodynamics.SecondLaw`: non-negative entropy
increment gives non-negative entropic time. -/
lemma entropicTimeOf_resonanceIncrement_nonneg
    (ℏ h m0 cLight spectralTerm kB betaInf redshift lambda0 alpha eps gamma ricci phi : ℝ)
    (hℏ : 0 < ℏ) (hcoef : 0 ≤ h / (m0 * cLight ^ 2))
    (hkB : 0 < kB) (hbeta : 0 < betaInf) (hredshift : 0 < redshift)
    (hlambda0 : 0 < lambda0) (halpha : 0 ≤ alpha) (heps : 0 < eps)
    (hgamma : 0 ≤ gamma) (hricci : 0 ≤ ricci) :
    0 ≤ entropicTimeOf
      (entropyIncrementOverResonanceStep
        (localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi)
        h m0 cLight spectralTerm)
      ℏ := by
  have hrate :
      0 ≤ localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi :=
    localEntropyProductionRate_nonneg kB betaInf redshift lambda0 alpha eps gamma ricci phi
      hkB hbeta hredshift hlambda0 halpha heps hgamma hricci
  have hS :
      0 ≤ entropyIncrementOverResonanceStep
        (localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi)
        h m0 cLight spectralTerm :=
    entropyIncrementOverResonanceStep_nonneg
      (localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi)
      h m0 cLight spectralTerm hrate hcoef
  exact (secondLaw_timeFree hS hℏ).1

/-! ## Dimensional exclusion and resonance kernels -/

/-- A dimensional exclusion carrier with integer and fractional occupation branches. -/
structure DimensionalExclusionCarrier (H : Type*) where
  /-- Effective dimension of the statistics fiber. -/
  dimension : ℝ
  /-- Whether the model is on an integer-dimensional exclusion branch. -/
  isIntegerDimension : Bool
  /-- Exclusion predicate selected from an antisymmetric branch or fractional-occupation branch. -/
  checkExclusion : (H → Bool) → (H → ℝ → Bool) → H → Bool
  /-- On an integer branch, exclusion is ordinary antisymmetric exclusion. -/
  integer_branch :
    isIntegerDimension = true → ∀ anti occ state, checkExclusion anti occ state = anti state
  /-- On a fractional branch, exclusion is realized by an occupation threshold dimension. -/
  fractional_branch :
    isIntegerDimension = false → ∀ anti occ state, ∃ dim, checkExclusion anti occ state = occ state dim

/-- The fractional statistics model at effective dimension `d`. -/
def fractionalStatisticsModel (d : ℝ) : DimensionalExclusionCarrier ℂ where
  dimension := d
  isIntegerDimension := false
  checkExclusion := fun _ occ state => occ state d
  integer_branch := by
    intro h
    cases h
  fractional_branch := by
    intro _ anti occ state
    exact ⟨d, rfl⟩

/-- The fractional statistics model has the requested effective dimension. -/
lemma fractionalStatisticsModel_dimension (d : ℝ) :
    (fractionalStatisticsModel d).dimension = d := rfl

/-- Integer-dimensional carriers reduce to antisymmetric exclusion. -/
lemma exclusion_integer_branch {H : Type*} (M : DimensionalExclusionCarrier H)
    (h : M.isIntegerDimension = true) (anti : H → Bool) (occ : H → ℝ → Bool) (state : H) :
    M.checkExclusion anti occ state = anti state :=
  M.integer_branch h anti occ state

/-- Fractional-dimensional carriers reduce to an occupation branch for some effective dimension. -/
lemma exclusion_fractional_branch {H : Type*} (M : DimensionalExclusionCarrier H)
    (h : M.isIntegerDimension = false) (anti : H → Bool) (occ : H → ℝ → Bool) (state : H) :
    ∃ dim, M.checkExclusion anti occ state = occ state dim :=
  M.fractional_branch h anti occ state

/-- Exact equality of complex amplitudes in the sharp resonance model. -/
def amplitudeEqual (a b : ℂ) : Prop := a = b

/-- Every complex amplitude is equal to itself in the sharp equality model. -/
lemma amplitudeEqual_refl (a : ℂ) : amplitudeEqual a a := rfl

/-- Half-step scalar decoherence map used in the resonance kernel. -/
noncomputable def halfStepDecoherence (x : ℝ) : ℝ := x / 2

/-- Scalar purity used in the resonance kernel. -/
noncomputable def scalarPurity (x : ℝ) : ℝ := x ^ 2

/-- Half-step decoherence contracts absolute value. -/
lemma halfStepDecoherence_abs_contracts (x : ℝ) : |halfStepDecoherence x| ≤ |x| := by
  unfold halfStepDecoherence
  rw [abs_div]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  have hx : 0 ≤ |x| := abs_nonneg x
  nlinarith

/-- Scalar purity is non-negative. -/
lemma scalarPurity_nonneg (x : ℝ) : 0 ≤ scalarPurity x := by
  unfold scalarPurity
  exact sq_nonneg x

/-- Executing a protocol chain by left-folding scalar operators. -/
def execProtocolChain (ops : List (ℝ → ℝ)) (x : ℝ) : ℝ :=
  ops.foldl (fun acc op => op acc) x

/-- Appending protocol chains composes their executions. -/
lemma execProtocolChain_append (ops more : List (ℝ → ℝ)) (x : ℝ) :
    execProtocolChain (ops ++ more) x = execProtocolChain more (execProtocolChain ops x) := by
  unfold execProtocolChain
  rw [List.foldl_append]

/-- The elementary two-channel wavelet transform. -/
noncomputable def waveletTransform (xy : ℝ × ℝ) : ℝ × ℝ :=
  (xy.1 + xy.2, xy.1 - xy.2)

/-- The first input is recovered from the sum of wavelet channels. -/
lemma wavelet_inverse_x (x y : ℝ) :
    ((waveletTransform (x, y)).1 + (waveletTransform (x, y)).2) / 2 = x := by
  unfold waveletTransform
  ring

/-- The second input is recovered from the difference of wavelet channels. -/
lemma wavelet_inverse_y (x y : ℝ) :
    ((waveletTransform (x, y)).1 - (waveletTransform (x, y)).2) / 2 = y := by
  unfold waveletTransform
  ring

/-- Projector probability of a complex amplitude, written directly as `re^2 + im^2`. -/
noncomputable def projectorProbability (amp : ℂ) : ℝ :=
  amp.re ^ 2 + amp.im ^ 2

/-- Projector probability is non-negative. -/
lemma projectorProbability_nonneg (amp : ℂ) : 0 ≤ projectorProbability amp := by
  unfold projectorProbability
  nlinarith [sq_nonneg amp.re, sq_nonneg amp.im]

/-- Entropy metric used by the resonance kernel. -/
noncomputable def entropyMetric (p : ℝ) : ℝ :=
  -p * Real.log (p + 1)

/-- The entropy metric evaluated on projector probability. -/
lemma entropy_metric_of_projector_probability (amp : ℂ) :
    entropyMetric (projectorProbability amp) =
      -projectorProbability amp * Real.log (projectorProbability amp + 1) := rfl

/-- Resonance purity obtained by applying scalar purity to the dual-sphere defect density. -/
noncomputable def defectResonancePurity
    (gradXiSq gradEtaSq crossSq curvSq lam : ℝ) : ℝ :=
  scalarPurity (dualSphereDefect gradXiSq gradEtaSq crossSq curvSq lam)

/-- Resonance purity is non-negative. -/
lemma defectResonancePurity_nonneg
    (gradXiSq gradEtaSq crossSq curvSq lam : ℝ) :
    0 ≤ defectResonancePurity gradXiSq gradEtaSq crossSq curvSq lam := by
  unfold defectResonancePurity
  exact scalarPurity_nonneg _

/-! ## Physlib synthesis -/

/-- The ported curvature/entropy kernels attached to the existing physlib defect/gravity/fluid spine. -/
lemma curvatureEntropy_defect_gravity_fluid_synthesis
    (gradXiSq gradEtaSq crossSq curvSq lam : ℝ)
    (lambda0 alpha eps gamma ricci phi : ℝ)
    (kB betaInf redshift hbarTau omegaTau cLight h m0 spectralTerm : ℝ)
    (kappa area G nu palinstrophy vortexStretching : ℝ)
    (hgradXi : 0 ≤ gradXiSq) (hgradEta : 0 ≤ gradEtaSq)
    (hcross : 0 ≤ crossSq) (hcurv : 0 ≤ curvSq) (hlam : 0 ≤ lam)
    (hlambda0 : 0 < lambda0) (halpha : 0 ≤ alpha) (heps : 0 < eps)
    (hgamma : 0 ≤ gamma) (hricci : 0 ≤ ricci)
    (hkB : 0 < kB) (hbeta : 0 < betaInf) (hredshift : 0 < redshift)
    (hhbarTau : 0 ≤ hbarTau) (homegaTau : 0 ≤ omegaTau)
    (hcoef : 0 ≤ h / (m0 * cLight ^ 2)) (hspectral : 0 ≤ spectralTerm) :
    0 ≤ dualSphereDefect gradXiSq gradEtaSq crossSq curvSq lam
      ∧ 0 < curvatureEntropyCoupling lambda0 alpha eps gamma ricci phi
      ∧ 0 ≤ localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi
      ∧ 0 ≤ frequencyMass hbarTau omegaTau cLight
      ∧ 0 ≤ entropyIncrementOverResonanceStep
          (localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi)
          h m0 cLight spectralTerm
      ∧ resonanceTimeStep h m0 cLight spectralTerm ^ 2 =
          (h / (m0 * cLight ^ 2)) ^ 2 * spectralTerm
      ∧ enstrophyRate 0 nu palinstrophy = enstrophyDissipationRate nu palinstrophy
      ∧ (gravFluidNoetherCharge kappa area G nu palinstrophy vortexStretching).im =
          enstrophyRate vortexStretching nu palinstrophy / 2 := by
  exact
    ⟨dualSphereDefect_nonneg gradXiSq gradEtaSq crossSq curvSq lam
        hgradXi hgradEta hcross hcurv hlam,
      curvatureEntropyCoupling_pos lambda0 alpha eps gamma ricci phi
        hlambda0 halpha heps hgamma hricci,
      localEntropyProductionRate_nonneg kB betaInf redshift lambda0 alpha eps gamma ricci phi
        hkB hbeta hredshift hlambda0 halpha heps hgamma hricci,
      frequencyMass_nonneg hbarTau omegaTau cLight hhbarTau homegaTau,
      entropyIncrementOverResonanceStep_nonneg
        (localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi)
        h m0 cLight spectralTerm
        (localEntropyProductionRate_nonneg kB betaInf redshift lambda0 alpha eps gamma ricci phi
          hkB hbeta hredshift hlambda0 halpha heps hgamma hricci)
        hcoef,
      resonanceTimeStep_sq h m0 cLight spectralTerm hspectral,
      enstrophyRate_zeroVS_eq_coadjointDissipation nu palinstrophy,
      gravFluidNoetherCharge_im kappa area G nu palinstrophy vortexStretching⟩

/-! ## Links into the wider repository -/

/-- **[Dual-sphere decomposition link].** The curvature/entropy coupling can take its curvature input from
the dual-sphere defect itself.  The same theorem packages the cross-sphere Lagrange identity, defect
non-negativity, and positivity of the defect-fed coupling. -/
lemma curvatureEntropy_dualSphere_decomposition_link (xi eta : Fin 3 → ℝ)
    (gradXiSq gradEtaSq curvSq lam lambda0 alpha eps gamma phi : ℝ)
    (hgradXi : 0 ≤ gradXiSq) (hgradEta : 0 ≤ gradEtaSq) (hcurv : 0 ≤ curvSq)
    (hlam : 0 < lam) (hlambda0 : 0 < lambda0) (halpha : 0 ≤ alpha)
    (heps : 0 < eps) (hgamma : 0 ≤ gamma) :
    crossSphereDefect xi eta = sphereNormSq xi * sphereNormSq eta - (sphereInner xi eta) ^ 2
      ∧ 0 ≤ crossSphereDefect xi eta
      ∧ 0 ≤ dualSphereDefect gradXiSq gradEtaSq (crossSphereDefect xi eta) curvSq lam
      ∧ 0 < curvatureEntropyCouplingFromDefect lambda0 alpha eps gamma
          gradXiSq gradEtaSq (crossSphereDefect xi eta) curvSq lam phi := by
  have hdecomp := dualSphere_fiber_decomposition xi eta gradXiSq gradEtaSq curvSq lam
    hgradXi hgradEta hcurv hlam
  exact
    ⟨hdecomp.1, hdecomp.2.1, hdecomp.2.2.1,
      curvatureEntropyCouplingFromDefect_pos lambda0 alpha eps gamma
        gradXiSq gradEtaSq (crossSphereDefect xi eta) curvSq lam phi
        hlambda0 halpha heps hgamma hgradXi hgradEta hdecomp.2.1 hcurv hlam.le⟩

/-- **[Fourier/Sobolev Navier-Stokes link].** A band-limited Navier-Stokes Fourier field satisfies the
Bernstein Sobolev ladder while the local curvature/entropy production rate is non-negative.  This attaches
the coupling kernel to the repository's `T³` Fourier hierarchy and the `6/5` Sobolev dual exponent. -/
lemma curvatureEntropy_fourierSobolev_link
    (v : NSFieldFourier) (kmax : ℕ) (hfreq : ∀ i, v.freq i ≤ kmax)
    (kB betaInf redshift lambda0 alpha eps gamma ricci phi : ℝ)
    (hkB : 0 < kB) (hbeta : 0 < betaInf) (hredshift : 0 < redshift)
    (hlambda0 : 0 < lambda0) (halpha : 0 ≤ alpha) (heps : 0 < eps)
    (hgamma : 0 ≤ gamma) (hricci : 0 ≤ ricci) :
    0 ≤ localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi
      ∧ NSFieldFourier.palinstrophy v ≤ (kmax : ℝ) ^ 2 * NSFieldFourier.enstrophy v
      ∧ NSFieldFourier.superPalinstrophy v ≤ (kmax : ℝ) ^ 2 * NSFieldFourier.palinstrophy v
      ∧ Hopf.DualSphereSobolevPerfectSquare.sobolevConjugate 3 = 6 := by
  have hrate := localEntropyProductionRate_nonneg kB betaInf redshift lambda0 alpha eps gamma ricci phi
    hkB hbeta hredshift hlambda0 halpha heps hgamma hricci
  have hladder := NSFieldFourier.bandlimited_smooth_ladder v kmax hfreq
  exact ⟨hrate, hladder.1, hladder.2, NSFieldFourier.sobolev_critical_three⟩

/-- **[Causal-diamond zeroth-law link].** Constant surface gravity gives uniform Hawking/Unruh temperature,
and the same hypotheses give a non-negative local curvature/entropy production rate. -/
lemma curvatureEntropy_zerothLaw_temperature_link
    (ℏ κ κ' c kB betaInf redshift lambda0 alpha eps gamma ricci phi : ℝ)
    (hκ : κ = κ') (hkB : 0 < kB) (hbeta : 0 < betaInf) (hredshift : 0 < redshift)
    (hlambda0 : 0 < lambda0) (halpha : 0 ≤ alpha) (heps : 0 < eps)
    (hgamma : 0 ≤ gamma) (hricci : 0 ≤ ricci) :
    hawkingTemperature ℏ κ c kB = hawkingTemperature ℏ κ' c kB
      ∧ Physlib.Thermodynamics.unruhTemperature ℏ kB c κ
        = Physlib.Thermodynamics.unruhTemperature ℏ kB c κ'
      ∧ 0 ≤ localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi := by
  have htemp := zerothLaw_uniform_temperature ℏ κ κ' c kB hκ
  exact
    ⟨htemp.1, htemp.2,
      localEntropyProductionRate_nonneg kB betaInf redshift lambda0 alpha eps gamma ricci phi
        hkB hbeta hredshift hlambda0 halpha heps hgamma hricci⟩

/-- **[Verch quasifree gravitational-Noether link].** The curvature/entropy production rate is compatible
with the repository's identification of the real gravitational-fluid Noether sector with the Verch
quasifree Bekenstein-Hawking horizon. -/
lemma curvatureEntropy_verchQuasifree_noether_link
    (kB betaInf redshift lambda0 alpha eps gamma ricci phi : ℝ)
    (κ A G ℓP ν P VS ħ η : ℝ) (varphi : Fin 2 → ℝ)
    (hkB : 0 < kB) (hbeta : 0 < betaInf) (hredshift : 0 < redshift)
    (hlambda0 : 0 < lambda0) (halpha : 0 ≤ alpha) (heps : 0 < eps)
    (hgamma : 0 ≤ gamma) (hricci : 0 ≤ ricci)
    (hℓ : ℓP ≠ 0) (hħ : ħ ≠ 0) (hη : 0 < η)
    (hcell : schmidtNumber η = cellBondDimension) :
    0 ≤ localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi
      ∧ (gravFluidNoetherCharge κ A G ν P VS).re = noetherCharge κ A G
      ∧ microstateEntropy (A / ℓP ^ 2) = A / (4 * ℓP ^ 2)
      ∧ quasifreeWeight (fun _ _ => entanglementOneParticle ħ η) varphi = Real.exp (-(1 / 4)) := by
  have hrate := localEntropyProductionRate_nonneg kB betaInf redshift lambda0 alpha eps gamma ricci phi
    hkB hbeta hredshift hlambda0 halpha heps hgamma hricci
  have hverch := gravNoether_area_is_verchQuasifree_entropy κ A G ℓP ν P VS ħ η
    hℓ hħ hη varphi hcell
  exact ⟨hrate, hverch.1, hverch.2.1, hverch.2.2⟩

/-- **[Field-algebra Yoneda link].** The local curvature/entropy production rate can be used alongside
Yoneda faithfulness of the complex field-formula algebra: probe-equivalent endomorphisms of the field
algebra are equal. -/
lemma curvatureEntropy_fieldAlgebra_yoneda_link
    {U : Type} [AddCommGroup U] [Module ℂ U]
    {f g : fieldAlgebraObj U ⟶ fieldAlgebraObj U}
    (hprobe : (yoneda (C := ModuleCat ℂ)).map f = (yoneda (C := ModuleCat ℂ)).map g)
    (kB betaInf redshift lambda0 alpha eps gamma ricci phi : ℝ)
    (hkB : 0 < kB) (hbeta : 0 < betaInf) (hredshift : 0 < redshift)
    (hlambda0 : 0 < lambda0) (halpha : 0 ≤ alpha) (heps : 0 < eps)
    (hgamma : 0 ≤ gamma) (hricci : 0 ≤ ricci) :
    0 ≤ localEntropyProductionRate kB betaInf redshift lambda0 alpha eps gamma ricci phi
      ∧ f = g := by
  exact
    ⟨localEntropyProductionRate_nonneg kB betaInf redshift lambda0 alpha eps gamma ricci phi
        hkB hbeta hredshift hlambda0 halpha heps hgamma hricci,
      fieldAlgebra_hom_ext hprobe⟩

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.CurvatureEntropyCouplingKernel

end
