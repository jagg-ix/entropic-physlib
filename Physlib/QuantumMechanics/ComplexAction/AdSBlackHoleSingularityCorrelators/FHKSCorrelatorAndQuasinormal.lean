/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.PicardLefschetzMorseContour
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour
public import Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
public import Physlib.SpaceAndTime.EntropicProperTime
public import Physlib.SpaceAndTime.ProblemOfTimeInstance
public import Physlib.Thermodynamics.BekensteinJacobsonEntropicBits
public import Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.BranchSaddleAndStokesContour
meta import Zil

/-! # FHKS AdS black-hole singularity — FHKSCorrelatorAndQuasinormal

Part of the Fidkowski--Hubeny--Kleban--Shenker formalization (JHEP 02 (2004) 014); see the umbrella
module `AdSBlackHoleSingularityCorrelators` for the full paper docstring. The namespace and every
declaration name are unchanged across the parts; the umbrella module re-exports all of them.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.PicardLefschetzMorseContour
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourShift
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourGaussian
open Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
open Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourEntropicTime
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDMatsubaraContour
open Physlib.QuantumMechanics.NonHermitian.WickRotation
open Physlib.SpaceAndTime
open QuantumInfo.Finite
open MeasureTheory

/-! ## Remaining FHKS correlator and branch-sheet content -/

/-- FHKS Eq. (3.1) on a diagonal energy pair: the thermofield Hamiltonian
`H_L - H_R` annihilates equal-energy pairs. -/
def tfdHamiltonianEigenvalue (ELeft ERight : ℝ) : ℝ :=
  ELeft - ERight

@[simp] lemma tfdHamiltonianEigenvalue_diagonal (E : ℝ) :
    tfdHamiltonianEigenvalue E E = 0 := by
  simp [tfdHamiltonianEigenvalue]

/-- FHKS Eq. (3.2): the unnormalized Boltzmann amplitude
`exp(-beta E/2)` appearing in the thermofield-double state. -/
noncomputable def tfdBoltzmannAmplitude (beta E : ℝ) : ℝ :=
  Real.exp (-(beta * E) / 2)

lemma tfdBoltzmannAmplitude_pos (beta E : ℝ) :
    0 < tfdBoltzmannAmplitude beta E := by
  unfold tfdBoltzmannAmplitude
  positivity

lemma tfdBoltzmannAmplitude_sq (beta E : ℝ) :
    tfdBoltzmannAmplitude beta E ^ 2 = Real.exp (-(beta * E)) := by
  unfold tfdBoltzmannAmplitude
  rw [sq]
  rw [← Real.exp_add]
  congr 1
  ring

/-- A primary-sheet thermal correlator with the FHKS Cauchy-Schwarz bound
Eq. (3.10): `|G(t)| <= G(0)`. -/
structure PrimarySheetBoundedCorrelator where
  corr : ℝ → ℂ
  equalTimeBound : ℝ
  bound_nonneg : 0 ≤ equalTimeBound
  cauchySchwarz_bound : ∀ t : ℝ, ‖corr t‖ ≤ equalTimeBound

/-- A sample value exceeds the FHKS primary-sheet Cauchy-Schwarz bound. -/
def ExceedsPrimarySheetBound (G : PrimarySheetBoundedCorrelator) (t : ℝ) : Prop :=
  G.equalTimeBound < ‖G.corr t‖

/-- FHKS Eq. (3.10) rules out any primary-sheet value above the equal-time
bound.  This is the checked form of "the naive `t_c` light-cone singularity
is not on the primary CFT sheet." -/
lemma primarySheet_no_boundViolation
    (G : PrimarySheetBoundedCorrelator) (t : ℝ) :
    ¬ ExceedsPrimarySheetBound G t :=
  not_lt_of_ge (G.cauchySchwarz_bound t)

/-- If a proposed geodesic value would exceed the primary-sheet bound, then it
cannot be the primary-sheet correlator value at that time. -/
lemma primarySheet_excludes_value_above_bound
    (G : PrimarySheetBoundedCorrelator) {t : ℝ} {z : ℂ}
    (hz : G.equalTimeBound < ‖z‖) :
    G.corr t ≠ z := by
  intro h
  exact primarySheet_no_boundViolation G t (by simpa [ExceedsPrimarySheetBound, h] using hz)

/-- The finite-cutoff resolution of FHKS Eq. (3.13) has three real algebraic
roots when `a >= 0`: `0` and `± sqrt(a)`. -/
lemma resolvedCubicTime_sqrt_root {a : ℝ} (ha : 0 ≤ a) :
    resolvedCubicTime a (Real.sqrt a) = 0 :=
  resolvedCubicTime_root_of_sq_eq (Real.sq_sqrt ha)

lemma resolvedCubicTime_neg_sqrt_root {a : ℝ} (ha : 0 ≤ a) :
    resolvedCubicTime a (-Real.sqrt a) = 0 := by
  apply resolvedCubicTime_root_of_sq_eq
  simpa using Real.sq_sqrt ha

/-- In the finite-black-hole resolution FHKS Eq. (3.14), `a < 0`; the resolved
cubic `E^3 - aE` has only the central real root. -/
lemma resolvedCubicTime_eq_zero_iff_of_neg
    {a E : ℝ} (ha : a < 0) :
    resolvedCubicTime a E = 0 ↔ E = 0 := by
  constructor
  · intro h
    have hfactor : E * (E ^ 2 - a) = 0 := by
      have hpoly : resolvedCubicTime a E = E * (E ^ 2 - a) := by
        unfold resolvedCubicTime
        ring
      rwa [hpoly] at h
    rcases mul_eq_zero.mp hfactor with hE | hquad
    · exact hE
    · have hsq : E ^ 2 = a := by linarith
      have hnonneg : 0 ≤ E ^ 2 := sq_nonneg E
      nlinarith
  · intro h
    simp [resolvedCubicTime, h]

/-- FHKS Eq. (3.16): the Lorentzian correlator is the sum of the two complex
geodesic branches.  In conjugate-pair form this is `w + conjugate(w)`. -/
noncomputable def fhksTwoComplexBranchCorrelator (m : ℝ) (L : ℂ) : ℂ :=
  complexGeodesicWeight m L + starRingEnd ℂ (complexGeodesicWeight m L)

/-- The FHKS two-complex-branch correlator is fixed by complex conjugation. -/
lemma fhksTwoComplexBranchCorrelator_star_fixed (m : ℝ) (L : ℂ) :
    starRingEnd ℂ (fhksTwoComplexBranchCorrelator m L) =
      fhksTwoComplexBranchCorrelator m L := by
  simp [fhksTwoComplexBranchCorrelator, add_comm]

/-- If the second branch weight is the conjugate of the first, Eq. (3.16)
reduces to the explicit conjugate-pair carrier above. -/
lemma fhksTwoBranchCorrelator_eq_conjugatePair
    {m : ℝ} {L₁ L₂ : ℂ}
    (hL : complexGeodesicWeight m L₂ =
      starRingEnd ℂ (complexGeodesicWeight m L₁)) :
    complexGeodesicWeight m L₁ + complexGeodesicWeight m L₂ =
      fhksTwoComplexBranchCorrelator m L₁ := by
  rw [hL]
  rfl

/-- FHKS finite-mass quartic model integrand from Eq. (3.17):
`exp(-m V_tau(x))`. -/
noncomputable def quarticBifurcationIntegrand (m tau x : ℝ) : ℝ :=
  Real.exp (-m * quarticBifurcationPotential tau x)

lemma quarticBifurcationIntegrand_pos (m tau x : ℝ) :
    0 < quarticBifurcationIntegrand m tau x := by
  unfold quarticBifurcationIntegrand
  positivity

/-- The real saddle exponent associated with the quartic model. -/
noncomputable def quarticSaddleExponent (m tau x : ℝ) : ℂ :=
  (-(m * quarticBifurcationPotential tau x) : ℝ)

/-- FHKS Eq. (3.19), exponent form: at a stationary point `x^3 = tau`,
`-m V_tau(x) = (3m/4) x^4`. -/
lemma quarticSaddleExponent_at_stationary
    {m tau x : ℝ} (h : quarticBifurcationStationary tau x) :
    quarticSaddleExponent m tau x = ((3 * m / 4) * x ^ 4 : ℝ) := by
  unfold quarticSaddleExponent
  rw [quarticBifurcationPotential_at_stationary h]
  push_cast
  ring

/-- Any two real quartic saddle exponents are Stokes-aligned in the
Picard-Lefschetz carrier because their imaginary parts are zero. -/
lemma quarticRealSaddles_stokesAligned
    (m tau x y : ℝ) :
    StokesAligned
      (stokesCriticalPoint (quarticSaddleExponent m tau x))
      (stokesCriticalPoint (quarticSaddleExponent m tau y)) := by
  simp [StokesAligned, stokesCriticalPoint, quarticSaddleExponent]

/-- Therefore the repo's Picard-Lefschetz layer supplies a Stokes flow line
between any two real quartic saddle exponents in the FHKS normal form. -/
lemma quarticRealSaddles_have_flowLine
    (m tau x y : ℝ) :
    Nonempty (ChernSimonsStokesFlowLine
      { source := stokesCriticalPoint (quarticSaddleExponent m tau x)
        target := stokesCriticalPoint (quarticSaddleExponent m tau y)
        multiplicity := 1
        aligned := quarticRealSaddles_stokesAligned m tau x y }) :=
  chernSimonsStokesFlowLine_exists _

/-- Appendix F's secondary-sheet variable has a logarithmic singularity
`L ~ 2 log(x - x_c)`. -/
noncomputable def secondarySheetLengthModel (x x_c : ℝ) : ℝ :=
  2 * Real.log (x - x_c)

/-- The secondary-sheet logarithmic length gives the same pole exponent,
now in the Appendix-F variable `x - x_c`. -/
lemma secondarySheetCorrelator_logPole
    (m x x_c : ℝ) (hx : 0 < x - x_c) :
    geodesicCorrelator m (secondarySheetLengthModel x x_c) =
      (x - x_c) ^ (-2 * m) :=
  geodesicCorrelator_criticalLogLength m (x - x_c) hx

/-- Appendix-F numerical location of the secondary-sheet singularity in the
`x = t^(2/3)` variable. -/
def fhksSecondarySheetXc : ℝ :=
  1.35128345

lemma fhksSecondarySheetXc_pos : 0 < fhksSecondarySheetXc := by
  norm_num [fhksSecondarySheetXc]

/-- Appendix E lattice of branch features for the exact geodesic map:
`p + q` even gives the `t^(1/3)` branch points, while odd gives poles. -/
inductive FhksAnalyticFeature
  | cubicBranchPoint
  | pole
  deriving DecidableEq, Repr

/-- The lattice point `(p + i q) pi/2` in the exact `E(t)` sheet analysis. -/
def fhksLatticeTime (p q : ℤ) : ℂ :=
  (((p : ℝ) * Real.pi / 2 : ℝ) : ℂ) +
    Complex.I * (((q : ℝ) * Real.pi / 2 : ℝ) : ℂ)

/-- Appendix E's parity classification of the lattice features. -/
def fhksFeatureAtLattice (p q : ℤ) : FhksAnalyticFeature :=
  if Even (p + q) then
    FhksAnalyticFeature.cubicBranchPoint
  else
    FhksAnalyticFeature.pole

lemma fhksFeatureAtLattice_even {p q : ℤ} (h : Even (p + q)) :
    fhksFeatureAtLattice p q = FhksAnalyticFeature.cubicBranchPoint := by
  simp [fhksFeatureAtLattice, h]

lemma fhksFeatureAtLattice_not_even {p q : ℤ} (h : ¬ Even (p + q)) :
    fhksFeatureAtLattice p q = FhksAnalyticFeature.pole := by
  simp [fhksFeatureAtLattice, h]

/-! ## Large-mass quasinormal-mode bookkeeping -/

/-- FHKS Eq. (3.28), in carrier form:
`omega_n = (m + b0 + 2n)(1 ± i)`. -/
def largeMassQuasinormalMode (m b0 : ℝ) (n : ℕ) (positiveSign : Bool) : ℂ :=
  let amp : ℝ := m + b0 + 2 * (n : ℝ)
  { re := amp, im := if positiveSign then amp else -amp }

/-- The two signs in the large-mass quasinormal spectrum are complex conjugate
branches. -/
lemma largeMassQuasinormalMode_conj
    (m b0 : ℝ) (n : ℕ) :
    starRingEnd ℂ (largeMassQuasinormalMode m b0 n true) =
      largeMassQuasinormalMode m b0 n false := by
  apply Complex.ext
  · simp [largeMassQuasinormalMode]
  · simp [largeMassQuasinormalMode]

/-- The spacing of the large-mass quasinormal tower: increasing `n` by one
adds `2(1 ± i)`. -/
def largeMassQuasinormalSpacing (positiveSign : Bool) : ℂ :=
  { re := 2, im := if positiveSign then 2 else -2 }

lemma largeMassQuasinormalMode_spacing
    (m b0 : ℝ) (n : ℕ) (positiveSign : Bool) :
    largeMassQuasinormalMode m b0 (n + 1) positiveSign -
      largeMassQuasinormalMode m b0 n positiveSign =
        largeMassQuasinormalSpacing positiveSign := by
  cases positiveSign <;>
    apply Complex.ext <;>
      simp [largeMassQuasinormalMode, largeMassQuasinormalSpacing] <;> ring

/-- The real part of the large-mass quasinormal tower is
`m + b0 + 2n`. -/
@[simp] lemma largeMassQuasinormalMode_re
    (m b0 : ℝ) (n : ℕ) (positiveSign : Bool) :
    (largeMassQuasinormalMode m b0 n positiveSign).re =
      m + b0 + 2 * (n : ℝ) := by
  cases positiveSign <;> simp [largeMassQuasinormalMode]

/-- The positive-sign branch has imaginary part `m + b0 + 2n`. -/
@[simp] lemma largeMassQuasinormalMode_im_true
    (m b0 : ℝ) (n : ℕ) :
    (largeMassQuasinormalMode m b0 n true).im =
      m + b0 + 2 * (n : ℝ) := by
  simp [largeMassQuasinormalMode]

/-- The negative-sign branch has imaginary part `-(m + b0 + 2n)`. -/
@[simp] lemma largeMassQuasinormalMode_im_false
    (m b0 : ℝ) (n : ℕ) :
    (largeMassQuasinormalMode m b0 n false).im =
      -(m + b0 + 2 * (n : ℝ)) := by
  simp [largeMassQuasinormalMode]

/-! ## Paper-level synthesis: all sections linked -/

/-- A checked map from the FHKS paper's main sections into one Lean object.

The fields intentionally cross-reference the whole file:

* §2: AdS5 blackening factor, critical time, null singularity hit, geodesic length;
* Appendix A: Kruskal coordinates, horizon regularity, and hyperbola asymmetry;
* §3.1: the primary-sheet Cauchy-Schwarz bound;
* §3.2-3.5: contour deformation, complex branch pair, resolved cubic branches,
  quartic saddle/Stokes normal form, and the secondary-sheet pole;
* Appendix E/F: branch-point/pole lattice and `x_c`;
* §3.6: the large-mass quasinormal-mode tower.

This is the "rest of the paper" link: the later branch/correlator/QNM additions
are not isolated statements; they are checked together with the earlier geometric,
thermal, contour, and GKP-Witten layer. -/
structure FhksPaperLinkedSynthesis
    (theta theta' beta eps c Ham m delta x x_c b0 aCut aBH E tau y
      μ lam xBoundary area GNewton A ℓP S_R S_ent kBphys hbar : ℝ)
    (n : ℕ) (zN : ℤ) (G : PrimarySheetBoundedCorrelator) (t : ℝ) (L : ℂ) : Prop where
  horizon : ads5Blackening 1 = 0
  kruskalHorizon : ads5KruskalRadialUV 1 = 0
  kruskalSingularity : ads5KruskalRadialUV 0 = 1
  kruskalBoundaryFarther : 1 < Real.exp Real.pi
  kruskalBoundaryBelowSingularity :
    ads5KruskalBoundaryUV < ads5KruskalRadialUV 0
  kruskalConformalFactorFinite :
    ads5KruskalRegularConformalFactor 1 = 2 / Real.exp (Real.pi / 2)
  kruskalAppendix : FhksKruskalAppendixBridge
  criticalTime : ads5CriticalBoundaryStartTime = -ads5InverseTemperature / 4
  nullCriticalRe : (nullSingularityTime ads5CriticalBoundaryStartTime).re = 0
  zeroEnergyLength : regularizedGeodesicLength 0 = Real.log 2
  naiveRealBouncePole :
    geodesicCorrelator m (criticalLogLength delta) = delta ^ (-2 * m)
  primarySheetBound : ¬ ExceedsPrimarySheetBound G t
  penroseCriticalNullRayContour :
    nullSingularityTime ads5CriticalBoundaryStartTime =
      penroseNullContourPoint ads5InverseTemperature
  penroseCriticalContourSpacelike :
    lorentzianForm (penroseNullContourPoint ads5InverseTemperature) < 0
  penroseCriticalContourNotPrimaryRay :
    ¬ 0 < lorentzianForm (penroseNullContourPoint ads5InverseTemperature)
  penroseCriticalSecondaryPole :
    hasTcPole (penroseFeatureSheet FhksPenroseFeature.criticalNullRay)
  contourPermitted : 0 < lorentzianForm (Complex.exp (theta * Complex.I))
  deltaContour :
    (∫ s : ℝ, deltaEpsC eps (Complex.exp (theta * Complex.I) * s) *
      Complex.exp (theta * Complex.I)) = 1
  gaussianContour :
    (∫ s : ℝ, contourIntegrand (gaussH c) theta s) =
      ∫ s : ℝ, contourIntegrand (gaussH c) theta' s
  thermalShift : tfdOneSidedTime beta 0 = complexEnergy 0 (beta / 2)
  thermalWeight :
    lapseWeight 0 (beta / 2) Ham =
      complexActionPathIntegralWeight 0 ((beta / 2) * Ham) 1
  thermalDamping :
    ‖lapseWeight 0 (beta / 2) Ham‖ =
      entropyDamping ((beta / 2) * Ham) 1
  matsubaraPole :
    Complex.exp ((beta : ℂ) * matsubaraFreq beta zN) = 1
  complexBranchPair :
    starRingEnd ℂ (fhksTwoComplexBranchCorrelator m L) =
      fhksTwoComplexBranchCorrelator m L
  finiteCutoffRoot : resolvedCubicTime aCut (Real.sqrt aCut) = 0
  finiteBlackHoleCentralBranch : resolvedCubicTime aBH E = 0 ↔ E = 0
  quarticStationaryExponent :
    quarticSaddleExponent m tau y = ((3 * m / 4) * y ^ 4 : ℝ)
  secondarySheetPole :
    geodesicCorrelator m (secondarySheetLengthModel x x_c) =
      (x - x_c) ^ (-2 * m)
  secondarySheetXcPositive : 0 < fhksSecondarySheetXc
  adsCftMassDimension :
    conformalDimension 4 μ * (conformalDimension 4 μ - 4) = μ
  adsCftTwoPointScaling :
    cftTwoPoint (conformalDimension 4 μ) (lam * xBoundary) =
      lam ^ (-2 * conformalDimension 4 μ) *
        cftTwoPoint (conformalDimension 4 μ) xBoundary
  rtEntropyNonnegative : 0 ≤ rtAreaEntropy area GNewton
  bekensteinTauEntropy :
    Physlib.Thermodynamics.bekensteinTauEnt A ℓP =
      Physlib.Thermodynamics.bekensteinEntropy A ℓP / Constants.kB
  bekensteinTauBits :
    Physlib.Thermodynamics.bekensteinTauEnt A ℓP =
      Real.log 2 * Physlib.Thermodynamics.bekensteinBits A ℓP
  horizonCellCapacity :
    microstateEntropy (A / ℓP ^ 2) = A / (4 * ℓP ^ 2)
  masterEntropyDamping :
    ‖complexActionPathIntegralWeight S_R ((hbar / kBphys) * S_ent) hbar‖ =
      Real.exp (-(S_ent / kBphys))
  appendixEBranchPoint :
    fhksFeatureAtLattice 0 0 = FhksAnalyticFeature.cubicBranchPoint
  appendixEPole :
    fhksFeatureAtLattice 1 0 = FhksAnalyticFeature.pole
  qnmConjugate :
    starRingEnd ℂ (largeMassQuasinormalMode m b0 n true) =
      largeMassQuasinormalMode m b0 n false
  qnmSpacing :
    largeMassQuasinormalMode m b0 (n + 1) true -
      largeMassQuasinormalMode m b0 n true =
        largeMassQuasinormalSpacing true

/-- The FHKS paper-level synthesis theorem.  Supplying the analytic side
conditions for the chosen contour, pole variable, and branch resolutions lets
Lean assemble the whole paper's formal content into `FhksPaperLinkedSynthesis`. -/
lemma fhksPaper_linkedSynthesis
    (theta theta' beta eps c Ham m delta x x_c b0 aCut aBH E tau y
      μ lam xBoundary area GNewton A ℓP S_R S_ent kBphys hbar : ℝ)
    (n : ℕ) (zN : ℤ) (G : PrimarySheetBoundedCorrelator) (t : ℝ) (L : ℂ)
    (htheta : |theta| < Real.pi / 4) (htheta' : |theta'| < Real.pi / 4)
    (heps : 0 < eps) (hc : 0 < c) (hdelta : 0 < delta)
    (hx : 0 < x - x_c) (haCut : 0 ≤ aCut) (haBH : aBH < 0)
    (hbeta : beta ≠ 0) (hBF : 0 ≤ (4 / 2 : ℝ) ^ 2 + μ)
    (hlam : 0 < lam) (harea : 0 ≤ area) (hGNewton : 0 < GNewton)
    (hℓP : ℓP ≠ 0) (hhbar : hbar ≠ 0) (hkBphys : kBphys ≠ 0)
    (hstat : quarticBifurcationStationary tau y) :
    FhksPaperLinkedSynthesis theta theta' beta eps c Ham m delta x x_c b0
      aCut aBH E tau y μ lam xBoundary area GNewton A ℓP S_R S_ent kBphys hbar
      n zN G t L where
  horizon := ads5Blackening_horizon
  kruskalHorizon := ads5KruskalRadialUV_horizon
  kruskalSingularity := ads5KruskalRadialUV_singularity
  kruskalBoundaryFarther := ads5KruskalBoundary_farther_than_singularity
  kruskalBoundaryBelowSingularity := ads5KruskalBoundaryUV_lt_singularityUV
  kruskalConformalFactorFinite := ads5KruskalRegularConformalFactor_horizon
  kruskalAppendix := fhksKruskalAppendix_bridge
  criticalTime := ads5CriticalBoundaryStartTime_eq_neg_beta_div_four
  nullCriticalRe := nullSingularityTime_critical_re
  zeroEnergyLength := regularizedGeodesicLength_zero
  naiveRealBouncePole := geodesicCorrelator_criticalLogLength m delta hdelta
  primarySheetBound := primarySheet_no_boundViolation G t
  penroseCriticalNullRayContour := penroseCriticalNullRay_eq_contourPoint
  penroseCriticalContourSpacelike := penroseCriticalNullContour_spacelike
  penroseCriticalContourNotPrimaryRay := penroseCriticalNullContour_not_primaryRay
  penroseCriticalSecondaryPole := penroseCriticalNullRay_has_tcPole
  contourPermitted := fhksContourRay_permitted htheta
  deltaContour := fhksContour_deltaNormalization heps htheta
  gaussianContour := fhksGaussianContour_independent hc htheta htheta'
  thermalShift := fhksTfdShift_eq_complexEnergy beta
  thermalWeight := fhksThermalContourWeight_eq_master beta Ham
  thermalDamping := lapseWeight_modulus_eq_entropyDamping 0 (beta / 2) Ham
  matsubaraPole := bose_pole beta zN hbeta
  complexBranchPair := fhksTwoComplexBranchCorrelator_star_fixed m L
  finiteCutoffRoot := resolvedCubicTime_sqrt_root haCut
  finiteBlackHoleCentralBranch := resolvedCubicTime_eq_zero_iff_of_neg haBH
  quarticStationaryExponent := quarticSaddleExponent_at_stationary hstat
  secondarySheetPole := secondarySheetCorrelator_logPole m x x_c hx
  secondarySheetXcPositive := fhksSecondarySheetXc_pos
  adsCftMassDimension := massDimension_relation 4 μ hBF
  adsCftTwoPointScaling :=
    cftTwoPoint_scaling (conformalDimension 4 μ) xBoundary lam hlam
  rtEntropyNonnegative := rtAreaEntropy_nonneg area GNewton harea hGNewton
  bekensteinTauEntropy :=
    Physlib.Thermodynamics.bekensteinTauEnt_eq_entropy_div_kB
      (A := A) (ℓP := ℓP) hℓP
  bekensteinTauBits :=
    Physlib.Thermodynamics.bekensteinTauEnt_eq_ln2_mul_bits
      (A := A) (ℓP := ℓP) hℓP
  horizonCellCapacity := bekensteinHawking_recovery A ℓP hℓP
  masterEntropyDamping := master_modulus_is_entropy S_R S_ent kBphys hbar hhbar hkBphys
  appendixEBranchPoint := by
    have h : Even ((0 : ℤ) + 0) := by norm_num
    exact fhksFeatureAtLattice_even h
  appendixEPole := by
    have h : ¬ Even ((1 : ℤ) + 0) := by norm_num
    exact fhksFeatureAtLattice_not_even h
  qnmConjugate := largeMassQuasinormalMode_conj m b0 n
  qnmSpacing := largeMassQuasinormalMode_spacing m b0 n true


end Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.quarticSaddleExponent_at_stationary where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.quarticBifurcationPotential_at_stationary",
  formalizes @ "claim:at-a-stationary-point-where-x-cubed-equals-tau-the-fhks-quartic-saddle-exponent-minus-m-times-the-potential-equals-three-m-over-four-times-x-to-the-fourth-fhks-equation-3-19"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.quarticRealSaddles_stokesAligned where
  formalizes @ "claim:any-two-real-quartic-saddle-exponents-are-stokes-aligned-in-the-picard-lefschetz-carrier-because-their-imaginary-parts-both-vanish",
  requires @ "claim:at-a-stationary-point-where-x-cubed-equals-tau-the-fhks-quartic-saddle-exponent-minus-m-times-the-potential-equals-three-m-over-four-times-x-to-the-fourth-fhks-equation-3-19"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.fhksTwoBranchCorrelator_eq_conjugatePair where
  formalizes @ "claim:when-the-second-complex-geodesic-branch-weight-is-the-conjugate-of-the-first-the-fhks-two-branch-correlator-equation-3-16-reduces-to-the-explicit-conjugate-pair-real-correlator"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.quarticBifurcationIntegrand_pos where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-fhks-finite-mass-quartic-model-integrand-exp-minus-m-times-the-potential-is-strictly-positive-a-bona-fide-saddle-point-integrand"

zil_file_contract physlib.fhksCorrelatorAndQuasinormal where
  promises "The FHKS boundary correlator via the complex-saddle / Stokes analysis (Fidkowski-Hubeny-Kleban-Shenker, JHEP 02 (2004) 014). At a stationary point x^3 = tau the quartic saddle exponent is 3m/4 x^4 (quarticSaddleExponent_at_stationary, Eq. 3.19), and any two real quartic saddle exponents are Stokes-aligned because their imaginary parts vanish (quarticRealSaddles_stokesAligned) -- the Stokes phenomenon that selects the contributing saddles. When the second complex-geodesic branch weight is the conjugate of the first, the two-branch correlator (Eq. 3.16) reduces to the explicit conjugate-pair real correlator (fhksTwoBranchCorrelator_eq_conjugatePair), with the finite-mass quartic integrand exp(-m V) strictly positive (quarticBifurcationIntegrand_pos)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.fhksTwoComplexBranchCorrelator",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.quarticSaddleExponent"]
  forbids_substitutes ["the quasinormal-mode sum and the analytic continuation of the boundary two-point function to the complexified time plane, which are the cited AdS/CFT infrastructure",
    "any claim that the light-cone singularity is resolved in the exact quantum correlator, only the semiclassical saddle and Stokes-alignment algebra are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.quarticSaddleExponent_at_stationary,
    Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.quarticRealSaddles_stokesAligned,
    Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.fhksTwoBranchCorrelator_eq_conjugatePair,
    Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.quarticBifurcationIntegrand_pos]

/- ZIL-END -/
