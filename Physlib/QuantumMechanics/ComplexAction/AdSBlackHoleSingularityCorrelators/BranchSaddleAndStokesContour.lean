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
public import Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.GeodesicThermofieldPenrose
meta import Zil

/-! # FHKS AdS black-hole singularity — BranchSaddleAndStokesContour

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

/-! ## Cubic branch point and quartic saddle model -/

/-- FHKS Eq. (3.12): near the branch point, the time has cubic behavior
`t ~ E^3`. -/
def cubicBranchTime (E : ℝ) : ℝ :=
  E ^ 3

/-- FHKS Eq. (3.12): near the same point, the length has even quartic behavior
`L ~ -E^4`. -/
def quarticBranchLength (E : ℝ) : ℝ :=
  -E ^ 4

/-- The cubic local time has a triple zero at the branch point in the algebraic
sense `E^3 = 0 iff E = 0`. -/
lemma cubicBranchTime_eq_zero_iff (E : ℝ) :
    cubicBranchTime E = 0 ↔ E = 0 := by
  simp [cubicBranchTime]

/-- The cubic time changes sign under `E -> -E`. -/
lemma cubicBranchTime_odd (E : ℝ) :
    cubicBranchTime (-E) = -cubicBranchTime E := by
  simp [cubicBranchTime]
  ring

/-- The quartic length is even under `E -> -E`. -/
lemma quarticBranchLength_even (E : ℝ) :
    quarticBranchLength (-E) = quarticBranchLength E := by
  simp [quarticBranchLength]
  ring

/-- FHKS Eq. (3.13)/(3.14) normal form for a resolved cubic branch:
`t ~ E^3 - a E`. -/
def resolvedCubicTime (a E : ℝ) : ℝ :=
  E ^ 3 - a * E

@[simp] lemma resolvedCubicTime_zero (a : ℝ) :
    resolvedCubicTime a 0 = 0 := by
  simp [resolvedCubicTime]

/-- If `E^2 = a`, then `E` is one of the two nonzero resolved roots of
`E^3 - a E = 0` (possibly coincident at `E = 0`). -/
lemma resolvedCubicTime_root_of_sq_eq {a E : ℝ} (h : E ^ 2 = a) :
    resolvedCubicTime a E = 0 := by
  unfold resolvedCubicTime
  calc
    E ^ 3 - a * E = E * (E ^ 2 - a) := by ring
    _ = 0 := by rw [h]; ring

/-- FHKS Eq. (3.18): the universal quartic bifurcation model
`V_tau(x) = x^4/4 - tau*x`. -/
def quarticBifurcationPotential (tau x : ℝ) : ℝ :=
  x ^ 4 / 4 - tau * x

/-- FHKS Eq. (3.19): stationary points satisfy `x^3 = tau`. -/
def quarticBifurcationStationary (tau x : ℝ) : Prop :=
  x ^ 3 = tau

/-- At a stationary point, the quartic potential has value `-3/4 x^4`. -/
lemma quarticBifurcationPotential_at_stationary
    {tau x : ℝ} (h : quarticBifurcationStationary tau x) :
    quarticBifurcationPotential tau x = -(3 / 4) * x ^ 4 := by
  unfold quarticBifurcationStationary at h
  unfold quarticBifurcationPotential
  rw [← h]
  ring

/-! ## Link to Picard-Lefschetz/Stokes flow and the GKP-Witten dictionary -/

/-- FHKS Stokes alignment: two saddle exponents are on a Stokes line when
their imaginary parts agree. -/
def FhksStokesLine (I J : ℂ) : Prop :=
  I.im = J.im

/-- The geodesic branch change becomes a Stokes connection when the two
complex saddle exponents have equal imaginary part, exactly the conserved
quantity in the repo's Picard-Lefschetz contour layer. -/
def geodesicStokesConnection (Iprimary Isecondary : ℂ)
    (haligned : Iprimary.im = Isecondary.im) : StokesConnection where
  source := stokesCriticalPoint Iprimary
  target := stokesCriticalPoint Isecondary
  multiplicity := 1
  aligned := haligned

/-- Any aligned primary/secondary FHKS pair has a concrete Stokes flow line,
reusing `OperatorAlgebra.PicardLefschetzMorseContour` rather than reimplementing flow
existence. -/
lemma geodesicStokesConnection_has_flowLine
    (Iprimary Isecondary : ℂ) (haligned : Iprimary.im = Isecondary.im) :
    Nonempty (ChernSimonsStokesFlowLine
      (geodesicStokesConnection Iprimary Isecondary haligned)) :=
  chernSimonsStokesFlowLine_exists
    (geodesicStokesConnection Iprimary Isecondary haligned)

/-- A compact checked bridge from the FHKS Penrose diagram to the repo contour
machinery.  The diagrammatic critical null ray is identified with the contour
point `0 - iβ/4`, shown to be outside the primary ray cone, assigned to the
secondary sheet, and linked to the existing Picard-Lefschetz/Stokes flow layer. -/
structure FhksPenroseDiagramContourBridge (Iprimary Isecondary : ℂ) : Prop where
  criticalNullRayContour :
    nullSingularityTime ads5CriticalBoundaryStartTime =
      penroseNullContourPoint ads5InverseTemperature
  criticalNullRayRe : (penroseNullContourPoint ads5InverseTemperature).re = 0
  criticalNullRayIm : (penroseNullContourPoint ads5InverseTemperature).im = -Real.pi / 4
  criticalContourSpacelike :
    lorentzianForm (penroseNullContourPoint ads5InverseTemperature) < 0
  notPrimaryRay :
    ¬ 0 < lorentzianForm (penroseNullContourPoint ads5InverseTemperature)
  halfTfdShift :
    (penroseNullContourPoint ads5InverseTemperature).im =
      (tfdOneSidedTime ads5InverseTemperature 0).im / 2
  secondarySheet :
    penroseFeatureSheet FhksPenroseFeature.criticalNullRay =
      GeodesicSheet.secondaryBounce
  notPrimarySheet :
    ¬ IsPrimarySheet (penroseFeatureSheet FhksPenroseFeature.criticalNullRay)
  secondaryPole : hasTcPole (penroseFeatureSheet FhksPenroseFeature.criticalNullRay)
  stokesLine : FhksStokesLine Iprimary Isecondary
  stokesFlow :
    Nonempty (ChernSimonsStokesFlowLine
      (geodesicStokesConnection Iprimary Isecondary stokesLine))

/-- The FHKS Penrose diagram is linked to the contour formalism whenever the
primary and secondary saddle exponents satisfy the usual Stokes-line
alignment condition. -/
lemma fhksPenroseDiagram_contourBridge
    (Iprimary Isecondary : ℂ) (hIJ : FhksStokesLine Iprimary Isecondary) :
    FhksPenroseDiagramContourBridge Iprimary Isecondary where
  criticalNullRayContour := penroseCriticalNullRay_eq_contourPoint
  criticalNullRayRe := penroseCriticalNullRay_re_zero
  criticalNullRayIm := penroseCriticalNullRay_im
  criticalContourSpacelike := penroseCriticalNullContour_spacelike
  notPrimaryRay := penroseCriticalNullContour_not_primaryRay
  halfTfdShift := penroseNullContour_im_eq_half_tfdShift_im ads5InverseTemperature
  secondarySheet := penroseCriticalNullRay_sheet
  notPrimarySheet := penroseCriticalNullRay_not_primarySheet
  secondaryPole := penroseCriticalNullRay_has_tcPole
  stokesLine := hIJ
  stokesFlow := geodesicStokesConnection_has_flowLine Iprimary Isecondary hIJ

/-- GKP-Witten supplies the CFT operator dimension used by the heavy geodesic
approximation: the same `Delta` satisfies `Delta(Delta-d)=m^2 R^2`. -/
lemma fhks_uses_gkp_witten_massDimension
    (d mu : ℝ) (h : 0 ≤ (d / 2) ^ 2 + mu) :
    conformalDimension d mu * (conformalDimension d mu - d) = mu :=
  massDimension_relation d mu h

/-- The geodesic weight is the real damping part of the existing master complex
action when the real phase is zero and `hbar = 1`. -/
lemma geodesicWeight_eq_master_modulus_at_unit_hbar (L : ℝ) :
    geodesicCorrelator 1 L =
      ‖complexActionPathIntegralWeight 0 L 1‖ := by
  rw [master_modulus_is_kuiken]
  simp [geodesicCorrelator, kuikenWeight]

/-! ## FHKS contour analysis linked to the repo contour infrastructure -/

/-- FHKS's complex-geodesic contour rays use the same Nagao-Nielsen convergence
form: the ray direction `e^{i theta}` has `L = cos(2 theta)`. -/
lemma fhksContourRay_lorentzianForm (theta : ℝ) :
    lorentzianForm (Complex.exp (theta * Complex.I)) = Real.cos (2 * theta) :=
  lorentzianForm_rayDir theta

/-- A FHKS contour ray inside `|theta| < pi/4` lies in the Nagao-Nielsen
permitted/timelike cone. -/
lemma fhksContourRay_permitted {theta : ℝ} (htheta : |theta| < Real.pi / 4) :
    0 < lorentzianForm (Complex.exp (theta * Complex.I)) := by
  rw [fhksContourRay_lorentzianForm]
  rw [abs_lt] at htheta
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- The regularized complex delta normalizes to `1` along every FHKS/Nagao-Nielsen
permitted contour ray.  This reuses the existing contour theorem directly. -/
lemma fhksContour_deltaNormalization {theta eps : ℝ}
    (heps : 0 < eps) (htheta : |theta| < Real.pi / 4) :
    (∫ s : ℝ, deltaEpsC eps (Complex.exp (theta * Complex.I) * s) *
      Complex.exp (theta * Complex.I)) = 1 :=
  contour_normalization heps htheta

/-- The Gaussian saddle integral is independent of the permitted contour ray.
This is the concrete Gaussian contour theorem used for the FHKS complex-saddle
approximation. -/
lemma fhksGaussianContour_independent {c theta₀ theta₁ : ℝ}
    (hc : 0 < c) (h0 : |theta₀| < Real.pi / 4) (h1 : |theta₁| < Real.pi / 4) :
    (∫ s : ℝ, contourIntegrand (gaussH c) theta₀ s) =
      ∫ s : ℝ, contourIntegrand (gaussH c) theta₁ s :=
  gaussianContourIntegral_indep hc h0 h1

/-- General holomorphic contour deformation for FHKS saddle integrands: under
the differentiation-under-the-integral and integrability certificates already
used by `ComplexDelta.ContourShift`, the contour integral equals the real-axis
integral. -/
lemma fhksHolomorphicContour_eq_real {h h' : ℂ → ℂ}
    (hh : ∀ z, HasDerivAt h (h' z) z) {a b theta : ℝ}
    (hdui : ∀ theta ∈ Set.Ioo a b,
      HasDerivAt (fun theta => ∫ s, contourIntegrand h theta s)
        (∫ s, contourDeriv h h' theta s) theta)
    (hP : ∀ theta ∈ Set.Ioo a b, Integrable (fun s : ℝ => contourPrimitive h theta s))
    (hD : ∀ theta ∈ Set.Ioo a b, Integrable (fun s : ℝ => contourDeriv h h' theta s))
    (hmem0 : (0 : ℝ) ∈ Set.Ioo a b) (htheta : theta ∈ Set.Ioo a b) :
    (∫ s : ℝ, contourIntegrand h theta s) = ∫ s : ℝ, h (s : ℂ) :=
  contourIntegral_eq_real hh hdui hP hD hmem0 htheta

/-- FHKS anti-Stokes alignment: two saddle exponents have equal real part, so
their exponential weights have equal magnitude. -/
def FhksAntiStokesLine (I J : ℂ) : Prop :=
  I.re = J.re

/-- The FHKS Stokes-line condition is exactly the repo's
`OperatorAlgebra.PicardLefschetzMorseContour.StokesAligned` predicate. -/
lemma fhksStokesLine_iff_picardAligned (I J : ℂ) :
    FhksStokesLine I J ↔
      StokesAligned (stokesCriticalPoint I) (stokesCriticalPoint J) := by
  rfl

/-- On an FHKS Stokes line, the existing Picard-Lefschetz layer supplies a
Stokes flow line between the two geodesic saddle exponents. -/
lemma fhksStokesLine_has_flowLine (I J : ℂ) (hIJ : FhksStokesLine I J) :
    Nonempty (ChernSimonsStokesFlowLine (geodesicStokesConnection I J hIJ)) :=
  geodesicStokesConnection_has_flowLine I J hIJ

/-- Anti-Stokes equality is equality of exponential saddle magnitudes.  This is
the Lean form of "both FHKS complex branches contribute equally" on the
Lorentzian line. -/
lemma fhksAntiStokes_equal_exp_norm {I J : ℂ}
    (hIJ : FhksAntiStokesLine I J) :
    ‖Complex.exp I‖ = ‖Complex.exp J‖ := by
  rw [Complex.norm_exp, Complex.norm_exp, hIJ]

/-- The complex geodesic saddle weight `exp(-m L)`. -/
noncomputable def complexGeodesicWeight (m : ℝ) (L : ℂ) : ℂ :=
  Complex.exp (-(m : ℂ) * L)

/-- The norm of a complex geodesic weight only depends on the real part of the
regularized length. -/
lemma complexGeodesicWeight_norm (m : ℝ) (L : ℂ) :
    ‖complexGeodesicWeight m L‖ = Real.exp (-m * L.re) := by
  unfold complexGeodesicWeight
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- If two FHKS complex geodesic branches have equal real length, their
geodesic saddle weights have equal magnitude. -/
lemma fhksComplexBranches_equalWeight_of_equalRealLength
    {m : ℝ} {L₁ L₂ : ℂ} (hL : L₁.re = L₂.re) :
    ‖complexGeodesicWeight m L₁‖ = ‖complexGeodesicWeight m L₂‖ := by
  rw [complexGeodesicWeight_norm, complexGeodesicWeight_norm, hL]

/-- FHKS Eq. (3.6)'s thermal shift `-i beta/2` is exactly the
gravitational-lapse contour point `complexEnergy 0 (beta/2)`. -/
lemma fhksTfdShift_eq_complexEnergy (beta : ℝ) :
    tfdOneSidedTime beta 0 = complexEnergy 0 (beta / 2) := by
  simp [tfdOneSidedTime, complexEnergy]

/-- The same FHKS thermal shift is the gravity-contour point
`0 + i(-beta/2)` from `GravLapse.ContourEntropicTime`. -/
lemma fhksTfdShift_eq_gravityContourPoint (beta : ℝ) :
    tfdOneSidedTime beta 0 = (0 : ℂ) + (((-(beta / 2) : ℝ) : ℂ) * Complex.I) := by
  rw [fhksTfdShift_eq_complexEnergy]
  exact complexLapse_eq_contourPoint 0 (beta / 2)

/-- The FHKS thermal contour displacement has the same Lorentzian-form reading
as the gravitational lapse contour: `L(0 - i beta/2) = 0^2 - (beta/2)^2`. -/
lemma fhksTfdShift_lorentzianForm (beta : ℝ) :
    lorentzianForm (tfdOneSidedTime beta 0) = 0 ^ 2 - (beta / 2) ^ 2 := by
  rw [fhksTfdShift_eq_complexEnergy]
  exact lapse_lorentzianForm_eq 0 (beta / 2)

/-- The FHKS thermal contour weight at zero real lapse is the existing
complex-action master weight with imaginary action `(beta/2) * Ham`. -/
lemma fhksThermalContourWeight_eq_master (beta Ham : ℝ) :
    lapseWeight 0 (beta / 2) Ham =
      complexActionPathIntegralWeight 0 ((beta / 2) * Ham) 1 := by
  rw [lapseWeight_eq_master]
  simp

/-- Main result: the FHKS contour analysis uses the repo's Nagao-Nielsen contour,
Picard-Lefschetz/Stokes, and gravitational lapse-contour machinery as one
consistent contour contract. -/
lemma fhksContour_synthesis
    (theta theta' beta eps c Ham : ℝ)
    (htheta : |theta| < Real.pi / 4) (htheta' : |theta'| < Real.pi / 4)
    (heps : 0 < eps) (hc : 0 < c) :
    0 < lorentzianForm (Complex.exp (theta * Complex.I))
      ∧ (∫ s : ℝ, deltaEpsC eps (Complex.exp (theta * Complex.I) * s) *
            Complex.exp (theta * Complex.I)) = 1
      ∧ (∫ s : ℝ, contourIntegrand (gaussH c) theta s)
          = (∫ s : ℝ, contourIntegrand (gaussH c) theta' s)
      ∧ tfdOneSidedTime beta 0 = complexEnergy 0 (beta / 2)
      ∧ lorentzianForm (tfdOneSidedTime beta 0) = 0 ^ 2 - (beta / 2) ^ 2
      ∧ lapseWeight 0 (beta / 2) Ham =
          complexActionPathIntegralWeight 0 ((beta / 2) * Ham) 1 := by
  exact
    ⟨fhksContourRay_permitted htheta,
      fhksContour_deltaNormalization heps htheta,
      fhksGaussianContour_independent hc htheta htheta',
      fhksTfdShift_eq_complexEnergy beta,
      fhksTfdShift_lorentzianForm beta,
      fhksThermalContourWeight_eq_master beta Ham⟩


end Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.fhksContourRay_lorentzianForm where
  formalizes @ "claim:the-fhks-complex-geodesic-contour-ray-in-the-direction-exp-i-theta-has-nagao-nielsen-convergence-form-equal-to-cosine-of-two-theta",
  supported_by @ "paper:fidkowski-hubeny-kleban-shenker-jhep-02-2004-014-the-black-hole-singularity-in-ads-cft"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.fhksContourRay_permitted where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.fhksContourRay_lorentzianForm",
  formalizes @ "claim:a-fhks-complex-geodesic-contour-ray-with-rapidity-below-pi-over-four-in-absolute-value-lies-in-the-permitted-timelike-convergence-cone-with-positive-lorentzian-form-the-admissible-contour-condition",
  requires @ "claim:the-fhks-complex-geodesic-contour-ray-in-the-direction-exp-i-theta-has-nagao-nielsen-convergence-form-equal-to-cosine-of-two-theta"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.fhksContour_deltaNormalization where
  formalizes @ "claim:the-regularized-complex-delta-normalizes-to-one-along-every-permitted-fhks-contour-ray-so-the-admissible-contour-supports-a-well-defined-integral",
  requires @ "claim:a-fhks-complex-geodesic-contour-ray-with-rapidity-below-pi-over-four-in-absolute-value-lies-in-the-permitted-timelike-convergence-cone-with-positive-lorentzian-form-the-admissible-contour-condition"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.quarticBifurcationPotential_at_stationary where
  formalizes @ "claim:at-a-stationary-point-of-the-fhks-quartic-bifurcation-the-potential-equals-minus-three-quarters-x-to-the-fourth-the-saddle-value-of-the-finite-mass-quartic-model"

zil_file_contract physlib.branchSaddleAndStokesContour where
  promises "The contour-admissibility core of the Fidkowski-Hubeny-Kleban-Shenker AdS black-hole singularity (JHEP 02 (2004) 014): the cubic branch point, the quartic saddle model, and the Picard-Lefschetz/Stokes contour. FHKS complex-geodesic contour rays in the direction exp(i theta) have Nagao-Nielsen convergence form cos(2 theta) (fhksContourRay_lorentzianForm); a ray with |theta| < pi/4 lies in the permitted timelike convergence cone with positive Lorentzian form -- the admissible-contour condition (fhksContourRay_permitted) -- along which the regularized complex delta normalizes to one, so the admissible contour supports a well-defined integral (fhksContour_deltaNormalization). At a stationary point the quartic bifurcation potential is -3/4 x^4, the saddle value (quarticBifurcationPotential_at_stationary). Two saddle exponents lie on a Stokes line when their imaginary parts agree, feeding the repository's Picard-Lefschetz flow layer."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.FhksStokesLine",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.quarticBifurcationPotential"]
  forbids_substitutes ["the full Picard-Lefschetz thimble decomposition and the steepest-descent asymptotics of the boundary correlator, which are the cited complex-analysis infrastructure summarized by the permitted-cone and Stokes-alignment conditions",
    "any claim about the exact bulk metric reconstruction from the boundary correlator, only the admissible-contour and saddle algebra are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.fhksContourRay_lorentzianForm,
    Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.fhksContourRay_permitted,
    Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.fhksContour_deltaNormalization,
    Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.quarticBifurcationPotential_at_stationary]

/- ZIL-END -/
