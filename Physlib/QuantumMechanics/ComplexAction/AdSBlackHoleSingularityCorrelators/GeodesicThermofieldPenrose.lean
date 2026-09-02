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
public import Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.NullRayAndEntropicProperTime

/-! # FHKS AdS black-hole singularity — GeodesicThermofieldPenrose

Part of the Fidkowski--Hubeny--Kleban--Shenker formalization (JHEP 02 (2004) 014); see the umbrella
module `AdSBlackHoleSingularityCorrelators` for the full paper docstring. The namespace and every
declaration name are unchanged across the parts; the umbrella module re-exports all of them.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
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

/-! ## Turning point, geodesic length, and the naive critical correlator -/

/-- Near the singularity the `-1/r^2` term dominates the radial potential. -/
def nearSingularityBlackening (r : ℝ) : ℝ :=
  -1 / r ^ 2

/-- The large-energy turning-point approximation from FHKS Eq. (2.14):
`r_i ~ 1/E`. -/
def largeEnergyTurningPointApprox (E : ℝ) : ℝ :=
  1 / E

/-- The approximation `r_i = 1/E` exactly solves the near-singularity balance
`E^2 - 1/r_i^2 = 0`, for nonzero `E`. -/
lemma largeEnergyTurningPointApprox_solves_nearSingularity_balance
    (E : ℝ) (_hE : E ≠ 0) :
    E ^ 2 + nearSingularityBlackening (largeEnergyTurningPointApprox E) = 0 := by
  unfold nearSingularityBlackening largeEnergyTurningPointApprox
  field_simp [_hE]
  ring

/-- FHKS Eq. (2.18): the regularized geodesic length in the large AdS5 model. -/
noncomputable def regularizedGeodesicLength (E : ℝ) : ℝ :=
  Real.log (2 / Real.sqrt (E ^ 4 / 4 + 1))

/-- FHKS Eq. (2.13): the `E = 0` length is `log 2`. -/
@[simp] lemma regularizedGeodesicLength_zero :
    regularizedGeodesicLength 0 = Real.log 2 := by
  norm_num [regularizedGeodesicLength]

/-- Geodesic approximation to the heavy-operator two-sided correlator:
`G ~ exp(-m L)`. -/
noncomputable def geodesicCorrelator (m L : ℝ) : ℝ :=
  Real.exp (-m * L)

/-- The local FHKS critical length asymptotic, written as the model
`L = 2 log(delta)`. -/
noncomputable def criticalLogLength (delta : ℝ) : ℝ :=
  2 * Real.log delta

/-- If the real bouncing geodesic controlled the correlator, then
`L ~ 2 log(t - t_c)` would give `G ~ (t - t_c)^(-2m)`.  FHKS then show this
singularity is not on the primary CFT sheet. -/
lemma geodesicCorrelator_criticalLogLength
    (m delta : ℝ) (hdelta : 0 < delta) :
    geodesicCorrelator m (criticalLogLength delta) = delta ^ (-2 * m) := by
  unfold geodesicCorrelator criticalLogLength
  rw [Real.rpow_def_of_pos hdelta]
  congr 1
  ring

/-! ## Thermofield continuation and branch bookkeeping -/

/-- FHKS Eq. (3.6): the two-sided thermofield correlator is evaluated as a
one-sided thermal correlator at `-t - i beta/2`. -/
def tfdOneSidedTime (beta : ℝ) (t : ℂ) : ℂ :=
  -t - Complex.I * ((beta / 2 : ℝ) : ℂ)

/-- In the large AdS5 normalization `beta = pi`, the imaginary shift is
`-i pi/2`. -/
lemma tfdOneSidedTime_ads5 (t : ℂ) :
    tfdOneSidedTime ads5InverseTemperature t =
      -t - Complex.I * ((Real.pi / 2 : ℝ) : ℂ) := by
  rfl

/-- The three relevant geodesic sheets in the FHKS analytic-continuation
picture: two primary complex branches and the secondary real-bounce sheet. -/
inductive GeodesicSheet
  | primaryComplexPlus
  | primaryComplexMinus
  | secondaryBounce
  deriving DecidableEq, Repr

/-- Which sheet carries the `t_c` light-cone pole. -/
def hasTcPole (sheet : GeodesicSheet) : Prop :=
  sheet = GeodesicSheet.secondaryBounce

/-- FHKS result: the plus primary complex branch has no `t_c` pole. -/
lemma primaryComplexPlus_no_tcPole :
    ¬ hasTcPole GeodesicSheet.primaryComplexPlus := by
  simp [hasTcPole]

/-- FHKS result: the minus primary complex branch has no `t_c` pole. -/
lemma primaryComplexMinus_no_tcPole :
    ¬ hasTcPole GeodesicSheet.primaryComplexMinus := by
  simp [hasTcPole]

/-- The `t_c` pole is assigned to the secondary bounce sheet. -/
lemma secondaryBounce_has_tcPole :
    hasTcPole GeodesicSheet.secondaryBounce := by
  simp [hasTcPole]

/-- A primary sheet is exactly one of the two complex sheets. -/
def IsPrimarySheet (s : GeodesicSheet) : Prop :=
  s = GeodesicSheet.primaryComplexPlus ∨ s = GeodesicSheet.primaryComplexMinus

/-- The paper's primary-sheet conclusion as a checked case split. -/
lemma primarySheet_no_tcPole {s : GeodesicSheet} (hs : IsPrimarySheet s) :
    ¬ hasTcPole s := by
  rcases hs with rfl | rfl
  · exact primaryComplexPlus_no_tcPole
  · exact primaryComplexMinus_no_tcPole

/-! ## Penrose diagram to contour bridge -/

/-- The FHKS Penrose-diagram features used by the checked contour bridge.

The formal content below is not a drawing: the critical null ray is the
diagrammatic null line which leaves the boundary at `t_c = -β/4` and reaches
the singularity.  Lean then identifies its endpoint with a complex contour
point. -/
inductive FhksPenroseFeature
  | rightBoundaryExterior
  | leftBoundaryExterior
  | eventHorizon
  | spacelikeSingularity
  | criticalNullRay
  deriving DecidableEq, Repr

/-- The geodesic sheet selected by each FHKS Penrose-diagram feature.  The
critical null ray and the singularity are assigned to the secondary bounce
sheet, matching FHKS's conclusion that the naive `t_c` light-cone singularity
is not present on the primary CFT sheet. -/
def penroseFeatureSheet : FhksPenroseFeature → GeodesicSheet
  | FhksPenroseFeature.rightBoundaryExterior => GeodesicSheet.primaryComplexPlus
  | FhksPenroseFeature.leftBoundaryExterior => GeodesicSheet.primaryComplexMinus
  | FhksPenroseFeature.eventHorizon => GeodesicSheet.primaryComplexPlus
  | FhksPenroseFeature.spacelikeSingularity => GeodesicSheet.secondaryBounce
  | FhksPenroseFeature.criticalNullRay => GeodesicSheet.secondaryBounce

/-- The Penrose-diagram null ray endpoint, expressed as the contour point
`0 - i β/4`.  In the large AdS5 black-hole normalization this is the endpoint
of the critical boundary null ray at `t_c = -β/4`. -/
def penroseNullContourPoint (beta : ℝ) : ℂ :=
  complexEnergy 0 (beta / 4)

/-- The FHKS Penrose-diagram critical null ray reaches the singularity at the
same complex point as the contour displacement `0 - i β/4`. -/
lemma penroseCriticalNullRay_eq_contourPoint :
    nullSingularityTime ads5CriticalBoundaryStartTime =
      penroseNullContourPoint ads5InverseTemperature := by
  apply Complex.ext
  · simp [penroseNullContourPoint, nullSingularityTime,
      ads5CriticalBoundaryStartTime, ads5InverseTemperature, complexEnergy]
    ring
  · simp [penroseNullContourPoint, nullSingularityTime,
      ads5CriticalBoundaryStartTime, ads5InverseTemperature, complexEnergy]

/-- The critical Penrose null ray endpoint has real part zero. -/
lemma penroseCriticalNullRay_re_zero :
    (penroseNullContourPoint ads5InverseTemperature).re = 0 := by
  rw [← penroseCriticalNullRay_eq_contourPoint]
  exact nullSingularityTime_critical_re

/-- The critical Penrose null ray endpoint has imaginary part `-β/4`. -/
lemma penroseCriticalNullRay_im :
    (penroseNullContourPoint ads5InverseTemperature).im = -Real.pi / 4 := by
  simp [penroseNullContourPoint, ads5InverseTemperature, complexEnergy]
  ring

/-- The Penrose null endpoint has Lorentzian contour form `-(β/4)^2`. -/
lemma penroseNullContour_lorentzianForm (beta : ℝ) :
    lorentzianForm (penroseNullContourPoint beta) = -(beta / 4) ^ 2 := by
  unfold penroseNullContourPoint
  rw [lapse_lorentzianForm_eq]
  ring

/-- In the FHKS normalization `β = π`, the Penrose null endpoint is outside
the primary permitted contour cone: its contour Lorentzian form is negative. -/
lemma penroseCriticalNullContour_spacelike :
    lorentzianForm (penroseNullContourPoint ads5InverseTemperature) < 0 := by
  rw [penroseNullContour_lorentzianForm, ads5InverseTemperature]
  have hpi4_ne : (Real.pi / 4 : ℝ) ≠ 0 := by positivity
  have hsq : 0 < (Real.pi / 4 : ℝ) ^ 2 := sq_pos_of_ne_zero hpi4_ne
  nlinarith

/-- Consequently the Penrose critical null endpoint is not a primary
Nagao-Nielsen/FHKS permitted ray point. -/
lemma penroseCriticalNullContour_not_primaryRay :
    ¬ 0 < lorentzianForm (penroseNullContourPoint ads5InverseTemperature) := by
  have h := penroseCriticalNullContour_spacelike
  linarith

/-- The `β/4` Penrose null endpoint is half the imaginary displacement of the
TFD contour shift `-iβ/2`. -/
lemma penroseNullContour_im_eq_half_tfdShift_im (beta : ℝ) :
    (penroseNullContourPoint beta).im = (tfdOneSidedTime beta 0).im / 2 := by
  simp [penroseNullContourPoint, tfdOneSidedTime, complexEnergy]
  ring

/-- The critical Penrose null ray selects the secondary geodesic sheet. -/
@[simp] lemma penroseCriticalNullRay_sheet :
    penroseFeatureSheet FhksPenroseFeature.criticalNullRay =
      GeodesicSheet.secondaryBounce := by
  rfl

/-- The Penrose critical null ray is not a primary-sheet feature. -/
lemma penroseCriticalNullRay_not_primarySheet :
    ¬ IsPrimarySheet (penroseFeatureSheet FhksPenroseFeature.criticalNullRay) := by
  simp [penroseFeatureSheet, IsPrimarySheet]

/-- The Penrose critical null ray carries the `t_c` pole because it lies on the
secondary bounce sheet. -/
lemma penroseCriticalNullRay_has_tcPole :
    hasTcPole (penroseFeatureSheet FhksPenroseFeature.criticalNullRay) := by
  simp [penroseFeatureSheet, hasTcPole]


end Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators

end
