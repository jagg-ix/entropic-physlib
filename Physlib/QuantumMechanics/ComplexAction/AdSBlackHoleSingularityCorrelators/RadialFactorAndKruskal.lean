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

/-! # FHKS AdS black-hole singularity — RadialFactorAndKruskal

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

/-! ## Bibliographic anchor -/

/-- Metadata anchor for the local paper formalized in this file. -/
structure FidkowskiHubenyKlebanShenker2004 where
  title : String
  authors : String
  journal : String
  localPdf : String
  mainClaim : String

/-- The local source used for this formalization. -/
def fidkowskiHubenyKlebanShenker2004 : FidkowskiHubenyKlebanShenker2004 where
  title := "The black hole singularity in AdS/CFT"
  authors := "Lukasz Fidkowski, Veronika Hubeny, Matthew Kleban, Stephen Shenker"
  journal := "JHEP 02 (2004) 014"
  localPdf := "Lukasz_Fidkowski_2004_J._High_Energy_Phys._2004_014.pdf"
  mainClaim :=
    "The naive real-geodesic singularity at t_c is absent on the primary CFT sheet; complex geodesics dominate, and the t_c singularity is on a secondary sheet."

/-! ## The large AdS5-Schwarzschild radial factor and critical time -/

/-- FHKS Eq. (2.2), in the large five-dimensional black-hole limit:
`f(r) = r^2 - 1/r^2`. -/
def ads5Blackening (r : ℝ) : ℝ :=
  r ^ 2 - 1 / r ^ 2

/-- The horizon is at `r = 1`, where the blackening factor vanishes. -/
@[simp] lemma ads5Blackening_horizon :
    ads5Blackening 1 = 0 := by
  norm_num [ads5Blackening]

/-- FHKS use `beta = pi` for the large AdS5 black hole. -/
def ads5InverseTemperature : ℝ :=
  Real.pi

/-- The boundary start-time critical value from FHKS Eq. (2.9):
`t_c = -pi/4 = -beta/4`. -/
def ads5CriticalBoundaryStartTime : ℝ :=
  -Real.pi / 4

/-- The critical time is exactly `-beta/4`. -/
lemma ads5CriticalBoundaryStartTime_eq_neg_beta_div_four :
    ads5CriticalBoundaryStartTime = -ads5InverseTemperature / 4 := by
  rfl

/-- FHKS Eq. (2.8) evaluated at the singularity in the large AdS5 limit:
starting from boundary time `t0`, the null ray reaches `r = 0` at
`t0 + pi/4 - i pi/4`. -/
def nullSingularityTime (t0 : ℝ) : ℂ :=
  ((t0 + Real.pi / 4 : ℝ) : ℂ) - Complex.I * ((Real.pi / 4 : ℝ) : ℂ)

@[simp] lemma nullSingularityTime_zero_re :
    (nullSingularityTime 0).re = Real.pi / 4 := by
  simp [nullSingularityTime]

@[simp] lemma nullSingularityTime_zero_im :
    (nullSingularityTime 0).im = -Real.pi / 4 := by
  simp [nullSingularityTime]
  ring_nf

/-- At `t0 = t_c`, the real part of the singularity hit is zero. -/
lemma nullSingularityTime_critical_re :
    (nullSingularityTime ads5CriticalBoundaryStartTime).re = 0 := by
  simp [nullSingularityTime, ads5CriticalBoundaryStartTime]
  ring

/-! ## Appendix A: Kruskal coordinates -/

/-- FHKS Appendix A null coordinate `u = t - r_*`. -/
def kruskalNullU (t rstar : ℝ) : ℝ :=
  t - rstar

/-- FHKS Appendix A null coordinate `v = t + r_*`. -/
def kruskalNullV (t rstar : ℝ) : ℝ :=
  t + rstar

/-- FHKS Appendix A Kruskal coordinate `U = -exp(-2u)`. -/
noncomputable def kruskalU (u : ℝ) : ℝ :=
  -Real.exp (-2 * u)

/-- FHKS Appendix A Kruskal coordinate `V = exp(2v)`. -/
noncomputable def kruskalV (v : ℝ) : ℝ :=
  Real.exp (2 * v)

@[simp] lemma kruskalU_neg (u : ℝ) :
    kruskalU u < 0 := by
  unfold kruskalU
  linarith [Real.exp_pos (-2 * u)]

@[simp] lemma kruskalV_pos (v : ℝ) :
    0 < kruskalV v := by
  simpa [kruskalV] using Real.exp_pos (2 * v)

/-- Kruskal `U` as a function of Schwarzschild time and tortoise coordinate. -/
noncomputable def kruskalUFromTR (t rstar : ℝ) : ℝ :=
  kruskalU (kruskalNullU t rstar)

/-- Kruskal `V` as a function of Schwarzschild time and tortoise coordinate. -/
noncomputable def kruskalVFromTR (t rstar : ℝ) : ℝ :=
  kruskalV (kruskalNullV t rstar)

/-- The real exterior patch used before extension has `U < 0 < V`. -/
lemma kruskalRightExterior_signs (t rstar : ℝ) :
    kruskalUFromTR t rstar < 0 ∧ 0 < kruskalVFromTR t rstar := by
  simp [kruskalUFromTR, kruskalVFromTR]

/-- Cartesian Kruskal time `T`, with `U = T - X`, `V = T + X`. -/
def kruskalT (U V : ℝ) : ℝ :=
  (U + V) / 2

/-- Cartesian Kruskal space coordinate `X`, with `U = T - X`, `V = T + X`. -/
def kruskalX (U V : ℝ) : ℝ :=
  (V - U) / 2

/-- Kruskal time from `(t,r_*)`. -/
noncomputable def kruskalTFromTR (t rstar : ℝ) : ℝ :=
  kruskalT (kruskalUFromTR t rstar) (kruskalVFromTR t rstar)

/-- Kruskal space coordinate from `(t,r_*)`. -/
noncomputable def kruskalXFromTR (t rstar : ℝ) : ℝ :=
  kruskalX (kruskalUFromTR t rstar) (kruskalVFromTR t rstar)

@[simp] lemma kruskalT_sub_X (U V : ℝ) :
    kruskalT U V - kruskalX U V = U := by
  unfold kruskalT kruskalX
  ring

@[simp] lemma kruskalT_add_X (U V : ℝ) :
    kruskalT U V + kruskalX U V = V := by
  unfold kruskalT kruskalX
  ring

/-- Appendix A identity `T^2 - X^2 = U V`. -/
lemma kruskalTX_interval_eq_UV (U V : ℝ) :
    kruskalT U V ^ 2 - kruskalX U V ^ 2 = U * V := by
  unfold kruskalT kruskalX
  ring

/-- The horizon `UV=0` is the pair of Kruskal null axes. -/
lemma kruskalTX_horizon_axes (U V : ℝ) :
    kruskalT U V ^ 2 - kruskalX U V ^ 2 = 0 ↔ U = 0 ∨ V = 0 := by
  rw [kruskalTX_interval_eq_UV]
  exact mul_eq_zero

/-- In Cartesian Kruskal coordinates the horizon is `T=X` or `T=-X`. -/
lemma kruskalInterval_zero_iff_axes (T X : ℝ) :
    T ^ 2 - X ^ 2 = 0 ↔ T = X ∨ T = -X := by
  constructor
  · intro h
    have hs : T ^ 2 = X ^ 2 := by linarith
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hs
  · intro h
    rcases h with h | h
    · rw [h]
      ring
    · rw [h]
      ring

/-- Appendix A identity `UV = -exp(4r_*)` for `u=t-r_*`, `v=t+r_*`. -/
lemma kruskalUV_from_tortoise (t rstar : ℝ) :
    kruskalUFromTR t rstar * kruskalVFromTR t rstar =
      -Real.exp (4 * rstar) := by
  unfold kruskalUFromTR kruskalVFromTR kruskalU kruskalV kruskalNullU kruskalNullV
  calc
    -Real.exp (-2 * (t - rstar)) * Real.exp (2 * (t + rstar))
        = -(Real.exp (-2 * (t - rstar)) * Real.exp (2 * (t + rstar))) := by ring
    _ = -Real.exp (-2 * (t - rstar) + 2 * (t + rstar)) := by rw [Real.exp_add]
    _ = -Real.exp (4 * rstar) := by ring_nf

/-- Appendix A identity `T^2 - X^2 = -exp(4r_*)`. -/
lemma kruskalTX_interval_from_tortoise (t rstar : ℝ) :
    kruskalTFromTR t rstar ^ 2 - kruskalXFromTR t rstar ^ 2 =
      -Real.exp (4 * rstar) := by
  unfold kruskalTFromTR kruskalXFromTR
  rw [kruskalTX_interval_eq_UV, kruskalUV_from_tortoise]

/-- Equivalent time-coordinate statement: `-V/U = exp(4t)`.  This is the
exponential form of Appendix A's `2t = tanh^{-1}(T/X)`. -/
lemma kruskalV_div_negU_from_time (t rstar : ℝ) :
    kruskalVFromTR t rstar / (-(kruskalUFromTR t rstar)) =
      Real.exp (4 * t) := by
  unfold kruskalVFromTR kruskalUFromTR kruskalV kruskalU kruskalNullV kruskalNullU
  simp only [neg_neg]
  rw [← Real.exp_sub]
  congr 1
  ring_nf

/-- FHKS Appendix A radial formula, with the integration constant chosen so
`r_*` is real outside the horizon:
`exp(4r_*) = ((r-1)/(r+1)) exp(2 atan r)`. -/
noncomputable def ads5TortoiseExp4 (r : ℝ) : ℝ :=
  ((r - 1) / (r + 1)) * Real.exp (2 * Real.arctan r)

/-- The Kruskal radial invariant `UV = T^2 - X^2 = -exp(4r_*)`. -/
noncomputable def ads5KruskalRadialUV (r : ℝ) : ℝ :=
  -ads5TortoiseExp4 r

/-- The horizon `r=1` is the Kruskal cross `UV=0`. -/
@[simp] lemma ads5KruskalRadialUV_horizon :
    ads5KruskalRadialUV 1 = 0 := by
  norm_num [ads5KruskalRadialUV, ads5TortoiseExp4]

/-- The singularity `r=0` is the Kruskal hyperbola `T^2-X^2=UV=1`. -/
@[simp] lemma ads5KruskalRadialUV_singularity :
    ads5KruskalRadialUV 0 = 1 := by
  norm_num [ads5KruskalRadialUV, ads5TortoiseExp4]

/-- FHKS Appendix A boundary hyperbola value `UV = -e^π`, i.e.
`X^2 - T^2 = e^π`. -/
noncomputable def ads5KruskalBoundaryUV : ℝ :=
  -Real.exp Real.pi

/-- The singularity hyperbola is closer to the Kruskal origin than the AdS
boundary hyperbola: the ratio of boundary distance to singularity distance is
`e^π > 1`. -/
lemma ads5KruskalBoundary_farther_than_singularity :
    1 < Real.exp Real.pi := by
  rw [show (1 : ℝ) = Real.exp 0 by simp]
  exact Real.exp_lt_exp.mpr Real.pi_pos

/-- The FHKS Kruskal radial range from Appendix A:
`-e^π < UV < 1`. -/
def FhksKruskalRadialRange (UV : ℝ) : Prop :=
  ads5KruskalBoundaryUV < UV ∧ UV < 1

/-- The lower boundary value is strictly below the singularity value. -/
lemma ads5KruskalBoundaryUV_lt_singularityUV :
    ads5KruskalBoundaryUV < ads5KruskalRadialUV 0 := by
  rw [ads5KruskalRadialUV_singularity, ads5KruskalBoundaryUV]
  linarith [Real.exp_pos Real.pi]

/-- The FHKS singularity hyperbola in Cartesian Kruskal coordinates. -/
def FhksKruskalSingularityHyperbola (T X : ℝ) : Prop :=
  T ^ 2 - X ^ 2 = 1

/-- The FHKS AdS boundary hyperbola in Cartesian Kruskal coordinates. -/
def FhksKruskalBoundaryHyperbola (T X : ℝ) : Prop :=
  X ^ 2 - T ^ 2 = Real.exp Real.pi

/-- The boundary hyperbola is the lower endpoint `T^2-X^2=-e^π` of the
Kruskal radial range. -/
lemma fhksKruskalBoundaryHyperbola_iff_interval (T X : ℝ) :
    FhksKruskalBoundaryHyperbola T X ↔
      T ^ 2 - X ^ 2 = ads5KruskalBoundaryUV := by
  unfold FhksKruskalBoundaryHyperbola ads5KruskalBoundaryUV
  constructor <;> intro h <;> linarith

/-- The singularity hyperbola is the upper endpoint `T^2-X^2=1` of the
Kruskal radial range. -/
lemma fhksKruskalSingularityHyperbola_iff_interval (T X : ℝ) :
    FhksKruskalSingularityHyperbola T X ↔
      T ^ 2 - X ^ 2 = ads5KruskalRadialUV 0 := by
  simp [FhksKruskalSingularityHyperbola]

/-- In AdS5 the boundary hyperbola has larger squared radius than the
singularity hyperbola.  This is the checked `e^π > 1` asymmetry. -/
lemma ads5KruskalBoundarySquaredRadius_gt_singularity :
    ads5KruskalRadialUV 0 < -ads5KruskalBoundaryUV := by
  rw [ads5KruskalRadialUV_singularity, ads5KruskalBoundaryUV]
  simpa using ads5KruskalBoundary_farther_than_singularity

/-- BTZ-style symmetric Kruskal normalization, used only for the paper's
contrast with the higher-dimensional AdS-Schwarzschild diagram. -/
def btzSymmetricKruskalBoundaryUV : ℝ :=
  -1

/-- In the BTZ-style symmetric normalization the boundary and singularity have
the same squared hyperbola radius. -/
lemma btzSymmetricKruskal_equal_squared_hyperbola_radii :
    -btzSymmetricKruskalBoundaryUV = ads5KruskalRadialUV 0 := by
  norm_num [btzSymmetricKruskalBoundaryUV]

/-- The large AdS5 Kruskal diagram is not BTZ-symmetric: the boundary and
singularity squared hyperbola radii differ. -/
lemma ads5Kruskal_not_symmetric_hyperbola_radii :
    -ads5KruskalBoundaryUV ≠ ads5KruskalRadialUV 0 := by
  intro h
  have hlt := ads5KruskalBoundarySquaredRadius_gt_singularity
  linarith

/-- Appendix A's horizon statement combines the Schwarzschild coordinate
singularity `f(1)=0` with the regular Kruskal invariant `UV=0`. -/
lemma ads5_horizon_blackening_and_kruskal :
    ads5Blackening 1 = 0 ∧ ads5KruskalRadialUV 1 = 0 :=
  ⟨ads5Blackening_horizon, ads5KruskalRadialUV_horizon⟩

/-- The regular Kruskal conformal factor obtained after cancelling the
blackening zero against `exp(-4r_*)`; this is the finite expression behind
Appendix A's claim that the metric extends across the horizon. -/
noncomputable def ads5KruskalRegularConformalFactor (r : ℝ) : ℝ :=
  ((r + 1) ^ 2 * (r ^ 2 + 1)) / (4 * r ^ 2 * Real.exp (2 * Real.arctan r))

/-- The regularized Kruskal conformal factor has a finite value at the horizon. -/
lemma ads5KruskalRegularConformalFactor_horizon :
    ads5KruskalRegularConformalFactor 1 = 2 / Real.exp (Real.pi / 2) := by
  unfold ads5KruskalRegularConformalFactor
  rw [Real.arctan_one]
  field_simp
  ring_nf


end Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators

end
