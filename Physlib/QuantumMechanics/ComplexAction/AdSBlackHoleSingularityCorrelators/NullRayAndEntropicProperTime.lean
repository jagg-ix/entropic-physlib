/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiFormulaAlgebra
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.CellBondDimension
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.PicardLefschetzMorseContour
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour
public import Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
public import Physlib.SpaceAndTime.EntropicProperTime
public import Physlib.SpaceAndTime.ProblemOfTimeInstance
public import Physlib.Thermodynamics.BekensteinJacobsonEntropicBits
public import Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.RadialFactorAndKruskal
meta import Zil

/-! # FHKS AdS black-hole singularity — NullRayAndEntropicProperTime

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

/-! ### Appendix A null-ray geometry -/

/-- Right-boundary Kruskal `U` coordinate at Schwarzschild time `t`, obtained
from `UV=-e^π` and `V/(-U)=e^{4t}`. -/
noncomputable def ads5RightBoundaryUOfTime (t : ℝ) : ℝ :=
  -Real.exp (Real.pi / 2 - 2 * t)

/-- Right-boundary Kruskal `V` coordinate at Schwarzschild time `t`, obtained
from `UV=-e^π` and `V/(-U)=e^{4t}`. -/
noncomputable def ads5RightBoundaryVOfTime (t : ℝ) : ℝ :=
  Real.exp (Real.pi / 2 + 2 * t)

/-- Right-boundary Kruskal `T` coordinate at Schwarzschild time `t`. -/
noncomputable def ads5RightBoundaryTOfTime (t : ℝ) : ℝ :=
  kruskalT (ads5RightBoundaryUOfTime t) (ads5RightBoundaryVOfTime t)

/-- Right-boundary Kruskal `X` coordinate at Schwarzschild time `t`. -/
noncomputable def ads5RightBoundaryXOfTime (t : ℝ) : ℝ :=
  kruskalX (ads5RightBoundaryUOfTime t) (ads5RightBoundaryVOfTime t)

/-- The right-boundary parametrization lies on the FHKS boundary hyperbola. -/
lemma ads5RightBoundaryUV_eq_boundary (t : ℝ) :
    ads5RightBoundaryUOfTime t * ads5RightBoundaryVOfTime t =
      ads5KruskalBoundaryUV := by
  unfold ads5RightBoundaryUOfTime ads5RightBoundaryVOfTime ads5KruskalBoundaryUV
  calc
    -Real.exp (Real.pi / 2 - 2 * t) * Real.exp (Real.pi / 2 + 2 * t)
        = -(Real.exp (Real.pi / 2 - 2 * t) *
            Real.exp (Real.pi / 2 + 2 * t)) := by ring
    _ = -Real.exp ((Real.pi / 2 - 2 * t) + (Real.pi / 2 + 2 * t)) := by
      rw [← Real.exp_add]
    _ = -Real.exp Real.pi := by ring_nf

/-- The right-boundary parametrization has the Appendix A time ratio
`V/(-U)=e^{4t}`. -/
lemma ads5RightBoundary_timeRatio (t : ℝ) :
    ads5RightBoundaryVOfTime t / (-(ads5RightBoundaryUOfTime t)) =
      Real.exp (4 * t) := by
  unfold ads5RightBoundaryUOfTime ads5RightBoundaryVOfTime
  simp only [neg_neg]
  rw [← Real.exp_sub]
  congr 1
  ring_nf

@[simp] lemma ads5RightBoundaryT_zero :
    ads5RightBoundaryTOfTime 0 = 0 := by
  unfold ads5RightBoundaryTOfTime ads5RightBoundaryUOfTime
    ads5RightBoundaryVOfTime kruskalT
  norm_num

@[simp] lemma ads5RightBoundaryX_zero :
    ads5RightBoundaryXOfTime 0 = Real.exp (Real.pi / 2) := by
  unfold ads5RightBoundaryXOfTime ads5RightBoundaryUOfTime
    ads5RightBoundaryVOfTime kruskalX
  norm_num

@[simp] lemma ads5RightBoundaryU_critical :
    ads5RightBoundaryUOfTime ads5CriticalBoundaryStartTime =
      -Real.exp Real.pi := by
  unfold ads5RightBoundaryUOfTime ads5CriticalBoundaryStartTime
  rw [show Real.pi / 2 - 2 * (-Real.pi / 4) = Real.pi by ring]

@[simp] lemma ads5RightBoundaryV_critical :
    ads5RightBoundaryVOfTime ads5CriticalBoundaryStartTime = 1 := by
  unfold ads5RightBoundaryVOfTime ads5CriticalBoundaryStartTime
  rw [show Real.pi / 2 + 2 * (-Real.pi / 4) = 0 by ring]
  simp

lemma ads5RightBoundaryT_critical :
    ads5RightBoundaryTOfTime ads5CriticalBoundaryStartTime =
      (1 - Real.exp Real.pi) / 2 := by
  unfold ads5RightBoundaryTOfTime
  rw [ads5RightBoundaryU_critical, ads5RightBoundaryV_critical]
  unfold kruskalT
  ring

lemma ads5RightBoundaryX_critical :
    ads5RightBoundaryXOfTime ads5CriticalBoundaryStartTime =
      (1 + Real.exp Real.pi) / 2 := by
  unfold ads5RightBoundaryXOfTime
  rw [ads5RightBoundaryU_critical, ads5RightBoundaryV_critical]
  unfold kruskalX
  ring

/-- Radial null lines in the Kruskal diagram are 45-degree lines:
the squared coordinate differences agree. -/
def kruskalRadialNullSeparated (T₁ X₁ T₂ X₂ : ℝ) : Prop :=
  (T₂ - T₁) ^ 2 = (X₂ - X₁) ^ 2

/-- Appendix A's obstruction: the `t=0` boundary point cannot send a 45-degree
radial null line to the middle of the future singularity. -/
lemma ads5_tZeroBoundary_not_null_to_futureMiddleSingularity :
    ¬ kruskalRadialNullSeparated 0 (Real.exp (Real.pi / 2)) 1 0 := by
  intro h
  unfold kruskalRadialNullSeparated at h
  have hsq : (Real.exp (Real.pi / 2)) ^ 2 = 1 := by nlinarith [h]
  have hpi : (Real.exp (Real.pi / 2)) ^ 2 = Real.exp Real.pi := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hgt : 1 < (Real.exp (Real.pi / 2)) ^ 2 := by
    rw [hpi]
    exact ads5KruskalBoundary_farther_than_singularity
  nlinarith

/-- Same obstruction using the explicit right-boundary time parametrization. -/
lemma ads5RightBoundary_tZero_not_null_to_futureMiddleSingularity :
    ¬ kruskalRadialNullSeparated
      (ads5RightBoundaryTOfTime 0) (ads5RightBoundaryXOfTime 0) 1 0 := by
  simpa using ads5_tZeroBoundary_not_null_to_futureMiddleSingularity

/-- At the FHKS critical time `t_c=-π/4`, the right-boundary point is exactly
null-separated from the middle of the future singularity. -/
lemma ads5CriticalBoundary_null_to_futureMiddleSingularity :
    kruskalRadialNullSeparated
      (ads5RightBoundaryTOfTime ads5CriticalBoundaryStartTime)
      (ads5RightBoundaryXOfTime ads5CriticalBoundaryStartTime) 1 0 := by
  rw [ads5RightBoundaryT_critical, ads5RightBoundaryX_critical]
  unfold kruskalRadialNullSeparated
  ring

/-! ### Entropic proper-time parametrization of the Kruskal bounce -/

/-- A chosen FHKS clock calibration from metric entropic proper time to the
right-boundary Schwarzschild start time:

`t_start := -τ_ent`.

The metric entropic proper time itself is a nonnegative magnitude.  The minus
sign here is only the `.past` orientation sign in the boundary time coordinate.
This is a parametrization convention, not a derivation that every physical
state pair realizes every boundary time.  The checked consequence is that
nonnegative metric entropic proper time maps to nonpositive boundary start
time, and strictly positive calibrated readings map to strictly negative start
times. -/
def ads5BoundaryStartTimeFromEntropicProperTime
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits)
    (ρ σ : MState d) : ℝ :=
  TimeOrientation.past.sign * entropicProperTimeMetric U ρ σ

/-- The FHKS start-time convention is the past-oriented signed entropic-time
representation from `ProblemOfTimeInstance`. -/
noncomputable def ads5PastEntropicStartTime
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (ρ σ : MState d) : Time :=
  ⟨ads5BoundaryStartTimeFromEntropicProperTime U ρ σ⟩

/-- The local FHKS start-time symbol is represented by the repo's existing
`SignedEntropicTimeRepresentation` with orientation `.past`. -/
def ads5PastEntropicStartTime_representation
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (ρ σ : MState d) :
    SignedEntropicTimeRepresentation (d := d)
      (ads5PastEntropicStartTime U ρ σ) where
  U := U
  ρ := ρ
  σ := σ
  orientation := TimeOrientation.past
  represents := rfl

@[simp] lemma ads5BoundaryStartTimeFromEntropicProperTime_eq_neg
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (ρ σ : MState d) :
    ads5BoundaryStartTimeFromEntropicProperTime U ρ σ =
      -entropicProperTimeMetric U ρ σ := by
  simp [ads5BoundaryStartTimeFromEntropicProperTime]

lemma ads5BoundaryStartTimeFromEntropicProperTime_nonpos
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits)
    (ρ σ : MState d) :
    ads5BoundaryStartTimeFromEntropicProperTime U ρ σ ≤ 0 := by
  rw [ads5BoundaryStartTimeFromEntropicProperTime_eq_neg]
  exact neg_nonpos.mpr (entropicProperTimeMetric_nonneg U ρ σ)

/-- If the entropic proper-time magnitude is strictly positive, then the
past-oriented FHKS boundary start coordinate is strictly negative.  This is the
checked form of the `-τ_ent` convention: the negativity belongs to orientation,
not to the entropic proper-time magnitude. -/
lemma ads5BoundaryStartTimeFromEntropicProperTime_neg_of_pos
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits)
    (ρ σ : MState d)
    (hτpos : 0 < entropicProperTimeMetric U ρ σ) :
    ads5BoundaryStartTimeFromEntropicProperTime U ρ σ < 0 := by
  rw [ads5BoundaryStartTimeFromEntropicProperTime_eq_neg]
  linarith

/-- Taking the absolute value of the past-oriented boundary start coordinate
recovers the nonnegative entropic proper-time magnitude. -/
lemma ads5PastEntropicStartTime_abs_eq_entropicProperTime
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (ρ σ : MState d) :
    |ads5BoundaryStartTimeFromEntropicProperTime U ρ σ| =
      entropicProperTimeMetric U ρ σ := by
  rw [ads5BoundaryStartTimeFromEntropicProperTime_eq_neg, abs_neg]
  exact abs_of_nonneg (entropicProperTimeMetric_nonneg U ρ σ)

/-- Under `t_start=-τ_ent`, the `t=0` slice is exactly the zero entropic
proper-time reading.  This does **not** assert the converse state identity
`τ_ent=0 -> ρ=σ`. -/
lemma ads5BoundaryStartTimeFromEntropicProperTime_eq_zero_iff
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (ρ σ : MState d) :
    ads5BoundaryStartTimeFromEntropicProperTime U ρ σ = 0 ↔
      entropicProperTimeMetric U ρ σ = 0 := by
  rw [ads5BoundaryStartTimeFromEntropicProperTime_eq_neg]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    simp

@[simp] lemma ads5BoundaryStartTimeFromEntropicProperTime_frozen
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (ρ : MState d) :
    ads5BoundaryStartTimeFromEntropicProperTime U ρ ρ = 0 := by
  rw [ads5BoundaryStartTimeFromEntropicProperTime_eq_neg,
    entropicProperTimeMetric_self]
  simp

/-- Under the chosen clock calibration `t_start=-τ_ent`, a metric entropic
proper-time reading `τ_ent=π/4` is exactly the FHKS critical start time
`t_c=-π/4`. -/
lemma ads5BoundaryStartTimeFromEntropicProperTime_eq_critical_of_quarter
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (ρ σ : MState d)
    (hτ : entropicProperTimeMetric U ρ σ = Real.pi / 4) :
    ads5BoundaryStartTimeFromEntropicProperTime U ρ σ =
      ads5CriticalBoundaryStartTime := by
  rw [ads5BoundaryStartTimeFromEntropicProperTime_eq_neg]
  unfold ads5CriticalBoundaryStartTime
  rw [hτ]
  ring

/-- The FHKS critical calibrated entropic-time reading is a strictly positive
proper-time magnitude. -/
lemma ads5CriticalEntropicProperTime_pos
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (ρ σ : MState d)
    (hτ : entropicProperTimeMetric U ρ σ = Real.pi / 4) :
    0 < entropicProperTimeMetric U ρ σ := by
  rw [hτ]
  positivity

/-- At the FHKS critical calibration, the start coordinate is strictly negative
because it is the past-oriented coordinate `-τ_ent`, while `τ_ent` itself is
strictly positive. -/
lemma ads5BoundaryStartTimeFromEntropicProperTime_critical_neg
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (ρ σ : MState d)
    (hτ : entropicProperTimeMetric U ρ σ = Real.pi / 4) :
    ads5BoundaryStartTimeFromEntropicProperTime U ρ σ < 0 :=
  ads5BoundaryStartTimeFromEntropicProperTime_neg_of_pos U ρ σ
    (ads5CriticalEntropicProperTime_pos U ρ σ hτ)

/-- Exact calibration equivalence: the chosen entropic-clock start time is the
FHKS critical start time iff the metric entropic proper-time reading is
`π/4`. -/
lemma ads5BoundaryStartTimeFromEntropicProperTime_eq_critical_iff
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (ρ σ : MState d) :
    ads5BoundaryStartTimeFromEntropicProperTime U ρ σ =
      ads5CriticalBoundaryStartTime ↔
      entropicProperTimeMetric U ρ σ = Real.pi / 4 := by
  rw [ads5BoundaryStartTimeFromEntropicProperTime_eq_neg]
  unfold ads5CriticalBoundaryStartTime
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    ring

/-- Under the chosen clock calibration, frozen entropic proper time (`ρ=σ`,
hence `τ_ent=0`) maps to the `t=0` boundary slice, and that slice cannot
null-bounce to the middle of the future singularity. -/
lemma ads5_frozenEntropicProperTime_not_null_to_futureMiddleSingularity
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (ρ : MState d) :
    ¬ kruskalRadialNullSeparated
      (ads5RightBoundaryTOfTime (ads5BoundaryStartTimeFromEntropicProperTime U ρ ρ))
      (ads5RightBoundaryXOfTime (ads5BoundaryStartTimeFromEntropicProperTime U ρ ρ))
      1 0 := by
  rw [ads5BoundaryStartTimeFromEntropicProperTime_frozen]
  exact ads5RightBoundary_tZero_not_null_to_futureMiddleSingularity

/-- If a state pair is calibrated so that its metric entropic proper-time
reading is `π/4`, then the entropic-time parametrized boundary point is the
FHKS critical point and is null-separated from the middle of the future
singularity. -/
lemma ads5_quarterEntropicProperTime_null_to_futureMiddleSingularity
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits) (ρ σ : MState d)
    (hτ : entropicProperTimeMetric U ρ σ = Real.pi / 4) :
    kruskalRadialNullSeparated
      (ads5RightBoundaryTOfTime (ads5BoundaryStartTimeFromEntropicProperTime U ρ σ))
      (ads5RightBoundaryXOfTime (ads5BoundaryStartTimeFromEntropicProperTime U ρ σ))
      1 0 := by
  rw [ads5BoundaryStartTimeFromEntropicProperTime_eq_critical_of_quarter U ρ σ hτ]
  exact ads5CriticalBoundary_null_to_futureMiddleSingularity

/-- A checked bridge saying precisely what the chosen entropic proper-time
parametrization proves about Appendix A:

* frozen entropic proper time gives the `t=0` slice and cannot hit the middle;
* a **calibrated** `π/4` entropic proper-time reading is strictly positive;
* the associated start time is strictly negative only because the boundary
  coordinate is past-oriented;
* that FHKS critical start time does hit the middle.

The structure deliberately keeps `criticalEntropicProperTime` as a field: this
file does not prove that arbitrary states realize the `π/4` reading. -/
structure FhksEntropicProperTimeKruskalBounceBridge
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits)
    (ρFrozen ρCritical σCritical : MState d) : Prop where
  pastStartTimeRepresentation :
    Nonempty (SignedEntropicTimeRepresentation (d := d)
      (ads5PastEntropicStartTime U ρCritical σCritical))
  frozenOriginTimeRepresentation :
    Nonempty (EntropicTimeRepresentation (d := d) (⟨0⟩ : Time))
  criticalStartTimeNonpos :
    ads5BoundaryStartTimeFromEntropicProperTime U ρCritical σCritical ≤ 0
  criticalStartTimeNegative :
    ads5BoundaryStartTimeFromEntropicProperTime U ρCritical σCritical < 0
  criticalStartMagnitude :
    |ads5BoundaryStartTimeFromEntropicProperTime U ρCritical σCritical| =
      entropicProperTimeMetric U ρCritical σCritical
  frozenEntropicProperTime :
    entropicProperTimeMetric U ρFrozen ρFrozen = 0
  frozenStartTime :
    ads5BoundaryStartTimeFromEntropicProperTime U ρFrozen ρFrozen = 0
  frozenNoMiddleBounce :
    ¬ kruskalRadialNullSeparated
      (ads5RightBoundaryTOfTime
        (ads5BoundaryStartTimeFromEntropicProperTime U ρFrozen ρFrozen))
      (ads5RightBoundaryXOfTime
        (ads5BoundaryStartTimeFromEntropicProperTime U ρFrozen ρFrozen))
      1 0
  criticalEntropicProperTime :
    entropicProperTimeMetric U ρCritical σCritical = Real.pi / 4
  criticalEntropicProperTimePositive :
    0 < entropicProperTimeMetric U ρCritical σCritical
  criticalStartTime :
    ads5BoundaryStartTimeFromEntropicProperTime U ρCritical σCritical =
      ads5CriticalBoundaryStartTime
  criticalMiddleBounce :
    kruskalRadialNullSeparated
      (ads5RightBoundaryTOfTime
        (ads5BoundaryStartTimeFromEntropicProperTime U ρCritical σCritical))
      (ads5RightBoundaryXOfTime
        (ads5BoundaryStartTimeFromEntropicProperTime U ρCritical σCritical))
      1 0

/-- The entropic proper-time Kruskal bridge follows from the single calibration
assumption `τ_ent=π/4` for the critical preparation.  The theorem is therefore
conditional: it connects an already-calibrated entropic clock reading to the
FHKS Kruskal bounce, rather than deriving that reading from the state pair. -/
lemma fhksEntropicProperTimeKruskalBounce_bridge
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : EntropicTimeUnits)
    (ρFrozen ρCritical σCritical : MState d)
    (hτ : entropicProperTimeMetric U ρCritical σCritical =
      Real.pi / 4) :
    FhksEntropicProperTimeKruskalBounceBridge U ρFrozen ρCritical σCritical where
  pastStartTimeRepresentation :=
    ⟨ads5PastEntropicStartTime_representation U ρCritical σCritical⟩
  frozenOriginTimeRepresentation :=
    ⟨frozenOriginRepresentation U ρFrozen⟩
  criticalStartTimeNonpos :=
    ads5BoundaryStartTimeFromEntropicProperTime_nonpos U ρCritical σCritical
  criticalStartTimeNegative :=
    ads5BoundaryStartTimeFromEntropicProperTime_critical_neg
      U ρCritical σCritical hτ
  criticalStartMagnitude :=
    ads5PastEntropicStartTime_abs_eq_entropicProperTime
      U ρCritical σCritical
  frozenEntropicProperTime :=
    entropicProperTimeMetric_self U ρFrozen
  frozenStartTime :=
    ads5BoundaryStartTimeFromEntropicProperTime_frozen U ρFrozen
  frozenNoMiddleBounce :=
    ads5_frozenEntropicProperTime_not_null_to_futureMiddleSingularity U ρFrozen
  criticalEntropicProperTime := hτ
  criticalEntropicProperTimePositive :=
    ads5CriticalEntropicProperTime_pos U ρCritical σCritical hτ
  criticalStartTime :=
    ads5BoundaryStartTimeFromEntropicProperTime_eq_critical_of_quarter
      U ρCritical σCritical hτ
  criticalMiddleBounce :=
    ads5_quarterEntropicProperTime_null_to_futureMiddleSingularity
      U ρCritical σCritical hτ

/-- A checked summary of Appendix A's Kruskal-coordinate geometry and its
main relation to the paper's critical null ray. -/
structure FhksKruskalAppendixBridge : Prop where
  exteriorSigns :
    ∀ t rstar : ℝ, kruskalUFromTR t rstar < 0 ∧ 0 < kruskalVFromTR t rstar
  tortoiseInvariant :
    ∀ t rstar : ℝ,
      kruskalTFromTR t rstar ^ 2 - kruskalXFromTR t rstar ^ 2 =
        -Real.exp (4 * rstar)
  horizonAxes :
    ∀ U V : ℝ, kruskalT U V ^ 2 - kruskalX U V ^ 2 = 0 ↔ U = 0 ∨ V = 0
  boundaryProduct :
    ∀ t : ℝ, ads5RightBoundaryUOfTime t * ads5RightBoundaryVOfTime t =
      ads5KruskalBoundaryUV
  boundaryTimeRatio :
    ∀ t : ℝ, ads5RightBoundaryVOfTime t / (-(ads5RightBoundaryUOfTime t)) =
      Real.exp (4 * t)
  boundaryFartherThanSingularity :
    ads5KruskalRadialUV 0 < -ads5KruskalBoundaryUV
  noTZeroMiddleBounce :
    ¬ kruskalRadialNullSeparated
      (ads5RightBoundaryTOfTime 0) (ads5RightBoundaryXOfTime 0) 1 0
  criticalMiddleBounce :
    kruskalRadialNullSeparated
      (ads5RightBoundaryTOfTime ads5CriticalBoundaryStartTime)
      (ads5RightBoundaryXOfTime ads5CriticalBoundaryStartTime) 1 0

/-- Appendix A assembled as one checked bridge. -/
lemma fhksKruskalAppendix_bridge : FhksKruskalAppendixBridge where
  exteriorSigns := kruskalRightExterior_signs
  tortoiseInvariant := kruskalTX_interval_from_tortoise
  horizonAxes := kruskalTX_horizon_axes
  boundaryProduct := ads5RightBoundaryUV_eq_boundary
  boundaryTimeRatio := ads5RightBoundary_timeRatio
  boundaryFartherThanSingularity := ads5KruskalBoundarySquaredRadius_gt_singularity
  noTZeroMiddleBounce := ads5RightBoundary_tZero_not_null_to_futureMiddleSingularity
  criticalMiddleBounce := ads5CriticalBoundary_null_to_futureMiddleSingularity


end Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.ads5CriticalBoundary_null_to_futureMiddleSingularity where
  formalizes @ "claim:the-ads5-right-boundary-point-at-the-critical-start-time-is-kruskal-radial-null-separated-from-the-future-interior-singularity-the-fhks-bulk-cone-null-geodesic-that-signals-the-singularity",
  supported_by @ "paper:fidkowski-hubeny-kleban-shenker-jhep-02-2004-014-the-black-hole-singularity-in-ads-cft"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.ads5BoundaryStartTimeFromEntropicProperTime_nonpos where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.ads5BoundaryStartTimeFromEntropicProperTime_eq_neg",
  formalizes @ "claim:the-past-oriented-fhks-boundary-start-coordinate-parametrized-by-the-metric-entropic-proper-time-is-non-positive-the-minus-tau-ent-orientation-convention"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.ads5PastEntropicStartTime_abs_eq_entropicProperTime where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.ads5BoundaryStartTimeFromEntropicProperTime_eq_neg",
  formalizes @ "claim:the-absolute-value-of-the-past-oriented-fhks-boundary-start-coordinate-recovers-the-non-negative-entropic-proper-time-magnitude-so-the-negativity-belongs-to-orientation-not-magnitude",
  requires @ "claim:the-past-oriented-fhks-boundary-start-coordinate-parametrized-by-the-metric-entropic-proper-time-is-non-positive-the-minus-tau-ent-orientation-convention"

zil attach Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.ads5BoundaryStartTimeFromEntropicProperTime_eq_zero_iff where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.ads5BoundaryStartTimeFromEntropicProperTime_eq_neg",
  formalizes @ "claim:under-the-minus-tau-ent-convention-the-t-equals-zero-slice-is-exactly-the-zero-entropic-proper-time-reading-not-asserting-the-converse-state-identity"

zil_file_contract physlib.nullRayAndEntropicProperTime where
  promises "The FHKS bulk-cone null geodesic that signals the AdS5 black-hole singularity, parametrized by the entropic proper time. The right-boundary point at the critical start time is Kruskal radial null-separated from the future interior singularity (ads5CriticalBoundary_null_to_futureMiddleSingularity) -- the null geodesic whose boundary endpoint marks the light-cone singularity of the correlator. The FHKS boundary start coordinate is parametrized by the metric entropic proper time under the -tau_ent convention: it is non-positive (ads5BoundaryStartTimeFromEntropicProperTime_nonpos), its absolute value recovers the non-negative entropic proper-time magnitude so the negativity is orientation not magnitude (ads5PastEntropicStartTime_abs_eq_entropicProperTime), and the t=0 slice is exactly the zero entropic proper-time reading (ads5BoundaryStartTimeFromEntropicProperTime_eq_zero_iff), without asserting the converse state identity."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.ads5BoundaryStartTimeFromEntropicProperTime",
    "lean:Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.kruskalRadialNullSeparated"]
  forbids_substitutes ["the global Kruskal extension geometry and the null-geodesic completeness of the eternal AdS-Schwarzschild spacetime, which are the cited global-geometry inputs",
    "any claim that the entropic proper time is the unique physical clock, only the -tau_ent parametrization of the FHKS boundary start coordinate is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.ads5CriticalBoundary_null_to_futureMiddleSingularity,
    Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.ads5BoundaryStartTimeFromEntropicProperTime_nonpos,
    Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.ads5PastEntropicStartTime_abs_eq_entropicProperTime,
    Physlib.QuantumMechanics.ComplexAction.AdSBlackHoleSingularityCorrelators.ads5BoundaryStartTimeFromEntropicProperTime_eq_zero_iff]

/- ZIL-END -/
