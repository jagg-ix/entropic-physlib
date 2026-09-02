/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenComplexChernSimonsQuantization
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenJonesPolynomialChernSimons
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.BraidRelationTrefoilTorus
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.Field
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.HopfAlgebraWilsonLoop
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.lessDiracTrefoilPhaseRegion
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSFieldFourierSobolevHierarchy
public import Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.Basic
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.PicardLefschetzMorseContour
public import Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.TrefoilBracketTemperleyLieb
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon

/-! # WittenAnalyticContinuationChernSimons — part `SourceAnchorsAndTrefoilThimbles`. Full docstring in the umbrella module
`Physlib.QuantumMechanics.ComplexAction.WittenAnalyticContinuationChernSimons`; namespace and declaration names unchanged (the umbrella re-exports them). -/

set_option autoImplicit false

universe u

open Complex
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.BraidRelationTrefoilTorus
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeConvolution
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.HopfAlgebraWilsonLoop
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.lessDiracTrefoilPhaseRegion
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.lessDiracTrefoilPhaseRegion.ThreeNodulePhaseRegion
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.Basic
open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.RMatrixYangBaxter
open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.TrefoilBracketTemperleyLieb
open Physlib.QuantumMechanics.ComplexAction.QuantumGroupSkein.QuantumGroupSl2Casimir
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

/-! ## A. Source anchors -/

/-- Local bibliographic/source record for Witten's analytic-continuation paper. -/
structure WittenAnalyticContinuationReference where
  title : String
  author : String
  arxiv : String
  paperVersion : String
  localPdf : String
  deriving Repr, DecidableEq

/-- The local Witten source inspected for this formalization. -/
def wittenAnalyticContinuationReference : WittenAnalyticContinuationReference :=
  { title := "Analytic Continuation Of Chern-Simons Theory"
    author := "Edward Witten"
    arxiv := "1001.2933"
    paperVersion := "v4"
    localPdf :=
      "Analytic Continuation Of Chern-Simons Theory1001.2933v4.pdf" }

/-- Stable anchors for the parts of Witten 1001.2933v4 formalized below. -/
inductive WittenAnalyticContinuationAnchor where
  | generalizedIntegrationCycle
  | lefschetzThimble
  | stokesJump
  | trefoilFlatConnectionSingularity
  | trefoilCycleFormula
  | trefoilSemiclassicalExponent
  | trefoilStokesCurve
  deriving Repr, DecidableEq

/-- Paper locator for each analytic-continuation anchor. -/
def WittenAnalyticContinuationAnchor.paperLabel :
    WittenAnalyticContinuationAnchor → String
  | .generalizedIntegrationCycle => "Sections 2-3: generalized integration cycles"
  | .lefschetzThimble => "Section 3: Lefschetz thimbles"
  | .stokesJump => "Section 3.3-3.4: Stokes phenomena"
  | .trefoilFlatConnectionSingularity => "Section 5.2.1, equations (5.16)-(5.24)"
  | .trefoilCycleFormula => "Section 5.2.3, equation (5.31)"
  | .trefoilSemiclassicalExponent => "Section 5.2.2-5.2.3, equations (5.30)-(5.33)"
  | .trefoilStokesCurve => "Section 5.2.4, equation (5.39)"

/-! ## B. Picard-Lefschetz cycle bookkeeping -/

/-- A critical point carrier for the finite-dimensional Picard-Lefschetz shadow: the only datum needed
for Stokes alignment is the value of the complex exponent `I`. -/
structure LefschetzCriticalPoint where
  exponent : ℂ

/-- Witten's Stokes condition: the conserved quantity `Im I` agrees for two critical points. -/
def StokesAligned (p q : LefschetzCriticalPoint) : Prop :=
  p.exponent.im = q.exponent.im

/-- Stokes alignment is reflexive. -/
lemma stokesAligned_refl (p : LefschetzCriticalPoint) : StokesAligned p p := rfl

/-- Stokes alignment is symmetric. -/
lemma stokesAligned_symm {p q : LefschetzCriticalPoint} :
    StokesAligned p q → StokesAligned q p := by
  intro h
  exact h.symm

/-- A thimble cycle is an integer coefficient for every Lefschetz-thimble label. -/
abbrev ThimbleCycle (ι : Type u) : Type u :=
  ι → ℤ

/-- Add `n` copies of a thimble `j` to an integration cycle. -/
def addThimble {ι : Type*} [DecidableEq ι] (C : ThimbleCycle ι) (j : ι) (n : ℤ) :
    ThimbleCycle ι :=
  fun i => C i + if i = j then n else 0

/-- The coefficient of the thimble crossed at a Stokes jump changes by the jump multiplicity. -/
lemma addThimble_coeff_self {ι : Type*} [DecidableEq ι]
    (C : ThimbleCycle ι) (j : ι) (n : ℤ) :
    addThimble C j n j = C j + n := by
  simp [addThimble]

/-- Unrelated thimble coefficients are unchanged by a Stokes jump. -/
lemma addThimble_coeff_other {ι : Type*} [DecidableEq ι]
    (C : ThimbleCycle ι) {i j : ι} (n : ℤ) (hij : i ≠ j) :
    addThimble C j n i = C i := by
  simp [addThimble, hij]

/-- Two Stokes additions at distinct thimbles commute at the level of cycles. -/
lemma addThimble_comm {ι : Type*} [DecidableEq ι]
    (C : ThimbleCycle ι) {i j : ι} (m n : ℤ) (hij : i ≠ j) :
    addThimble (addThimble C i m) j n =
      addThimble (addThimble C j n) i m := by
  funext x
  by_cases hxi : x = i
  · subst hxi
    simp [addThimble, hij]
  · by_cases hxj : x = j
    · subst hxj
      simp [addThimble, hxi]
    · simp [addThimble, hxi, hxj]

/-! ## C. Trefoil thimbles and Witten Eq. (5.31) -/

/-- The Lefschetz thimbles used in Witten's trefoil analysis:
`J_ab` for the abelian flat connection and `J_y` for a nonabelian lift meeting it at `gamma = y`. -/
inductive TrefoilThimble where
  | abelian
  | nonabelian (y : ℚ)
  deriving Repr, DecidableEq

namespace TrefoilThimble

/-- `1/6`, the first positive trefoil Stokes value. -/
def y1 : ℚ := (1 : ℚ) / 6

/-- `5/6`, the second positive trefoil Stokes value. -/
def y5 : ℚ := (5 : ℚ) / 6

/-- `7/6`, the third positive trefoil Stokes value. -/
def y7 : ℚ := (7 : ℚ) / 6

/-- `11/6`, the fourth positive trefoil Stokes value. -/
def y11 : ℚ := (11 : ℚ) / 6

/-- Nonabelian trefoil thimble at the first positive Stokes value. -/
def J1 : TrefoilThimble := nonabelian y1

/-- Nonabelian trefoil thimble at the second positive Stokes value. -/
def J5 : TrefoilThimble := nonabelian y5

/-- Nonabelian trefoil thimble at the third positive Stokes value. -/
def J7 : TrefoilThimble := nonabelian y7

/-- Nonabelian trefoil thimble at the fourth positive Stokes value. -/
def J11 : TrefoilThimble := nonabelian y11

/-- Witten Eq. (5.28): relevant trefoil Stokes values satisfy `y = ±(1/6 + p)`. -/
def IsTrefoilStokesValue (y : ℚ) : Prop :=
  ∃ p : ℤ, y = (p : ℚ) + (1 : ℚ) / 6 ∨ y = -((p : ℚ) + (1 : ℚ) / 6)

lemma y1_isStokesValue : IsTrefoilStokesValue y1 := by
  use 0
  left
  norm_num [y1]

lemma y5_isStokesValue : IsTrefoilStokesValue y5 := by
  use -1
  right
  norm_num [y5]

lemma y7_isStokesValue : IsTrefoilStokesValue y7 := by
  use 1
  left
  norm_num [y7]

lemma y11_isStokesValue : IsTrefoilStokesValue y11 := by
  use -2
  right
  norm_num [y11]

end TrefoilThimble

open TrefoilThimble

/-! ## C1. The trefoil singularity and lift parameters, Witten Eqs. (5.21)-(5.30) -/

/-- **[Witten Eq. (5.21)]** The real `SU(2)` branch near the abelian/nonabelian collision is
`x^2 + y^2 = epsilon`. -/
def TrefoilSU2OrbitEquation (epsilon x y : ℝ) : Prop :=
  x ^ 2 + y ^ 2 = epsilon

/-- A real trefoil orbit forces `epsilon >= 0`, matching the paper's statement that the
`SU(2)` nonabelian branch exists only on the nonnegative side of the singularity. -/
lemma trefoilSU2Orbit_forces_nonnegative_epsilon {epsilon x y : ℝ}
    (h : TrefoilSU2OrbitEquation epsilon x y) :
    0 ≤ epsilon := by
  rw [← h]
  exact add_nonneg (sq_nonneg x) (sq_nonneg y)

/-- Conversely, every nonnegative `epsilon` has a real point on the local `SU(2)` branch. -/
lemma trefoilSU2Orbit_exists_of_nonnegative_epsilon {epsilon : ℝ}
    (h : 0 ≤ epsilon) :
    ∃ x y : ℝ, TrefoilSU2OrbitEquation epsilon x y := by
  refine ⟨Real.sqrt epsilon, 0, ?_⟩
  simp [TrefoilSU2OrbitEquation, Real.sq_sqrt h]

/-- **[Witten Eq. (5.22)]** The finite local model of the trefoil singularity:
`F = c(1/2 (x^2+y^2)^2 - epsilon (x^2+y^2))`. -/
noncomputable def trefoilSingularityModel (c epsilon x y : ℝ) : ℝ :=
  c * ((1 / 2) * (x ^ 2 + y ^ 2) ^ 2 - epsilon * (x ^ 2 + y ^ 2))

/-- The abelian orbit `x = y = 0` has zero local model action. -/
@[simp] lemma trefoilSingularityModel_origin (c epsilon : ℝ) :
    trefoilSingularityModel c epsilon 0 0 = 0 := by
  simp [trefoilSingularityModel]

/-- On the nonabelian orbit `x^2+y^2=epsilon`, the local model action is quadratic in the
collision parameter. This is the algebraic content used in Witten's passage from Eq. (5.22)
to the quadratic exponent Eq. (5.30). -/
lemma trefoilSingularityModel_on_nonabelian_orbit {c epsilon x y : ℝ}
    (h : TrefoilSU2OrbitEquation epsilon x y) :
    trefoilSingularityModel c epsilon x y = -(c * epsilon ^ 2) / 2 := by
  unfold TrefoilSU2OrbitEquation at h
  unfold trefoilSingularityModel
  rw [h]
  ring

/-- At the singular point `epsilon = 0`, the abelian and nonabelian local model values coincide. -/
lemma trefoilSingularityModel_zero_collision {c x y : ℝ}
    (h : TrefoilSU2OrbitEquation 0 x y) :
    trefoilSingularityModel c 0 x y = 0 := by
  rw [trefoilSingularityModel_on_nonabelian_orbit h]
  ring

/-- Positive real-axis Stokes values of type `p + 1/6`; these are the `+` entries in
Witten's Eq. (5.31) pattern. -/
def positiveTrefoilPlusStokesValue (p : ℤ) : ℚ :=
  (p : ℚ) + (1 : ℚ) / 6

/-- Positive real-axis Stokes values of type `p + 5/6`; these are the `-` entries in
Witten's Eq. (5.31) pattern. -/
def positiveTrefoilMinusStokesValue (p : ℤ) : ℚ :=
  (p : ℚ) + (5 : ℚ) / 6

/-- **[Witten Eq. (5.29)]** Lift label `s = 3y^2/2 - 1/24`. -/
def trefoilLiftS (y : ℚ) : ℚ :=
  3 * y ^ 2 / 2 - 1 / 24

/-- **[Witten Eq. (5.29)]** Lift label `r = 1/2 - 3y`. -/
def trefoilLiftR (y : ℚ) : ℚ :=
  1 / 2 - 3 * y

lemma positiveTrefoilPlusStokesValue_isStokesValue (p : ℤ) :
    IsTrefoilStokesValue (positiveTrefoilPlusStokesValue p) := by
  use p
  left
  simp [positiveTrefoilPlusStokesValue]

lemma positiveTrefoilMinusStokesValue_isStokesValue (p : ℤ) :
    IsTrefoilStokesValue (positiveTrefoilMinusStokesValue p) := by
  use -p - 1
  right
  simp [positiveTrefoilMinusStokesValue]
  ring

/-- For `y = p + 1/6`, Witten's lift parameter is the integer-valued quadratic
`s = p(3p+1)/2`. -/
lemma trefoilLiftS_positivePlusStokesValue (p : ℤ) :
    trefoilLiftS (positiveTrefoilPlusStokesValue p)
      = ((p : ℚ) * (3 * (p : ℚ) + 1)) / 2 := by
  simp [trefoilLiftS, positiveTrefoilPlusStokesValue]
  ring

/-- For `y = p + 1/6`, Witten's branch parameter is `r = -3p`. -/
lemma trefoilLiftR_positivePlusStokesValue (p : ℤ) :
    trefoilLiftR (positiveTrefoilPlusStokesValue p) = -3 * (p : ℚ) := by
  simp [trefoilLiftR, positiveTrefoilPlusStokesValue]
  ring

/-- For `y = p + 5/6`, Witten's lift parameter is the integer-valued quadratic
`s = (p+1)(3p+2)/2`. -/
lemma trefoilLiftS_positiveMinusStokesValue (p : ℤ) :
    trefoilLiftS (positiveTrefoilMinusStokesValue p)
      = (((p : ℚ) + 1) * (3 * (p : ℚ) + 2)) / 2 := by
  simp [trefoilLiftS, positiveTrefoilMinusStokesValue]
  ring

/-- For `y = p + 5/6`, Witten's branch parameter is `r = -(3p+2)`. -/
lemma trefoilLiftR_positiveMinusStokesValue (p : ℤ) :
    trefoilLiftR (positiveTrefoilMinusStokesValue p) = -(3 * (p : ℚ) + 2) := by
  simp [trefoilLiftR, positiveTrefoilMinusStokesValue]
  ring

@[simp] lemma trefoilLiftS_y1 : trefoilLiftS y1 = 0 := by
  norm_num [trefoilLiftS, y1]

@[simp] lemma trefoilLiftR_y1 : trefoilLiftR y1 = 0 := by
  norm_num [trefoilLiftR, y1]

@[simp] lemma trefoilLiftS_y5 : trefoilLiftS y5 = 1 := by
  norm_num [trefoilLiftS, y5]

@[simp] lemma trefoilLiftR_y5 : trefoilLiftR y5 = -2 := by
  norm_num [trefoilLiftR, y5]

@[simp] lemma trefoilLiftS_y7 : trefoilLiftS y7 = 2 := by
  norm_num [trefoilLiftS, y7]

@[simp] lemma trefoilLiftR_y7 : trefoilLiftR y7 = -3 := by
  norm_num [trefoilLiftR, y7]

@[simp] lemma trefoilLiftS_y11 : trefoilLiftS y11 = 5 := by
  norm_num [trefoilLiftS, y11]

@[simp] lemma trefoilLiftR_y11 : trefoilLiftR y11 = -5 := by
  norm_num [trefoilLiftR, y11]

/-- Near `gamma = 0`, Witten's real integration cycle is just the abelian thimble `J_ab`. -/
def trefoilCycle_near_zero : ThimbleCycle TrefoilThimble :=
  fun j => if j = TrefoilThimble.abelian then 1 else 0

@[simp] lemma trefoilCycle_near_zero_abelian :
    trefoilCycle_near_zero .abelian = 1 := by
  simp [trefoilCycle_near_zero]

@[simp] lemma trefoilCycle_near_zero_nonabelian (y : ℚ) :
    trefoilCycle_near_zero (.nonabelian y) = 0 := by
  simp [trefoilCycle_near_zero]

/-- Just to the right of `gamma = 1/6`: `J_ab + J_1/6`. -/
def trefoilCycle_after_1_over_6 : ThimbleCycle TrefoilThimble :=
  addThimble trefoilCycle_near_zero J1 1

/-- The first trefoil jump is the generic Stokes coefficient jump from Witten §2.3:
crossing the wall at `gamma = 1/6` adds one copy of the thimble `J_1/6`. -/
lemma trefoilCycle_after_1_over_6_is_general_stokesCoefficientJump :
    trefoilCycle_after_1_over_6 =
      OperatorAlgebra.PicardLefschetzMorseContour.stokesCoefficientJump trefoilCycle_near_zero J1 1 :=
  rfl

/-- The coefficient of `J_1/6` after the first trefoil Stokes crossing is obtained by
the general target-coefficient theorem for Stokes jumps. -/
lemma trefoilCycle_after_1_over_6_J1_from_general_stokes :
    trefoilCycle_after_1_over_6 J1 = 1 := by
  rw [trefoilCycle_after_1_over_6_is_general_stokesCoefficientJump]
  have h :=
    OperatorAlgebra.PicardLefschetzMorseContour.stokesCoefficientJump_target
      trefoilCycle_near_zero J1 1
  simpa [trefoilCycle_near_zero, J1] using h

/-- Just to the right of `gamma = 5/6`: `J_ab + J_1/6 - J_5/6`. -/
def trefoilCycle_after_5_over_6 : ThimbleCycle TrefoilThimble :=
  addThimble trefoilCycle_after_1_over_6 J5 (-1)

/-- Just to the right of `gamma = 7/6`: `J_ab + J_1/6 - J_5/6 + J_7/6`. -/
def trefoilCycle_after_7_over_6 : ThimbleCycle TrefoilThimble :=
  addThimble trefoilCycle_after_5_over_6 J7 1

/-- Just to the right of `gamma = 11/6`: `J_ab + J_1/6 - J_5/6 + J_7/6 - J_11/6`. -/
def trefoilCycle_after_11_over_6 : ThimbleCycle TrefoilThimble :=
  addThimble trefoilCycle_after_7_over_6 J11 (-1)

lemma trefoilCycle_after_1_over_6_coefficients :
    trefoilCycle_after_1_over_6 .abelian = 1
      ∧ trefoilCycle_after_1_over_6 J1 = 1
      ∧ trefoilCycle_after_1_over_6 J5 = 0 := by
  simp [trefoilCycle_after_1_over_6, addThimble, trefoilCycle_near_zero, J1, J5, y1, y5]
  norm_num

/-- **[Witten Eq. (5.31), first two jumps]** Just beyond `gamma = 5/6`, the trefoil cycle is
`J_ab + J_1/6 - J_5/6`. -/
lemma trefoilCycle_after_5_over_6_coefficients :
    trefoilCycle_after_5_over_6 .abelian = 1
      ∧ trefoilCycle_after_5_over_6 J1 = 1
      ∧ trefoilCycle_after_5_over_6 J5 = -1
      ∧ trefoilCycle_after_5_over_6 J7 = 0 := by
  simp [trefoilCycle_after_5_over_6, trefoilCycle_after_1_over_6,
    addThimble, trefoilCycle_near_zero, J1, J5, J7, y1, y5, y7]
  norm_num

/-- **[Witten Eq. (5.31), first four positive jumps]** Just beyond `gamma = 11/6`, the trefoil cycle is
`J_ab + J_1/6 - J_5/6 + J_7/6 - J_11/6`. -/
lemma trefoilCycle_after_11_over_6_coefficients :
    trefoilCycle_after_11_over_6 .abelian = 1
      ∧ trefoilCycle_after_11_over_6 J1 = 1
      ∧ trefoilCycle_after_11_over_6 J5 = -1
      ∧ trefoilCycle_after_11_over_6 J7 = 1
      ∧ trefoilCycle_after_11_over_6 J11 = -1 := by
  simp [trefoilCycle_after_11_over_6, trefoilCycle_after_7_over_6,
    trefoilCycle_after_5_over_6, trefoilCycle_after_1_over_6,
    addThimble, trefoilCycle_near_zero, J1, J5, J7, J11, y1, y5, y7, y11]
  norm_num


end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
