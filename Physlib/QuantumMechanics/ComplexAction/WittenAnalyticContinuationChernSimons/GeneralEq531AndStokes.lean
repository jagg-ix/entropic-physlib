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
public import Physlib.QuantumMechanics.ComplexAction.WittenAnalyticContinuationChernSimons.SourceAnchorsAndTrefoilThimbles

/-! # WittenAnalyticContinuationChernSimons — part `GeneralEq531AndStokes`. Full docstring in the umbrella module
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

open TrefoilThimble

/-! ## C2. General finite prefix of Witten Eq. (5.31) -/

/-- Labels for the positive real-axis version of Witten Eq. (5.31).

`plus p` labels `J_{p+1/6}` and `minus p` labels `J_{p+5/6}`. A paired prefix through
`p < N` is therefore
`J_ab + Σ_{p<N} J_{p+1/6} - Σ_{p<N} J_{p+5/6}`. -/
inductive TrefoilEq531PositiveLabel where
  | abelian
  | plus (p : ℕ)
  | minus (p : ℕ)
  deriving Repr, DecidableEq

namespace TrefoilEq531PositiveLabel

/-- The thimble represented by a positive-axis Eq. (5.31) label. -/
def thimble : TrefoilEq531PositiveLabel → TrefoilThimble
  | .abelian => .abelian
  | .plus p => .nonabelian (positiveTrefoilPlusStokesValue p)
  | .minus p => .nonabelian (positiveTrefoilMinusStokesValue p)

@[simp] lemma thimble_abelian : thimble .abelian = TrefoilThimble.abelian := rfl

@[simp] lemma thimble_plus (p : ℕ) :
    thimble (.plus p) = .nonabelian (positiveTrefoilPlusStokesValue p) := rfl

@[simp] lemma thimble_minus (p : ℕ) :
    thimble (.minus p) = .nonabelian (positiveTrefoilMinusStokesValue p) := rfl

/-- The first four positive-axis labels recover Witten's named thimbles
`J_1/6`, `J_5/6`, `J_7/6`, and `J_11/6`. -/
lemma first_four_thimbles :
    thimble (.plus 0) = J1
      ∧ thimble (.minus 0) = J5
      ∧ thimble (.plus 1) = J7
      ∧ thimble (.minus 1) = J11 := by
  simp [thimble, positiveTrefoilPlusStokesValue, positiveTrefoilMinusStokesValue,
    J1, J5, J7, J11, y1, y5, y7, y11]
  norm_num

end TrefoilEq531PositiveLabel

/-- **[Witten Eq. (5.31), finite positive paired prefix]**
The paired prefix through `p < N` is
`J_ab + Σ_{p<N} J_{p+1/6} - Σ_{p<N} J_{p+5/6}`. This is the general version of the
alternating pattern whose first four terms are `J_1/6 - J_5/6 + J_7/6 - J_11/6`. -/
def trefoilEq531PositivePairedPrefixCycle (N : ℕ) :
    TrefoilEq531PositiveLabel → ℤ
  | .abelian => 1
  | .plus p => if p < N then 1 else 0
  | .minus p => if p < N then -1 else 0

@[simp] lemma trefoilEq531PositivePairedPrefixCycle_abelian (N : ℕ) :
    trefoilEq531PositivePairedPrefixCycle N .abelian = 1 := rfl

lemma trefoilEq531PositivePairedPrefixCycle_plus (N p : ℕ) :
    trefoilEq531PositivePairedPrefixCycle N (.plus p) = if p < N then 1 else 0 := rfl

lemma trefoilEq531PositivePairedPrefixCycle_minus (N p : ℕ) :
    trefoilEq531PositivePairedPrefixCycle N (.minus p) = if p < N then -1 else 0 := rfl

lemma trefoilEq531PositivePairedPrefixCycle_plus_of_lt {N p : ℕ} (h : p < N) :
    trefoilEq531PositivePairedPrefixCycle N (.plus p) = 1 := by
  simp [trefoilEq531PositivePairedPrefixCycle, h]

lemma trefoilEq531PositivePairedPrefixCycle_minus_of_lt {N p : ℕ} (h : p < N) :
    trefoilEq531PositivePairedPrefixCycle N (.minus p) = -1 := by
  simp [trefoilEq531PositivePairedPrefixCycle, h]

lemma trefoilEq531PositivePairedPrefixCycle_plus_of_ge {N p : ℕ} (h : N ≤ p) :
    trefoilEq531PositivePairedPrefixCycle N (.plus p) = 0 := by
  simp [trefoilEq531PositivePairedPrefixCycle, not_lt.mpr h]

lemma trefoilEq531PositivePairedPrefixCycle_minus_of_ge {N p : ℕ} (h : N ≤ p) :
    trefoilEq531PositivePairedPrefixCycle N (.minus p) = 0 := by
  simp [trefoilEq531PositivePairedPrefixCycle, not_lt.mpr h]

/-- The paired prefix with `N = 2` is exactly the first four positive jumps appearing explicitly
in Witten Eq. (5.31): `+J_1/6 - J_5/6 + J_7/6 - J_11/6`. -/
lemma trefoilEq531PositivePairedPrefixCycle_two_coefficients :
    trefoilEq531PositivePairedPrefixCycle 2 .abelian = 1
      ∧ trefoilEq531PositivePairedPrefixCycle 2 (.plus 0) = 1
      ∧ trefoilEq531PositivePairedPrefixCycle 2 (.minus 0) = -1
      ∧ trefoilEq531PositivePairedPrefixCycle 2 (.plus 1) = 1
      ∧ trefoilEq531PositivePairedPrefixCycle 2 (.minus 1) = -1
      ∧ TrefoilEq531PositiveLabel.thimble (.plus 0) = J1
      ∧ TrefoilEq531PositiveLabel.thimble (.minus 0) = J5
      ∧ TrefoilEq531PositiveLabel.thimble (.plus 1) = J7
      ∧ TrefoilEq531PositiveLabel.thimble (.minus 1) = J11 := by
  have hfirst := TrefoilEq531PositiveLabel.first_four_thimbles
  simp [trefoilEq531PositivePairedPrefixCycle, hfirst.1, hfirst.2.1, hfirst.2.2.1,
    hfirst.2.2.2]

/-! ## D. Witten Eq. (5.30), Eq. (5.33), and the Stokes-curve carrier -/

/-- **[Witten Eq. (5.30)]** The nonabelian contribution lifted to meet the abelian one at `gamma = y` has
semiclassical exponent `I_y = -3*pi*i*n*gamma^{-1}(gamma-y)^2`. -/
noncomputable def trefoilNonabelianExponent (n gamma y : ℂ) : ℂ :=
  -3 * (Real.pi : ℂ) * Complex.I * n * gamma⁻¹ * (gamma - y) ^ 2

/-- At the collision value `gamma = y`, the nonabelian exponent vanishes, matching the stable-equivalence
point where `J_y` is born from the abelian thimble. -/
@[simp] lemma trefoilNonabelianExponent_at_stokes (n y : ℂ) :
    trefoilNonabelianExponent n y y = 0 := by
  simp [trefoilNonabelianExponent]

/-- At the trefoil birth value `gamma = y`, the abelian exponent and nonabelian exponent
are Stokes-aligned in the general sense of Witten §2.3: their conserved `Im I`
values agree. -/
lemma trefoil_birth_is_general_stokesAlignment (n y : ℂ) :
    OperatorAlgebra.PicardLefschetzMorseContour.StokesAligned
      (OperatorAlgebra.PicardLefschetzMorseContour.stokesCriticalPoint 0)
      (OperatorAlgebra.PicardLefschetzMorseContour.stokesCriticalPoint
        (trefoilNonabelianExponent n y y)) := by
  simp [OperatorAlgebra.PicardLefschetzMorseContour.StokesAligned,
    OperatorAlgebra.PicardLefschetzMorseContour.stokesCriticalPoint]

/-- The Stokes connection at the trefoil birth point `gamma = y`, where the
abelian and nonabelian critical exponents coincide. -/
noncomputable def trefoilBirthStokesConnection (n y : ℂ) :
    OperatorAlgebra.PicardLefschetzMorseContour.StokesConnection where
  source := OperatorAlgebra.PicardLefschetzMorseContour.stokesCriticalPoint 0
  target := OperatorAlgebra.PicardLefschetzMorseContour.stokesCriticalPoint
    (trefoilNonabelianExponent n y y)
  multiplicity := 1
  aligned := trefoil_birth_is_general_stokesAlignment n y

/-- At the trefoil birth point, the target has the same Morse height as the
source, so the Stokes connection is height-ordered. -/
lemma trefoilBirthStokesConnection_heightOrdered (n y : ℂ) :
    (trefoilBirthStokesConnection n y).HeightOrdered := by
  simp [trefoilBirthStokesConnection,
    OperatorAlgebra.PicardLefschetzMorseContour.StokesConnection.HeightOrdered,
    OperatorAlgebra.PicardLefschetzMorseContour.stokesCriticalPoint]

/-- Therefore the trefoil birth Stokes connection has a Chern-Simons
gradient-flow line in the repo's Picard-Lefschetz carrier. -/
lemma trefoil_birth_gradientFlowLine_exists (n y : ℂ) :
    Nonempty
      (OperatorAlgebra.PicardLefschetzMorseContour.ChernSimonsGradientFlowLine
        (trefoilBirthStokesConnection n y)) :=
  OperatorAlgebra.PicardLefschetzMorseContour.chernSimonsGradientFlowLine_exists_of_heightOrdered
    (trefoilBirthStokesConnection n y)
    (trefoilBirthStokesConnection_heightOrdered n y)

/-- The nonabelian exponent is quadratic in the displacement from the Stokes value. -/
lemma trefoilNonabelianExponent_eq_quadratic (n gamma y : ℂ) :
    trefoilNonabelianExponent n gamma y =
      (-3 * (Real.pi : ℂ) * Complex.I * n * gamma⁻¹) * (gamma - y) ^ 2 := by
  simp [trefoilNonabelianExponent]

/-- **[Witten Eq. (5.33), real-growth carrier]** For `gamma = a + i b`, the real part of the logarithmic
asymptotic growth is carried by `3*pi*n*b*(1 - y^2/(a^2+b^2))`. -/
noncomputable def trefoilGrowthRate (n a b y : ℝ) : ℝ :=
  3 * Real.pi * n * b * (1 - y ^ 2 / (a ^ 2 + b ^ 2))

/-- Conditional positivity of the Witten growth carrier: positive `n`, positive imaginary part, and a
positive parenthetical factor imply exponential growth. -/
lemma trefoilGrowthRate_pos {n a b y : ℝ}
    (hn : 0 < n) (hb : 0 < b) (hfactor : 0 < 1 - y ^ 2 / (a ^ 2 + b ^ 2)) :
    0 < trefoilGrowthRate n a b y := by
  unfold trefoilGrowthRate
  positivity

/-- Near the real axis, if `y^2 < a^2` and `b > 0`, Witten's growth carrier is positive.
This is the Lean-checked form of the statement after Eq. (5.33): once the relevant thimble
coefficient is nonzero, the upper half-plane gives exponential growth. -/
lemma trefoilGrowthRate_pos_of_y_sq_lt_a_sq {n a b y : ℝ}
    (hn : 0 < n) (hb : 0 < b) (hy : y ^ 2 < a ^ 2) :
    0 < trefoilGrowthRate n a b y := by
  apply trefoilGrowthRate_pos hn hb
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have hden_gt : y ^ 2 < a ^ 2 + b ^ 2 :=
    lt_of_lt_of_le hy (le_add_of_nonneg_right hb2)
  have hden_pos : 0 < a ^ 2 + b ^ 2 :=
    lt_of_le_of_lt (sq_nonneg y) hden_gt
  have hdiv : y ^ 2 / (a ^ 2 + b ^ 2) < 1 := by
    exact (div_lt_one hden_pos).2 hden_gt
  linarith

/-- **[Witten Eq. (5.39)]** The relevant trefoil Stokes curve through `y` is
`b^2 = - a(a-y)^2/(a-2y)`. -/
def TrefoilStokesCurve (a b y : ℝ) : Prop :=
  b ^ 2 = -(a * (a - y) ^ 2) / (a - 2 * y)

/-- **[Witten Eq. (5.38)]** The abelian/nonabelian Stokes curve before substituting the special
trefoil lift parameters `r,s`. -/
def TrefoilAbelianNonabelianStokesCurve (a b r s : ℝ) : Prop :=
  b ^ 2 = -(a * (3 * a ^ 2 + (2 * r - 1) * a + (2 * s + 1 / 12))) /
    (3 * a + 2 * r - 1)

/-- Real version of Witten's lift parameter `s = 3y^2/2 - 1/24`. -/
noncomputable def trefoilLiftSReal (y : ℝ) : ℝ :=
  3 * y ^ 2 / 2 - 1 / 24

/-- Real version of Witten's branch parameter `r = 1/2 - 3y`. -/
noncomputable def trefoilLiftRReal (y : ℝ) : ℝ :=
  1 / 2 - 3 * y

/-- Substituting Witten's special lift parameters from Eq. (5.29) into the general
abelian/nonabelian Stokes curve Eq. (5.38) gives the reduced trefoil curve Eq. (5.39). -/
lemma trefoilAbelianNonabelianStokesCurve_lift_iff (a b y : ℝ) :
    TrefoilAbelianNonabelianStokesCurve a b (trefoilLiftRReal y) (trefoilLiftSReal y)
      ↔ TrefoilStokesCurve a b y := by
  unfold TrefoilAbelianNonabelianStokesCurve TrefoilStokesCurve
  unfold trefoilLiftRReal trefoilLiftSReal
  have hnum :
      3 * a ^ 2 + (2 * (1 / 2 - 3 * y) - 1) * a
          + (2 * (3 * y ^ 2 / 2 - 1 / 24) + 1 / 12)
        = 3 * (a - y) ^ 2 := by
    ring
  have hden : 3 * a + 2 * (1 / 2 - 3 * y) - 1 = 3 * (a - 2 * y) := by
    ring
  rw [hnum, hden]
  have hquot :
      -(a * (3 * (a - y) ^ 2)) / (3 * (a - 2 * y))
        = -(a * (a - y) ^ 2) / (a - 2 * y) := by
    by_cases h : a - 2 * y = 0
    · rw [h]
      simp
    · field_simp [h]
  rw [hquot]

/-- Witten keeps the part of the Stokes curve producing a jump, namely `y*b*(y-a) > 0`. -/
def TrefoilJumpingSide (a b y : ℝ) : Prop :=
  0 < y * b * (y - a)

/-- Unlike the full Stokes curve, the retained jump-producing side flips under simultaneous
sign reversal. This records the orientation information in Witten's selection
`y*b*(y-a) > 0`. -/
lemma trefoilJumpingSide_neg_iff {a b y : ℝ} :
    TrefoilJumpingSide (-a) (-b) (-y) ↔ y * b * (y - a) < 0 := by
  unfold TrefoilJumpingSide
  have hsym : (-y) * (-b) * ((-y) - (-a)) = -(y * b * (y - a)) := by
    ring
  rw [hsym]
  constructor <;> intro h <;> nlinarith

/-- On the left side of a positive Stokes value `y`, the retained jumping side is precisely the
upper half-plane. -/
lemma trefoilJumpingSide_iff_upper_left_of_pos {a b y : ℝ}
    (hy : 0 < y) (ha : a < y) :
    TrefoilJumpingSide a b y ↔ 0 < b := by
  unfold TrefoilJumpingSide
  constructor
  · intro h
    have hyay : 0 < y * (y - a) := mul_pos hy (sub_pos.mpr ha)
    have hquot : 0 < (y * b * (y - a)) / (y * (y - a)) := div_pos h hyay
    have heq : (y * b * (y - a)) / (y * (y - a)) = b := by
      field_simp [ne_of_gt hy, ne_of_gt (sub_pos.mpr ha)]
    rwa [heq] at hquot
  · intro hb
    exact mul_pos (mul_pos hy hb) (sub_pos.mpr ha)

/-- The relevant Stokes curve is invariant under simultaneous sign reversal of `a`, `b`, and `y`. This is
the algebraic symmetry behind the companion negative-axis cycle formula. -/
lemma trefoilStokesCurve_neg {a b y : ℝ} (h : TrefoilStokesCurve a b y) :
    TrefoilStokesCurve (-a) (-b) (-y) := by
  unfold TrefoilStokesCurve at h ⊢
  calc
    (-b) ^ 2 = b ^ 2 := by ring
    _ = -(a * (a - y) ^ 2) / (a - 2 * y) := h
    _ = -((-a) * ((-a) - (-y)) ^ 2) / ((-a) - 2 * (-y)) := by
      rw [show ((-a) - 2 * (-y)) = 2 * y - a by ring]
      rw [show -((-a) * ((-a) - (-y)) ^ 2) = a * (a - y) ^ 2 by ring]
      simp only [div_eq_mul_inv]
      have hinv : (2 * y - a)⁻¹ = -((a - 2 * y)⁻¹) := by
        rw [show 2 * y - a = -(a - 2 * y) by ring]
        rw [inv_neg]
      rw [hinv]
      ring


end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
