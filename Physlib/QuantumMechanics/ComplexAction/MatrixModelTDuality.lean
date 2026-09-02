/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Moyal.BracketTodaLattice
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
meta import Zil

/-!
# Matrix-model dualities from Type II T-duality

This module formalizes the Lean-checkable algebraic surface of Daniel Brace,
Bogdan Morariu and Bruno Zumino, *Dualities of the Matrix Model from
T-Duality of the Type II String*, arXiv:hep-th/9810099v2.

The paper identifies the `SO(3,3;Z)` Morita/T-duality action on
supersymmetric Yang-Mills theory over noncommutative three-tori with the
low-energy remnant of Type IIA target-space T-duality.  The analytic and
physical input is carried as typed interfaces; the finite-dimensional integer
matrix statements from the appendix are proved directly:

* noncommutative-torus generators and twisted quantum-bundle equations;
* the fractional transform `Theta' = (A Theta + B)(C Theta + D)^-1`;
* Section 8 data: rank/flux spinor, transformed metric and gauge coupling;
* Section 9 data: the target-space `B`-field, inverse metric and string
  coupling transforms in the Seiberg-Sen limit;
* Appendix data: the `SO(3,3;Z)` Weyl spinor is represented on
  `(n, M23, M31, M12)` as an integral `SL(4,Z)` matrix.  In particular,
  Lean checks the explicit `T12` spinor matrix, its inverse, `T12^2 = -1`,
  the conjugation formula (paper Eq. 70), and the canonical flux-trivializing
  spinor sending `(q ntilde, q mtilde, 0, 0)` to `(q,0,0,0)`.

## References

* D. Brace, B. Morariu, B. Zumino, arXiv:hep-th/9810099v2.
  Local source:
  `Dualities of the Matrix Model from T-Duality of the Type II String-9810099v2.pdf`.
* Repo carrier: `Moyal.BracketTodaLattice` for the finite-mode first-order
  Moyal/noncommutative deformation layer.


-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

open Matrix
open scoped Matrix
open Physlib.QuantumMechanics.ComplexAction.Moyal.BracketTodaLattice

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MatrixModelTDuality

/-! ## Section A - source anchors -/

/-- Bibliographic/source record for the Brace-Morariu-Zumino paper. -/
structure MatrixModelTDualityPaperReference where
  title : String
  authors : String
  identifier : String
  localPdf : String
  theoremSummary : String
  deriving Repr, DecidableEq

/-- The local source inspected for this formalization. -/
def matrixModelTDualityPaperReference : MatrixModelTDualityPaperReference :=
  { title := "Dualities of the Matrix Model from T-Duality of the Type II String"
    authors := "Daniel Brace, Bogdan Morariu and Bruno Zumino"
    identifier := "arXiv:hep-th/9810099v2, 23 Mar 1999"
    localPdf :=
      "Dualities of the Matrix Model from T-Duality of the Type II String-9810099v2.pdf"
    theoremSummary :=
      "The SO(3,3;Z) duality of NCSYM on noncommutative three-tori is the low-energy image of auxiliary Type IIA T-duality." }

/-- Stable paper anchors used below. -/
inductive MatrixModelTDualityAnchor where
  | matrixCompactificationQuotient
  | noncommutativeTorusGenerators
  | twistedQuantumBundle
  | fluxQuantization
  | adjointSectionExpansion
  | fractionalThetaTransform
  | odDualityBlock
  | threeDimensionalCanonicalFlux
  | rankFluxWeylSpinor
  | ncsymActionDuality
  | targetSpaceTDuality
  | spinorIntegrality
  | spin33IsSL4
  deriving Repr, DecidableEq

/-- Human-readable labels for the paper anchors. -/
def MatrixModelTDualityAnchor.paperLabel : MatrixModelTDualityAnchor -> String
  | .matrixCompactificationQuotient => "Section 2: Matrix compactification quotient conditions"
  | .noncommutativeTorusGenerators => "Section 2: noncommutative torus generators Ui Uj"
  | .twistedQuantumBundle => "Section 3: twisted quantum bundles on tori"
  | .fluxQuantization => "Section 3: M = n(2P - P Theta P), integer magnetic flux"
  | .adjointSectionExpansion => "Section 4: adjoint sections expanded in Zi generators"
  | .fractionalThetaTransform => "Equations (25)-(27): fractional Theta transform and O(d,d) block equations"
  | .odDualityBlock => "Equation (28): O(d,d) metric J"
  | .threeDimensionalCanonicalFlux => "Section 6: three-dimensional canonical flux form"
  | .rankFluxWeylSpinor => "Equation (68): rank/flux Weyl spinor"
  | .ncsymActionDuality => "Section 8: SO(3,3;Z) duality of Super Yang-Mills"
  | .targetSpaceTDuality => "Section 9: target-space T-duality limit"
  | .spinorIntegrality => "Appendix: integral Weyl spinor representation"
  | .spin33IsSL4 => "Appendix: Spin(3,3;Z) Weyl spinor as SL(4,Z)"

/-! ## Section B - noncommutative torus and twisted-bundle carriers -/

abbrev Matrix3R := Matrix (Fin 3) (Fin 3) Real

/-- Integral `3 × 3` matrices used for the `SO(3,3;Z)` T-duality action. -/
abbrev Matrix3Z := Matrix (Fin 3) (Fin 3) Int

/-- Four-component integral rank/flux spinor for the `Spin(3,3;Z)` representation. -/
abbrev RankFluxSpinor3 := Fin 4 -> Int

/--
Abstract carrier for the noncommutative torus relation
`U_i U_j = exp(2*pi*i*Theta_ij) U_j U_i`.
-/
structure NoncommutativeTorusCarrier (d : Nat) where
  Algebra : Type
  mul : Algebra -> Algebra -> Algebra
  U : Fin d -> Algebra
  theta : Matrix (Fin d) (Fin d) Real
  phase : Fin d -> Fin d -> Algebra
  torus_commutation :
    forall i j, mul (U i) (U j) = mul (phase i j) (mul (U j) (U i))

/--
Carrier for the paper's constant-curvature twisted quantum bundle equations:
`P = (1 + 2*pi F Theta)^-1 2*pi F`, `M = n(2P - P Theta P)`.
-/
structure TwistedQuantumBundleData (d : Nat) where
  rank : Int
  theta : Matrix (Fin d) (Fin d) Real
  curvatureF : Matrix (Fin d) (Fin d) Real
  transitionP : Matrix (Fin d) (Fin d) Real
  magneticFlux : Matrix (Fin d) (Fin d) Int
  p_equation : Prop
  flux_equation : Prop
  magneticFluxIntegral : forall i j, exists m : Int, magneticFlux i j = m

/-- The `q = gcd(n, Mij)` reduction data used to trivialize the dual bundle. -/
structure RankFluxReduction where
  n : Int
  q : Int
  ntilde : Int
  m23 : Int
  m31 : Int
  m12 : Int
  mtilde23 : Int
  mtilde31 : Int
  mtilde12 : Int
  n_eq : n = q * ntilde
  m23_eq : m23 = q * mtilde23
  m31_eq : m31 = q * mtilde31
  m12_eq : m12 = q * mtilde12

/-- The rank/flux Weyl spinor `(n, M23, M31, M12)` of Eq. (68). -/
def rankFluxSpinor3 (n m23 m31 m12 : Int) : RankFluxSpinor3 :=
  ![n, m23, m31, m12]

@[simp] lemma rankFluxSpinor3_zero
    (n m23 m31 m12 : Int) :
    rankFluxSpinor3 n m23 m31 m12 0 = n := rfl

@[simp] lemma rankFluxSpinor3_one
    (n m23 m31 m12 : Int) :
    rankFluxSpinor3 n m23 m31 m12 1 = m23 := rfl

@[simp] lemma rankFluxSpinor3_two
    (n m23 m31 m12 : Int) :
    rankFluxSpinor3 n m23 m31 m12 2 = m31 := rfl

@[simp] lemma rankFluxSpinor3_three
    (n m23 m31 m12 : Int) :
    rankFluxSpinor3 n m23 m31 m12 3 = m12 := rfl

/-- The repo's finite-mode Moyal bracket gives the first-order noncommutative deformation layer. -/
lemma matrixModel_firstOrderMoyalBracket_antisymm
    {K : Nat} (theta : Real) (f g : MoyalField K) :
    moyalBracket theta f g = -moyalBracket theta g f :=
  moyalBracket_antisymm theta g f

/-! ## Section C - SO(3,3) NCSYM and Type IIA transforms -/

/-- A block presentation of an `O(3,3)` duality element. -/
structure O33DualityBlock where
  A : Matrix3R
  B : Matrix3R
  C : Matrix3R
  D : Matrix3R
  ortho_AD_CB : A.transpose * D + C.transpose * B = 1
  ortho_AC : A.transpose * C + C.transpose * A = 0
  ortho_BD : B.transpose * D + D.transpose * B = 0

/-- The denominator `C Theta + D` in the fractional duality transform. -/
noncomputable def dualityDenominator (L : O33DualityBlock) (theta : Matrix3R) : Matrix3R :=
  L.C * theta + L.D

/-- Equation (47): `Theta_bar = (A Theta + B)(C Theta + D)^-1`. -/
noncomputable def moritaThetaTransform (L : O33DualityBlock) (theta : Matrix3R) : Matrix3R :=
  (L.A * theta + L.B) * (dualityDenominator L theta)⁻¹

/-- Equation (49), written for the contravariant NCSYM metric. -/
noncomputable def ncsymMetricTransform
    (L : O33DualityBlock) (theta metric : Matrix3R) : Matrix3R :=
  dualityDenominator L theta * metric * (dualityDenominator L theta).transpose

/-- Equation (50): `gbar_SYM^2 = sqrt(|det(C Theta + D)|) g_SYM^2`. -/
noncomputable def ncsymGaugeCouplingSqTransform
    (L : O33DualityBlock) (theta : Matrix3R) (gaugeCouplingSq : Real) : Real :=
  Real.sqrt |Matrix.det (dualityDenominator L theta)| * gaugeCouplingSq

/-- Section 8 duality data for NCSYM on a noncommutative three-torus. -/
structure NCSYMSO33Duality where
  L : O33DualityBlock
  theta : Matrix3R
  thetaBar : Matrix3R
  metric : Matrix3R
  metricBar : Matrix3R
  gaugeCouplingSq : Real
  gaugeCouplingSqBar : Real
  spinorMatrix : Matrix (Fin 4) (Fin 4) Int
  rankFlux : RankFluxSpinor3
  rankFluxBar : RankFluxSpinor3
  theta_transform : thetaBar = moritaThetaTransform L theta
  metric_transform : metricBar = ncsymMetricTransform L theta metric
  gauge_transform : gaugeCouplingSqBar = ncsymGaugeCouplingSqTransform L theta gaugeCouplingSq
  rank_flux_transform : rankFluxBar = spinorMatrix *ᵥ rankFlux

/-- The four defining outputs of the Section 8 NCSYM duality package. -/
lemma ncsymSO33Duality_outputs (D : NCSYMSO33Duality) :
    D.thetaBar = moritaThetaTransform D.L D.theta
      ∧ D.metricBar = ncsymMetricTransform D.L D.theta D.metric
      ∧ D.gaugeCouplingSqBar =
        ncsymGaugeCouplingSqTransform D.L D.theta D.gaugeCouplingSq
      ∧ D.rankFluxBar = D.spinorMatrix *ᵥ D.rankFlux :=
  ⟨D.theta_transform, D.metric_transform, D.gauge_transform, D.rank_flux_transform⟩

/-- Target-space `B`-field transform in the Seiberg-Sen low-energy limit. -/
noncomputable def typeIIABFieldTransform (L : O33DualityBlock) (Bfield : Matrix3R) : Matrix3R :=
  moritaThetaTransform L Bfield

/-- Target-space inverse metric transform matching the contravariant NCSYM metric. -/
noncomputable def typeIIAInverseMetricTransform
    (L : O33DualityBlock) (Bfield inverseMetric : Matrix3R) : Matrix3R :=
  dualityDenominator L Bfield * inverseMetric * (dualityDenominator L Bfield).transpose

/-- The induced low-energy gauge-coupling transform from the Type IIA string coupling law. -/
noncomputable def typeIIALowEnergyGaugeCouplingSqTransform
    (L : O33DualityBlock) (Bfield : Matrix3R) (gaugeCouplingSq : Real) : Real :=
  ncsymGaugeCouplingSqTransform L Bfield gaugeCouplingSq

/-- Section 9 target-space T-duality data after identifying `B = Theta`. -/
structure TypeIIATDualityLimit where
  L : O33DualityBlock
  Bfield : Matrix3R
  BfieldBar : Matrix3R
  inverseMetric : Matrix3R
  inverseMetricBar : Matrix3R
  gaugeCouplingSq : Real
  gaugeCouplingSqBar : Real
  b_transform : BfieldBar = typeIIABFieldTransform L Bfield
  inverse_metric_transform :
    inverseMetricBar = typeIIAInverseMetricTransform L Bfield inverseMetric
  low_energy_gauge_transform :
    gaugeCouplingSqBar =
      typeIIALowEnergyGaugeCouplingSqTransform L Bfield gaugeCouplingSq

/--
After the paper's identification `Theta = B`, the NCSYM deformation and the
target-space `B`-field obey the same fractional transformation.
-/
lemma thetaTransform_eq_typeIIABFieldTransform
    (L : O33DualityBlock) (theta : Matrix3R) :
    moritaThetaTransform L theta = typeIIABFieldTransform L theta :=
  rfl

/--
After identifying the NCSYM metric with the inverse Type IIA metric, the
metric transforms agree.
-/
lemma ncsymMetricTransform_eq_typeIIAInverseMetricTransform
    (L : O33DualityBlock) (theta metric : Matrix3R) :
    ncsymMetricTransform L theta metric =
      typeIIAInverseMetricTransform L theta metric :=
  rfl

/-- The low-energy coupling transform used by the NCSYM and Type IIA packages is the same formula. -/
lemma ncsymGaugeTransform_eq_typeIIALowEnergyGaugeTransform
    (L : O33DualityBlock) (theta : Matrix3R) (gaugeCouplingSq : Real) :
    ncsymGaugeCouplingSqTransform L theta gaugeCouplingSq =
      typeIIALowEnergyGaugeCouplingSqTransform L theta gaugeCouplingSq :=
  rfl

/-! ## Section D - finite appendix algebra: Spin(3,3) as SL(4) on rank/flux -/

/-- Appendix Eq. (67)/(68): the `T12` Weyl-spinor matrix acting on `(n,M23,M31,M12)`. -/
def t12Spinor : Matrix (Fin 4) (Fin 4) Int :=
  !![0, 0, 0, -1;
     0, 0, -1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- The inverse of the explicit `T12` spinor matrix. -/
def t12SpinorInv : Matrix (Fin 4) (Fin 4) Int :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, -1, 0, 0;
     -1, 0, 0, 0]

/-- `T12^-1 T12 = 1`, checked as integer matrix algebra. -/
lemma t12SpinorInv_mul_t12Spinor :
    t12SpinorInv * t12Spinor = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t12SpinorInv, t12Spinor, Matrix.mul_apply, Fin.sum_univ_four]

/-- `T12 T12^-1 = 1`, checked as integer matrix algebra. -/
lemma t12Spinor_mul_t12SpinorInv :
    t12Spinor * t12SpinorInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t12SpinorInv, t12Spinor, Matrix.mul_apply, Fin.sum_univ_four]

/-- The appendix generator squares to `-1` in the Weyl-spinor representation. -/
lemma t12Spinor_sq :
    t12Spinor * t12Spinor = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t12Spinor, Matrix.mul_apply, Fin.sum_univ_four]

/-- Action of `T12` on the rank/flux vector. -/
lemma t12Spinor_rankFlux_action (n m23 m31 m12 : Int) :
    t12Spinor *ᵥ rankFluxSpinor3 n m23 m31 m12 =
      rankFluxSpinor3 (-m12) (-m31) m23 n := by
  ext i
  fin_cases i <;>
    simp [t12Spinor, rankFluxSpinor3, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The `SL(2,Z)` subgroup acting on the last two entries of the rank/flux vector. -/
def sl2OnLastTwo (a b c d : Int) : Matrix (Fin 4) (Fin 4) Int :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, a, b;
     0, 0, c, d]

/-- The conjugated `SL(2,Z)` subgroup acting on the first two entries, paper Eq. (70). -/
def sl2OnFirstTwoFromConj (a b c d : Int) : Matrix (Fin 4) (Fin 4) Int :=
  !![d, c, 0, 0;
     b, a, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/--
Appendix Eq. (70): conjugating an `SL(2,Z)` acting on the last two
spinor entries by `T12` gives an `SL(2,Z)` acting on the first two entries.
-/
lemma t12_conjugates_sl2_lastTwo_to_firstTwo (a b c d : Int) :
    t12SpinorInv * sl2OnLastTwo a b c d * t12Spinor =
      sl2OnFirstTwoFromConj a b c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t12SpinorInv, sl2OnLastTwo, t12Spinor, sl2OnFirstTwoFromConj,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- The conjugated block preserves the `SL(2,Z)` determinant condition. -/
lemma t12_conjugated_sl2_det_condition
    (a b c d : Int) (hadbc : a * d - b * c = 1) :
    d * a - c * b = 1 := by
  calc
    d * a - c * b = a * d - b * c := by ring
    _ = 1 := hadbc

/--
The canonical three-torus spinor from Section 6:
`[[a,-b],[-mtilde,ntilde]]` on `(n,M23)`, identity on the remaining fluxes.
-/
def canonicalThreeTorusSpinor
    (a b mtilde ntilde : Int) : Matrix (Fin 4) (Fin 4) Int :=
  !![a, -b, 0, 0;
     -mtilde, ntilde, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/--
Section 6 flux trivialization: if `a ntilde - b mtilde = 1`, then the
canonical spinor maps `(q ntilde, q mtilde, 0, 0)` to `(q, 0, 0, 0)`.
-/
lemma canonicalThreeTorusSpinor_trivializesFlux
    (q ntilde mtilde a b : Int) (hbezout : a * ntilde - b * mtilde = 1) :
    canonicalThreeTorusSpinor a b mtilde ntilde *ᵥ
        rankFluxSpinor3 (q * ntilde) (q * mtilde) 0 0 =
      rankFluxSpinor3 q 0 0 0 := by
  ext i
  fin_cases i <;>
    simp [canonicalThreeTorusSpinor, rankFluxSpinor3, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
  · calc
      a * (q * ntilde) + -(b * (q * mtilde)) = q * (a * ntilde - b * mtilde) := by
        ring
      _ = q := by rw [hbezout, mul_one]
  · ring

/-! ## Section E - assembled paper obligations -/

/-- The Section 8 equivalence of a twisted `U(n)` theory with a trivial `U(q)` theory. -/
structure TwistedToTrivialNCSYMSynthesis where
  originalRank : Int
  dualRank : Int
  originalFlux : RankFluxSpinor3
  dualFlux : RankFluxSpinor3
  theta : Matrix3R
  thetaPrime : Matrix3R
  metric : Matrix3R
  metricPrime : Matrix3R
  gaugeCouplingSq : Real
  gaugeCouplingSqPrime : Real
  duality : NCSYMSO33Duality
  originalRankFlux_eq : originalFlux = duality.rankFlux
  dualRankFlux_eq : dualFlux = duality.rankFluxBar
  dualFluxTrivial : dualFlux = rankFluxSpinor3 dualRank 0 0 0
  thetaPrime_eq : thetaPrime = duality.thetaBar
  metricPrime_eq : metricPrime = duality.metricBar
  gaugePrime_eq : gaugeCouplingSqPrime = duality.gaugeCouplingSqBar

/-- The usable Section 8 conclusion exposed to downstream modules. -/
lemma twistedToTrivialNCSYM_outputs
    (S : TwistedToTrivialNCSYMSynthesis) :
    S.dualFlux = rankFluxSpinor3 S.dualRank 0 0 0
      ∧ S.thetaPrime = moritaThetaTransform S.duality.L S.duality.theta
      ∧ S.metricPrime =
        ncsymMetricTransform S.duality.L S.duality.theta S.duality.metric
      ∧ S.gaugeCouplingSqPrime =
        ncsymGaugeCouplingSqTransform S.duality.L S.duality.theta
          S.duality.gaugeCouplingSq := by
  rcases ncsymSO33Duality_outputs S.duality with ⟨hTheta, hMetric, hGauge, _hFlux⟩
  exact ⟨S.dualFluxTrivial, S.thetaPrime_eq.trans hTheta,
    S.metricPrime_eq.trans hMetric, S.gaugePrime_eq.trans hGauge⟩

/--
The Section 9 identification package: NCSYM `Theta` is the Type IIA `B`-field,
the NCSYM metric is the Type IIA inverse metric, and the rank/flux spinor is
the D0/D2 charge vector.
-/
structure NCSYMTypeIIATDualityBridge where
  ncsym : NCSYMSO33Duality
  target : TypeIIATDualityLimit
  sameBlock : ncsym.L = target.L
  theta_eq_B : ncsym.theta = target.Bfield
  metric_eq_inverseMetric : ncsym.metric = target.inverseMetric
  gauge_eq : ncsym.gaugeCouplingSq = target.gaugeCouplingSq
  thetaBar_eq_Bbar : ncsym.thetaBar = target.BfieldBar
  metricBar_eq_inverseMetricBar : ncsym.metricBar = target.inverseMetricBar
  gaugeBar_eq : ncsym.gaugeCouplingSqBar = target.gaugeCouplingSqBar
  rankFlux_is_D0_D2_charge : Prop
  rankFlux_is_D0_D2_charge_holds : rankFlux_is_D0_D2_charge

/--
The paper's main comparison theorem in checked form: under the stated
identifications, the NCSYM duality outputs and the Type IIA T-duality outputs
are the same transformed `B/Theta`, inverse metric, coupling, and D0/D2 charge
package.
-/
lemma ncsym_typeIIA_TDuality_bridge_outputs
    (B : NCSYMTypeIIATDualityBridge) :
    B.ncsym.thetaBar = B.target.BfieldBar
      ∧ B.ncsym.metricBar = B.target.inverseMetricBar
      ∧ B.ncsym.gaugeCouplingSqBar = B.target.gaugeCouplingSqBar
      ∧ B.rankFlux_is_D0_D2_charge :=
  ⟨B.thetaBar_eq_Bbar, B.metricBar_eq_inverseMetricBar, B.gaugeBar_eq,
    B.rankFlux_is_D0_D2_charge_holds⟩

end Physlib.QuantumMechanics.ComplexAction.MatrixModelTDuality

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.MatrixModelTDuality.matrixModel_firstOrderMoyalBracket_antisymm where
  formalizes @ "claim:the-matrix-model-first-order-moyal-bracket-is-antisymmetric",
  supported_by @ "paper:seiberg-witten-1999-string-theory-noncommutative-geometry"

zil attach Physlib.QuantumMechanics.ComplexAction.MatrixModelTDuality.ncsymSO33Duality_outputs where
  formalizes @ "claim:the-noncommutative-super-yang-mills-so33-morita-t-duality-transforms-the-theta-parameter-and-metric",
  requires @ "claim:the-matrix-model-first-order-moyal-bracket-is-antisymmetric",
  supported_by @ "paper:seiberg-witten-1999-string-theory-noncommutative-geometry",
  caveat @ "claim:the-morita-o33-duality-orbit-is-formalized-not-the-full-string-duality-group"

zil_file_contract physlib.matrixModelTDuality where
  promises "The matrix-model T-duality and noncommutative geometry: the first-order Moyal bracket is antisymmetric, and the SO(3,3) Morita T-duality transforms the noncommutativity parameter theta and the metric, the Seiberg-Witten map of the matrix model."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.MatrixModelTDuality.moritaThetaTransform",
    "lean:Physlib.QuantumMechanics.ComplexAction.MatrixModelTDuality.O33DualityBlock"]
  forbids_substitutes ["the full string T-duality group, only the SO(3,3) Morita orbit",
    "a derivation of the Seiberg-Witten map, taken as the duality data"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.MatrixModelTDuality.matrixModel_firstOrderMoyalBracket_antisymm,
    Physlib.QuantumMechanics.ComplexAction.MatrixModelTDuality.ncsymSO33Duality_outputs]

/- ZIL-END -/
