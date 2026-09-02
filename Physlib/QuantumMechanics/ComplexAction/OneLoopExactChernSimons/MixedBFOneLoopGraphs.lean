/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ConcreteSynthesis
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ThetaModular
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonOperators
public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour
public import Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
public import Physlib.QFT.PathIntegral.EuclideanPropagator
public import Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.DeRhamChiralFunctionals
meta import Zil

/-! # OneLoopExactChernSimons — part `MixedBFOneLoopGraphs`. Full paper docstring in the umbrella module `Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons`; namespace and
declaration names are unchanged across the parts (the umbrella re-exports them). -/

set_option autoImplicit false
@[expose] public section
namespace Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons
open MeasureTheory
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourShift
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourGaussian
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComptonVacuumBell
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDMatsubaraContour


/--
Component-level carrier for the action in Definition 1.1.

`kinetic alpha beta` represents `∫ <beta, (dbar + d_t) alpha>`.
`interaction alpha beta` represents `∫ <beta, [alpha, alpha]>`.
`csDeformation alpha` represents `1/2 ∫ <alpha, partial alpha>`.
-/
structure MixedBFActionData where
  FieldA : Type
  FieldB : Type
  kinetic : FieldA → FieldB → ℂ
  interaction : FieldA → FieldB → ℂ
  csDeformation : FieldA → ℂ

/-- The mixed BF classical action `S_mix(alpha,beta)`. -/
noncomputable def mixedBFAction (D : MixedBFActionData) (alpha : D.FieldA)
    (beta : D.FieldB) : ℂ :=
  D.kinetic alpha beta + (1 / 2 : ℂ) * D.interaction alpha beta

/-- The Chern-Simons deformation `I_CS(alpha)`. -/
noncomputable def chernSimonsChiralDeformation (D : MixedBFActionData)
    (alpha : D.FieldA) : ℂ :=
  D.csDeformation alpha

/-- The deformed action `S_mix + I_CS`, i.e. the Chern-Simons action in the paper's variables. -/
noncomputable def mixedPlusChernSimonsAction (D : MixedBFActionData) (alpha : D.FieldA)
    (beta : D.FieldB) : ℂ :=
  mixedBFAction D alpha beta + chernSimonsChiralDeformation D alpha

/-- The deformed action is exactly mixed BF plus the chiral Chern-Simons deformation. -/
lemma mixedPlusChernSimonsAction_eq (D : MixedBFActionData) (alpha : D.FieldA)
    (beta : D.FieldB) :
    mixedPlusChernSimonsAction D alpha beta =
      mixedBFAction D alpha beta + chernSimonsChiralDeformation D alpha :=
  rfl

/--
Scalar-projected carrier for the paper's equations of motion.

The vector-valued equations in the paper can be tested against a basis vector or
linear functional; this carrier stores the resulting scalar component.  The
mixed alpha-equation is `(dbar+d_t)alpha + 1/2[alpha,alpha] = 0`; after the
chiral CS deformation it becomes the flatness equation with the added
`partial alpha` term.
-/
structure MixedBFChernSimonsEquationData where
  FieldA : Type
  FieldB : Type
  dbarDtAlpha : FieldA → ℂ
  bracketAlphaAlpha : FieldA → ℂ
  partialAlpha : FieldA → ℂ
  dbarDtBeta : FieldB → ℂ
  bracketAlphaBeta : FieldA → FieldB → ℂ

/-- Scalar component of the mixed BF alpha equation. -/
noncomputable def mixedBFAlphaEquation (E : MixedBFChernSimonsEquationData)
    (alpha : E.FieldA) : ℂ :=
  E.dbarDtAlpha alpha + (1 / 2 : ℂ) * E.bracketAlphaAlpha alpha

/-- Scalar component of the mixed BF beta equation. -/
noncomputable def mixedBFBetaEquation (E : MixedBFChernSimonsEquationData)
    (alpha : E.FieldA) (beta : E.FieldB) : ℂ :=
  E.dbarDtBeta beta + E.bracketAlphaBeta alpha beta

/-- Scalar component of the deformed Chern-Simons flatness equation. -/
noncomputable def chernSimonsAlphaEquation (E : MixedBFChernSimonsEquationData)
    (alpha : E.FieldA) : ℂ :=
  mixedBFAlphaEquation E alpha + E.partialAlpha alpha

/-- The paper's `partial alpha` term is exactly the extra term in the deformed alpha equation. -/
lemma chernSimonsAlphaEquation_eq_mixed_plus_partial
    (E : MixedBFChernSimonsEquationData) (alpha : E.FieldA) :
    chernSimonsAlphaEquation E alpha =
      mixedBFAlphaEquation E alpha + E.partialAlpha alpha :=
  rfl

/-- If the mixed BF alpha equation and the `partial alpha` component vanish, the CS flatness component vanishes. -/
lemma chernSimonsAlphaEquation_eq_zero_of_mixed_and_partial_zero
    (E : MixedBFChernSimonsEquationData) (alpha : E.FieldA)
    (hmix : mixedBFAlphaEquation E alpha = 0) (hpartial : E.partialAlpha alpha = 0) :
    chernSimonsAlphaEquation E alpha = 0 := by
  rw [chernSimonsAlphaEquation, hmix, hpartial, zero_add]


/-- A one-loop effective action: tree contribution, one-loop correction, and no higher-loop residue. -/
structure OneLoopEffectiveAction where
  treeAction : ℂ
  oneLoopCorrection : ℂ
  higherLoopResidue : ℂ
  effectiveAction : ℂ
  higherLoopResidue_eq_zero : higherLoopResidue = 0
  effective_eq : effectiveAction = treeAction + oneLoopCorrection + higherLoopResidue

/-- One-loop exactness collapses the effective action to tree plus one-loop correction. -/
lemma OneLoopEffectiveAction.effective_eq_tree_plus_one_loop
    (A : OneLoopEffectiveAction) :
    A.effectiveAction = A.treeAction + A.oneLoopCorrection := by
  rw [A.effective_eq, A.higherLoopResidue_eq_zero, add_zero]

/--
The paper's central algebraic bridge: the one-loop correction to mixed BF is
the Chern-Simons deformation, so the one-loop effective action is the
Chern-Simons action.
-/
structure MixedBFToChernSimonsOneLoopBridge where
  mixedAction : ℂ
  csDeformation : ℂ
  oneLoopCorrection : ℂ
  totalChernSimonsAction : ℂ
  total_eq_mixed_plus_cs : totalChernSimonsAction = mixedAction + csDeformation
  oneLoopCorrection_eq_cs : oneLoopCorrection = csDeformation

/-- The one-loop correction turns mixed BF into Chern-Simons. -/
lemma oneLoopCorrection_turns_mixedBF_into_ChernSimons
    (B : MixedBFToChernSimonsOneLoopBridge) :
    B.mixedAction + B.oneLoopCorrection = B.totalChernSimonsAction := by
  rw [B.oneLoopCorrection_eq_cs, B.total_eq_mixed_plus_cs]

/-- The mixed BF to CS bridge supplies a one-loop exact effective action. -/
noncomputable def MixedBFToChernSimonsOneLoopBridge.toEffectiveAction
    (B : MixedBFToChernSimonsOneLoopBridge) : OneLoopEffectiveAction where
  treeAction := B.mixedAction
  oneLoopCorrection := B.oneLoopCorrection
  higherLoopResidue := 0
  effectiveAction := B.totalChernSimonsAction
  higherLoopResidue_eq_zero := rfl
  effective_eq := by
    rw [B.total_eq_mixed_plus_cs, B.oneLoopCorrection_eq_cs]
    simp

/-- For the mixed BF to CS bridge, the effective action is tree plus the one-loop CS correction. -/
lemma mixedBFToChernSimons_effective_eq
    (B : MixedBFToChernSimonsOneLoopBridge) :
    B.toEffectiveAction.effectiveAction =
      B.toEffectiveAction.treeAction + B.toEffectiveAction.oneLoopCorrection :=
  B.toEffectiveAction.effective_eq_tree_plus_one_loop


/-- The graph shapes that survive the chiral-deformation power counting in the paper. -/
inductive OneLoopExactGraphShape where
  | tree
  | oneLoopWithExternalBeta
  | oneLoopVacuum
  deriving DecidableEq, Repr

/-- Loop number attached to each allowed graph shape. -/
def OneLoopExactGraphShape.loopNumber : OneLoopExactGraphShape → ℕ
  | .tree => 0
  | .oneLoopWithExternalBeta => 1
  | .oneLoopVacuum => 1

@[simp] lemma OneLoopExactGraphShape.loopNumber_tree :
    OneLoopExactGraphShape.loopNumber .tree = 0 :=
  rfl

@[simp] lemma OneLoopExactGraphShape.loopNumber_oneLoopWithExternalBeta :
    OneLoopExactGraphShape.loopNumber .oneLoopWithExternalBeta = 1 :=
  rfl

@[simp] lemma OneLoopExactGraphShape.loopNumber_oneLoopVacuum :
    OneLoopExactGraphShape.loopNumber .oneLoopVacuum = 1 :=
  rfl

/-- Every graph shape admitted by the chiral expansion has loop number at most one. -/
lemma OneLoopExactGraphShape.loopNumber_le_one
    (Gamma : OneLoopExactGraphShape) :
    Gamma.loopNumber ≤ 1 := by
  cases Gamma <;> simp [OneLoopExactGraphShape.loopNumber]

/-- Equivalently, the allowed graph shapes contain no two-loop-or-higher diagram. -/
lemma OneLoopExactGraphShape.no_two_loop_or_higher
    (Gamma : OneLoopExactGraphShape) :
    ¬ 2 ≤ Gamma.loopNumber := by
  exact not_le.mpr (Nat.lt_succ_iff.mpr Gamma.loopNumber_le_one)

/-- The Section 1.2 connected chiral graph shapes are a subfamily of the later one-loop-exact graph
shapes used in the global one-loop exactness statement. -/
def ConnectedChiralGraphShape.toOneLoopExactGraphShape :
    ConnectedChiralGraphShape → OneLoopExactGraphShape
  | .betaRootedTree => .tree
  | .singleWeightZeroVertex => .tree
  | .oneLoopNoBeta => .oneLoopVacuum

/-- The conversion from chiral graph counting to the one-loop-exact graph package preserves loop number. -/
@[simp] lemma ConnectedChiralGraphShape.loopNumber_toOneLoopExactGraphShape
    (Gamma : ConnectedChiralGraphShape) :
    Gamma.toOneLoopExactGraphShape.loopNumber = Gamma.loopNumber := by
  cases Gamma <;> rfl

/-- The chiral graph-counting lemma therefore proves the one-loop package's no-two-loop condition. -/
lemma ConnectedChiralGraphShape.toOneLoopExactGraphShape_no_two_loop_or_higher
    (Gamma : ConnectedChiralGraphShape) :
    ¬ 2 ≤ Gamma.toOneLoopExactGraphShape.loopNumber := by
  exact OneLoopExactGraphShape.no_two_loop_or_higher Gamma.toOneLoopExactGraphShape


end Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.OneLoopEffectiveAction.effective_eq_tree_plus_one_loop where
  formalizes @ "claim:one-loop-exactness-collapses-the-effective-action-to-the-tree-contribution-plus-the-one-loop-correction-since-the-higher-loop-residue-vanishes",
  supported_by @ "paper:one-loop-exactness-of-mixed-bf-chern-simons-theory"

zil attach Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.oneLoopCorrection_turns_mixedBF_into_ChernSimons where
  formalizes @ "claim:the-one-loop-correction-to-the-mixed-bf-action-is-the-chern-simons-deformation-so-the-mixed-bf-action-plus-its-one-loop-correction-equals-the-total-chern-simons-action"

zil attach Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.mixedBFToChernSimons_effective_eq where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.OneLoopEffectiveAction.effective_eq_tree_plus_one_loop",
  formalizes @ "claim:for-the-mixed-bf-to-chern-simons-one-loop-bridge-the-one-loop-exact-effective-action-is-the-tree-mixed-bf-action-plus-the-one-loop-chern-simons-correction",
  requires @ "claim:one-loop-exactness-collapses-the-effective-action-to-the-tree-contribution-plus-the-one-loop-correction-since-the-higher-loop-residue-vanishes"

zil attach Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.chernSimonsAlphaEquation_eq_zero_of_mixed_and_partial_zero where
  formalizes @ "claim:if-the-mixed-bf-alpha-equation-and-the-partial-alpha-component-both-vanish-the-deformed-chern-simons-flatness-equation-vanishes"

zil_file_contract physlib.mixedBFOneLoopGraphs where
  promises "The one-loop graph structure by which mixed BF theory flows to Chern-Simons under the chiral deformation. One-loop exactness collapses the effective action to the tree contribution plus the one-loop correction, because the higher-loop residue vanishes (effective_eq_tree_plus_one_loop). The paper's central algebraic bridge: the one-loop correction to the mixed BF action is exactly the Chern-Simons deformation, so the mixed BF action plus its one-loop correction is the total Chern-Simons action (oneLoopCorrection_turns_mixedBF_into_ChernSimons), giving a one-loop-exact effective action equal to tree plus the CS correction (mixedBFToChernSimons_effective_eq). The deformed Chern-Simons flatness equation is the mixed BF alpha equation plus a partial-alpha term, vanishing when both vanish (chernSimonsAlphaEquation_eq_zero_of_mixed_and_partial_zero)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.OneLoopEffectiveAction",
    "lean:Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.MixedBFToChernSimonsOneLoopBridge"]
  forbids_substitutes ["the power-counting proof that no two-loop or higher graphs survive the chiral deformation, which is the cited perturbative-QFT infrastructure carried as the graph-shape hypotheses",
    "any claim about the exact partition function or observables of the Chern-Simons theory, only the one-loop-exactness action algebra is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.OneLoopEffectiveAction.effective_eq_tree_plus_one_loop,
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.oneLoopCorrection_turns_mixedBF_into_ChernSimons,
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.mixedBFToChernSimons_effective_eq,
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.chernSimonsAlphaEquation_eq_zero_of_mixed_and_partial_zero]

/- ZIL-END -/
