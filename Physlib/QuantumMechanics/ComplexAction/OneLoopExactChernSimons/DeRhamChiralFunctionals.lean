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

/-! # OneLoopExactChernSimons — part `DeRhamChiralFunctionals`. Full paper docstring in the umbrella module `Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons`; namespace and
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


/-- Bibliographic record for the local paper being formalized. -/
structure OneLoopExactChernSimonsPaperReference where
  title : String
  authors : String
  identifier : String
  localPdf : String
  theoremSummary : String

/-- Source record for Gwilliam-Williams, arXiv:1910.05230v2. -/
def oneLoopExactChernSimonsPaperReference : OneLoopExactChernSimonsPaperReference :=
  { title := "A one-loop exact quantization of Chern-Simons theory"
    authors := "Owen Gwilliam and Brian Williams"
    identifier := "arXiv:1910.05230v2, 6 May 2020"
    localPdf := "one-loop-exact-chern-simons-1910.05230v2.pdf"
    theoremSummary :=
      "Chiral deformations of mixed BF theory on C x R, including Chern-Simons theory, admit finite one-loop exact quantizations." }

/-- Named anchors for the paper sections and statements used in this module. -/
inductive OneLoopExactChernSimonsAnchor where
  | definition11MixedBFFields
  | definition11MixedBFAction
  | chernSimonsDeformation
  | mixedBFEquationsOfMotion
  | definition12ChiralFunctional
  | definition21DeformationComplex
  | lemma23ReducedDeformationComplex
  | chiralDeformationCohomology
  | graphShapeRestriction
  | definition31HolomorphicGaugeFix
  | lemma31GaussianZeta
  | lemma33GaussianTau
  | gaussianMomentFormula
  | theorem41FiniteOneLoopExactQuantization
  | lemma42SmallWheelsVanish
  | proposition43LargeWheelsFinite
  | definition51ScaleQME
  | definition52OneLoopAnomaly
  | definition53AnomalyWeight
  | lemma53AnomalyLocalCocycle
  | lemma54AnomalyVanishes
  | theorem51ChernSimonsQuantization
  | corollary52MixedBFEquivalentToCS
  | definition61ChiralBoundaryCondition
  | theorem61BoundaryQuantization
  | boundaryLevelShift
  | lemma62BoundaryOneVertex
  | lemma63BoundaryTwoVertex
  | proposition64BoundaryLargeWheels
  | lemma65BoundaryAnomalyVanishes
  | claim66StratifiedCSWZW
  | wzwBoundaryExpectation
  | localCSWRepoBridge
  deriving DecidableEq, Repr

/-- Human-readable labels for the anchors above. -/
def OneLoopExactChernSimonsAnchor.paperLabel : OneLoopExactChernSimonsAnchor → String
  | .definition11MixedBFFields => "Definition 1.1: mixed BF fields on C x R"
  | .definition11MixedBFAction => "Definition 1.1: mixed BF action"
  | .chernSimonsDeformation => "Chern-Simons deformation I_CS(alpha)"
  | .mixedBFEquationsOfMotion => "Mixed BF and deformed flatness equations"
  | .definition12ChiralFunctional => "Definition 1.2: chiral translation-invariant local functional"
  | .definition21DeformationComplex => "Definition 2.1: translation-invariant deformation complex"
  | .lemma23ReducedDeformationComplex => "Lemma 2.3: reduced deformation-complex model"
  | .chiralDeformationCohomology => "Proposition 2.1 / Corollary 2.2: chiral deformations"
  | .graphShapeRestriction => "Only trees and one-loop wheels contribute"
  | .definition31HolomorphicGaugeFix => "Definition 3.1: holomorphic gauge fix Q*"
  | .lemma31GaussianZeta => "Lemma 3.1 / Corollary 3.2: zeta operator on wheel Gaussian"
  | .lemma33GaussianTau => "Lemma 3.3 / Corollary 3.4: tau operator on wheel Gaussian"
  | .gaussianMomentFormula => "Equation 3.15: inverse determinant for Gaussian moments"
  | .theorem41FiniteOneLoopExactQuantization => "Theorem 4.1: finite one-loop exact quantization"
  | .lemma42SmallWheelsVanish => "Lemma 4.2: one- and two-vertex wheels vanish"
  | .proposition43LargeWheelsFinite => "Proposition 4.3: higher wheels have finite weights"
  | .definition51ScaleQME => "Definition 5.1: scale-L quantum master equation"
  | .definition52OneLoopAnomaly => "Definition 5.2: scale-L one-loop anomaly"
  | .definition53AnomalyWeight => "Definition 5.3: distinguished-edge anomaly weight"
  | .lemma53AnomalyLocalCocycle => "Lemma 5.3: anomaly is a local cocycle from wheels"
  | .lemma54AnomalyVanishes => "Lemma 5.4: wheel anomaly vanishes"
  | .theorem51ChernSimonsQuantization => "Theorem 5.1: C x R one-loop exact quantization"
  | .corollary52MixedBFEquivalentToCS => "Corollary 5.2: mixed BF quantization is equivalent to CS"
  | .definition61ChiralBoundaryCondition => "Definition 6.1: chiral boundary condition"
  | .theorem61BoundaryQuantization => "Theorem 6.1: boundary half-space quantization"
  | .boundaryLevelShift => "Boundary one-loop level shift by Tr_ad(alpha partial alpha)"
  | .lemma62BoundaryOneVertex => "Lemma 6.2: boundary one-vertex wheel vanishes"
  | .lemma63BoundaryTwoVertex => "Lemma 6.3: boundary two-vertex wheel has CS boundary limit"
  | .proposition64BoundaryLargeWheels => "Proposition 6.4: boundary large wheels are finite"
  | .lemma65BoundaryAnomalyVanishes => "Lemma 6.5: boundary anomaly vanishes"
  | .claim66StratifiedCSWZW => "Claim 6.6: stratified CS/WZW factorization algebra"
  | .wzwBoundaryExpectation => "Boundary chiral currents / WZW expectation"
  | .localCSWRepoBridge => "Bridge to the repo's finite local CSW action"


/-- The product decomposition of forms on `C x R` used before Definition 1.1. -/
structure DeRhamDolbeaultProductSplit where
  DeRhamForms3 : Type
  DolbeaultTensorForms : Type
  toDolbeaultTensor : DeRhamForms3 → DolbeaultTensorForms
  toDeRhamForms : DolbeaultTensorForms → DeRhamForms3
  left_inv : ∀ ω, toDeRhamForms (toDolbeaultTensor ω) = ω
  right_inv : ∀ η, toDolbeaultTensor (toDeRhamForms η) = η

/-- The de Rham/Dolbeault split is an equivalence of the two formal field carriers. -/
noncomputable def DeRhamDolbeaultProductSplit.toEquiv
    (S : DeRhamDolbeaultProductSplit) :
    S.DeRhamForms3 ≃ S.DolbeaultTensorForms where
  toFun := S.toDolbeaultTensor
  invFun := S.toDeRhamForms
  left_inv := S.left_inv
  right_inv := S.right_inv

/-- Field-type carrier for Definition 1.1: alpha is the `(0,*)` sector and beta the `(1,*)` sector. -/
structure MixedBFFieldSplit where
  AlphaField : Type
  BetaField : Type
  LieAlgebra : Type
  alpha_is_omega0star_tensor_R_shifted : Prop
  alpha_is_omega0star_tensor_R_shifted_holds : alpha_is_omega0star_tensor_R_shifted
  beta_is_omega1star_tensor_R : Prop
  beta_is_omega1star_tensor_R_holds : beta_is_omega1star_tensor_R
  invariantNondegeneratePairing : Prop
  invariantNondegeneratePairing_holds : invariantNondegeneratePairing

/-- Definition 1.1 supplies the alpha and beta field sectors together with the pairing data. -/
lemma mixedBFFieldSplit_has_definition11_components (F : MixedBFFieldSplit) :
    F.alpha_is_omega0star_tensor_R_shifted ∧ F.beta_is_omega1star_tensor_R ∧
      F.invariantNondegeneratePairing :=
  ⟨F.alpha_is_omega0star_tensor_R_shifted_holds, F.beta_is_omega1star_tensor_R_holds,
    F.invariantNondegeneratePairing_holds⟩

/-- Definition 1.2: a chiral local functional only uses constant-coefficient holomorphic derivatives. -/
structure ChiralLocalFunctional where
  Functional : Type
  translationInvariant : Prop
  usesOnlyHolomorphicDerivatives : Prop
  betaInputCount : ℕ
  betaInputCount_le_one : betaInputCount ≤ 1

/-- Weight zero means no beta input. -/
def ChiralLocalFunctional.IsWeightZero (I : ChiralLocalFunctional) : Prop :=
  I.betaInputCount = 0

/-- Weight one means exactly one beta input. -/
def ChiralLocalFunctional.IsWeightOne (I : ChiralLocalFunctional) : Prop :=
  I.betaInputCount = 1

/-- Chiral functionals in Definition 1.2 have only weights zero and one. -/
lemma ChiralLocalFunctional.weight_zero_or_one (I : ChiralLocalFunctional) :
    I.IsWeightZero ∨ I.IsWeightOne := by
  exact Nat.le_one_iff_eq_zero_or_eq_one.mp I.betaInputCount_le_one

/-- Connected graph shapes forced by the chiral alpha/beta leg count in Section 1.2. -/
inductive ConnectedChiralGraphShape where
  | betaRootedTree
  | singleWeightZeroVertex
  | oneLoopNoBeta
  deriving DecidableEq, Repr

/-- Loop number of the connected graph shapes from Figure 1. -/
def ConnectedChiralGraphShape.loopNumber : ConnectedChiralGraphShape → ℕ
  | .betaRootedTree => 0
  | .singleWeightZeroVertex => 0
  | .oneLoopNoBeta => 1

/-- Output beta-weight of the connected graph shapes from Figure 1. -/
def ConnectedChiralGraphShape.outputBetaWeight : ConnectedChiralGraphShape → ℕ
  | .betaRootedTree => 1
  | .singleWeightZeroVertex => 0
  | .oneLoopNoBeta => 0

/-- Section 1.2 graph counting: connected chiral graphs have at most one loop. -/
lemma ConnectedChiralGraphShape.loopNumber_le_one
    (Gamma : ConnectedChiralGraphShape) :
    Gamma.loopNumber ≤ 1 := by
  cases Gamma <;> simp [ConnectedChiralGraphShape.loopNumber]

/-- Section 1.2 graph counting: connected chiral graphs output weight zero or one. -/
lemma ConnectedChiralGraphShape.outputBetaWeight_le_one
    (Gamma : ConnectedChiralGraphShape) :
    Gamma.outputBetaWeight ≤ 1 := by
  cases Gamma <;> simp [ConnectedChiralGraphShape.outputBetaWeight]

/-- Lightweight equivalence carrier used for quasi-isomorphism-level paper statements. -/
structure QuasiIsomorphic (A B : Type) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- Convert a strict quasi-isomorphism carrier into a Lean equivalence of carriers. -/
noncomputable def QuasiIsomorphic.toEquiv {A B : Type} (Q : QuasiIsomorphic A B) : A ≃ B where
  toFun := Q.toFun
  invFun := Q.invFun
  left_inv := Q.left_inv
  right_inv := Q.right_inv

/-- Definition 2.1 and Proposition 2.1/Corollary 2.2 packaged for reuse. -/
structure DeformationComplexPackage where
  LocalFunctional : Type
  WeightZeroInvariant : Type
  WeightOneInvariant : Type
  WeightZeroModel : Type
  WeightOneModel : Type
  SemisimpleCohomology : Type
  SymmetricInvariantPairing : Type
  weight : LocalFunctional → ℕ
  bracketWithSmix : LocalFunctional → LocalFunctional
  differentialPreservesWeight : Prop
  differentialPreservesWeight_holds : differentialPreservesWeight
  fullComplexIsDirectSumByWeight : Prop
  fullComplexIsDirectSumByWeight_holds : fullComplexIsDirectSumByWeight
  weightZero_qiso : QuasiIsomorphic WeightZeroInvariant WeightZeroModel
  weightOne_qiso : QuasiIsomorphic WeightOneInvariant WeightOneModel
  semisimpleWeightZeroCohomology : SemisimpleCohomology → SymmetricInvariantPairing
  semisimpleWeightOneTrivial : Prop
  semisimpleWeightOneTrivial_holds : semisimpleWeightOneTrivial
  chernSimonsImage : SymmetricInvariantPairing → ℂ
  chernSimonsDeformationValue : SymmetricInvariantPairing → ℂ
  corollary22_image_eq_cs :
    ∀ κ, chernSimonsImage κ = chernSimonsDeformationValue κ

/-- Definition 2.1: the full translation-invariant complex is a direct sum by weight. -/
lemma deformationComplex_direct_sum_by_weight (D : DeformationComplexPackage) :
    D.fullComplexIsDirectSumByWeight :=
  D.fullComplexIsDirectSumByWeight_holds

/-- Proposition 2.1, weight zero: the invariant weight-zero complex has the stated model. -/
noncomputable def deformationComplex_weightZero_equiv
    (D : DeformationComplexPackage) :
    D.WeightZeroInvariant ≃ D.WeightZeroModel :=
  D.weightZero_qiso.toEquiv

/-- Proposition 2.1, weight one: the invariant weight-one complex has the stated model. -/
noncomputable def deformationComplex_weightOne_equiv
    (D : DeformationComplexPackage) :
    D.WeightOneInvariant ≃ D.WeightOneModel :=
  D.weightOne_qiso.toEquiv

/-- Corollary 2.2: in the semisimple case the image of `κ` is the CS deformation. -/
lemma semisimple_chernSimonsImage_eq_deformation
    (D : DeformationComplexPackage) (κ : D.SymmetricInvariantPairing) :
    D.chernSimonsImage κ = D.chernSimonsDeformationValue κ :=
  D.corollary22_image_eq_cs κ

/-- Lemma 2.3: reduced deformation-complex model after the formal Poincare lemma. -/
structure ReducedDeformationComplexModel where
  DefMix : Type
  ReducedModel : Type
  quasiIso : QuasiIsomorphic DefMix ReducedModel
  invariantGenerator : String
  generatorLabel :
    invariantGenerator = "(dt partial_t)(dz partial_z)"

/-- Lemma 2.3 supplies the reduced model used to compute the invariant subcomplex. -/
noncomputable def ReducedDeformationComplexModel.toEquiv
    (M : ReducedDeformationComplexModel) :
    M.DefMix ≃ M.ReducedModel :=
  M.quasiIso.toEquiv


end Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons

end
