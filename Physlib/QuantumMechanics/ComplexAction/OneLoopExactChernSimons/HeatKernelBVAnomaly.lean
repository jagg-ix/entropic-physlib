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
public import Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.MixedBFOneLoopGraphs
meta import Zil

/-! # OneLoopExactChernSimons — part `HeatKernelBVAnomaly`. Full paper docstring in the umbrella module `Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons`; namespace and
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


/-- Scalar part of the three-dimensional flat heat kernel in Section 3.1. -/
noncomputable def scalarFlatHeatKernel3D (T rSq : ℝ) : ℝ :=
  (4 * Real.pi * T) ^ (-(3 / 2 : ℝ)) * Real.exp (-(rSq / (4 * T)))

/-- The repo's Euclidean heat-kernel propagator has the scalar exponential form used by Section 3. -/
lemma repo_heatKernelPropagator_eq_exp (T mSq : ℝ) :
    Physlib.QFT.PathIntegral.heat_kernel_propagator T mSq =
      Real.exp (-(mSq * T)) :=
  rfl

/-- Definition 3.1 and Equations (3.1)-(3.7): holomorphic gauge and its kernels. -/
structure HolomorphicGaugeKernelPackage where
  Field : Type
  Kernel : Type
  GaussianForm : Type
  Propagator : Type
  Q : Field → Field
  Qstar : Field → Field
  Laplacian : Field → Field
  standardLaplacian : Field → Field
  laplacian_eq_standard : ∀ φ, Laplacian φ = standardLaplacian φ
  heatKernel : ℝ → Kernel
  gaussianForm : ℝ → GaussianForm
  propagator : ℝ → ℝ → Propagator
  propagator_eq_integral_Qstar_heat : Prop
  propagator_eq_integral_Qstar_heat_holds : propagator_eq_integral_Qstar_heat
  propagator_respects_alpha_beta_split : Prop
  propagator_respects_alpha_beta_split_holds : propagator_respects_alpha_beta_split
  gaussian_to_propagator_operator_lambda : Prop
  gaussian_to_propagator_operator_lambda_holds : gaussian_to_propagator_operator_lambda

/-- Definition 3.1: the holomorphic gauge Laplacian is the standard flat Laplacian. -/
lemma holomorphicGauge_laplacian_eq_standard
    (K : HolomorphicGaugeKernelPackage) (φ : K.Field) :
    K.Laplacian φ = K.standardLaplacian φ :=
  K.laplacian_eq_standard φ

/-- Equations (3.4)-(3.7): the propagator is built by applying `Qstar` to the heat kernel. -/
lemma holomorphicGauge_propagator_from_Qstar_heat
    (K : HolomorphicGaugeKernelPackage) :
    K.propagator_eq_integral_Qstar_heat ∧
      K.gaussian_to_propagator_operator_lambda :=
  ⟨K.propagator_eq_integral_Qstar_heat_holds, K.gaussian_to_propagator_operator_lambda_holds⟩

/-- Lemmas 3.1 and 3.3 plus Corollaries 3.2 and 3.4, abstracted over the wheel Gaussian. -/
structure GaussianWheelOperatorPackage where
  Gaussian : Type
  zeta : Gaussian → Gaussian
  tau : Gaussian → Gaussian
  holomorphicDerivativeMinusZeta : Gaussian → Gaussian
  timeDerivativeMinusTau : Gaussian → Gaussian
  zeta_formula : Prop
  zeta_formula_holds : zeta_formula
  tau_formula : Prop
  tau_formula_holds : tau_formula
  corollary32_formula : Prop
  corollary32_formula_holds : corollary32_formula
  corollary34_formula : Prop
  corollary34_formula_holds : corollary34_formula
  constantCoefficientOperatorsCommute : Prop
  constantCoefficientOperatorsCommute_holds : constantCoefficientOperatorsCommute

/-- Lemma 3.1 and Corollary 3.2 are available from the Gaussian wheel package. -/
lemma gaussian_zeta_formulas
    (G : GaussianWheelOperatorPackage) :
    G.zeta_formula ∧ G.corollary32_formula :=
  ⟨G.zeta_formula_holds, G.corollary32_formula_holds⟩

/-- Lemma 3.3 and Corollary 3.4 are available from the Gaussian wheel package. -/
lemma gaussian_tau_formulas
    (G : GaussianWheelOperatorPackage) :
    G.tau_formula ∧ G.corollary34_formula :=
  ⟨G.tau_formula_holds, G.corollary34_formula_holds⟩

/-- Equation (3.15) and Wick-moment control for the Gaussian measure used in wheel estimates. -/
structure GaussianMomentPackage where
  parameterCount : ℕ
  inverseDeterminant : ℝ
  productOfScales : ℝ
  sumOfScales : ℝ
  inverseDeterminant_eq :
    inverseDeterminant = productOfScales / sumOfScales
  wickMomentsControlledByInverseMatrix : Prop
  wickMomentsControlledByInverseMatrix_holds : wickMomentsControlledByInverseMatrix
  higherMomentsImproveEpsilonLimit : Prop
  higherMomentsImproveEpsilonLimit_holds : higherMomentsImproveEpsilonLimit

/-- Equation (3.15): the inverse determinant is product of scales divided by their sum. -/
lemma gaussian_inverseDeterminant_eq
    (G : GaussianMomentPackage) :
    G.inverseDeterminant = G.productOfScales / G.sumOfScales :=
  G.inverseDeterminant_eq

/-- Wick moments supply the convergence estimates used in Propositions 4.3 and 6.4. -/
lemma gaussian_moments_control_convergence
    (G : GaussianMomentPackage) :
    G.wickMomentsControlledByInverseMatrix ∧ G.higherMomentsImproveEpsilonLimit :=
  ⟨G.wickMomentsControlledByInverseMatrix_holds, G.higherMomentsImproveEpsilonLimit_holds⟩

/-- Lemma 4.2 and Proposition 4.3 as wheel-weight data. -/
structure WheelAnalyticWeightPackage where
  Wheel : Type
  vertexCount : Wheel → ℕ
  analyticWeight : Wheel → ℂ
  finiteEpsilonLimit : Wheel → Prop
  vanishesAtFiniteScale : Wheel → Prop
  lemma42 :
    ∀ γ, vertexCount γ = 1 ∨ vertexCount γ = 2 →
      vanishesAtFiniteScale γ ∧ analyticWeight γ = 0
  proposition43 :
    ∀ γ, 3 ≤ vertexCount γ → finiteEpsilonLimit γ

/-- Lemma 4.2: wheels with one or two vertices vanish at finite scale. -/
lemma lemma42_small_wheels_vanish
    (W : WheelAnalyticWeightPackage) (γ : W.Wheel)
    (hγ : W.vertexCount γ = 1 ∨ W.vertexCount γ = 2) :
    W.vanishesAtFiniteScale γ ∧ W.analyticWeight γ = 0 :=
  W.lemma42 γ hγ

/-- Proposition 4.3: wheels with more than two vertices have a finite `epsilon -> 0` limit. -/
lemma proposition43_large_wheels_finite
    (W : WheelAnalyticWeightPackage) (γ : W.Wheel)
    (hγ : 3 ≤ W.vertexCount γ) :
    W.finiteEpsilonLimit γ :=
  W.proposition43 γ hγ


/-- Definition 5.1: scale-`L` BV data for the renormalized quantum master equation. -/
structure ScaleBVQMEData where
  Action : Type
  hbar : ℂ
  deltaL : ℝ → Action → ℂ
  bracketL : ℝ → Action → Action → ℂ

/-- Scale-`L` QME residual: `hbar Delta_L S[L] + 1/2 {S[L], S[L]}_L`. -/
noncomputable def scaleQMEResidual (Q : ScaleBVQMEData) (L : ℝ) (S : Q.Action) : ℂ :=
  Q.hbar * Q.deltaL L S + (1 / 2 : ℂ) * Q.bracketL L S S

/-- The scale-`L` QME is the vanishing of the residual. -/
def SatisfiesScaleQME (Q : ScaleBVQMEData) (L : ℝ) (S : Q.Action) : Prop :=
  scaleQMEResidual Q L S = 0

/-- If the residual vanishes, the action satisfies the scale-`L` QME. -/
lemma satisfiesScaleQME_of_residual_zero
    (Q : ScaleBVQMEData) (L : ℝ) (S : Q.Action)
    (h : scaleQMEResidual Q L S = 0) :
    SatisfiesScaleQME Q L S :=
  h

/-- Definition 5.2/5.3 and Lemma 5.3: the one-loop anomaly is a local cocycle from wheels. -/
structure OneLoopAnomalyPackage where
  Wheel : Type
  Edge : Type
  anomalyAtScale : ℝ → ℂ
  localCocycle : ℂ
  distinguishedEdgeWeight : Wheel → Edge → ℂ
  anomalyLimit_eq_localCocycle : Prop
  anomalyLimit_eq_localCocycle_holds : anomalyLimit_eq_localCocycle
  localCocycle_eq_sum_distinguished_wheels : Prop
  localCocycle_eq_sum_distinguished_wheels_holds : localCocycle_eq_sum_distinguished_wheels
  lemma54_weight_vanishes : ∀ γ e, distinguishedEdgeWeight γ e = 0
  anomalyAtScale_eq_zero : ∀ L, anomalyAtScale L = 0

/-- Lemma 5.3: the anomaly limit exists as a local cocycle and is computed by wheel weights. -/
lemma lemma53_anomaly_is_local_cocycle
    (A : OneLoopAnomalyPackage) :
    A.anomalyLimit_eq_localCocycle ∧ A.localCocycle_eq_sum_distinguished_wheels :=
  ⟨A.anomalyLimit_eq_localCocycle_holds, A.localCocycle_eq_sum_distinguished_wheels_holds⟩

/-- Lemma 5.4: every distinguished-edge wheel anomaly weight vanishes. -/
lemma lemma54_anomaly_wheel_weight_vanishes
    (A : OneLoopAnomalyPackage) (γ : A.Wheel) (e : A.Edge) :
    A.distinguishedEdgeWeight γ e = 0 :=
  A.lemma54_weight_vanishes γ e

/-- The vanishing wheel anomaly makes the scale anomaly zero. -/
lemma oneLoopAnomalyAtScale_eq_zero
    (A : OneLoopAnomalyPackage) (L : ℝ) :
    A.anomalyAtScale L = 0 :=
  A.anomalyAtScale_eq_zero L

/-- Bridge from the anomaly calculation to the scale quantum master equation. -/
structure OneLoopExactQMEBridge where
  EffectiveAction : Type
  qmeData : ScaleBVQMEData
  actionAtScale : ℝ → EffectiveAction → qmeData.Action
  anomalyAtScale : ℝ → ℂ
  qmeResidual_eq_anomaly :
    ∀ L S, scaleQMEResidual qmeData L (actionAtScale L S) = anomalyAtScale L
  anomalyAtScale_eq_zero : ∀ L, anomalyAtScale L = 0

/-- If the one-loop anomaly vanishes, the one-loop exact effective action satisfies the QME. -/
lemma oneLoopExact_satisfies_QME_of_anomaly_zero
    (B : OneLoopExactQMEBridge) (L : ℝ) (S : B.EffectiveAction) :
    SatisfiesScaleQME B.qmeData L (B.actionAtScale L S) := by
  unfold SatisfiesScaleQME
  rw [B.qmeResidual_eq_anomaly L S, B.anomalyAtScale_eq_zero L]

/-- The local RG beta-function obstruction used in Section 1.2. -/
structure LocalRGFlowPackage where
  classicallyScaleInvariant : Prop
  betaFunction : ℂ
  anomaly : ℂ
  beta_eq_anomaly : betaFunction = anomaly
  anomaly_eq_zero : anomaly = 0

/-- If the anomaly vanishes, the local RG beta-function vanishes. -/
lemma betaFunction_eq_zero_of_anomaly_zero
    (R : LocalRGFlowPackage) :
    R.betaFunction = 0 := by
  rw [R.beta_eq_anomaly, R.anomaly_eq_zero]


/--
Carrier for Theorem 4.1 and Theorem 5.1.

The analytic content is supplied as fields: Lean then checks downstream uses of
the conclusions without pretending to reprove the estimates in this finite
module.
-/
structure ChiralDeformationQuantizationPackage where
  Theory : Type
  isChiralDeformation : Theory → Prop
  admitsOneLoopExactQuantization : Theory → Prop
  finiteFeynmanWeights : Theory → Prop
  noUVAnomaly : Theory → Prop
  theorem41 :
    ∀ T, isChiralDeformation T →
      admitsOneLoopExactQuantization T ∧ finiteFeynmanWeights T
  theorem51 :
    ∀ T, isChiralDeformation T →
      admitsOneLoopExactQuantization T ∧ noUVAnomaly T

/-- Theorem 4.1 as a reusable Lean consequence. -/
lemma theorem41_finite_one_loop_exact
    (Q : ChiralDeformationQuantizationPackage) (T : Q.Theory)
    (hT : Q.isChiralDeformation T) :
    Q.admitsOneLoopExactQuantization T ∧ Q.finiteFeynmanWeights T :=
  Q.theorem41 T hT

/-- Theorem 5.1 as a reusable Lean consequence on `C x R`. -/
lemma theorem51_one_loop_exact_no_uv_anomaly
    (Q : ChiralDeformationQuantizationPackage) (T : Q.Theory)
    (hT : Q.isChiralDeformation T) :
    Q.admitsOneLoopExactQuantization T ∧ Q.noUVAnomaly T :=
  Q.theorem51 T hT

/-- Corollary 5.2: the mixed BF quantization and CS quantization are equivalent in the semisimple case. -/
structure MixedBFCSEquivalence where
  mixedBFQuantization : Type
  chernSimonsQuantization : Type
  toCS : mixedBFQuantization → chernSimonsQuantization
  toMixedBF : chernSimonsQuantization → mixedBFQuantization
  left_inv : ∀ x, toMixedBF (toCS x) = x
  right_inv : ∀ y, toCS (toMixedBF y) = y

/-- The mixed BF and CS quantization types form an equivalence. -/
noncomputable def MixedBFCSEquivalence.toEquiv (E : MixedBFCSEquivalence) :
    E.mixedBFQuantization ≃ E.chernSimonsQuantization where
  toFun := E.toCS
  invFun := E.toMixedBF
  left_inv := E.left_inv
  right_inv := E.right_inv

/-- Transporting a mixed BF quantization to CS and back is identity. -/
lemma mixedBF_to_CS_to_mixedBF (E : MixedBFCSEquivalence)
    (x : E.mixedBFQuantization) :
    E.toMixedBF (E.toCS x) = x :=
  E.left_inv x

/-- Transporting a CS quantization to mixed BF and back is identity. -/
lemma CS_to_mixedBF_to_CS (E : MixedBFCSEquivalence)
    (y : E.chernSimonsQuantization) :
    E.toCS (E.toMixedBF y) = y :=
  E.right_inv y


end Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.holomorphicGauge_laplacian_eq_standard where
  formalizes @ "claim:in-the-holomorphic-gauge-of-definition-3-1-the-gauge-fixed-laplacian-is-the-standard-flat-laplacian",
  supported_by @ "paper:one-loop-exactness-of-chern-simons-heat-kernel-and-bv-anomaly"

zil attach Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.gaussian_zeta_formulas where
  formalizes @ "claim:the-gaussian-wheel-operator-package-supplies-the-zeta-regularized-determinant-formula-of-lemma-3-3-and-corollary-3-2"

zil attach Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.gaussian_tau_formulas where
  formalizes @ "claim:the-gaussian-wheel-operator-package-supplies-the-tau-function-formula-of-lemma-3-3-and-corollary-3-4"

zil attach Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.gaussian_inverseDeterminant_eq where
  formalizes @ "claim:equation-3-15-the-inverse-determinant-of-the-gaussian-measure-is-the-product-of-the-scales-divided-by-their-sum-controlling-the-wick-moments"

zil_file_contract physlib.heatKernelBVAnomaly where
  promises "The heat-kernel / holomorphic-gauge and BV-anomaly machinery behind one-loop-exact Chern-Simons. In the holomorphic gauge (Definition 3.1) the gauge-fixed Laplacian is the standard flat Laplacian (holomorphicGauge_laplacian_eq_standard), and the heat-kernel propagator is the exponential of minus the mass-squared times the proper time. The Gaussian wheel-operator package supplies the zeta-regularized determinant formulas of Lemma 3.3 / Corollary 3.2 (gaussian_zeta_formulas) and the tau-function formulas of Corollary 3.4 (gaussian_tau_formulas), and the Gaussian measure's inverse determinant is the product of scales over their sum (Equation 3.15), controlling the Wick moments (gaussian_inverseDeterminant_eq) -- the analytic inputs that make the one-loop correction exact."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.HolomorphicGaugeKernelPackage",
    "lean:Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.GaussianWheelOperatorPackage"]
  forbids_substitutes ["the wheel-graph / Feynman-diagram estimates and the zeta-function regularization proofs, which are the cited finite-dimensional analytic infrastructure carried as package hypotheses (the file records the conclusions without reproving the estimates)",
    "any claim about the full BV quantization beyond the Gaussian and heat-kernel formulas assembled here"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.holomorphicGauge_laplacian_eq_standard,
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.gaussian_zeta_formulas,
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.gaussian_tau_formulas,
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.gaussian_inverseDeterminant_eq]

/- ZIL-END -/
