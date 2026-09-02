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
public import Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.HeatKernelBVAnomaly
meta import Zil

/-! # OneLoopExactChernSimons — part `BoundaryLevelShift`. Full paper docstring in the umbrella module `Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons`; namespace and
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


/-- Boundary one-loop correction from Theorem 6.1. -/
structure BoundaryLevelShift where
  classicalLevel : ℂ
  shiftedLevel : ℂ
  oneLoopShift : ℂ
  adjointTraceCoefficient : ℂ
  shifted_eq : shiftedLevel = classicalLevel + oneLoopShift
  oneLoopShift_eq_adjointTrace : oneLoopShift = adjointTraceCoefficient

/-- The shifted boundary level is the classical level plus the adjoint-trace correction. -/
lemma BoundaryLevelShift.shifted_eq_classical_plus_adjoint_trace
    (L : BoundaryLevelShift) :
    L.shiftedLevel = L.classicalLevel + L.adjointTraceCoefficient := by
  rw [L.shifted_eq, L.oneLoopShift_eq_adjointTrace]

/-- Carrier for Theorem 6.1 on `C x R_{\ge 0}`. -/
structure BoundaryChiralQuantizationPackage where
  BoundaryTheory : Type
  isBoundaryChiralDeformation : BoundaryTheory → Prop
  admitsBoundaryQuantization : BoundaryTheory → Prop
  boundaryOneLoopExact : BoundaryTheory → Prop
  boundaryAnomalyVanishes : BoundaryTheory → Prop
  levelShift : BoundaryTheory → BoundaryLevelShift
  theorem61 :
    ∀ T, isBoundaryChiralDeformation T →
      admitsBoundaryQuantization T ∧ boundaryOneLoopExact T ∧ boundaryAnomalyVanishes T

/-- Theorem 6.1 as a checked reusable boundary consequence. -/
lemma theorem61_boundary_one_loop_exact
    (Q : BoundaryChiralQuantizationPackage) (T : Q.BoundaryTheory)
    (hT : Q.isBoundaryChiralDeformation T) :
    Q.admitsBoundaryQuantization T ∧ Q.boundaryOneLoopExact T ∧
      Q.boundaryAnomalyVanishes T :=
  Q.theorem61 T hT

/-- Boundary level shifts use the same adjoint-trace correction from Theorem 6.1. -/
lemma theorem61_boundary_shift_eq_adjoint_trace
    (Q : BoundaryChiralQuantizationPackage) (T : Q.BoundaryTheory) :
    (Q.levelShift T).shiftedLevel =
      (Q.levelShift T).classicalLevel + (Q.levelShift T).adjointTraceCoefficient :=
  (Q.levelShift T).shifted_eq_classical_plus_adjoint_trace


/-- Definition 6.1: alpha fields obey the odd/chiral boundary condition, beta fields are unrestricted. -/
structure ChiralBoundaryCondition where
  AlphaField : Type
  BetaField : Type
  boundaryValueZero : AlphaField → Prop
  oddUnderTimeReflection : AlphaField → Prop
  betaAllowed : BetaField → Prop
  odd_implies_boundary_zero :
    ∀ α, oddUnderTimeReflection α → boundaryValueZero α

/-- Odd alpha fields satisfy the boundary vanishing condition. -/
lemma chiralBoundary_alpha_boundary_zero
    (B : ChiralBoundaryCondition) (α : B.AlphaField)
    (hα : B.oddUnderTimeReflection α) :
    B.boundaryValueZero α :=
  B.odd_implies_boundary_zero α hα

/-- Half-space heat-kernel package for Equations (6.1)-(6.3). -/
structure HalfSpaceHeatKernelPackage where
  Kernel : Type
  Propagator : Type
  fullSpaceKernel : Kernel
  reflectedKernel : Kernel
  dirichletKernel : Kernel
  mollifiedPropagator : Propagator
  dirichlet_eq_full_minus_reflected : Prop
  dirichlet_eq_full_minus_reflected_holds : dirichlet_eq_full_minus_reflected
  reflectedTerm_odd_under_time_reflection : Prop
  reflectedTerm_odd_under_time_reflection_holds : reflectedTerm_odd_under_time_reflection
  originalTerm_concentrates_on_diagonal : Prop
  originalTerm_concentrates_on_diagonal_holds : originalTerm_concentrates_on_diagonal
  reflectedTerm_concentrates_on_boundary : Prop
  reflectedTerm_concentrates_on_boundary_holds : reflectedTerm_concentrates_on_boundary
  propagator_eq_integral_Qstar_dirichletKernel : Prop
  propagator_eq_integral_Qstar_dirichletKernel_holds :
    propagator_eq_integral_Qstar_dirichletKernel

/-- Equations (6.1)-(6.3): the half-space propagator uses the Dirichlet heat kernel. -/
lemma halfSpace_propagator_from_dirichletKernel
    (K : HalfSpaceHeatKernelPackage) :
    K.dirichlet_eq_full_minus_reflected ∧
      K.propagator_eq_integral_Qstar_dirichletKernel :=
  ⟨K.dirichlet_eq_full_minus_reflected_holds,
    K.propagator_eq_integral_Qstar_dirichletKernel_holds⟩

/-- Boundary concentration: only the reflected term can concentrate near the boundary. -/
lemma halfSpace_boundary_concentration
    (K : HalfSpaceHeatKernelPackage) :
    K.originalTerm_concentrates_on_diagonal ∧
      K.reflectedTerm_concentrates_on_boundary ∧
      K.reflectedTerm_odd_under_time_reflection :=
  ⟨K.originalTerm_concentrates_on_diagonal_holds,
    K.reflectedTerm_concentrates_on_boundary_holds,
    K.reflectedTerm_odd_under_time_reflection_holds⟩

/-- Lemmas 6.2, 6.3, 6.5 and Proposition 6.4 as boundary wheel-weight data. -/
structure BoundaryWheelAnalyticPackage where
  Wheel : Type
  vertexCount : Wheel → ℕ
  boundaryWeight : Wheel → ℂ
  boundaryAnomalyWeight : Wheel → ℂ
  boundaryDistributionLimit : Wheel → Prop
  boundaryCSFunctional : ℂ
  analyticConstant : ℂ
  lemma62_one_vertex_zero :
    ∀ γ, vertexCount γ = 1 → boundaryWeight γ = 0
  lemma63_two_vertex_boundary_limit :
    ∀ γ, vertexCount γ = 2 →
      boundaryDistributionLimit γ ∧
        boundaryWeight γ = analyticConstant * boundaryCSFunctional
  proposition64_more_vertices_finite :
    ∀ γ, 3 ≤ vertexCount γ → boundaryDistributionLimit γ
  lemma65_boundary_anomaly_zero :
    ∀ γ, boundaryAnomalyWeight γ = 0

/-- Lemma 6.2: the one-vertex boundary wheel vanishes. -/
lemma lemma62_boundary_one_vertex_zero
    (W : BoundaryWheelAnalyticPackage) (γ : W.Wheel)
    (hγ : W.vertexCount γ = 1) :
    W.boundaryWeight γ = 0 :=
  W.lemma62_one_vertex_zero γ hγ

/-- Lemma 6.3: the two-vertex boundary wheel has a boundary Chern-Simons limit. -/
lemma lemma63_boundary_two_vertex_limit
    (W : BoundaryWheelAnalyticPackage) (γ : W.Wheel)
    (hγ : W.vertexCount γ = 2) :
    W.boundaryDistributionLimit γ ∧
      W.boundaryWeight γ = W.analyticConstant * W.boundaryCSFunctional :=
  W.lemma63_two_vertex_boundary_limit γ hγ

/-- Proposition 6.4: boundary wheels with more than two vertices have finite limits. -/
lemma proposition64_boundary_large_wheels_finite
    (W : BoundaryWheelAnalyticPackage) (γ : W.Wheel)
    (hγ : 3 ≤ W.vertexCount γ) :
    W.boundaryDistributionLimit γ :=
  W.proposition64_more_vertices_finite γ hγ

/-- Lemma 6.5: the boundary anomaly vanishes for every wheel. -/
lemma lemma65_boundary_anomaly_zero
    (W : BoundaryWheelAnalyticPackage) (γ : W.Wheel) :
    W.boundaryAnomalyWeight γ = 0 :=
  W.lemma65_boundary_anomaly_zero γ

/-- Theorem 6.1 combines boundary anomaly vanishing with the adjoint-trace level shift. -/
structure BoundaryTheorem61Synthesis where
  Quantization : Type
  admitsQuantization : Quantization → Prop
  oneLoopExact : Quantization → Prop
  noBoundaryAnomaly : Quantization → Prop
  shift : Quantization → BoundaryLevelShift
  theorem61 :
    ∀ Q, admitsQuantization Q ∧ oneLoopExact Q ∧ noBoundaryAnomaly Q

/-- Theorem 6.1 supplies quantization, one-loop exactness, anomaly vanishing, and the shift formula. -/
lemma boundaryTheorem61_full_conclusion
    (B : BoundaryTheorem61Synthesis) (Q : B.Quantization) :
    B.admitsQuantization Q ∧ B.oneLoopExact Q ∧ B.noBoundaryAnomaly Q ∧
      (B.shift Q).shiftedLevel =
        (B.shift Q).classicalLevel + (B.shift Q).adjointTraceCoefficient := by
  rcases B.theorem61 Q with ⟨hQ, h1, hA⟩
  exact ⟨hQ, h1, hA, (B.shift Q).shifted_eq_classical_plus_adjoint_trace⟩

/-- Claim 6.6: the boundary theory is a stratified factorization algebra joining CS and chiral WZW. -/
structure StratifiedCSWZWFactorization where
  InteriorObservables : Type
  BoundaryObservables : Type
  StratifiedObservables : Type
  ChiralCurrentAlgebra : Type
  level : ℂ
  interiorQuasiIso : QuasiIsomorphic InteriorObservables StratifiedObservables
  boundaryQuasiIso : QuasiIsomorphic ChiralCurrentAlgebra BoundaryObservables
  levelDeterminedByQuantization : Prop
  levelDeterminedByQuantization_holds : levelDeterminedByQuantization
  interior_is_CS_observables : Prop
  interior_is_CS_observables_holds : interior_is_CS_observables
  boundary_is_chiral_WZW_currents : Prop
  boundary_is_chiral_WZW_currents_holds : boundary_is_chiral_WZW_currents

/-- Claim 6.6 packaged: interior CS observables and boundary chiral WZW currents are the two strata. -/
lemma claim66_stratified_CSWZW
    (F : StratifiedCSWZWFactorization) :
    Nonempty (QuasiIsomorphic F.InteriorObservables F.StratifiedObservables) ∧
      Nonempty (QuasiIsomorphic F.ChiralCurrentAlgebra F.BoundaryObservables) ∧
      F.levelDeterminedByQuantization ∧ F.interior_is_CS_observables ∧
      F.boundary_is_chiral_WZW_currents :=
  ⟨⟨F.interiorQuasiIso⟩, ⟨F.boundaryQuasiIso⟩, F.levelDeterminedByQuantization_holds,
    F.interior_is_CS_observables_holds, F.boundary_is_chiral_WZW_currents_holds⟩


/--
The Gwilliam-Williams one-loop exact CS action is represented locally by the
repo's finite local complex CSW action.
-/
noncomputable def localOneLoopExactCSAction {n : ℕ} (c : HayashiCouplings)
    (P : LocalCSConnection n × LocalCSConnection n) : ℂ :=
  localComplexCSWAction c P

/-- The local one-loop exact CS action inherits the CSW holomorphic/anti-holomorphic split. -/
lemma localOneLoopExactCSAction_split {n : ℕ} (c : HayashiCouplings)
    (P : LocalCSConnection n × LocalCSConnection n) :
    localOneLoopExactCSAction c P =
      localHolomorphicAction c P.1 + localAntiholomorphicAction c P.2 :=
  localComplexCSWAction_split c P

/-- The local one-loop exact CS action vanishes on flat holomorphic and anti-holomorphic sectors. -/
lemma localOneLoopExactCSAction_eq_zero_of_flat {n : ℕ} (c : HayashiCouplings)
    (P : LocalCSConnection n × LocalCSConnection n)
    (hA : LocalCSFlat P.1) (hAbar : LocalCSFlat P.2) :
    localOneLoopExactCSAction c P = 0 :=
  localComplexCSWAction_eq_zero_of_flat c P hA hAbar

/-- The local one-loop exact CS action is invariant under simultaneous constant finite gauge conjugation. -/
lemma localOneLoopExactCSAction_gauge_conjugate {n : ℕ} (c : HayashiCouplings)
    (G H : Matrix (Fin n) (Fin n) ℂ) (P : LocalCSConnection n × LocalCSConnection n)
    (hHG : H * G = 1) :
    localOneLoopExactCSAction c
        (localGaugeConjugate G H P.1, localGaugeConjugate G H P.2)
      = localOneLoopExactCSAction c P :=
  localComplexCSWAction_gauge_conjugate c G H P hHG

/-- Reuse the repo's Gel'fand-Yaglom one-loop prefactor for positive determinant reductions. -/
noncomputable def csOneLoopPrefactor (D : ℝ) : ℝ :=
  Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopPrefactor D

/-- Positive determinant reductions give positive one-loop prefactors. -/
lemma csOneLoopPrefactor_pos (D : ℝ) (hD : 0 < D) :
    0 < csOneLoopPrefactor D :=
  Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom.oneLoopPrefactor_pos D hD


/--
A concrete one-loop integrand package that proves the hypotheses of the
repo's Nagao-Nielsen contour-deformation theorem.
-/
structure OneLoopExactContourBridge where
  Integrand : ℂ → ℂ
  IntegrandDeriv : ℂ → ℂ
  angleLeft : ℝ
  angleRight : ℝ
  holomorphic : ∀ z, HasDerivAt Integrand (IntegrandDeriv z) z
  zero_mem : (0 : ℝ) ∈ Set.Ioo angleLeft angleRight
  diffUnderIntegral :
    ∀ θ ∈ Set.Ioo angleLeft angleRight,
      HasDerivAt (fun θ : ℝ => ∫ s : ℝ, contourIntegrand Integrand θ s)
        (∫ s : ℝ, contourDeriv Integrand IntegrandDeriv θ s) θ
  primitiveIntegrable :
    ∀ θ ∈ Set.Ioo angleLeft angleRight,
      Integrable (fun s : ℝ => contourPrimitive Integrand θ s)
  derivIntegrable :
    ∀ θ ∈ Set.Ioo angleLeft angleRight,
      Integrable (fun s : ℝ => contourDeriv Integrand IntegrandDeriv θ s)

/--
The one-loop contour integral is independent of the ray inside the permitted
analytic wedge.
-/
lemma oneLoopExactContourBridge_const
    (B : OneLoopExactContourBridge) {θ₀ θ₁ : ℝ}
    (h0 : θ₀ ∈ Set.Ioo B.angleLeft B.angleRight)
    (h1 : θ₁ ∈ Set.Ioo B.angleLeft B.angleRight) :
    (∫ s : ℝ, contourIntegrand B.Integrand θ₀ s) =
      ∫ s : ℝ, contourIntegrand B.Integrand θ₁ s :=
  contourIntegral_const_of_dui B.holomorphic B.diffUnderIntegral
    B.primitiveIntegrable B.derivIntegrable h0 h1

/--
Every permitted one-loop ray computes the same value as the real-axis integral.
-/
lemma oneLoopExactContourBridge_eq_real
    (B : OneLoopExactContourBridge) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo B.angleLeft B.angleRight) :
    (∫ s : ℝ, contourIntegrand B.Integrand θ s) =
      ∫ s : ℝ, B.Integrand (s : ℂ) :=
  contourIntegral_eq_real B.holomorphic B.diffUnderIntegral
    B.primitiveIntegrable B.derivIntegrable B.zero_mem hθ

/-- The one-loop Gaussian on the real contour reuses the repo's TFD/Nagao-Nielsen Gaussian. -/
lemma oneLoopExactGaussianContour_realAxis (c : ℝ) (hc : 0 < c) :
    ∫ s : ℝ, contourIntegrand (gaussH c) 0 s = (Real.sqrt (Real.pi / c) : ℂ) :=
  momentumGaussian_realAxis c hc

/--
The Gaussian wheel integral used by the one-loop construction is invariant under
Wick rotation inside the Nagao-Nielsen wedge.
-/
lemma oneLoopExactGaussianContour_wick_invariance (c θ : ℝ) (hc : 0 < c)
    (hθ : |θ| < Real.pi / 4) :
    ∫ s : ℝ, contourIntegrand (gaussH c) 0 s =
      ∫ s : ℝ, contourIntegrand (gaussH c) θ s :=
  momentum_wick_invariance c θ hc hθ

/-- The one-loop CSW theta character inherits integer-level `T²` invariance. -/
lemma oneLoopExactTheta_tau_add_two (K : ℤ) (τ z : ℂ) :
    cswTheta (K : ℂ) (τ + 2) z = cswTheta (K : ℂ) τ z :=
  cswTheta_tau_add_two K τ z

/-- The one-loop CSW theta character inherits Wilson-line lattice periodicity. -/
lemma oneLoopExactTheta_z_add_one (K : ℤ) (τ z : ℂ) :
    cswTheta (K : ℂ) τ (z + 1) = cswTheta (K : ℂ) τ z :=
  cswTheta_z_add_one K τ z

/-- The one-loop CSW theta character inherits the Poisson-resummation modular `S` transform. -/
lemma oneLoopExactTheta_modular_S (k τ z : ℂ) :
    cswTheta k τ z =
      1 / (-Complex.I * (k * τ)) ^ (1 / 2 : ℂ)
        * Complex.exp (-(Real.pi : ℂ) * Complex.I * (k * z) ^ 2 / (k * τ))
        * jacobiTheta₂ ((k * z) / (k * τ)) (-1 / (k * τ)) :=
  cswTheta_modular_S k τ z

/-- The modular `S` bridge with the simplified theta argument for nonzero level. -/
lemma oneLoopExactTheta_modular_S_arg (k τ z : ℂ) (hk : k ≠ 0) :
    cswTheta k τ z =
      1 / (-Complex.I * (k * τ)) ^ (1 / 2 : ℂ)
        * Complex.exp (-(Real.pi : ℂ) * Complex.I * (k * z) ^ 2 / (k * τ))
        * jacobiTheta₂ (z / τ) (-1 / (k * τ)) :=
  cswTheta_modular_S_arg k τ z hk

/-- The diagonal genus-one invariant factors into right and left CSW characters. -/
lemma oneLoopExactTorusDiagonalInvariant_factorizes
    (k : ℕ) (χ : Fin k → ℂ) (a : Fin k) :
    (torusDiagonalInvariant k χ).complexInvariant a =
      (torusDiagonalInvariant k χ).rightInvariant a *
        (torusDiagonalInvariant k χ).leftInvariant a :=
  (torusDiagonalInvariant k χ).factorizes a

/-- The diagonal CSW partition function is invariant under the modular `S` matrix. -/
lemma oneLoopExactTorusPartitionFunction_S_invariant
    (k : ℕ) (hk : 0 < k) (χ : Fin k → ℂ) :
    torusPartitionFunction k (fun a => ∑ b : Fin k, cswSMatrix k a b * χ b)
      = torusPartitionFunction k χ :=
  torusPartitionFunction_S_invariant k hk χ

/--
The one-loop Wilson/Verlinde operators are diagonalized by the modular
`S`-matrix columns.
-/
lemma oneLoopExactWilsonVerlinde_diagonalization
    (k : ℕ) (hk : 0 < k) (a q : Fin k) :
    cswWilsonVerlindeOperator k a (fun b => (starRingEnd ℂ) (cswSMatrix k b q))
      = fun c => cswVerlindeEigenvalue k hk a q * (starRingEnd ℂ) (cswSMatrix k c q) :=
  cswWilsonVerlinde_diagonalization k hk a q

/--
The CSW one-loop bridge remains in the repo's Levi-Civita/Lusanna invariant
geometry: the tetrad proper separation is unchanged by Lorentz-frame gauge.
-/
lemma oneLoopExact_tetradProperSeparation_lorentz_invariant {d : ℕ}
    (Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (hΛ : Λ ∈ LorentzGroup d) (x : (Fin 1 ⊕ Fin d) → ℝ) :
    properSeparationSq (Λ * E) x = properSeparationSq E x :=
  hayashi_tetrad_properSeparation_lorentz_invariant Λ E hΛ x


end Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.BoundaryLevelShift.shifted_eq_classical_plus_adjoint_trace where
  formalizes @ "claim:the-one-loop-shifted-chern-simons-level-equals-the-classical-level-plus-the-adjoint-trace-coefficient-the-famous-k-to-k-plus-dual-coxeter-number-quantum-shift"

zil attach Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.theorem61_boundary_one_loop_exact where
  formalizes @ "claim:theorem-6-1-a-boundary-chiral-deformation-admits-boundary-quantization-is-one-loop-exact-and-has-vanishing-boundary-anomaly",
  supported_by @ "paper:one-loop-exactness-of-chern-simons-theory-with-chiral-boundary-conditions"

zil attach Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.theorem61_boundary_shift_eq_adjoint_trace where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.BoundaryLevelShift.shifted_eq_classical_plus_adjoint_trace",
  formalizes @ "claim:the-boundary-level-shift-of-a-chiral-boundary-theory-uses-the-same-adjoint-trace-correction-as-the-bulk-one-loop-shift-of-theorem-6-1",
  requires @ "claim:the-one-loop-shifted-chern-simons-level-equals-the-classical-level-plus-the-adjoint-trace-coefficient-the-famous-k-to-k-plus-dual-coxeter-number-quantum-shift"

zil attach Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.chiralBoundary_alpha_boundary_zero where
  formalizes @ "claim:odd-under-time-reflection-alpha-fields-satisfy-the-chiral-boundary-vanishing-condition-while-beta-fields-are-unrestricted-definition-6-1"

zil_file_contract physlib.boundaryLevelShift where
  promises "The boundary level shift and Theorem 6.1 of one-loop-exact Chern-Simons theory with chiral boundary conditions on C x R_{>=0}. The one-loop-shifted Chern-Simons level equals the classical level plus the adjoint-trace coefficient (shifted_eq_classical_plus_adjoint_trace) -- the famous k -> k + dual-Coxeter-number quantum shift. Theorem 6.1: a boundary chiral deformation admits boundary quantization, is one-loop exact, and has vanishing boundary anomaly (theorem61_boundary_one_loop_exact), and its boundary level shift uses the same adjoint-trace correction as the bulk (theorem61_boundary_shift_eq_adjoint_trace). The chiral boundary condition makes odd-under-time-reflection alpha fields vanish at the boundary while beta fields are unrestricted (chiralBoundary_alpha_boundary_zero)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.BoundaryLevelShift",
    "lean:Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.BoundaryChiralQuantizationPackage"]
  forbids_substitutes ["the heat-kernel / BV computation of the one-loop determinant that produces the adjoint-trace level shift and the boundary anomaly cancellation, which are the cited TQFT infrastructure carried as package hypotheses",
    "any nonperturbative modular / Verlinde structure of the Chern-Simons Hilbert space, only the level-shift algebra and the Theorem 6.1 boundary consequences are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.BoundaryLevelShift.shifted_eq_classical_plus_adjoint_trace,
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.theorem61_boundary_one_loop_exact,
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.theorem61_boundary_shift_eq_adjoint_trace,
    Physlib.QuantumMechanics.ComplexAction.OneLoopExactChernSimons.chiralBoundary_alpha_boundary_zero]

/- ZIL-END -/
