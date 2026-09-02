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
public import Physlib.QuantumMechanics.ComplexAction.WittenAnalyticContinuationChernSimons.GeneralEq531AndStokes

/-! # WittenAnalyticContinuationChernSimons — part `TrefoilKauffmanRepoLinks`. Full docstring in the umbrella module
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

/-! ## E. Links to existing trefoil, Kauffman, and Wilson-loop infrastructure -/

/-- The trefoil braid word used in the analytic-continuation/Jones-polynomial discussion is the existing
`B_3` trefoil carrier `(sigma1*sigma2)^2`. -/
lemma analyticContinuation_trefoilBraidWord {G : Type*} [Monoid G] {sigma1 sigma2 : G}
    (h : YangBaxter sigma1 sigma2) :
    (sigma1 * sigma2) ^ 2 = sigma1 * sigma1 * sigma2 * sigma1 :=
  trefoilBraidWord_eq h

/-- The same trefoil object has the already-formalized Temperley-Lieb/Kauffman bracket. This links the
analytic-continuation cycle formalization back to the algebraic knot invariant layer. -/
lemma analyticContinuation_trefoilKauffmanBracket (A : ℂ) (hA : A ≠ 0) :
    kauffmanClosure (kauffmanLoopValue A)
        (tlMul (kauffmanLoopValue A) (crossingTL A)
          (tlMul (kauffmanLoopValue A) (crossingTL A) (crossingTL A)))
      = A ^ 7 + A ^ 3 + A⁻¹ - (A ^ 9)⁻¹ :=
  trefoil_kauffman_bracket A hA

/-- Wilson-loop braiding in the analytically continued CSW/Jones layer reuses the existing Verlinde
`S`-matrix diagonalization carrier. -/
lemma analyticContinuation_wilsonBraiding_eq_S (k : ℕ) (hk : 0 < k) (a b : Fin k) :
    wilsonBraidingPhase k a b = (Real.sqrt k : ℂ) * (starRingEnd ℂ) (cswSMatrix k a b) :=
  wilsonBraidingPhase_eq_S k hk a b

/-! ## F. Integration with the rest of the repository -/

/-- The analytic-continuation exponent is linked to the Witten complex-CS coupling layer:
the integer level is still the half-sum of the holomorphic and anti-holomorphic couplings, the continuous
parameter is their normalized difference, and the trefoil nonabelian exponent is the quadratic
Picard-Lefschetz carrier. -/
lemma analyticContinuation_coupling_level_and_trefoilExponent
    (c : HayashiCouplings) (n gamma y : ℂ) :
    (holomorphicCoupling c + antiholomorphicCoupling c) / 2 = (c.level : ℂ)
      ∧ (holomorphicCoupling c - antiholomorphicCoupling c) / (2 * Complex.I) = c.s
      ∧ trefoilNonabelianExponent n gamma y =
        (-3 * (Real.pi : ℂ) * Complex.I * n * gamma⁻¹) * (gamma - y) ^ 2 := by
  exact ⟨level_eq_half_coupling_sum c, s_eq_coupling_diff c,
    trefoilNonabelianExponent_eq_quadratic n gamma y⟩

/-- Flat finite local CSW sectors give zero local complex action, while the analytic-continuation cycle
starts at the abelian trefoil thimble. This joins the concrete finite CSW synthesis to Witten's trefoil
Picard-Lefschetz starting cycle. -/
lemma analyticContinuation_flatLocalCSW_and_trefoilBirth {n : ℕ}
    (c : HayashiCouplings) (P : LocalCSConnection n × LocalCSConnection n)
    (hA : LocalCSFlat P.1) (hAbar : LocalCSFlat P.2) :
    localComplexCSWAction c P = 0
      ∧ trefoilCycle_near_zero .abelian = 1
      ∧ trefoilCycle_near_zero J1 = 0 := by
  exact ⟨localComplexCSWAction_eq_zero_of_flat c P hA hAbar,
    trefoilCycle_near_zero_abelian, trefoilCycle_near_zero_nonabelian y1⟩

/-- The existing analytic infrastructure supplies the checked hypotheses needed
to turn a height-ordered Chern-Simons Stokes connection into an actual
gradient-flow line in the repo carrier.

This theorem deliberately names the already-formalized pieces used by the
argument: finite local CSW gauge covariance and flatness, one-loop holomorphic
gauge/elliptic kernel data, Gaussian convergence estimates, large-wheel
compactness/finite-limit control, one-loop exact quantization/no-anomaly data,
and the `T³` Sobolev critical exponent carrier. -/
lemma analyticContinuation_existingInfrastructure_gives_gradientFlowLine
    {n : ℕ} (c : HayashiCouplings) (P : LocalCSConnection n × LocalCSConnection n)
    (G H : Matrix (Fin n) (Fin n) ℂ) (hHG : H * G = 1)
    (hA : LocalCSFlat P.1) (hAbar : LocalCSFlat P.2)
    (K : OneLoopExactChernSimons.HolomorphicGaugeKernelPackage) (φ : K.Field)
    (M : OneLoopExactChernSimons.GaussianMomentPackage)
    (W : OneLoopExactChernSimons.WheelAnalyticWeightPackage)
    (γ : W.Wheel) (hγ : 3 ≤ W.vertexCount γ)
    (Q : OneLoopExactChernSimons.ChiralDeformationQuantizationPackage)
    (T : Q.Theory) (hT : Q.isChiralDeformation T)
    (S : OperatorAlgebra.PicardLefschetzMorseContour.StokesConnection)
    (hheight : S.HeightOrdered) :
    localComplexCSWAction c
        (localGaugeConjugate G H P.1, localGaugeConjugate G H P.2)
      = localComplexCSWAction c P
      ∧ localComplexCSWAction c P = 0
      ∧ K.Laplacian φ = K.standardLaplacian φ
      ∧ M.wickMomentsControlledByInverseMatrix
      ∧ M.higherMomentsImproveEpsilonLimit
      ∧ W.finiteEpsilonLimit γ
      ∧ Q.admitsOneLoopExactQuantization T
      ∧ Q.finiteFeynmanWeights T
      ∧ Q.noUVAnomaly T
      ∧ Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereSobolevPerfectSquare.sobolevConjugate 3 = 6
      ∧ OperatorAlgebra.PicardLefschetzMorseContour.StokesAligned S.source S.target
      ∧ Nonempty (OperatorAlgebra.PicardLefschetzMorseContour.ChernSimonsGradientFlowLine S) := by
  have hgauge := localComplexCSWAction_gauge_conjugate c G H P hHG
  have hflat := localComplexCSWAction_eq_zero_of_flat c P hA hAbar
  have hkernel := OneLoopExactChernSimons.holomorphicGauge_laplacian_eq_standard K φ
  have hmoments := OneLoopExactChernSimons.gaussian_moments_control_convergence M
  have hwheel := OneLoopExactChernSimons.proposition43_large_wheels_finite W γ hγ
  have hq41 := OneLoopExactChernSimons.theorem41_finite_one_loop_exact Q T hT
  have hq51 := OneLoopExactChernSimons.theorem51_one_loop_exact_no_uv_anomaly Q T hT
  exact ⟨hgauge, hflat, hkernel, hmoments.1, hmoments.2, hwheel,
    hq41.1, hq41.2, hq51.2,
    NavierStokes.NSFieldFourierSobolevHierarchy.NSFieldFourier.sobolev_critical_three,
    S.aligned,
    OperatorAlgebra.PicardLefschetzMorseContour.chernSimonsGradientFlowLine_exists_of_heightOrdered
      S hheight⟩

/-- The analytic-continuation trefoil cycle is available at the same point where the repo proves the
CSW heat equation, theta/Poisson resummation, Verlinde convolution diagonalization, and Wilson-operator
diagonalization. This is the path-integral/tunneling diagonalization bridge consumed by later CSW files. -/
lemma analyticContinuation_cswDiagonalization_and_trefoilCycle
    (k : ℕ) (hk : 0 < k) (mode τ z : ℂ) (hτ : 0 < τ.im)
    (a q : Fin k) (f g : Fin k → ℂ) :
    (deriv (fun w => thetaMode (k : ℂ) mode w z) τ
        = (1 / (4 * Complex.I * (Real.pi : ℂ) * (k : ℂ)))
          * deriv (fun w => deriv (fun w' => thetaMode (k : ℂ) mode τ w') w) z
      ∧ (∑ b : Fin k, cswSMatrix k a b * cswThetaBasis k b τ z)
        = (1 / (Real.sqrt k : ℂ))
          * jacobiTheta₂ (z - (a.val : ℂ) / (k : ℂ)) (τ / (k : ℂ))
      ∧ (∀ x : Fin k,
        cswDFT (cswConvolution f g) x = (Real.sqrt k : ℂ) * cswDFT f x * cswDFT g x)
      ∧ cswWilsonVerlindeOperator k a (fun b => (starRingEnd ℂ) (cswSMatrix k b q))
        = fun c => cswVerlindeEigenvalue k hk a q * (starRingEnd ℂ) (cswSMatrix k c q))
      ∧ trefoilCycle_after_11_over_6 J1 = 1
      ∧ trefoilCycle_after_11_over_6 J5 = -1
      ∧ trefoilCycle_after_11_over_6 J7 = 1
      ∧ trefoilCycle_after_11_over_6 J11 = -1 := by
  have hdiag :=
    csw_heat_theta_convolution_wilson_diagonalization k hk mode τ z hτ a q f g
  have hcycle := trefoilCycle_after_11_over_6_coefficients
  exact ⟨hdiag, hcycle.2.1, hcycle.2.2.1, hcycle.2.2.2.1, hcycle.2.2.2.2⟩

/-- The Hopf/R-matrix carrier, Wilson braiding as Verlinde `S`, and the trefoil Stokes cycle are joined
in one statement. This lets the analytic-continuation thimble bookkeeping reuse the same algebraic
braiding layer as the Wilson-loop/Hopf-algebra files. -/
lemma analyticContinuation_hopfWilsonBraiding_and_trefoilCycle
    (s : ℂ) (hs : s ≠ 0) (k : ℕ) (hk : 0 < k) (a b : Fin k) :
    braidC1 s * braidC2 s * braidC1 s = braidC2 s * braidC1 s * braidC2 s
      ∧ wilsonBraidingPhase k a b
        = (Real.sqrt k : ℂ) * (starRingEnd ℂ) (cswSMatrix k a b)
      ∧ trefoilCycle_after_5_over_6 J1 = 1
      ∧ trefoilCycle_after_5_over_6 J5 = -1 := by
  have hhopf := hopf_rmatrix_yangBaxter_matches_wilson_braiding s hs k hk a b
  have hcycle := trefoilCycle_after_5_over_6_coefficients
  exact ⟨hhopf.1, hhopf.2, hcycle.2.1, hcycle.2.2.1⟩

/-- The analytic-continuation trefoil cycle feeds the same `S`-matrix orthogonality carrier used by the
Kálnay Bose-bilinear fermion-field bridge. Distinct `S`-charge sectors are orthogonal, and the field
statement is available together with the first nonabelian trefoil Stokes jump. -/
lemma analyticContinuation_sMatrixKalnayFields_and_trefoilJump
    (k : ℕ) (hk : 0 < k) (ψ φ : Fin k) (hψφ : ψ ≠ φ) (p : Momentum 3) :
    (cswSMatrixOrthogonalityCarrier k hk).inner ψ φ = 0
      ∧ KalnayBoseFermiFieldStatement p
      ∧ trefoilCycle_after_1_over_6 J1 = 1 := by
  have hfields := cswSMatrix_orthogonality_kalnay_fields k hk ψ φ hψφ p
  exact ⟨hfields.1, hfields.2, (trefoilCycle_after_1_over_6_coefficients).2.1⟩

/-- Witten's analytic-continuation trefoil cycle is connected to the repo's non-pointlike three-nodule
Dirac trefoil phase region: the phase-region theorem supplies the three internal nodules, counter-rotation,
one-turn magnitudes, trefoil braid word, and spinor/ribbon holonomy, while the analytic layer supplies the
four-jump Picard-Lefschetz cycle. -/
lemma analyticContinuation_threeNoduleRegion_and_trefoilCycle {G : Type*} [Monoid G]
    (R : ThreeNodulePhaseRegion) {sigma1 sigma2 : G}
    (h : RealizesTrefoilBraid sigma1 sigma2) :
    trefoilCycle_after_11_over_6 .abelian = 1
      ∧ trefoilCycle_after_11_over_6 J1 = 1
      ∧ trefoilCycle_after_11_over_6 J5 = -1
      ∧ trefoilCycle_after_11_over_6 J7 = 1
      ∧ trefoilCycle_after_11_over_6 J11 = -1
      ∧ Fintype.card Nodule = 3
      ∧ (phaseNetwork R).IsDecoupled
      ∧ R.turn 1 = -R.turn 0
      ∧ R.turn 2 = -R.turn 0
      ∧ (∀ i : Nodule, (R.phase i R.period - R.phase i 0) ^ 2 = (2 * Real.pi) ^ 2)
      ∧ (∀ i : Nodule, (phaseNetwork R).freeTrajectory i R.period =
          R.phase i R.period - R.phase i 0)
      ∧ (sigma1 * sigma2) ^ 2 = sigma1 * sigma1 * sigma2 * sigma1
      ∧ spinorThreeTurnHolonomy = ribbonTwist (1 / 2) := by
  have hcycle := trefoilCycle_after_11_over_6_coefficients
  have hregion := three_lobed_dirac_trefoil_phase_region R h
  exact ⟨hcycle.1, hcycle.2.1, hcycle.2.2.1, hcycle.2.2.2.1, hcycle.2.2.2.2,
    hregion.1, hregion.2.1, hregion.2.2.1, hregion.2.2.2.1, hregion.2.2.2.2.1,
    hregion.2.2.2.2.2.1, hregion.2.2.2.2.2.2.1, hregion.2.2.2.2.2.2.2⟩


end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
