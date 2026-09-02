/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenJonesPolynomialChernSimons
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ThetaModular
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonOperators
public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic
public import Physlib.QFT.PathIntegral.RigorousComplexFK
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # ABJMWilsonLoopsFermiGas — part `AnchorsBPSWilsonLoops`. Full paper docstring in the umbrella module `Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas`; namespace and
declaration names are unchanged across the parts (the umbrella re-exports them). -/

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory
open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic
@[expose] public section
namespace Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas


/-- Local bibliographic/source record for the ABJM Wilson-loop paper. -/
structure ABJMWilsonLoopsPaperReference where
  title : String
  author : String
  identifier : String
  localPdf : String
  deriving Repr, DecidableEq

/-- The local ABJM Wilson-loop source inspected for this formalization. -/
def abjmWilsonLoopsPaperReference : ABJMWilsonLoopsPaperReference :=
  { title := "Wilson loops in ABJM theory reloaded"
    author := "Bercel Boldis, Gregory P. Korchemsky, Alessandro Testa"
    identifier := "arXiv:2512.02119v3"
    localPdf := "Wilson loops in ABJM theory reloaded-2512.02119v3.pdf" }

/-- Stable anchors for the ABJM Wilson-loop claims formalized below. -/
inductive ABJMWilsonLoopsAnchor where
  | oneSixthWilsonDefinition
  | oneHalfWilsonLinearCombination
  | unnormalizedNormalization
  | convergenceLevelBound
  | abelianNOneClosedForm
  | fermiGasKernel
  | kernelOperatorFactorization
  | fugacityChemicalPotential
  | wZeroDerivativeLogXi
  | coefficientExtraction
  | grandCanonicalGenerating
  | fredholmDeterminant
  | determinantRatioFreeEnergy
  | tracyWidomPsiSystem
  | psiParityAndShift
  | phaseQuantization
  | potentialRecurrence
  | resolventWilsonTrace
  | fermiGasPlanckConstant
  | oneSixthDecomposition
  | halfBPSCancellation
  | explicitCoefficientFunctions
  | exactHalfBPSCoefficient
  | kSixAOnePolynomial
  | aTwoFromAOne
  | weakCouplingExpansion
  | largeMuWilsonLeading
  | largeMuConstantTerm
  | kFourClosedForm
  | nTwoFromNOneClosedForm
  deriving Repr, DecidableEq

/-- Paper locator for each formalized ABJM Wilson-loop anchor. -/
def ABJMWilsonLoopsAnchor.paperLabel : ABJMWilsonLoopsAnchor → String
  | .oneSixthWilsonDefinition => "Equation (1.1)"
  | .oneHalfWilsonLinearCombination => "Equation (1.2)"
  | .unnormalizedNormalization => "Equation (2.2)"
  | .convergenceLevelBound => "Equation (2.3)"
  | .abelianNOneClosedForm => "Equation (2.4)"
  | .fermiGasKernel => "Equations (2.9)-(2.10)"
  | .kernelOperatorFactorization => "Equation (2.12)"
  | .fugacityChemicalPotential => "Equation (2.7)"
  | .wZeroDerivativeLogXi => "Equation (2.6)"
  | .coefficientExtraction => "Equations (2.5), (2.8), (2.15)"
  | .grandCanonicalGenerating => "Equations (2.5)-(2.6)"
  | .fredholmDeterminant => "Equation (2.11)"
  | .determinantRatioFreeEnergy => "Equations (3.8)-(3.10)"
  | .tracyWidomPsiSystem => "Equations (3.1)-(3.22)"
  | .psiParityAndShift => "Equations (3.26)-(3.29)"
  | .phaseQuantization => "Equations (4.1)-(4.23)"
  | .potentialRecurrence => "Equations (4.24)-(4.28), (5.12)-(5.15), Appendix C-D"
  | .resolventWilsonTrace => "Equations (2.13)-(2.14)"
  | .fermiGasPlanckConstant => "Section 2.2"
  | .oneSixthDecomposition => "Equation (5.16)"
  | .halfBPSCancellation => "Equation (5.19)"
  | .explicitCoefficientFunctions => "Equations (5.17)-(5.18)"
  | .exactHalfBPSCoefficient => "Equations (5.16)-(5.19)"
  | .kSixAOnePolynomial => "Equation (5.22)"
  | .aTwoFromAOne => "Equation (5.23)"
  | .weakCouplingExpansion => "Equations (5.24)-(5.26)"
  | .largeMuWilsonLeading => "Equations (6.1)-(6.12)"
  | .largeMuConstantTerm => "Equation (6.13)"
  | .kFourClosedForm => "Equations (1.3), (5.21)"
  | .nTwoFromNOneClosedForm => "Equations (1.4), (5.23)"

/-- ABJM parameters: rank `N` and positive Chern-Simons level `k`. -/
structure ABJMParameters where
  rank : ℕ
  level : ℕ
  rank_pos : 0 < rank
  level_pos : 0 < level

/-- The Fermi-gas effective Planck constant of the ABJM matrix model, `hbar = 2πk`. -/
noncomputable def ABJMParameters.effectivePlanck (p : ABJMParameters) : ℝ :=
  2 * Real.pi * (p.level : ℝ)

/-- The 't Hooft coupling `λ = N/k` used in the large-rank regime. -/
noncomputable def ABJMParameters.tHooftCoupling (p : ABJMParameters) : ℝ :=
  (p.rank : ℝ) / (p.level : ℝ)

/-- **[ABJM Fermi-gas Planck constant]** Section 2.2 identifies `hbar = 2πk`. -/
lemma abjm_effectivePlanck_eq_two_pi_level (p : ABJMParameters) :
    p.effectivePlanck = 2 * Real.pi * (p.level : ℝ) :=
  rfl

/-- Local complex hyperbolic sine used to keep the ABJM coefficient formulas independent of namespace
choices for hyperbolic functions. -/
noncomputable def abjmCSinh (x : ℂ) : ℂ :=
  (Complex.exp x - Complex.exp (-x)) / 2

/-- Local complex hyperbolic cosine used in the ABJM coefficient and phase formulas. -/
noncomputable def abjmCCosh (x : ℂ) : ℂ :=
  (Complex.exp x + Complex.exp (-x)) / 2

/-- Local complex sine, used for phase quantization formulas with complexified phases. -/
noncomputable def abjmCSin (x : ℂ) : ℂ :=
  (Complex.exp (Complex.I * x) - Complex.exp (-Complex.I * x)) / (2 * Complex.I)

/-- Local complex cosine, used for phase quantization formulas with complexified phases. -/
noncomputable def abjmCCos (x : ℂ) : ℂ :=
  (Complex.exp (Complex.I * x) + Complex.exp (-Complex.I * x)) / 2

/-- The coordinate factor `χ(x)=1/(2 cosh(x/2))` appearing in equations (3.3) and (3.11). -/
noncomputable def abjmChiReal (x : ℝ) : ℝ :=
  1 / (2 * Real.cosh (x / 2))

/-- Complexified coordinate factor `χ(x)=1/(2 cosh(x/2))` for the Tracy-Widom carriers. -/
noncomputable def abjmChiComplex (x : ℂ) : ℂ :=
  1 / (2 * abjmCCosh (x / 2))

/-- The coordinate-space kernel of the momentum factor `1/(2 cosh(p/2))` in equation (2.12). -/
noncomputable def abjmMomentumCoshKernel (k x y : ℝ) : ℝ :=
  1 / (2 * Real.cosh ((x - y) / (2 * k)))

/-- The Fermi-gas kernel in equation (2.10):
`ρ(x,y)=1/(8πk cosh(x/2) cosh((x-y)/(2k)))`. -/
noncomputable def abjmFermiGasKernel (k x y : ℝ) : ℝ :=
  1 / (8 * Real.pi * k * Real.cosh (x / 2) * Real.cosh ((x - y) / (2 * k)))

/-- For positive level, the Fermi-gas kernel is strictly positive. -/
lemma abjmFermiGasKernel_pos (k x y : ℝ) (hk : 0 < k) :
    0 < abjmFermiGasKernel k x y := by
  unfold abjmFermiGasKernel
  positivity

/-- **[Equation (2.12), kernel factorization]** The printed kernel (2.10) is the product of the
coordinate factor `χ(x)`, the momentum-cosh kernel, and the Fourier normalization `1/(2πk)`. -/
lemma abjmFermiGasKernel_eq_chi_momentumKernel
    (k x y : ℝ) (hk : k ≠ 0) :
    abjmFermiGasKernel k x y =
      abjmChiReal x * abjmMomentumCoshKernel k x y / (2 * Real.pi * k) := by
  have hx : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hy : Real.cosh ((x - y) / (2 * k)) ≠ 0 := (Real.cosh_pos _).ne'
  unfold abjmFermiGasKernel abjmChiReal abjmMomentumCoshKernel
  field_simp [hk, hx, hy]
  ring

/-- **[Opposite CS levels]** ABJM contains two Chern-Simons sectors with levels `k` and `-k`. -/
lemma abjm_opposite_csimons_levels_sum_zero (k : ℤ) :
    k + (-k) = 0 := by
  ring

/-- The localization integral for winding `n` is in the paper's convergent range when `k > 2n`. -/
def ABJMWilsonConvergentLevel (k n : ℕ) : Prop :=
  2 * n < k

/-- **[Equation (2.3)]** The convergence condition is exactly `k > 2n`. -/
lemma abjm_convergentLevel_iff (k n : ℕ) :
    ABJMWilsonConvergentLevel k n ↔ 2 * n < k :=
  Iff.rfl

/-- At the pole `k = 2n`, the localization convergence condition `k > 2n` fails. -/
lemma abjm_not_convergent_at_pole (n : ℕ) :
    ¬ ABJMWilsonConvergentLevel (2 * n) n := by
  unfold ABJMWilsonConvergentLevel
  omega

/-- The Abelian `N = 1` closed form from equation (2.4). -/
noncomputable def abjmAbelianNOneWilson (n : ℕ) (k : ℝ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi : ℂ) * (n : ℂ) ^ 2 / (k : ℂ)) /
    ((4 : ℂ) * (k : ℂ) * (Real.cos (Real.pi * (n : ℝ) / k) : ℂ) ^ 2)

/-- Clearing the denominator in the `N = 1` closed form recovers its oscillatory numerator. -/
lemma abjmAbelianNOneWilson_mul_denominator (n : ℕ) (k : ℝ)
    (hden : (4 : ℂ) * (k : ℂ) * (Real.cos (Real.pi * (n : ℝ) / k) : ℂ) ^ 2 ≠ 0) :
    abjmAbelianNOneWilson n k *
        ((4 : ℂ) * (k : ℂ) * (Real.cos (Real.pi * (n : ℝ) / k) : ℂ) ^ 2)
      = Complex.exp (Complex.I * (Real.pi : ℂ) * (n : ℂ) ^ 2 / (k : ℂ)) := by
  unfold abjmAbelianNOneWilson
  exact div_mul_cancel₀
    (Complex.exp (Complex.I * (Real.pi : ℂ) * (n : ℂ) ^ 2 / (k : ℂ))) hden


/-- **[Equation (2.2), partition side]** The ABJM partition function is `Z = W₀/N` in the paper's
unnormalized convention. -/
noncomputable def abjmPartitionFromUnnormalized (N : ℕ) (W0 : ℂ) : ℂ :=
  W0 / (N : ℂ)

/-- **[Equation (2.2), Wilson side]** The normalized `1/6` BPS Wilson loop is `W_n/W_0`. -/
noncomputable def abjmOneSixthWilson (W0 Wn : ℂ) : ℂ :=
  Wn / W0

/-- The ABJM `1/6` normalization is Witten's normalized expectation convention. -/
lemma abjmOneSixthWilson_eq_wittenNormalizedExpectation (W0 Wn : ℂ) :
    abjmOneSixthWilson W0 Wn = normalizedExpectation W0 Wn :=
  rfl

/-- If the vacuum/unwound amplitude is nonzero, multiplying the normalized `1/6` loop by `W₀`
recovers the unnormalized loop. -/
lemma abjm_oneSixthWilson_mul_vacuum (W0 Wn : ℂ) (hW0 : W0 ≠ 0) :
    abjmOneSixthWilson W0 Wn * W0 = Wn := by
  unfold abjmOneSixthWilson
  field_simp [hW0]

/-- **[Equation (2.2), `n = 0`]** The normalized `1/6` Wilson loop at zero winding is `1`. -/
lemma abjm_oneSixthWilson_zero_winding (W0 : ℂ) (hW0 : W0 ≠ 0) :
    abjmOneSixthWilson W0 W0 = 1 := by
  unfold abjmOneSixthWilson
  field_simp [hW0]

/-- **[Equation (1.2)]** The `1/2` BPS Wilson loop is the signed linear combination of the two
opposite-level `1/6` BPS Wilson loops.  The second argument is the loop in the `-k` sector, equivalently
the conjugate sector in the paper's convention. -/
noncomputable def abjmOneHalfWilson (n : ℕ) (positiveLevel negativeLevel : ℂ) : ℂ :=
  positiveLevel - (-1 : ℂ) ^ n * negativeLevel

/-- **[Equation (1.2), `n = 0`]** With both zero-winding `1/6` loops normalized to `1`, the `1/2`
BPS Wilson loop is normalized to `0`. -/
lemma abjm_oneHalfWilson_zero_winding :
    abjmOneHalfWilson 0 1 1 = 0 := by
  simp [abjmOneHalfWilson]

/-- If the winding parity contributes phase `+1`, the `1/2` loop is the difference of the two
opposite-level sectors. -/
lemma abjm_oneHalfWilson_of_phase_one
    (n : ℕ) (Wplus Wminus : ℂ) (hphase : (-1 : ℂ) ^ n = 1) :
    abjmOneHalfWilson n Wplus Wminus = Wplus - Wminus := by
  simp [abjmOneHalfWilson, hphase]

/-- If the winding parity contributes phase `-1`, the `1/2` loop is the sum of the two opposite-level
sectors. -/
lemma abjm_oneHalfWilson_of_phase_neg_one
    (n : ℕ) (Wplus Wminus : ℂ) (hphase : (-1 : ℂ) ^ n = -1) :
    abjmOneHalfWilson n Wplus Wminus = Wplus + Wminus := by
  simp [abjmOneHalfWilson, hphase]

/-- The ABJM `1/2` BPS signed difference is also Witten's normalized expectation of the signed
unnormalized Wilson insertion. -/
lemma abjmOneHalfWilson_eq_wittenNormalizedExpectation_signed_difference
    (n : ℕ) (W0 Wplus Wminus : ℂ) :
    abjmOneHalfWilson n (normalizedExpectation W0 Wplus) (normalizedExpectation W0 Wminus) =
      normalizedExpectation W0 (Wplus - (-1 : ℂ) ^ n * Wminus) := by
  unfold abjmOneHalfWilson normalizedExpectation
  ring


end Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas

end
