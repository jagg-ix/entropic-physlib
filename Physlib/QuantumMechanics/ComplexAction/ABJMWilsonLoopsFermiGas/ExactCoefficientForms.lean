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
public import Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas.FermiGasTracyWidom

/-! # ABJMWilsonLoopsFermiGas — part `ExactCoefficientForms`. Full paper docstring in the umbrella module `Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas`; namespace and
declaration names are unchanged across the parts (the umbrella re-exports them). -/

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory
open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic
@[expose] public section
namespace Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas


/-- The paper's `1/2` BPS generating function in terms of the coefficient `A_n`, equation (5.19):
`2 i^(n-1) A_n / sin(2πn/k)`. -/
noncomputable def abjmHalfBPSFromA (n : ℕ) (k : ℝ) (A : ℂ) : ℂ :=
  (2 * Complex.I ^ (n - 1) / (Real.sin (2 * Real.pi * (n : ℝ) / k) : ℂ)) * A

/-- The prefactor `i^(n-1)/sin(2πn/k)` in the `1/6` generating function decomposition (5.16). -/
noncomputable def abjmOneSixthGeneratingPrefactor (n : ℕ) (k : ℝ) : ℂ :=
  Complex.I ^ (n - 1) / (Real.sin (2 * Real.pi * (n : ℝ) / k) : ℂ)

/-- The bracket in (5.16): `A_n + i z∂zΦ B_n + i z∂zF C_n`. -/
noncomputable def abjmOneSixthGeneratingBracket
    (A zDerivPhi B zDerivF C : ℂ) : ℂ :=
  A + Complex.I * zDerivPhi * B + Complex.I * zDerivF * C

/-- Cotangent used throughout the ABJM coefficient and large-`µ` formulas. -/
noncomputable def abjmCot (x : ℝ) : ℝ :=
  Real.cos x / Real.sin x

/-- **[Equation (5.17)]** `A₁=sinh(F) sin(Φ)`. -/
noncomputable def abjmCoeffA1 (F : ℂ) (phi : ℝ) : ℂ :=
  abjmCSinh F * (Real.sin phi : ℂ)

/-- **[Equation (5.17)]** `B₁=-sinh(F)(2 cot(2π/k) cos Φ + sin Φ)`. -/
noncomputable def abjmCoeffB1 (k : ℝ) (F : ℂ) (phi : ℝ) : ℂ :=
  -abjmCSinh F *
    (2 * (abjmCot (2 * Real.pi / k) : ℂ) * (Real.cos phi : ℂ) + (Real.sin phi : ℂ))

/-- **[Equation (5.17)]** The `C₁` coefficient. -/
noncomputable def abjmCoeffC1 (k : ℝ) (F : ℂ) (phi : ℝ) : ℂ :=
  -abjmCSinh F * (Real.cos phi : ℂ)
    - abjmCCosh F *
      (2 * (abjmCot (2 * Real.pi / k) : ℂ) * (Real.sin phi : ℂ) - (Real.cos phi : ℂ))

/-- **[Equation (5.18)]** The `A₂` coefficient before eliminating the phase. -/
noncomputable def abjmCoeffA2 (k : ℝ) (F : ℂ) (phi : ℝ) : ℂ :=
  (abjmCCosh (2 * F) - 1) *
      ((Real.cos (2 * Real.pi / k) : ℂ) ^ 2 - (Real.cos (2 * phi) : ℂ))
    + abjmCSinh (2 * F) * (Real.sin (2 * Real.pi / k) : ℂ) ^ 2

/-- **[Equation (5.18)]** The `B₂` coefficient. -/
noncomputable def abjmCoeffB2 (k : ℝ) (F : ℂ) (phi : ℝ) : ℂ :=
  (abjmCCosh (2 * F) - 1) *
      ((Real.cos (2 * phi) : ℂ)
        - (2 * (2 * (Real.cos (4 * Real.pi / k) : ℂ) + 1)
            / (Real.sin (4 * Real.pi / k) : ℂ)) * (Real.sin (2 * phi) : ℂ)
        - (1 / 2 : ℂ) * ((Real.cos (4 * Real.pi / k) : ℂ) + 3))
    + abjmCSinh (2 * F) * (Real.cos (2 * Real.pi / k) : ℂ) ^ 2

/-- **[Equation (5.18)]** The `C₂` coefficient. -/
noncomputable def abjmCoeffC2 (k : ℝ) (F : ℂ) (phi : ℝ) : ℂ :=
  -(abjmCCosh (2 * F) - 1) *
      ((Real.cos (4 * Real.pi / k) : ℂ) * (Real.tan (2 * Real.pi / k) : ℂ)
        + (Real.sin (2 * phi) : ℂ))
    - (Real.cos (4 * Real.pi / k) : ℂ) * (Real.tan (2 * Real.pi / k) : ℂ)
    + abjmCSinh (2 * F) *
      ((Real.sin (2 * phi) : ℂ)
        + (2 * (2 * (Real.cos (4 * Real.pi / k) : ℂ) + 1)
            / (Real.sin (4 * Real.pi / k) : ℂ)) * (Real.cos (2 * phi) : ℂ)
        - ((Real.cos (4 * Real.pi / k) : ℂ) + 2)
          * (abjmCot (2 * Real.pi / k) : ℂ))

/-- Coefficient triple for the first winding, equations (5.17). -/
noncomputable def abjmCoeffTripleOne (k : ℝ) (F : ℂ) (phi : ℝ) : ℂ × ℂ × ℂ :=
  (abjmCoeffA1 F phi, abjmCoeffB1 k F phi, abjmCoeffC1 k F phi)

/-- Coefficient triple for the second winding, equations (5.18). -/
noncomputable def abjmCoeffTripleTwo (k : ℝ) (F : ℂ) (phi : ℝ) : ℂ × ℂ × ℂ :=
  (abjmCoeffA2 k F phi, abjmCoeffB2 k F phi, abjmCoeffC2 k F phi)

/-- **[Equation (5.22)]** Polynomial equation for `A₁` at `k=6`, written as a vanishing residual. -/
noncomputable def abjmKSixAOnePolynomial (z F A1 : ℂ) : ℂ :=
  (64 * A1 ^ 3 + 24 * A1 - z) ^ 2
    - 9 * (256 * A1 ^ 4 + 96 * A1 ^ 2 - 4 * z * A1 + 3) * Complex.exp (-2 * F)
    + 54 * (8 * A1 ^ 2 + 1) * Complex.exp (-4 * F)
    - 27 * Complex.exp (-6 * F)

/-- **[Equation (5.24)]** Large-`k` expansion of the Tracy-Widom `ψ` function through `1/k³`,
with the `O(1/k⁴)` tail omitted and represented by the surrounding asymptotic carrier. -/
noncomputable def abjmPsiWeakCouplingTruncation (x z : ℂ) (k : ℝ) : ℂ :=
  2 *
    (1 + (2 * x + z) / (4 * (k : ℂ))
      + (2 * x ^ 2 + z ^ 2) / (16 * (k : ℂ) ^ 2)
      + (4 * x ^ 3 - 6 * x ^ 2 * z + 3 * z ^ 3) / (192 * (k : ℂ) ^ 3))

/-- **[Equation (5.25)]** Large-`k` phase expansion through `1/k⁶`, omitting the `O(1/k⁸)` tail. -/
noncomputable def abjmPhaseWeakCouplingTruncation (z : ℂ) (k : ℝ) : ℂ :=
  (Real.pi : ℂ) / (k : ℂ)
    - (Real.pi : ℂ) * z / (4 * (k : ℂ) ^ 2)
    + (Real.pi : ℂ) ^ 3 * z / (24 * (k : ℂ) ^ 4)
    + (5 * (Real.pi : ℂ) ^ 3 * z ^ 3 - 128 * (Real.pi : ℂ) ^ 5 * z) /
      (3840 * (k : ℂ) ^ 6)

/-- **[Equation (5.25)]** Large-`k` free-energy expansion through `1/k⁷`,
omitting the `O(1/k⁹)` tail. -/
noncomputable def abjmFreeEnergyWeakCouplingTruncation (z : ℂ) (k : ℝ) : ℂ :=
  z / (2 * (k : ℂ))
    + z ^ 3 / (96 * (k : ℂ) ^ 3)
    + (z ^ 5 - 20 * (Real.pi : ℂ) ^ 2 * z ^ 3) / (2560 * (k : ℂ) ^ 5)
    + (3 * z ^ 7 - 84 * (Real.pi : ℂ) ^ 2 * z ^ 5
        + 1792 * (Real.pi : ℂ) ^ 4 * z ^ 3) /
      (172032 * (k : ℂ) ^ 7)

/-- **[Equation (5.26)]** Weak-coupling expansion of `Wₙ(z,k)` through `1/k⁴`,
with the `O(1/k⁵)` tail carried separately by asymptotic hypotheses. -/
noncomputable def abjmWilsonWeakCouplingTruncation (n : ℕ) (z : ℂ) (k : ℝ) : ℂ :=
  z / (4 * (k : ℂ))
    + z * (-z + 4 * Complex.I * (Real.pi : ℂ) * (n : ℂ) ^ 2) / (16 * (k : ℂ) ^ 2)
    + z *
      (-8 * (Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 4
        + 4 * (Real.pi : ℂ) * (n : ℂ) ^ 2 * (4 * (Real.pi : ℂ) - Complex.I * z)
        + z ^ 2) / (64 * (k : ℂ) ^ 3)
    + z *
      (12 * Complex.I * (Real.pi : ℂ) * (n : ℂ) ^ 2 * z ^ 2
        + 24 * (Real.pi : ℂ) ^ 2 * ((n : ℂ) ^ 2 - 1) ^ 2 * z
        - 32 * Complex.I * (Real.pi : ℂ) ^ 3 * ((n : ℂ) ^ 2 - 6) * (n : ℂ) ^ 4
        - 3 * z ^ 3) / (768 * (k : ℂ) ^ 4)

/-- Carrier tying the printed weak-coupling truncations (5.24)-(5.26) to concrete functions. -/
structure ABJMWeakCouplingExpansionCarrier where
  level : ℝ
  psi : ℂ → ℂ → ℂ
  phase : ℂ → ℂ
  freeEnergy : ℂ → ℂ
  wilsonGenerating : ℕ → ℂ → ℂ
  psi_trunc : ∀ x z, psi x z = abjmPsiWeakCouplingTruncation x z level
  phase_trunc : ∀ z, phase z = abjmPhaseWeakCouplingTruncation z level
  freeEnergy_trunc : ∀ z, freeEnergy z = abjmFreeEnergyWeakCouplingTruncation z level
  wilson_trunc : ∀ n z, wilsonGenerating n z = abjmWilsonWeakCouplingTruncation n z level

/-- The Wilson-loop weak-coupling truncation is the printed equation (5.26). -/
lemma ABJMWeakCouplingExpansionCarrier.wilson_eq_truncation
    (E : ABJMWeakCouplingExpansionCarrier) (n : ℕ) (z : ℂ) :
    E.wilsonGenerating n z = abjmWilsonWeakCouplingTruncation n z E.level :=
  E.wilson_trunc n z

/-- A carrier for the printed explicit coefficient functions in (5.17)-(5.18). -/
structure ABJMExplicitCoefficientCarrier where
  level : ℝ
  F : ℂ → ℂ
  phase : ℂ → ℝ
  A : ℕ → ℂ → ℂ
  B : ℕ → ℂ → ℂ
  C : ℕ → ℂ → ℂ
  A_one : ∀ z, A 1 z = abjmCoeffA1 (F z) (phase z)
  B_one : ∀ z, B 1 z = abjmCoeffB1 level (F z) (phase z)
  C_one : ∀ z, C 1 z = abjmCoeffC1 level (F z) (phase z)
  A_two : ∀ z, A 2 z = abjmCoeffA2 level (F z) (phase z)
  B_two : ∀ z, B 2 z = abjmCoeffB2 level (F z) (phase z)
  C_two : ∀ z, C 2 z = abjmCoeffC2 level (F z) (phase z)

/-- The first-winding coefficient triple is exactly equation (5.17). -/
lemma ABJMExplicitCoefficientCarrier.coeff_one_eq
    (E : ABJMExplicitCoefficientCarrier) (z : ℂ) :
    (E.A 1 z, E.B 1 z, E.C 1 z) =
      abjmCoeffTripleOne E.level (E.F z) (E.phase z) := by
  simp [abjmCoeffTripleOne, E.A_one z, E.B_one z, E.C_one z]

/-- The second-winding coefficient triple is exactly equation (5.18). -/
lemma ABJMExplicitCoefficientCarrier.coeff_two_eq
    (E : ABJMExplicitCoefficientCarrier) (z : ℂ) :
    (E.A 2 z, E.B 2 z, E.C 2 z) =
      abjmCoeffTripleTwo E.level (E.F z) (E.phase z) := by
  simp [abjmCoeffTripleTwo, E.A_two z, E.B_two z, E.C_two z]

/-- **[(5.16) to (5.19), algebraic cancellation]** If the signed opposite-level sector has the same
imaginary bracket but the opposite `A_n` term, then the `1/2` BPS combination cancels the imaginary
pieces and leaves `2 prefactor * A_n`. -/
lemma abjmOneHalfWilson_cancellation_from_decomposition
    (n : ℕ) (pref A X Wplus Wminus : ℂ)
    (hplus : Wplus = pref * (A + X))
    (hminus : (-1 : ℂ) ^ n * Wminus = pref * (-A + X)) :
    abjmOneHalfWilson n Wplus Wminus = 2 * pref * A := by
  unfold abjmOneHalfWilson
  rw [hplus, hminus]
  ring

/-- **[Equation (5.19) from (5.16)]** The coefficient `A_n` determines the `1/2` BPS generating function
once the signed opposite-level sector cancels the derivative terms. -/
lemma abjmOneHalfWilson_eq_halfBPSFromA_of_516
    (n : ℕ) (k : ℝ) (A X Wplus Wminus : ℂ)
    (hplus : Wplus = abjmOneSixthGeneratingPrefactor n k * (A + X))
    (hminus :
      (-1 : ℂ) ^ n * Wminus = abjmOneSixthGeneratingPrefactor n k * (-A + X)) :
    abjmOneHalfWilson n Wplus Wminus = abjmHalfBPSFromA n k A := by
  rw [abjmOneHalfWilson_cancellation_from_decomposition n
    (abjmOneSixthGeneratingPrefactor n k) A X Wplus Wminus hplus hminus]
  unfold abjmHalfBPSFromA abjmOneSixthGeneratingPrefactor
  ring

/-- The coefficient relation (5.23):
`A₂ = 4 A₁² + (1 - exp(-2F)) sin²(2π/k)`. -/
noncomputable def abjmA2FromA1 (k : ℝ) (F A1 : ℂ) : ℂ :=
  4 * A1 ^ 2 + (1 - Complex.exp (-2 * F)) *
    (Real.sin (2 * Real.pi / k) : ℂ) ^ 2

lemma abjmA2FromA1_eq (k : ℝ) (F A1 : ℂ) :
    abjmA2FromA1 k F A1 =
      4 * A1 ^ 2 + (1 - Complex.exp (-2 * F)) *
        (Real.sin (2 * Real.pi / k) : ℂ) ^ 2 := rfl

/-- The large-`µ` constant term `C_n(k) = -Σ_{m=1}^n cot(2πm/k)`, equation (6.13). -/
noncomputable def abjmLargeMuConstantTerm (n : ℕ) (k : ℝ) : ℂ :=
  -∑ m ∈ Finset.Icc 1 n, (abjmCot (2 * Real.pi * (m : ℝ) / k) : ℂ)

lemma abjmLargeMuConstantTerm_eq_sum (n : ℕ) (k : ℝ) :
    abjmLargeMuConstantTerm n k =
      -∑ m ∈ Finset.Icc 1 n, (abjmCot (2 * Real.pi * (m : ℝ) / k) : ℂ) := rfl

@[simp] lemma abjmLargeMuConstantTerm_zero (k : ℝ) :
    abjmLargeMuConstantTerm 0 k = 0 := by
  simp [abjmLargeMuConstantTerm]

lemma abjmLargeMuConstantTerm_one (k : ℝ) :
    abjmLargeMuConstantTerm 1 k = -(abjmCot (2 * Real.pi / k) : ℂ) := by
  simp [abjmLargeMuConstantTerm]

/-- The cotangent sum appearing in the pre-substitution large-`µ` formula (6.9). -/
noncomputable def abjmLargeMuCotSum (n : ℕ) (k : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 n, (abjmCot (2 * Real.pi * (m : ℝ) / k) : ℂ)

/-- The constant term (6.13) is minus the cotangent sum of (6.9). -/
lemma abjmLargeMuConstantTerm_eq_neg_cotSum (n : ℕ) (k : ℝ) :
    abjmLargeMuConstantTerm n k = -abjmLargeMuCotSum n k := by
  rfl

/-- **[Equation (6.12), leading phase]** The polynomial part of the large-`µ` phase, with the
exponentially small tail omitted. -/
noncomputable def abjmLargeMuPhaseLeading (k : ℝ) (mu : ℂ) : ℂ :=
  -(2 / ((Real.pi : ℂ) * (k : ℂ))) * mu ^ 2
    - (Real.pi : ℂ) * (k : ℂ) / 24
    + (Real.pi : ℂ) / 2
    + (Real.pi : ℂ) / (3 * (k : ℂ))

/-- Derivative of the leading phase polynomial in (6.12). -/
noncomputable def abjmLargeMuPhaseDerivativeLeading (k : ℝ) (mu : ℂ) : ℂ :=
  -4 * mu / ((Real.pi : ℂ) * (k : ℂ))

/-- **[Equation (6.9)]** Leading large-`µ` Wilson generating function before substituting the
large-`µ` phase derivative. -/
noncomputable def abjmLargeMuWilsonLeadingRaw
    (n : ℕ) (k : ℝ) (mu phiPrime : ℂ) : ℂ :=
  Complex.I ^ (n - 1) * Complex.exp (2 * (n : ℂ) * mu / (k : ℂ)) /
    ((k : ℂ) * (Real.sin (2 * Real.pi * (n : ℝ) / k) : ℂ)) *
      ((k : ℂ) / 4 - Complex.I * ((k : ℂ) / 4 * phiPrime + abjmLargeMuCotSum n k))

/-- **[Equation (6.1)]** Leading large-`µ` Wilson generating function after using (6.12) and (6.13). -/
noncomputable def abjmLargeMuWilsonLeading (n : ℕ) (k : ℝ) (mu : ℂ) : ℂ :=
  Complex.I ^ (n - 1) * Complex.exp (2 * (n : ℂ) * mu / (k : ℂ)) /
    ((k : ℂ) * (Real.sin (2 * Real.pi * (n : ℝ) / k) : ℂ)) *
      ((k : ℂ) / 4 + Complex.I * (mu / (Real.pi : ℂ) + abjmLargeMuConstantTerm n k))

/-- Carrier for the large-`µ` regime in Section 6.  The exponentially suppressed tails are analytic
asymptotic obligations; this carrier exposes the leading algebraic expressions used downstream. -/
structure ABJMLargeMuAsymptoticCarrier where
  level : ℝ
  phaseLeading : ℂ → ℂ
  phaseDerivativeLeading : ℂ → ℂ
  wilsonRawLeading : ℕ → ℂ → ℂ
  wilsonLeading : ℕ → ℂ → ℂ
  phase_eq : ∀ mu, phaseLeading mu = abjmLargeMuPhaseLeading level mu
  phase_derivative_eq :
    ∀ mu, phaseDerivativeLeading mu = abjmLargeMuPhaseDerivativeLeading level mu
  wilson_raw_eq :
    ∀ n mu,
      wilsonRawLeading n mu =
        abjmLargeMuWilsonLeadingRaw n level mu (phaseDerivativeLeading mu)
  wilson_eq : ∀ n mu, wilsonLeading n mu = abjmLargeMuWilsonLeading n level mu

/-- The leading large-`µ` Wilson loop after phase substitution is equation (6.1). -/
lemma ABJMLargeMuAsymptoticCarrier.wilsonLeading_eq
    (A : ABJMLargeMuAsymptoticCarrier) (n : ℕ) (mu : ℂ) :
    A.wilsonLeading n mu = abjmLargeMuWilsonLeading n A.level mu :=
  A.wilson_eq n mu

/-- Coefficient-function carrier for equations (5.16)-(5.19). -/
structure ABJMHalfBPSCoefficientSystem where
  level : ℝ
  A : ℕ → ℂ → ℂ
  halfBPSGenerating : ℕ → ℂ → ℂ
  half_eq_A : ∀ n z, halfBPSGenerating n z = abjmHalfBPSFromA n level (A n z)

/-- **[Equation (5.19)]** The `1/2` BPS generating function is determined by `A_n`. -/
lemma ABJMHalfBPSCoefficientSystem.halfBPS_eq_A
    (S : ABJMHalfBPSCoefficientSystem) (n : ℕ) (z : ℂ) :
    S.halfBPSGenerating n z = abjmHalfBPSFromA n S.level (S.A n z) :=
  S.half_eq_A n z

/-- **[Equations (1.3), (5.21)]** At `k = 4`, if `A₁ = root/4`, equation (5.19) gives
`W_{1}^{1/2} = root/2`.  In the paper `root² = z - 4 + 4 exp(-2F(z))`. -/
lemma ABJMHalfBPSCoefficientSystem.kFour_nOne_closedForm
    (S : ABJMHalfBPSCoefficientSystem) (hk : S.level = 4) (z root : ℂ)
    (hA : S.A 1 z = (1 / 4 : ℂ) * root) :
    S.halfBPSGenerating 1 z = (1 / 2 : ℂ) * root := by
  have hsin : Real.sin (2 * Real.pi * (1 : ℝ) / (4 : ℝ)) = 1 := by
    have harg : 2 * Real.pi * (1 : ℝ) / (4 : ℝ) = Real.pi / 2 := by ring
    rw [harg, Real.sin_pi_div_two]
  calc
    S.halfBPSGenerating 1 z =
        (2 * (1 : ℂ) / (1 : ℂ)) * ((1 / 4 : ℂ) * root) := by
      rw [S.half_eq_A, hk, hA]
      unfold abjmHalfBPSFromA
      simp only [Nat.reduceSub, pow_zero, Nat.cast_one, hsin, Complex.ofReal_one]
    _ = (1 / 2 : ℂ) * root := by ring

/-- Carrier for the paper's closed `1/2` BPS formulas (1.3) and (1.4).  The square-root branch and the
phase quantization conditions are analytic inputs from the Tracy-Widom part of the paper. -/
structure ABJMExactHalfBPSClosedForms where
  level : ℝ
  freeEnergy : ℂ → ℂ
  halfN1 : ℂ → ℂ
  halfN2 : ℂ → ℂ
  kFour_nOne :
    level = 4 → ∀ z root, root ^ 2 = z - 4 + 4 * Complex.exp (-2 * freeEnergy z) →
      halfN1 z = (1 / 2 : ℂ) * root
  nTwo_from_nOne :
    ∀ z, halfN2 z =
      Complex.I * (Real.tan (2 * Real.pi / level) : ℂ)
        * (halfN1 z ^ 2 + 1 - Complex.exp (-2 * freeEnergy z))

/-- **[Equation (1.4)]** The multiply wound `n = 2` `1/2` BPS loop is determined by the `n = 1` loop
and the free energy once the paper's quantization conditions are supplied. -/
lemma ABJMExactHalfBPSClosedForms.nTwo_eq_nOne_freeEnergy
    (C : ABJMExactHalfBPSClosedForms) (z : ℂ) :
    C.halfN2 z =
      Complex.I * (Real.tan (2 * Real.pi / C.level) : ℂ)
        * (C.halfN1 z ^ 2 + 1 - Complex.exp (-2 * C.freeEnergy z)) :=
  C.nTwo_from_nOne z


end Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas

end
