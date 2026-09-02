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
public import Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas.AnchorsBPSWilsonLoops

/-! # ABJMWilsonLoopsFermiGas — part `FermiGasTracyWidom`. Full paper docstring in the umbrella module `Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas`; namespace and
declaration names are unchanged across the parts (the umbrella re-exports them). -/

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory
open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic
@[expose] public section
namespace Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas


/-- Fugacity/chemical-potential relation `z = exp μ`, equation (2.7). -/
noncomputable def abjmFugacity (μ : ℂ) : ℂ :=
  Complex.exp μ

/-- The fugacity is invariant under the grand-canonical `2πi` shift of the chemical potential. -/
lemma abjmFugacity_shift_two_pi_i (μ : ℂ) :
    abjmFugacity (μ + 2 * (Real.pi : ℂ) * Complex.I) = abjmFugacity μ := by
  simpa [abjmFugacity] using Complex.exp_periodic μ

/-- Grand-canonical normalization of the Wilson-loop generating function:
`W_n(z,k) = raw_n(z,k)/Xi(z,k)`, equation (2.5). -/
noncomputable def abjmGrandWilsonGenerating (Xi raw : ℂ) : ℂ :=
  raw / Xi

/-- If `Xi ≠ 0`, the grand-canonical normalization can be cleared. -/
lemma abjmGrandWilsonGenerating_mul_Xi (Xi raw : ℂ) (hXi : Xi ≠ 0) :
    abjmGrandWilsonGenerating Xi raw * Xi = raw := by
  unfold abjmGrandWilsonGenerating
  field_simp [hXi]

/-- Abstract grand-canonical data for ABJM Wilson loops.  This records the algebraic content of
equation (2.5) without rebuilding the analytic infinite series. -/
structure ABJMGrandCanonicalWilsonData where
  Xi : ℂ → ℂ
  rawWilson : ℕ → ℂ → ℂ
  wilsonGenerating : ℕ → ℂ → ℂ
  normalized_generating :
    ∀ n z, wilsonGenerating n z = abjmGrandWilsonGenerating (Xi z) (rawWilson n z)

/-- The raw generating function is recovered from the normalized one by multiplying by `Xi`. -/
lemma ABJMGrandCanonicalWilsonData.rawWilson_eq_mul
    (G : ABJMGrandCanonicalWilsonData) (n : ℕ) (z : ℂ) (hXi : G.Xi z ≠ 0) :
    G.wilsonGenerating n z * G.Xi z = G.rawWilson n z := by
  rw [G.normalized_generating]
  exact abjmGrandWilsonGenerating_mul_Xi (G.Xi z) (G.rawWilson n z) hXi

/-- Carrier for equation (2.6), `W₀(z,k)=z∂z log Ξ(z,k)`.  The derivative of `log Ξ` is kept as a
supplied function so the theorem records the exact interface without asserting analyticity of `Ξ`. -/
structure ABJMWZeroDerivativeLogCarrier where
  Xi : ℂ → ℂ
  Wzero : ℂ → ℂ
  derivLogXi : ℂ → ℂ
  Wzero_eq_z_derivLogXi : ∀ z, Wzero z = z * derivLogXi z

/-- **[Equation (2.6)]** The zero-winding grand-canonical Wilson loop is `z∂z log Ξ`. -/
lemma ABJMWZeroDerivativeLogCarrier.Wzero_eq
    (G : ABJMWZeroDerivativeLogCarrier) (z : ℂ) :
    G.Wzero z = z * G.derivLogXi z :=
  G.Wzero_eq_z_derivLogXi z

/-- Coefficient extraction carrier for equations (2.5), (2.8), and the small-`z` coefficient matching
behind (2.15): `Z(N,k)` is the coefficient of `Ξ`, while `W_n(N,k)` is the coefficient of
`Ξ(z,k) W_n(z,k)`. -/
structure ABJMGrandCanonicalCoefficientExtraction where
  Xi : ℂ → ℂ
  Wgen : ℕ → ℂ → ℂ
  Z : ℕ → ℂ
  Wraw : ℕ → ℕ → ℂ
  coefficient : ℕ → (ℂ → ℂ) → ℂ
  coeff_Xi : ∀ N, coefficient N Xi = Z N
  coeff_Xi_mul_Wgen : ∀ n N, coefficient N (fun z => Xi z * Wgen n z) = Wraw n N

/-- **[Coefficient extraction]** The abstract coefficient functional recovers both `Z(N,k)` and the
unnormalized Wilson loop coefficients from the grand-canonical functions. -/
lemma ABJMGrandCanonicalCoefficientExtraction.recovers_coefficients
    (G : ABJMGrandCanonicalCoefficientExtraction) (n N : ℕ) :
    G.coefficient N G.Xi = G.Z N
      ∧ G.coefficient N (fun z => G.Xi z * G.Wgen n z) = G.Wraw n N :=
  ⟨G.coeff_Xi N, G.coeff_Xi_mul_Wgen n N⟩

/-- The second small-`z` coefficient in equation (2.15):
`tr(ρUⁿ) tr ρ - tr(ρ²Uⁿ)`. -/
noncomputable def abjmSmallZWilsonSecondCoeff (trRhoUn trRho trRhoSqUn : ℂ) : ℂ :=
  trRhoUn * trRho - trRhoSqUn

/-- **[Equation (2.15), second coefficient]** The formal second coefficient is the connected trace
combination appearing in the paper. -/
lemma abjmSmallZWilsonSecondCoeff_eq
    (trRhoUn trRho trRhoSqUn : ℂ) :
    abjmSmallZWilsonSecondCoeff trRhoUn trRho trRhoSqUn =
      trRhoUn * trRho - trRhoSqUn := rfl

/-- Abstract Fermi-gas resolvent carrier for equations (2.11), (2.13), and (2.14).  The actual Fredholm
determinant and trace-class analysis are analytic inputs; Lean checks the transport between the named
representations once those inputs are supplied. -/
structure ABJMFermiGasResolventCarrier where
  Xi : ℂ → ℂ
  fredholmDet : ℂ → ℂ
  resolventTrace : ℕ → ℂ → ℂ
  shiftedHolonomyTrace : ℕ → ℂ → ℂ
  wilsonGenerating : ℕ → ℂ → ℂ
  Xi_eq_fredholmDet : ∀ z, Xi z = fredholmDet z
  wilson_eq_resolventTrace : ∀ n z, wilsonGenerating n z = resolventTrace n z
  bch_shifted_holonomy : ∀ n z, resolventTrace n z = shiftedHolonomyTrace n z

/-- **[Equations (2.13)-(2.14)]** The Wilson generating function can be rewritten in the shifted
holonomy form obtained from Baker-Campbell-Hausdorff. -/
lemma ABJMFermiGasResolventCarrier.wilson_eq_shiftedHolonomy
    (R : ABJMFermiGasResolventCarrier) (n : ℕ) (z : ℂ) :
    R.wilsonGenerating n z = R.shiftedHolonomyTrace n z := by
  rw [R.wilson_eq_resolventTrace, R.bch_shifted_holonomy]

/-- **[Equation (2.11)]** The grand partition function is the Fredholm determinant carrier. -/
lemma ABJMFermiGasResolventCarrier.Xi_is_fredholmDet
    (R : ABJMFermiGasResolventCarrier) (z : ℂ) :
    R.Xi z = R.fredholmDet z :=
  R.Xi_eq_fredholmDet z

/-- Fredholm determinant ratio `D(z)=Ξ(z)/Ξ(-z)`, equation (3.8). -/
noncomputable def abjmFredholmDetRatio (Xi : ℂ → ℂ) (z : ℂ) : ℂ :=
  Xi z / Xi (-z)

/-- **[Equation (3.8)]** When both determinant values are nonzero, the ratio obeys `D(z)D(-z)=1`. -/
lemma abjmFredholmDetRatio_mul_neg
    (Xi : ℂ → ℂ) (z : ℂ) (hz : Xi z ≠ 0) (hneg : Xi (-z) ≠ 0) :
    abjmFredholmDetRatio Xi z * abjmFredholmDetRatio Xi (-z) = 1 := by
  unfold abjmFredholmDetRatio
  simp only [neg_neg]
  field_simp [hz, hneg]

/-- Carrier for the parity-odd free energy `F(z)=log D(z)` from equations (3.8)-(3.10). -/
structure ABJMParityOddFreeEnergyCarrier where
  Xi : ℂ → ℂ
  D : ℂ → ℂ
  F : ℂ → ℂ
  D_eq_ratio : ∀ z, D z = abjmFredholmDetRatio Xi z
  D_mul_neg : ∀ z, D z * D (-z) = 1
  F_odd : ∀ z, F (-z) = -F z

/-- **[Equation (3.9)]** The parity-odd free energy changes sign under `z ↦ -z`. -/
lemma ABJMParityOddFreeEnergyCarrier.freeEnergy_odd
    (F : ABJMParityOddFreeEnergyCarrier) (z : ℂ) :
    F.F (-z) = -F.F z :=
  F.F_odd z


/-- Tracy-Widom `ψ`/`Γ` system for equations (3.1), (3.15), (3.22), (3.28), and (3.29).
The integral equation, meromorphic continuation, and contour deformation are analytic obligations;
the fields below expose the exact algebraic interface consumed by the Wilson-loop derivation. -/
structure ABJMTracyWidomPsiSystem where
  level : ℝ
  psi : ℂ → ℂ → ℂ
  Gamma : ℂ → ℂ → ℂ → ℂ
  F : ℂ → ℂ
  baxter :
    ∀ x z,
      psi (x + Complex.I * (Real.pi : ℂ) * (level : ℂ)) z
        + psi (x - Complex.I * (Real.pi : ℂ) * (level : ℂ)) z =
          z * abjmChiComplex x * psi x z
  wronskian :
    ∀ x z,
      psi (x + Complex.I * (Real.pi : ℂ) * (level : ℂ) / 2) z
          * psi (x - Complex.I * (Real.pi : ℂ) * (level : ℂ) / 2) (-z)
        + psi (x + Complex.I * (Real.pi : ℂ) * (level : ℂ) / 2) (-z)
          * psi (x - Complex.I * (Real.pi : ℂ) * (level : ℂ) / 2) z =
          4 * Complex.exp (x / (level : ℂ))
  parity :
    ∀ x z, psi (-x) z = Complex.exp (-x / (level : ℂ) + F z) * psi x (-z)
  gamma_parity_form :
    ∀ x y z,
      Gamma x y z =
        z * Complex.exp (-F z) /
          (2 * abjmCSinh ((x - y) / (level : ℂ))) *
          (psi x z * psi (-y) z - psi (-x) z * psi y z)

/-- **[Equation (3.15)]** The Tracy-Widom auxiliary function satisfies the Baxter equation. -/
lemma ABJMTracyWidomPsiSystem.baxter_eq
    (S : ABJMTracyWidomPsiSystem) (x z : ℂ) :
    S.psi (x + Complex.I * (Real.pi : ℂ) * (S.level : ℂ)) z
      + S.psi (x - Complex.I * (Real.pi : ℂ) * (S.level : ℂ)) z =
        z * abjmChiComplex x * S.psi x z :=
  S.baxter x z

/-- **[Equation (3.28)]** Parity relates `ψ(-x|z)` to `ψ(x|-z)` through the determinant-ratio free
energy. -/
lemma ABJMTracyWidomPsiSystem.parity_eq
    (S : ABJMTracyWidomPsiSystem) (x z : ℂ) :
    S.psi (-x) z = Complex.exp (-x / (S.level : ℂ) + S.F z) * S.psi x (-z) :=
  S.parity x z

/-- **[Equation (3.29)]** The `Γ`-kernel rewritten using the parity relation. -/
lemma ABJMTracyWidomPsiSystem.Gamma_eq_parity_form
    (S : ABJMTracyWidomPsiSystem) (x y z : ℂ) :
    S.Gamma x y z =
      z * Complex.exp (-S.F z) /
        (2 * abjmCSinh ((x - y) / (S.level : ℂ))) *
        (S.psi x z * S.psi (-y) z - S.psi (-x) z * S.psi y z) :=
  S.gamma_parity_form x y z

/-- Carrier for the one-step shift relation (3.27), written as the linear decomposition
`ψ(x+2πi|z)=A(x,z)ψ(x|z)+B(x,z)ψ(x|-z)`. -/
structure ABJMPsiTwoPiShiftCarrier where
  psi : ℂ → ℂ → ℂ
  shiftA : ℂ → ℂ → ℂ
  shiftB : ℂ → ℂ → ℂ
  shift_two_pi_i :
    ∀ x z,
      psi (x + 2 * (Real.pi : ℂ) * Complex.I) z =
        shiftA x z * psi x z + shiftB x z * psi x (-z)

/-- **[Equation (3.27)]** The `2πi` shift closes on the two-dimensional span generated by
`ψ(x|z)` and `ψ(x|-z)`. -/
lemma ABJMPsiTwoPiShiftCarrier.shift_eq
    (S : ABJMPsiTwoPiShiftCarrier) (x z : ℂ) :
    S.psi (x + 2 * (Real.pi : ℂ) * Complex.I) z =
      S.shiftA x z * S.psi x z + S.shiftB x z * S.psi x (-z) :=
  S.shift_two_pi_i x z

/-- Special value `ψ(iπ|z)=r(z)e^{iΦ(z)/2}`, equation (4.1). -/
noncomputable def abjmPsiIpiValue (r phi : ℂ) : ℂ :=
  r * Complex.exp (Complex.I * phi / 2)

/-- Special value `ψ(-iπ|z)=r(z)e^{-iΦ(z)/2}`, equation (4.1). -/
noncomputable def abjmPsiNegIpiValue (r phi : ℂ) : ℂ :=
  r * Complex.exp (-Complex.I * phi / 2)

/-- The radius-square relation (4.9), `r² = (2k/z)(e^{2F}-1)`. -/
noncomputable def abjmSpecialRadiusSq (k : ℝ) (z F : ℂ) : ℂ :=
  (2 * (k : ℂ) / z) * (Complex.exp (2 * F) - 1)

/-- Modified phase `Φ̃=Φ-π/k`, equation (4.21). -/
noncomputable def abjmModifiedPhase (k : ℝ) (phi : ℂ) : ℂ :=
  phi - (Real.pi : ℂ) / (k : ℂ)

/-- Quantization-condition carrier for Section 4.  It records the special-value parameterization,
the radius relation, the `z ↦ -z` phase law, and the printed low-level quantization constraints. -/
structure ABJMPhaseQuantizationCarrier where
  level : ℝ
  F : ℂ → ℂ
  radius : ℂ → ℂ
  phase : ℂ → ℂ
  psi : ℂ → ℂ → ℂ
  psi_ipi : ∀ z, psi (Complex.I * (Real.pi : ℂ)) z = abjmPsiIpiValue (radius z) (phase z)
  psi_neg_ipi : ∀ z, psi (-Complex.I * (Real.pi : ℂ)) z = abjmPsiNegIpiValue (radius z) (phase z)
  radius_sq : ∀ z, radius z ^ 2 = abjmSpecialRadiusSq level z (F z)
  phase_neg : ∀ z, phase (-z) = 2 * (Real.pi : ℂ) / (level : ℂ) - phase z
  kFour_constraint :
    level = 4 →
      ∀ z, z =
        4 * abjmCSinh (2 * F z)
          - 4 * (abjmCCosh (2 * F z) - 1) * abjmCCos (2 * phase z)

/-- **[Equation (4.9)]** The modulus/radius of the special value is fixed by `F`. -/
lemma ABJMPhaseQuantizationCarrier.radius_sq_eq
    (Q : ABJMPhaseQuantizationCarrier) (z : ℂ) :
    Q.radius z ^ 2 = abjmSpecialRadiusSq Q.level z (Q.F z) :=
  Q.radius_sq z

/-- **[Equation (4.2)]** The phase reflection law under `z ↦ -z`. -/
lemma ABJMPhaseQuantizationCarrier.phase_neg_eq
    (Q : ABJMPhaseQuantizationCarrier) (z : ℂ) :
    Q.phase (-z) = 2 * (Real.pi : ℂ) / (Q.level : ℂ) - Q.phase z :=
  Q.phase_neg z

/-- **[Equation (5.20) from the `k=4` quantization condition]** Denominator-cleared form of
`cos(2Φ)=(sinh(2F)-z/4)/(cosh(2F)-1)`. -/
lemma ABJMPhaseQuantizationCarrier.kFour_cos_phase_denominator_cleared
    (Q : ABJMPhaseQuantizationCarrier) (hk : Q.level = 4) (z : ℂ) :
    4 * (abjmCCosh (2 * Q.F z) - 1) * abjmCCos (2 * Q.phase z) =
      4 * abjmCSinh (2 * Q.F z) - z := by
  let S := abjmCSinh (2 * Q.F z)
  let C := abjmCCosh (2 * Q.F z)
  let P := abjmCCos (2 * Q.phase z)
  have h : z = 4 * S - 4 * (C - 1) * P := by
    simpa [S, C, P] using Q.kFour_constraint hk z
  calc
    4 * (abjmCCosh (2 * Q.F z) - 1) * abjmCCos (2 * Q.phase z)
        = 4 * (C - 1) * P := by simp [C, P]
    _ = 4 * S - (4 * S - 4 * (C - 1) * P) := by ring
    _ = 4 * S - z := by rw [← h]
    _ = 4 * abjmCSinh (2 * Q.F z) - z := by simp [S]


end Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas

end
