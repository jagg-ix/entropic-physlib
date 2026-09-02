/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QFT.PathIntegral.WickClock
public import Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.TodaLaxHirotaString
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ThetaModular
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.HopfAlgebraWilsonLoop
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDPathIntegralMeasureValid
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Nekrasov--Witten omega deformation, branes, integrability, and Liouville parameters

This file formalizes the finite algebraic core of

* N. Nekrasov and E. Witten, *The Omega Deformation, Branes, Integrability,
  and Liouville Theory*, arXiv:1002.0888v2.

The paper proves a broad physical correspondence.  The Lean layer below records
the parts that are exact algebraic interfaces to the rest of this repo:

* **§A -- gauge theory to Bethe equations**: equations (2.4)--(2.8).
  The exact WKB/Dirac-quantized condition
  `∂W̃/∂σ = i n` implies the Bethe equation
  `exp(2π ∂W̃/∂σ) = 1`; the theta-angle shift has the expected
  `θ -> θ + 2πm`, `n -> n + m` invariance.
* **§B -- coisotropic A-brane condition**: the rank-one coisotropic condition
  `I = ω⁻¹F`, `I² = -1` is represented by the standard two-dimensional
  complex-structure matrix.
* **§C -- omega deformation**: the diagonal omega metric term (3.20), the
  substitution `A₄ -> A₄ + ε V·D` (3.21--3.22), and the deformed supercharge
  square `Q² = gauge + ε W_V`.
* **§D -- `ε₁, ε₂`, Teichmuller/Liouville parameters**: equations (4.7),
  (4.12), and the standard Liouville duality `b² <-> b⁻²`.
* **§E -- integrability and path integrals**: the Nekrasov-Shatashvili
  quantization parameter calls the existing Toda shift/string-equation
  theorems; the omega partition weight is the existing Lorentzian
  complex-action path-integral weight and its damping is the existing
  Feynman--Kac damping; the same pointwise weight and Bochner-integrability
  bound are reused from the measure-valid QED exchange model.
* **§F -- Liouville/conformal-block carriers**: the conformal-block theta
  carrier reuses the Chern--Simons--Witten/Jacobi theta bridge; Wilson
  holonomy/topological-spin data reuse the Hopf/Wilson bridge; gluing two
  four-balls gives the norm-square algebraic form used in §4.10.

No new primitive assumptions.
-/

set_option autoImplicit false

open Complex
open Physlib.QFT.PathIntegral
open Physlib.QFT.Matsubara.PathIntegral
open Physlib.QuantumMechanics.NonHermitian.WickRotation
open Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.TodaLaxHirotaString
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.HopfAlgebraWilsonLoop
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDPathIntegralMeasureValid
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDMatsubaraContour
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.OmegaDeformation


/-- **Bethe exponential from the twisted effective superpotential**:
`exp(2π ∂W̃/∂σ)`.  In the paper this is equation (2.8), after (2.4)
and Dirac quantization combine to `∂W̃/∂σ = i n`. -/
def twistedBetheExponent (dW : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * dW)

/-- **The Bethe vacuum equation** `exp(2π ∂W̃/∂σ) = 1`. -/
def TwistedBetheEquation (dW : ℂ) : Prop :=
  twistedBetheExponent dW = 1

/-- **[Nekrasov--Witten (2.7) => (2.8)]** If the twisted-superpotential
gradient is Dirac-quantized, `∂W̃/∂σ = i n`, then it obeys the Bethe
equation `exp(2π ∂W̃/∂σ) = 1`. -/
lemma twistedBetheEquation_of_integral_gradient (n : ℤ) :
    TwistedBetheEquation (Complex.I * (n : ℂ)) := by
  unfold TwistedBetheEquation twistedBetheExponent
  rw [show 2 * (Real.pi : ℂ) * (Complex.I * (n : ℂ))
      = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- **Transport form of (2.7) => (2.8).** -/
lemma twistedBetheEquation_of_eq_integral_gradient {dW : ℂ} (n : ℤ)
    (h : dW = Complex.I * (n : ℂ)) :
    TwistedBetheEquation dW := by
  rw [h]
  exact twistedBetheEquation_of_integral_gradient n

/-- **Theta-shifted WKB quantum number**, equation (2.11):
`n - θ/(2π)`. -/
def thetaShiftedQuantumNumber (n : ℤ) (θ : ℝ) : ℝ :=
  (n : ℝ) - θ / (2 * Real.pi)

/-- **Theta-angle periodicity.**  The shift `θ -> θ + 2πm` is absorbed
by `n -> n + m`, so the physical shifted number `n - θ/(2π)` is
unchanged.  This is the algebraic content of the discussion following
(2.11)--(2.12). -/
lemma thetaShiftedQuantumNumber_periodic (n m : ℤ) (θ : ℝ) :
    thetaShiftedQuantumNumber (n + m) (θ + 2 * Real.pi * (m : ℝ))
      = thetaShiftedQuantumNumber n θ := by
  unfold thetaShiftedQuantumNumber
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hshift :
      (θ + 2 * Real.pi * (m : ℝ)) / (2 * Real.pi)
        = θ / (2 * Real.pi) + (m : ℝ) := by
    field_simp [hπ]
  rw [hshift]
  push_cast
  ring


/-- The rank-one coisotropic A-brane endomorphism condition `I² = -1`
for a space-filling brane with `I = ω⁻¹F`. -/
def IsRankOneCoisotropicEndomorphism (I : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  I * I = -1

/-- The standard complex-structure matrix on a real two-plane. -/
def standardComplexStructure2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1; 1, 0]

/-- **The standard complex structure squares to `-1`.**  This is the
local algebraic model of the paper's rank-one coisotropic condition
`I = ω⁻¹F`, `I² = -1`. -/
lemma standardComplexStructure2_sq :
    standardComplexStructure2 * standardComplexStructure2 = -1 := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals norm_num [standardComplexStructure2, Matrix.mul_apply]

/-- **The standard two-plane gives a rank-one coisotropic brane carrier.** -/
lemma standardComplexStructure2_isCoisotropic :
    IsRankOneCoisotropicEndomorphism standardComplexStructure2 :=
  standardComplexStructure2_sq


/-- **One diagonal omega-deformed metric block** `ρ²(dθ - ε dx)² + dx²`,
the scalar block appearing in (3.20) and in the two-parameter metric (4.2). -/
def omegaMetricOnePlane (rhoSq ε dθ dx : ℝ) : ℝ :=
  rhoSq * (dθ - ε * dx) ^ 2 + dx ^ 2

/-- At `ε = 0`, the omega-deformed block is the undeformed product block. -/
lemma omegaMetricOnePlane_zero (rhoSq dθ dx : ℝ) :
    omegaMetricOnePlane rhoSq 0 dθ dx = rhoSq * dθ ^ 2 + dx ^ 2 := by
  unfold omegaMetricOnePlane
  ring

/-- **The two-parameter diagonal omega metric block** from (4.2):
`f(w)(dα-ε₁dx₄)² + g(w)(dβ-ε₂dx₅)² + dx₄² + dx₅²`. -/
def omegaMetricTorusPart
    (f g ε1 ε2 dα dβ dx4 dx5 : ℝ) : ℝ :=
  f * (dα - ε1 * dx4) ^ 2 + g * (dβ - ε2 * dx5) ^ 2 + dx4 ^ 2 + dx5 ^ 2

/-- The two-parameter metric block reduces to the undeformed product metric
when `ε₁ = ε₂ = 0`. -/
lemma omegaMetricTorusPart_zero (f g dα dβ dx4 dx5 : ℝ) :
    omegaMetricTorusPart f g 0 0 dα dβ dx4 dx5
      = f * dα ^ 2 + g * dβ ^ 2 + dx4 ^ 2 + dx5 ^ 2 := by
  unfold omegaMetricTorusPart
  ring

/-- **Omega-deformation substitution**, equation (3.22):
`A₄ -> A₄ + ε V·D`. -/
def omegaGaugeSubstitution (A4 ε VD : ℝ) : ℝ :=
  A4 + ε * VD

/-- At zero omega deformation, the substitution is the original field. -/
lemma omegaGaugeSubstitution_zero (A4 VD : ℝ) :
    omegaGaugeSubstitution A4 0 VD = A4 := by
  unfold omegaGaugeSubstitution
  ring

/-- **Deformed supercharge square**, paper §3.2.1:
`Q² = gauge + ε W_V`, modulo gauge transformations. -/
def deformedSuperchargeSquare (gauge ε Wv : ℝ) : ℝ :=
  gauge + ε * Wv

/-- At `ε = 0`, the square of the preserved supercharge closes only on
the undeformed gauge transformation. -/
lemma deformedSuperchargeSquare_zero (gauge Wv : ℝ) :
    deformedSuperchargeSquare gauge 0 Wv = gauge := by
  unfold deformedSuperchargeSquare
  ring

/-- The omega contribution to `Q²` is exactly `ε W_V`. -/
lemma deformedSuperchargeSquare_sub_undeformed (gauge ε Wv : ℝ) :
    deformedSuperchargeSquare gauge ε Wv - gauge = ε * Wv := by
  unfold deformedSuperchargeSquare
  ring


/-- **The torus modular parameter** of the undeformed description,
paper (4.7)/(4.12): `τ_b = i ε₂/ε₁`. -/
def omegaTauB (ε1 ε2 : ℝ) : ℂ :=
  Complex.I * ((ε2 / ε1 : ℝ) : ℂ)

@[simp] lemma omegaTauB_re (ε1 ε2 : ℝ) :
    (omegaTauB ε1 ε2).re = 0 := by
  unfold omegaTauB
  simp [Complex.mul_re]

@[simp] lemma omegaTauB_im (ε1 ε2 : ℝ) :
    (omegaTauB ε1 ε2).im = ε2 / ε1 := by
  unfold omegaTauB
  simp [Complex.mul_im]

/-- **The Teichmuller/Weil--Petersson symplectic scale** in §4.6:
`ω_A = (ε₁/ε₂) ω_WP`. -/
def teichmullerSymplecticScale (ε1 ε2 : ℝ) : ℝ :=
  ε1 / ε2

/-- The imaginary part of `τ_b` and the Teichmuller quantization scale
are reciprocal. -/
lemma omegaTauB_im_mul_teichmullerSymplecticScale
    (ε1 ε2 : ℝ) (hε1 : ε1 ≠ 0) (hε2 : ε2 ≠ 0) :
    (omegaTauB ε1 ε2).im * teichmullerSymplecticScale ε1 ε2 = 1 := by
  simp [teichmullerSymplecticScale]
  field_simp [hε1, hε2]

/-- **Liouville coupling squared**, in the standard AGT/Teichmuller
normalization: `b² = ε₁/ε₂`. -/
def liouvilleBSquared (ε1 ε2 : ℝ) : ℝ :=
  ε1 / ε2

/-- The dual Liouville coupling squared, `b⁻² = ε₂/ε₁`. -/
def liouvilleDualBSquared (ε1 ε2 : ℝ) : ℝ :=
  ε2 / ε1

@[simp] lemma omegaTauB_im_eq_liouvilleDualBSquared (ε1 ε2 : ℝ) :
    (omegaTauB ε1 ε2).im = liouvilleDualBSquared ε1 ε2 := by
  simp [liouvilleDualBSquared]

@[simp] lemma teichmullerSymplecticScale_eq_liouvilleBSquared
    (ε1 ε2 : ℝ) :
    teichmullerSymplecticScale ε1 ε2 = liouvilleBSquared ε1 ε2 := rfl

@[simp] lemma liouvilleBSquared_swap_eq_dual (ε1 ε2 : ℝ) :
    liouvilleBSquared ε2 ε1 = liouvilleDualBSquared ε1 ε2 := rfl

/-- `b²` and its Liouville-dual parameter multiply to `1`. -/
lemma liouvilleBSquared_mul_dual
    (ε1 ε2 : ℝ) (hε1 : ε1 ≠ 0) (hε2 : ε2 ≠ 0) :
    liouvilleBSquared ε1 ε2 * liouvilleDualBSquared ε1 ε2 = 1 := by
  unfold liouvilleBSquared liouvilleDualBSquared
  field_simp [hε1, hε2]

/-- **Liouville background-charge square** as a function of `b² = x`:
`Q² = (b + b⁻¹)² = x + 2 + x⁻¹`. -/
def liouvilleQSquaredFromBSquared (x : ℝ) : ℝ :=
  x + 2 + x⁻¹

/-- **Liouville central charge** `c = 1 + 6Q²`, expressed in terms of
`b² = x`. -/
def liouvilleCentralChargeFromBSquared (x : ℝ) : ℝ :=
  1 + 6 * liouvilleQSquaredFromBSquared x

/-- **Liouville duality:** `Q²(b) = Q²(b⁻¹)`. -/
lemma liouvilleQSquared_duality (x : ℝ) (hx : x ≠ 0) :
    liouvilleQSquaredFromBSquared x⁻¹ = liouvilleQSquaredFromBSquared x := by
  unfold liouvilleQSquaredFromBSquared
  field_simp [hx]
  ring

/-- **Central-charge invariance under Liouville duality.** -/
lemma liouvilleCentralCharge_duality (x : ℝ) (hx : x ≠ 0) :
    liouvilleCentralChargeFromBSquared x⁻¹
      = liouvilleCentralChargeFromBSquared x := by
  unfold liouvilleCentralChargeFromBSquared
  rw [liouvilleQSquared_duality x hx]

/-- **AGT/Liouville `ε`-formula for the background charge.**  Substituting
`b² = ε₁/ε₂` gives `Q² = (ε₁ + ε₂)²/(ε₁ε₂)`. -/
lemma omegaLiouvilleQSquared_eq_eps_formula
    (ε1 ε2 : ℝ) (hε1 : ε1 ≠ 0) (hε2 : ε2 ≠ 0) :
    liouvilleQSquaredFromBSquared (liouvilleBSquared ε1 ε2)
      = (ε1 + ε2) ^ 2 / (ε1 * ε2) := by
  unfold liouvilleQSquaredFromBSquared liouvilleBSquared
  field_simp [hε1, hε2]
  ring

/-- **AGT/Liouville central charge in Omega-deformation parameters:**
`c = 1 + 6(ε₁ + ε₂)²/(ε₁ε₂)`. -/
lemma omegaLiouvilleCentralCharge_eq_eps_formula
    (ε1 ε2 : ℝ) (hε1 : ε1 ≠ 0) (hε2 : ε2 ≠ 0) :
    liouvilleCentralChargeFromBSquared (liouvilleBSquared ε1 ε2)
      = 1 + 6 * ((ε1 + ε2) ^ 2 / (ε1 * ε2)) := by
  unfold liouvilleCentralChargeFromBSquared
  rw [omegaLiouvilleQSquared_eq_eps_formula ε1 ε2 hε1 hε2]


/-- **Nekrasov--Shatashvili effective Planck parameter**: in the
`ε₂ -> 0` integrable-system limit, `ε₁` is the quantization parameter. -/
def nekrasovShatashviliPlanck (ε1 : ℂ) : ℂ :=
  ε1

/-- **NS limit calls the existing Toda shift algebra.**  The effective
Planck constant `ε₁` obeys the deformed Heisenberg/Toda relation
`[ω̂, s] = ε₁ ω̂`, reusing `MatrixQuantumMechanics.TodaLaxHirotaString`. -/
lemma nsLimit_toda_shift_commutator (ε1 : ℂ) (f : ℂ → ℂ) :
    shift (nekrasovShatashviliPlanck ε1) (mulVar f)
      - mulVar (shift (nekrasovShatashviliPlanck ε1) f)
        = nekrasovShatashviliPlanck ε1 •
          shift (nekrasovShatashviliPlanck ε1) f :=
  shift_mulVar_commutator (nekrasovShatashviliPlanck ε1) f

/-- **NS limit also reuses the Toda string equation** `[ω̂, sω̂⁻¹] = ε₁`. -/
lemma nsLimit_toda_stringEquation (ε1 : ℂ) (f : ℂ → ℂ) :
    shift (nekrasovShatashviliPlanck ε1)
        (mulVar (shift (-(nekrasovShatashviliPlanck ε1)) f))
      - mulVar (shift (-(nekrasovShatashviliPlanck ε1))
          (shift (nekrasovShatashviliPlanck ε1) f))
        = nekrasovShatashviliPlanck ε1 • f :=
  shift_mulShiftInv_commutator (nekrasovShatashviliPlanck ε1) f

/-- **Omega-deformed partition weight as the repo's master complex-action
weight.** -/
def omegaPathIntegralWeight (S_R S_I ℏ : ℝ) : ℂ :=
  complexActionPathIntegralWeight S_R S_I ℏ

/-- The omega partition weight is exactly the Lorentzian complex-action
kernel already used by the QED/path-integral stack. -/
lemma omegaPathIntegralWeight_eq_lorentzianKernel (S_R S_I ℏ : ℝ) :
    omegaPathIntegralWeight S_R S_I ℏ = lorentzianKernel S_R S_I ℏ :=
  complexActionPathIntegralWeight_eq_lorentzianKernel S_R S_I ℏ

/-- **Omega damping is Feynman--Kac damping** under the standard
constant-potential identification `S_I = V T ℏ`. -/
lemma omegaPathIntegralModulus_eq_feynmanKac
    (S_R S_I V T ℏ : ℝ) (hℏ : 0 < ℏ) (hSI : S_I = V * T * ℏ) :
    ‖omegaPathIntegralWeight S_R S_I ℏ‖
      = feynman_kac_weight (fun _ : Unit => V) T () := by
  unfold omegaPathIntegralWeight
  rw [master_modulus_is_kuiken]
  simpa [kuikenWeight] using
    fk_euclidean_entropic_damping_correspondence V T ℏ hℏ S_I hSI

/-- **Omega scalar weight equals the measure-valid QED exchange weight**
when the QED real-action coordinate is the same point `x` and the imaginary
action is the sum of the two fermion-line dampings. -/
lemma omegaPathIntegralWeight_eq_qedExchangeWeight
    (ℏ HI1 HI2 x : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) :
    omegaPathIntegralWeight x (HI1 + HI2) ℏ =
      (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).weight x := by
  unfold omegaPathIntegralWeight complexActionPathIntegralWeight
  unfold qedExchangeModel
  unfold Physlib.QFT.PathIntegral.MeasurePathIntegralModel.weight
  unfold Physlib.QFT.PathIntegral.MeasurePathIntegralModel.actionReScaled
  unfold Physlib.QFT.PathIntegral.MeasurePathIntegralModel.actionImScaled
  congr 1
  push_cast
  ring

/-- **The QED exchange modulus is a constant-potential Feynman--Kac
weight.**  This is the QED-specific version of the Omega/FK damping bridge. -/
lemma omegaQEDExchangeWeight_modulus_eq_feynmanKac
    (ℏ HI1 HI2 x : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) :
    ‖(qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).weight x‖ =
      feynman_kac_weight (fun _ : Unit => (HI1 + HI2) / ℏ) 1 () := by
  rw [qed_cameronMartin_eq_weight_modulus]
  unfold feynman_kac_weight
  ring_nf

/-- **Omega reuses the measure-valid QED path-integral carrier.**  The
damped QED exchange amplitude is a finite Bochner integral with the existing
partition-function bound. -/
lemma omega_reuses_qed_amplitude_bochner_finite
    (ℏ HI1 HI2 : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) :
    ‖(qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).complexFKExpectation
        (fun _ => 1)‖
      ≤ 1 * (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).partitionFunction :=
  qed_amplitude_bochner_finite ℏ HI1 HI2 hℏ h1 h2

/-- A compact checked bridge from the Omega complex-action scalar to the
measure-valid QED exchange path integral: the pointwise complex weight agrees,
its modulus is the constant-potential Feynman--Kac weight, and the corresponding
QED exchange amplitude satisfies the existing Bochner-integrability bound. -/
lemma omega_qed_feynmanKac_checked_summary
    (ℏ HI1 HI2 x : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) :
    omegaPathIntegralWeight x (HI1 + HI2) ℏ =
        (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).weight x
      ∧ ‖(qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).weight x‖ =
        feynman_kac_weight (fun _ : Unit => (HI1 + HI2) / ℏ) 1 ()
      ∧ ‖(qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).complexFKExpectation
          (fun _ => 1)‖
        ≤ 1 * (qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).partitionFunction :=
  ⟨omegaPathIntegralWeight_eq_qedExchangeWeight ℏ HI1 HI2 x hℏ h1 h2,
    omegaQEDExchangeWeight_modulus_eq_feynmanKac ℏ HI1 HI2 x hℏ h1 h2,
    omega_reuses_qed_amplitude_bochner_finite ℏ HI1 HI2 hℏ h1 h2⟩

/-- **Omega thermal weight is a Wick-rotated Matsubara weight.** -/
lemma omegaMatsubaraWeight_eq_wickRotate (E_R : ℝ) (T : ThermalCircle) :
    matsubaraWeight E_R T = reversiblePhaseC E_R T.hbar (wickRotate T.period) :=
  Physlib.QFT.PathIntegral.matsubaraWeight_eq_wickRotate E_R T

/-- **Omega/Matsubara pole carrier.**  The same Matsubara pole equation
used by the TFD contour formalization is available for the omega thermal
circle. -/
lemma omegaMatsubara_bose_pole (β : ℝ) (n : ℤ) (hβ : β ≠ 0) :
    Complex.exp ((β : ℂ) * matsubaraFreq β n) = 1 :=
  bose_pole β n hβ

/-- **Bosonic Omega/Matsubara KMS condition:** the bosonic mode is periodic
on the Euclidean thermal circle. -/
lemma omegaMatsubaraModeBoson_periodic
    (T : ThermalCircle) (n : ℤ) (τ : ℝ) :
    matsubaraModeBoson T n (τ + T.period) = matsubaraModeBoson T n τ :=
  matsubaraModeBoson_periodic T n τ

/-- **Fermionic Omega/Matsubara KMS condition:** the fermionic mode is
antiperiodic on the Euclidean thermal circle. -/
lemma omegaMatsubaraModeFermion_antiperiodic
    (T : ThermalCircle) (n : ℤ) (τ : ℝ) :
    matsubaraModeFermion T n (τ + T.period) = -matsubaraModeFermion T n τ :=
  matsubaraModeFermion_antiperiodic T n τ

/-- The Omega thermal branch reuses both Matsubara KMS boundary conditions:
bosonic modes are periodic and fermionic modes are antiperiodic. -/
lemma omega_matsubara_kms_checked_summary
    (T : ThermalCircle) (n : ℤ) (τ : ℝ) :
    matsubaraModeBoson T n (τ + T.period) = matsubaraModeBoson T n τ
      ∧ matsubaraModeFermion T n (τ + T.period) = -matsubaraModeFermion T n τ :=
  ⟨omegaMatsubaraModeBoson_periodic T n τ,
    omegaMatsubaraModeFermion_antiperiodic T n τ⟩


/-- The omega/Liouville theta-character carrier: the CSW theta character
evaluated at `τ_b = i ε₂/ε₁`. -/
def omegaThetaCharacter (k : ℂ) (ε1 ε2 : ℝ) (z : ℂ) : ℂ :=
  cswTheta k (omegaTauB ε1 ε2) z

/-- The omega theta character is the existing CSW/Jacobi-theta character
with the omega modular parameter substituted. -/
lemma omegaThetaCharacter_eq_jacobiTheta₂
    (k : ℂ) (ε1 ε2 : ℝ) (z : ℂ) :
    omegaThetaCharacter k ε1 ε2 z
      = jacobiTheta₂ (k * z) (k * omegaTauB ε1 ε2) := by
  unfold omegaThetaCharacter
  exact cswTheta_eq_jacobiTheta₂ k (omegaTauB ε1 ε2) z

/-- **Omega/Liouville holonomy carrier.**  Wilson-loop topological spin
is the same ribbon-twist carrier used by the Hopf-algebra Wilson bridge. -/
lemma omegaWilsonHolonomy_topologicalSpin (k : ℕ) (a : Fin k) :
    wilsonTopologicalSpin k a = ribbonTwist (wilsonConformalWeight k a)
      ∧ wilsonTopologicalSpin k a = ribbonTwist ((a.val : ℝ) ^ 2 / (2 * k)) :=
  hopf_ribbon_twist_is_wilson_topological_spin k a

/-- **Gluing two oppositely oriented four-balls gives a norm-square
partition function**, the algebraic content of the §4.10 statement that
the non-chiral `S⁴` partition function is `|W|²`. -/
lemma conjugate_gluing_eq_normSq (W : ℂ) :
    (starRingEnd ℂ) W * W = (Complex.normSq W : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self]

/-- A compact summary of the checked omega/Liouville bridge: nonzero
`ε₁, ε₂` give reciprocal Liouville parameters, the theta character is the
CSW/Jacobi carrier, and the ball-gluing amplitude is a norm square. -/
lemma omega_liouville_checked_summary
    (ε1 ε2 : ℝ) (hε1 : ε1 ≠ 0) (hε2 : ε2 ≠ 0) (k z W : ℂ) :
    liouvilleBSquared ε1 ε2 * liouvilleDualBSquared ε1 ε2 = 1
      ∧ omegaThetaCharacter k ε1 ε2 z
          = jacobiTheta₂ (k * z) (k * omegaTauB ε1 ε2)
      ∧ (starRingEnd ℂ) W * W = (Complex.normSq W : ℂ) :=
  ⟨liouvilleBSquared_mul_dual ε1 ε2 hε1 hε2,
    omegaThetaCharacter_eq_jacobiTheta₂ k ε1 ε2 z,
    conjugate_gluing_eq_normSq W⟩

end Physlib.QuantumMechanics.ComplexAction.OmegaDeformation

end

end
