/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.StandardModelYukawaCoupling
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.ComplexMassContour
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
meta import Zil

/-!
# QED with scalar and pseudoscalar Yukawa couplings: one-loop effective action

This file formalizes the algebraic constant-background core of

* T. N. Jacobson and T. ter Veldhuis,
  *Non-Perturbative One-Loop Effective Action for QED with Yukawa Couplings*,
  arXiv:1806.04040v2.

The paper integrates out a Dirac fermion coupled to a scalar background `Phi`,
a pseudoscalar background `Pi`, and a `U(1)` gauge field.  In the constant
background approximation the Dirac mass data enter through

`M = m + kappa Phi`, `P = lambda Pi`, and `mu2 = M^2 + P^2`.

The formalized content is deliberately the part Lean can check exactly:

* the effective mass-square is the chiral modulus `M^2 + P^2`;
* the even Schwinger proper-time kernel is the Euler-Heisenberg kernel with
  the replacement `m^2 -> M^2 + P^2`;
* the odd one-loop term is the arctangent phase
  `(e^2/(16*pi^2)) FtildeF * arctan(P/M)`;
* writing `theta = (1/2) arctan(P/M)` gives
  `L_odd = (e^2/(8*pi^2)) theta FtildeF`;
* differentiating the odd term gives the rational pseudoscalar-current factor
  `M/(M^2+P^2)`;
* the finite-dimensional Berezin determinant already present in the repo
  evaluates on the same effective Yukawa mass modulus.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Yukawa.StandardModelYukawaCoupling
open Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
open Physlib.QuantumMechanics.ComplexAction.Yukawa.ComplexMassContour
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-! ## Effective scalar/pseudoscalar mass data -/

/-- The scalar Yukawa-shifted mass `M = m + kappa Phi`. -/
def effectiveScalarMass (m kappa Phi : ℝ) : ℝ :=
  m + kappa * Phi

/-- The pseudoscalar Yukawa mass coordinate `P = lambda Pi`. -/
def effectivePseudoscalarMass (lambda Pi : ℝ) : ℝ :=
  lambda * Pi

/-- The paper's constant-background effective mass-square
`mu2 = (m + kappa Phi)^2 + (lambda Pi)^2`. -/
def effectiveYukawaMassSq (m kappa Phi lambda Pi : ℝ) : ℝ :=
  effectiveScalarMass m kappa Phi ^ 2 + effectivePseudoscalarMass lambda Pi ^ 2

/-- The positive mass modulus `sqrt(mu2)` used by the determinant/effective action. -/
def effectiveYukawaMassModulus (m kappa Phi lambda Pi : ℝ) : ℝ :=
  Real.sqrt (effectiveYukawaMassSq m kappa Phi lambda Pi)

lemma effectiveYukawaMassSq_nonneg (m kappa Phi lambda Pi : ℝ) :
    0 ≤ effectiveYukawaMassSq m kappa Phi lambda Pi := by
  unfold effectiveYukawaMassSq
  nlinarith [sq_nonneg (effectiveScalarMass m kappa Phi),
    sq_nonneg (effectivePseudoscalarMass lambda Pi)]

@[simp] lemma effectiveYukawaMassSq_noYukawa (m kappa lambda : ℝ) :
    effectiveYukawaMassSq m kappa 0 lambda 0 = m ^ 2 := by
  simp [effectiveYukawaMassSq, effectiveScalarMass, effectivePseudoscalarMass]

/-- The Standard Model mass relation appears as the scalar part of the paper's
background mass when the bare mass is zero and the scalar background is the
Higgs VEV `v/sqrt 2`. -/
lemma effectiveScalarMass_higgsVEV_eq_yukawaMass (y v : ℝ) :
    effectiveScalarMass 0 y (v / Real.sqrt 2) = yukawaMass y v := by
  unfold effectiveScalarMass yukawaMass
  ring

/-- With the Higgs VEV background and no pseudoscalar background, the paper's
`mu2` is exactly the square of the existing Standard Model Yukawa mass. -/
lemma effectiveYukawaMassSq_higgsVEV_eq_yukawaMass_sq (y v lambda : ℝ) :
    effectiveYukawaMassSq 0 y (v / Real.sqrt 2) lambda 0 = yukawaMass y v ^ 2 := by
  simp [effectiveYukawaMassSq, effectivePseudoscalarMass,
    effectiveScalarMass_higgsVEV_eq_yukawaMass]

/-! ## Chiral modulus and phase angle -/

/-- Rotation of the scalar mass coordinate. -/
def chiralRotateScalar (theta M P : ℝ) : ℝ :=
  M * Real.cos theta - P * Real.sin theta

/-- Rotation of the pseudoscalar mass coordinate. -/
def chiralRotatePseudoscalar (theta M P : ℝ) : ℝ :=
  M * Real.sin theta + P * Real.cos theta

/-- The even sector depends only on the chiral modulus `M^2 + P^2`. -/
lemma chiral_modulus_sq_invariant (theta M P : ℝ) :
    chiralRotateScalar theta M P ^ 2 + chiralRotatePseudoscalar theta M P ^ 2 =
      M ^ 2 + P ^ 2 := by
  unfold chiralRotateScalar chiralRotatePseudoscalar
  nlinarith [Real.sin_sq_add_cos_sq theta]

/-- The chiral angle used in the paper:
`theta = (1/2) arctan(P/M)`. -/
def qedYukawaChiralAngle (M P : ℝ) : ℝ :=
  (1 / 2) * Real.arctan (P / M)

/-- The same angle expressed in terms of the scalar and pseudoscalar
background fields. -/
def qedYukawaChiralAngleFromFields (m kappa Phi lambda Pi : ℝ) : ℝ :=
  qedYukawaChiralAngle
    (effectiveScalarMass m kappa Phi)
    (effectivePseudoscalarMass lambda Pi)

@[simp] lemma two_mul_qedYukawaChiralAngle (M P : ℝ) :
    2 * qedYukawaChiralAngle M P = Real.arctan (P / M) := by
  unfold qedYukawaChiralAngle
  ring

@[simp] lemma qedYukawaChiralAngle_zero_pseudoscalar (M : ℝ) :
    qedYukawaChiralAngle M 0 = 0 := by
  simp [qedYukawaChiralAngle]

/-! ## Odd effective action: phase / `F tilde F` term -/

/-- The odd one-loop effective Lagrangian from the paper:
`L_odd = e^2/(16*pi^2) * FtildeF * arctan(P/M)`.

Here `FtildeF` denotes the Lorentz pseudoscalar
`F_{\mu nu} \tilde F^{\mu nu}`. -/
def qedYukawaOddEffectiveLagrangian (e FtildeF M P : ℝ) : ℝ :=
  e ^ 2 / (16 * Real.pi ^ 2) * FtildeF * Real.arctan (P / M)

/-- The same odd term with `M = m + kappa Phi` and `P = lambda Pi`. -/
def qedYukawaOddEffectiveLagrangianFromFields
    (e FtildeF m kappa Phi lambda Pi : ℝ) : ℝ :=
  qedYukawaOddEffectiveLagrangian e FtildeF
    (effectiveScalarMass m kappa Phi)
    (effectivePseudoscalarMass lambda Pi)

/-- Paper's chiral-angle form:
`L_odd = e^2/(8*pi^2) * theta * FtildeF`. -/
lemma qedYukawaOddEffectiveLagrangian_eq_theta
    (e FtildeF M P : ℝ) :
    qedYukawaOddEffectiveLagrangian e FtildeF M P =
      e ^ 2 / (8 * Real.pi ^ 2) * qedYukawaChiralAngle M P * FtildeF := by
  unfold qedYukawaOddEffectiveLagrangian qedYukawaChiralAngle
  ring

@[simp] lemma qedYukawaOddEffectiveLagrangian_zero_FtildeF
    (e M P : ℝ) :
    qedYukawaOddEffectiveLagrangian e 0 M P = 0 := by
  simp [qedYukawaOddEffectiveLagrangian]

@[simp] lemma qedYukawaOddEffectiveLagrangian_zero_pseudoscalar
    (e FtildeF M : ℝ) :
    qedYukawaOddEffectiveLagrangian e FtildeF M 0 = 0 := by
  simp [qedYukawaOddEffectiveLagrangian]

/-- The rational factor in the pseudoscalar current obtained by differentiating
the arctangent phase. -/
def qedYukawaOddCurrentRationalFactor (e FtildeF M P : ℝ) : ℝ :=
  e ^ 2 / (16 * Real.pi ^ 2) * FtildeF * M / (M ^ 2 + P ^ 2)

/-- Differentiating the odd arctangent term with respect to the pseudoscalar
mass coordinate `P` gives the rational factor `M/(M^2+P^2)` from the paper's
pseudoscalar current.  The hypothesis `M != 0` is the constant-background
chart where the ratio `P/M` is used. -/
lemma qedYukawaOdd_hasDerivAt_pseudoscalar
    (e FtildeF M P : ℝ) (hM : M ≠ 0) :
    HasDerivAt (fun P => qedYukawaOddEffectiveLagrangian e FtildeF M P)
      (qedYukawaOddCurrentRationalFactor e FtildeF M P) P := by
  have hlin : HasDerivAt (fun P : ℝ => P / M) (1 / M) P := by
    simpa using (hasDerivAt_id P).div_const M
  have harctan :
      HasDerivAt (fun P : ℝ => Real.arctan (P / M))
        ((1 / (1 + (P / M) ^ 2)) * (1 / M)) P :=
    by
      exact (Real.hasDerivAt_arctan (P / M)).comp P hlin
  have hconst :
      HasDerivAt
        (fun P : ℝ =>
          (e ^ 2 / (16 * Real.pi ^ 2) * FtildeF) * Real.arctan (P / M))
        ((e ^ 2 / (16 * Real.pi ^ 2) * FtildeF) *
          ((1 / (1 + (P / M) ^ 2)) * (1 / M))) P :=
    harctan.const_mul (e ^ 2 / (16 * Real.pi ^ 2) * FtildeF)
  exact hconst.congr_deriv (by unfold qedYukawaOddCurrentRationalFactor; field_simp [hM])

/-- At `P = 0`, the odd-current rational factor is the familiar
axion/anomaly coefficient `e^2/(16*pi^2) * FtildeF / M`. -/
lemma qedYukawaOddCurrentRationalFactor_at_zero
    (e FtildeF M : ℝ) :
    qedYukawaOddCurrentRationalFactor e FtildeF M 0 =
      e ^ 2 / (16 * Real.pi ^ 2) * FtildeF / M := by
  by_cases hM : M = 0
  · simp [qedYukawaOddCurrentRationalFactor, hM]
  · unfold qedYukawaOddCurrentRationalFactor
    field_simp [hM]
    ring

/-! ## Even effective action: Euler-Heisenberg mass replacement -/

/-- Real cotangent, used only as the paper's proper-time kernel notation. -/
def cot (x : ℝ) : ℝ :=
  Real.cos x / Real.sin x

/-- Real hyperbolic cotangent, used only as the paper's proper-time kernel notation. -/
def coth (x : ℝ) : ℝ :=
  Real.cosh x / Real.sinh x

/-- The spin/proper-time factor `cot(e a s) coth(e b s)` in the closed form. -/
def qedYukawaSpinProperTimeFactor (e a b s : ℝ) : ℝ :=
  cot (e * a * s) * coth (e * b * s)

/-- The even proper-time integrand of the one-loop effective Lagrangian:
`e^2/(32*pi^2) FtildeF * exp(-s*mu2)/s * cot(eas)coth(ebs)`.

The full analytic improper integral is not reconstructed here; the kernel is
the algebraic object whose mass dependence and limits are checked below. -/
def qedYukawaEvenProperTimeKernel (e FtildeF a b mu2 s : ℝ) : ℝ :=
  e ^ 2 / (32 * Real.pi ^ 2) * FtildeF *
    (Real.exp (-(s * mu2)) / s) * qedYukawaSpinProperTimeFactor e a b s

/-- The same even kernel with the scalar/pseudoscalar Yukawa backgrounds
substituted into `mu2`. -/
def qedYukawaEvenProperTimeKernelFromFields
    (e FtildeF a b m kappa Phi lambda Pi s : ℝ) : ℝ :=
  qedYukawaEvenProperTimeKernel e FtildeF a b
    (effectiveYukawaMassSq m kappa Phi lambda Pi) s

/-- The Euler-Heisenberg kernel recovered when the Yukawa backgrounds vanish. -/
def eulerHeisenbergEvenProperTimeKernel
    (e FtildeF a b mass s : ℝ) : ℝ :=
  qedYukawaEvenProperTimeKernel e FtildeF a b (mass ^ 2) s

/-- In the `Phi, Pi -> 0` limit the even kernel is exactly the
Euler-Heisenberg kernel with mass `m`. -/
lemma qedYukawaEvenKernel_noYukawa_eq_eulerHeisenberg
    (e FtildeF a b m kappa lambda s : ℝ) :
    qedYukawaEvenProperTimeKernelFromFields e FtildeF a b m kappa 0 lambda 0 s =
      eulerHeisenbergEvenProperTimeKernel e FtildeF a b m s := by
  simp [qedYukawaEvenProperTimeKernelFromFields, eulerHeisenbergEvenProperTimeKernel]

/-- The even kernel is invariant under global chiral rotations of the
`(M,P)` mass plane, because it depends only on `M^2+P^2`. -/
lemma qedYukawaEvenKernel_chiral_invariant
    (e FtildeF a b theta M P s : ℝ) :
    qedYukawaEvenProperTimeKernel e FtildeF a b
        (chiralRotateScalar theta M P ^ 2 + chiralRotatePseudoscalar theta M P ^ 2) s =
      qedYukawaEvenProperTimeKernel e FtildeF a b (M ^ 2 + P ^ 2) s := by
  rw [chiral_modulus_sq_invariant]

/-! ## Weak-field finite part and Coleman-Weinberg limit -/

/-- The finite weak-field even contribution after the two counterterms in the
paper, before adding the free photon normalization convention.  The variable
`mu2` is the effective mass-square `M^2+P^2`. -/
def qedYukawaWeakFieldFiniteEven
    (e Fsq FtildeF mu2 Mscale : ℝ) : ℝ :=
  mu2 ^ 2 / (16 * Real.pi ^ 2) * (Real.log (mu2 / Mscale ^ 2) - 3 / 2)
    + e ^ 2 / (48 * Real.pi ^ 2) * Real.log (mu2 / Mscale ^ 2) * Fsq
    + e ^ 4 / (1440 * Real.pi ^ 2 * mu2 ^ 2) *
        (Fsq ^ 2 + (7 / 4) * FtildeF ^ 2)

/-- The Coleman-Weinberg-type scalar potential obtained when the gauge
background vanishes, using the shifted scale `Mbar` of the paper. -/
def qedYukawaColemanWeinbergPotential (mu2 Mbar : ℝ) : ℝ :=
  mu2 ^ 2 / (16 * Real.pi ^ 2) * Real.log (mu2 / Mbar ^ 2)

/-- The Coleman-Weinberg potential expressed directly in the scalar and
pseudoscalar Yukawa backgrounds. -/
def qedYukawaColemanWeinbergPotentialFromFields
    (m kappa Phi lambda Pi Mbar : ℝ) : ℝ :=
  qedYukawaColemanWeinbergPotential
    (effectiveYukawaMassSq m kappa Phi lambda Pi) Mbar

/-- With zero gauge invariants, the finite weak-field term reduces to the
scalar Coleman-Weinberg logarithm plus the explicit `-3/2` scheme constant. -/
lemma qedYukawaWeakFieldFiniteEven_zeroGauge
    (e mu2 Mscale : ℝ) :
    qedYukawaWeakFieldFiniteEven e 0 0 mu2 Mscale =
      mu2 ^ 2 / (16 * Real.pi ^ 2) *
        (Real.log (mu2 / Mscale ^ 2) - 3 / 2) := by
  simp [qedYukawaWeakFieldFiniteEven]

/-- The no-gauge Coleman-Weinberg expression from the paper is just the same
function evaluated at `mu2 = (m+kappa Phi)^2 + (lambda Pi)^2`. -/
lemma qedYukawaColemanWeinberg_from_effectiveMassSq
    (m kappa Phi lambda Pi Mbar : ℝ) :
    qedYukawaColemanWeinbergPotentialFromFields m kappa Phi lambda Pi Mbar =
      (effectiveYukawaMassSq m kappa Phi lambda Pi) ^ 2 /
        (16 * Real.pi ^ 2) *
        Real.log (effectiveYukawaMassSq m kappa Phi lambda Pi / Mbar ^ 2) := by
  rfl

/-! ## Links to existing repo infrastructure -/

/-- The repo's finite-dimensional Berezin determinant evaluates on the same
effective Yukawa mass modulus that enters the one-loop effective action. -/
lemma berezin_effectiveYukawaMassModulus_eq_det
    (m kappa Phi lambda Pi : ℝ) :
    berezin (fermionGaussian (effectiveYukawaMassModulus m kappa Phi lambda Pi))
      =
      (!![effectiveYukawaMassModulus m kappa Phi lambda Pi] :
        Matrix (Fin 1) (Fin 1) ℝ).det := by
  exact berezin_gaussian_eq_det (effectiveYukawaMassModulus m kappa Phi lambda Pi)

/-- For a Maxwell potential `A`, `F=dA` satisfies the Bianchi identity, while
the one-loop Yukawa odd term is controlled by the pseudoscalar invariant
`FtildeF`.  This theorem packages the gauge-side identity with the paper's
odd-sector phase formula. -/
lemma maxwellFaraday_bianchi_and_qedYukawaOddTheta
    (k A : Fin 4 → ℝ) (lam mu nu : Fin 4)
    (e FtildeF M P : ℝ) :
    k lam * faraday k A mu nu + k mu * faraday k A nu lam
        + k nu * faraday k A lam mu = 0
      ∧ qedYukawaOddEffectiveLagrangian e FtildeF M P =
        e ^ 2 / (8 * Real.pi ^ 2) * qedYukawaChiralAngle M P * FtildeF := by
  exact ⟨faraday_bianchi k A lam mu nu,
    qedYukawaOddEffectiveLagrangian_eq_theta e FtildeF M P⟩

/-- The one-loop Yukawa effective-action mass data and the existing
Nagao-Nielsen/contour Yukawa bridge use the same Standard Model Yukawa mass
input.  The real Higgs-side mass feeds the paper's `mu2`, while the already
formalized complex-mass bridge carries the associated entropy-production rate
as imaginary rest energy. -/
lemma qedYukawaOneLoop_complexMass_contour_link
    (y v omega0 hbar c e FtildeF M P : ℝ) (hc : c ≠ 0) :
    effectiveScalarMass 0 y (v / Real.sqrt 2) = yukawaMass y v
      ∧ (yukawaComplexRestEnergy y v omega0 hbar c).im =
          yukawaEntropyRate y omega0 hbar
      ∧ qedYukawaOddEffectiveLagrangian e FtildeF M P =
          e ^ 2 / (8 * Real.pi ^ 2) * qedYukawaChiralAngle M P * FtildeF := by
  exact ⟨effectiveScalarMass_higgsVEV_eq_yukawaMass y v,
    yukawaComplexRestEnergy_im_eq_entropyRate y v omega0 hbar c hc,
    qedYukawaOddEffectiveLagrangian_eq_theta e FtildeF M P⟩

/-- Bundled statement connecting the paper's one-loop constant-background data
to existing repo carriers: Standard Model Yukawa mass, Berezin determinant,
Euler-Heisenberg limit, odd arctangent phase, and the pseudoscalar-current
derivative. -/
lemma qedYukawa_oneLoop_repository_bridge
    (e FtildeF a b y v lambda s M P : ℝ) (hM : M ≠ 0) :
    effectiveScalarMass 0 y (v / Real.sqrt 2) = yukawaMass y v
      ∧ berezin (fermionGaussian (effectiveYukawaMassModulus 0 y (v / Real.sqrt 2) lambda 0))
          =
          (!![effectiveYukawaMassModulus 0 y (v / Real.sqrt 2) lambda 0] :
            Matrix (Fin 1) (Fin 1) ℝ).det
      ∧ qedYukawaEvenProperTimeKernelFromFields e FtildeF a b 0 y (v / Real.sqrt 2) lambda 0 s =
          qedYukawaEvenProperTimeKernel e FtildeF a b (yukawaMass y v ^ 2) s
      ∧ qedYukawaOddEffectiveLagrangian e FtildeF M P =
          e ^ 2 / (8 * Real.pi ^ 2) * qedYukawaChiralAngle M P * FtildeF
      ∧ HasDerivAt (fun P => qedYukawaOddEffectiveLagrangian e FtildeF M P)
          (qedYukawaOddCurrentRationalFactor e FtildeF M P) P := by
  refine ⟨effectiveScalarMass_higgsVEV_eq_yukawaMass y v,
    berezin_effectiveYukawaMassModulus_eq_det 0 y (v / Real.sqrt 2) lambda 0,
    ?_, qedYukawaOddEffectiveLagrangian_eq_theta e FtildeF M P,
    qedYukawaOdd_hasDerivAt_pseudoscalar e FtildeF M P hM⟩
  simp [qedYukawaEvenProperTimeKernelFromFields,
    effectiveYukawaMassSq_higgsVEV_eq_yukawaMass_sq]

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction

end

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction.effectiveYukawaMassSq_nonneg where
  formalizes @ "claim:the-one-loop-effective-yukawa-background-mass-squared-the-sum-of-the-scalar-and-pseudoscalar-effective-mass-squares-is-non-negative",
  supported_by @ "paper:jacobson-ter-veldhuis-non-perturbative-one-loop-effective-action-for-qed-with-yukawa-couplings"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction.effectiveScalarMass_higgsVEV_eq_yukawaMass where
  formalizes @ "claim:with-zero-bare-mass-and-the-scalar-background-set-to-the-higgs-vev-the-one-loop-effective-scalar-mass-equals-the-standard-model-yukawa-mass"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction.chiral_modulus_sq_invariant where
  formalizes @ "claim:the-even-sector-of-the-one-loop-effective-action-depends-only-on-the-chiral-modulus-the-sum-of-squared-scalar-and-pseudoscalar-mass-coordinates-invariant-under-the-chiral-rotation"

zil attach Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction.qedYukawaOddEffectiveLagrangian_eq_theta where
  formalizes @ "claim:the-odd-parity-one-loop-effective-lagrangian-is-e-squared-over-eight-pi-squared-times-the-chiral-angle-times-f-dual-f-the-axial-anomaly-theta-term-generated-by-the-pseudoscalar-yukawa-coupling"

zil_file_contract physlib.qedYukawaOneLoopEffectiveAction where
  promises "The constant-background algebraic core of the non-perturbative one-loop effective action for QED with scalar and pseudoscalar Yukawa couplings (Jacobson and ter Veldhuis). The effective background mass-squared -- the sum of the scalar and pseudoscalar effective mass-squares -- is non-negative (effectiveYukawaMassSq_nonneg), and with zero bare mass at the Higgs VEV background the effective scalar mass is the Standard Model Yukawa mass (effectiveScalarMass_higgsVEV_eq_yukawaMass). The even (parity-conserving) sector depends only on the chiral modulus M^2 + P^2, invariant under the chiral rotation (chiral_modulus_sq_invariant), while the odd (parity-violating) effective Lagrangian is e^2/(8 pi^2) times the chiral angle times F-dual-F -- the axial-anomaly theta term generated by the pseudoscalar Yukawa coupling (qedYukawaOddEffectiveLagrangian_eq_theta)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction.effectiveYukawaMassSq",
    "lean:Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction.qedYukawaChiralAngle"]
  forbids_substitutes ["the proper-time / heat-kernel evaluation of the one-loop fermion determinant that produces these effective couplings, which is the cited non-perturbative-QFT infrastructure summarized by the constant-background formulas",
    "any renormalization-group running of the couplings, only the constant-background effective-action algebra and the anomaly theta-term are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction.effectiveYukawaMassSq_nonneg,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction.effectiveScalarMass_higgsVEV_eq_yukawaMass,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction.chiral_modulus_sq_invariant,
    Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDYukawaOneLoopEffectiveAction.qedYukawaOddEffectiveLagrangian_eq_theta]

/- ZIL-END -/
