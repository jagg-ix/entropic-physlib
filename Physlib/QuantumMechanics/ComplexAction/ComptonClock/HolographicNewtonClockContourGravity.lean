/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3
public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor

/-!
# Holographic Newton coupling, Compton clocks, Nagao–Nielsen contours, and gravity

This module composes existing Physlib results into one auditable bridge.  A
single positive mass `m` is used for

* the Compton screen radius `r = λ_C log K`,
* the moving de Broglie clock,
* the Lorentz-invariant mass shell represented as a Nagao–Nielsen complex
  coordinate.

The same holographic Newton constant `G` supplies the Einstein coupling
`κ_G = 8πG/c⁴`.  The rapidity of the massive energy–momentum point determines a
permitted Nagao–Nielsen ray; the point is proved to lie on that ray with a
positive real parameter, and the complex delta has the proved normalization
there.  On the geometric side, the weak-field connection is identified with
the Christoffel symbols built from the metric, its exact `R₀₀` is computed, and
the resulting connection-derived Ricci matrix is used directly by the complex
Einstein equation together with the scalar curvature and metric derived from
the same geometry.  The complex equation then yields the ordinary Einstein
field equation, its connection-grounded `(0,0)` component, and Levi-Civita's
d'Alembert balance.

The capstone is conditional.  In particular:

* `G` is not numerically predicted; the holographic bit count contains `G`;
* the complex Einstein field equation is a hypothesis, not derived from the
  clock or contour identities;
* the exact `1+1` Einstein tensor vanishes, so the assumed field equation
  forces its `T` carrier to be zero; the nonzero-density Newtonian relation is
  a separate trace-reversed limit and a sourced equation requires a `3+1`
  geometry;
* the exact connection Ricci contains the displayed `O(c⁻⁴)` correction, which
  is not silently discarded;
* the rapidity-parametrized energy–momentum coordinate has an exact positive
  representation on the derived ray; this is not a uniqueness theorem for all
  admissible contours.

The name “Levi-Civita” occurs in two precise senses: the metric-compatible,
torsion-free connection used to construct curvature, and Levi-Civita's
gravitational/inertial tensor used in the d'Alembert balance.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity

open MeasureTheory
open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianAndGRLimit
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NewtonianLimitCurvatureAPI
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ScreenCouplingReductions
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.StaticPotentialJet3
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.WeakFieldEinstein3Plus1
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.Curvature.LeviCivitaFromMetric
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

/-! # A. The mass-shell rapidity determines a permitted contour -/

/--
The Nagao–Nielsen contour angle associated with a massive energy–momentum
rapidity `θ`.  Its tangent is the velocity-like slope `tanh θ` of the
`E/c + i p` coordinate.
-/
noncomputable def massShellContourAngle (θ : ℝ) : ℝ :=
  Real.arctan (Real.tanh θ)

/--
The rapidity-derived mass-shell angle lies strictly inside the permitted
Nagao–Nielsen contour sector `|ϑ| < π/4`.
-/
lemma massShellContourAngle_permitted (θ : ℝ) :
    |massShellContourAngle θ| < Real.pi / 4 := by
  rw [abs_lt]
  constructor
  · have h :=
      (Real.arctan_lt_arctan_iff).2 (Real.neg_one_lt_tanh θ)
    simpa [massShellContourAngle, Real.arctan_neg, Real.arctan_one] using h
  · have h :=
      (Real.arctan_lt_arctan_iff).2 (Real.tanh_lt_one θ)
    simpa [massShellContourAngle, Real.arctan_one] using h

/-- The tangent of the mass-shell contour angle is exactly `tanh θ`. -/
lemma tan_massShellContourAngle (θ : ℝ) :
    Real.tan (massShellContourAngle θ) = Real.tanh θ := by
  simp [massShellContourAngle]

/--
For positive mass and light speed, the imaginary-to-real slope of
`E/c + i p` at `p = mc sinh θ` is `tanh θ`.
-/
lemma energyMomentumComplex_slope_eq_tanh (m c θ : ℝ)
    (hm : 0 < m) (hc : 0 < c) :
    (energyMomentumComplex m c (m * c * Real.sinh θ)).im /
        (energyMomentumComplex m c (m * c * Real.sinh θ)).re =
      Real.tanh θ := by
  unfold energyMomentumComplex
  rw [einsteinEnergy_eq_rest_cosh_rapidity m c θ hm.le,
    Real.tanh_eq_sinh_div_cosh]
  field_simp [hm.ne', hc.ne', (Real.cosh_pos θ).ne']

/--
The rapidity-derived contour angle has the same tangent as the slope of the
mass-shell energy–momentum complex coordinate.
-/
lemma energyMomentumComplex_slope_eq_tan_massShellContourAngle
    (m c θ : ℝ) (hm : 0 < m) (hc : 0 < c) :
    (energyMomentumComplex m c (m * c * Real.sinh θ)).im /
        (energyMomentumComplex m c (m * c * Real.sinh θ)).re =
      Real.tan (massShellContourAngle θ) := by
  rw [energyMomentumComplex_slope_eq_tanh m c θ hm hc,
    tan_massShellContourAngle]

/--
The positive real parameter placing the massive energy–momentum coordinate on
the ray selected by `massShellContourAngle`.
-/
noncomputable def massShellContourRadius (m c θ : ℝ) : ℝ :=
  m * c * Real.cosh θ / Real.cos (massShellContourAngle θ)

/-- The rapidity-derived ray parameter is positive for positive `m` and `c`. -/
lemma massShellContourRadius_pos (m c θ : ℝ) (hm : 0 < m) (hc : 0 < c) :
    0 < massShellContourRadius m c θ := by
  unfold massShellContourRadius massShellContourAngle
  exact div_pos (mul_pos (mul_pos hm hc) (Real.cosh_pos θ))
    (Real.cos_arctan_pos (Real.tanh θ))

/--
The massive energy–momentum coordinate is exactly a positive point on the
Nagao–Nielsen ray determined by its rapidity.
-/
lemma energyMomentumComplex_eq_massShellContourRay
    (m c θ : ℝ) (hm : 0 < m) (hc : 0 < c) :
    energyMomentumComplex m c (m * c * Real.sinh θ) =
      Complex.exp (massShellContourAngle θ * Complex.I) *
        (massShellContourRadius m c θ : ℂ) := by
  have hAngleCos : Real.cos (massShellContourAngle θ) ≠ 0 := by
    unfold massShellContourAngle
    exact (Real.cos_arctan_pos (Real.tanh θ)).ne'
  apply Complex.ext
  · rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    simp only [energyMomentumComplex, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    rw [einsteinEnergy_eq_rest_cosh_rapidity m c θ hm.le]
    unfold massShellContourRadius
    field_simp [hc.ne', hAngleCos]
  · rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    simp only [energyMomentumComplex, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add]
    unfold massShellContourRadius
    have htan := tan_massShellContourAngle θ
    rw [Real.tan_eq_sin_div_cos, Real.tanh_eq_sinh_div_cosh] at htan
    field_simp [hAngleCos, (Real.cosh_pos θ).ne'] at htan ⊢
    nlinarith [htan]

/--
The complex delta is normalized on the contour ray selected by the same
rapidity as the massive energy–momentum point.
-/
lemma massShellContour_normalization (θ ε : ℝ) (hε : 0 < ε) :
    (∫ s : ℝ,
      deltaEpsC ε (Complex.exp (massShellContourAngle θ * Complex.I) * s) *
        Complex.exp (massShellContourAngle θ * Complex.I)) = 1 :=
  contour_normalization hε (massShellContourAngle_permitted θ)

/-! # B. Conditional end-to-end composition -/

/--
**Conditional end-to-end bridge from holographic `G` to clocks, contours, the
Levi-Civita connection, and the Einstein field equation.**

The shared coupling is `κ_G = 8πG/c⁴`.  The metric, Ricci matrix, and scalar
curvature used by `hComplex` are all constructed from the exact `1+1`
metric-derived Levi-Civita geometry, so no independent geometric carrier or
component-identification assumption is required.  The complex Einstein
equation itself remains an explicit hypothesis.  Its real source is proved to
vanish, exposing the dimensional limitation rather than treating this
demonstrator as a sourced `3+1` equation.
-/
theorem holographicNewton_comptonNagaoLeviCivita_einstein_chain
    (G ℏ c N d2Φ ρ M m kB Δx η θ ε A dΦ : ℝ)
    (Λ T S : Matrix (Fin 2) (Fin 2) ℝ)
    (hℏ : 0 < ℏ) (hkB : 0 < kB) (hc : 0 < c) (hm : 0 < m)
    (hη : 0 < η) (hΔx : 0 < Δx) (hG : G ≠ 0) (hA : A ≠ 0)
    (hε : 0 < ε)
    (hN : N = holographicBits
      (sphereArea (entropicProperDistance m c ℏ η)) G ℏ c)
    (hWeak : weakFieldRicci00 d2Φ c = 4 * Real.pi * G * ρ / c ^ 2)
    (hComplex :
      complexEinsteinFieldEquation
        (einsteinTensor (weakFieldRicciMatrix2 A dΦ d2Φ c)
          (weakFieldScalarCurvature2 A dΦ d2Φ c) (weakFieldMetric2 A)) Λ T S
        (8 * Real.pi * G / c ^ 4)) :
    G = sphereArea (entropicProperDistance m c ℏ η) * c ^ 3 / (ℏ * N)
    ∧ 8 * Real.pi * G / c ^ 4 =
        8 * Real.pi * (sphereArea (entropicProperDistance m c ℏ η) / N) / (ℏ * c)
    ∧ d2Φ = 4 * Real.pi * G * ρ
    ∧ verlindeEntropicForce (verlindeGravityTemperature M G ℏ c
          (entropicProperDistance m c ℏ η) kB)
        (verlindeDisplacementEntropy ℏ kB m c Δx) Δx =
          G * M * m / (entropicProperDistance m c ℏ η) ^ 2
    ∧ entropicProperDistance m c ℏ η =
        comptonWavelength m c ℏ * Real.log (schmidtNumber η)
    ∧ deBroglieFrequency (einsteinEnergy m c (m * c * Real.sinh θ)) ℏ =
        Real.cosh θ * comptonFrequency m c ℏ
    ∧ nnLorentzForm (energyMomentumComplex m c (m * c * Real.sinh θ)) =
        (m * c) ^ 2
    ∧ nnConverges (energyMomentumComplex m c (m * c * Real.sinh θ))
    ∧ (energyMomentumComplex m c (m * c * Real.sinh θ)).im /
          (energyMomentumComplex m c (m * c * Real.sinh θ)).re =
        Real.tan (massShellContourAngle θ)
    ∧ 0 < massShellContourRadius m c θ
    ∧ energyMomentumComplex m c (m * c * Real.sinh θ) =
        Complex.exp (massShellContourAngle θ * Complex.I) *
          (massShellContourRadius m c θ : ℂ)
    ∧ (∫ s : ℝ,
        deltaEpsC ε
            (Complex.exp (massShellContourAngle θ * Complex.I) * s) *
          Complex.exp (massShellContourAngle θ * Complex.I)) = 1
    ∧ weakFieldLeviCivita2 A (2 * dΦ / c ^ 2) =
        christoffelFromMetric (weakFieldMetric2Inv A)
          (weakFieldMetricDeriv2 (2 * dΦ / c ^ 2))
    ∧ ricciFromConnection
          (weakFieldLeviCivita2 A (2 * dΦ / c ^ 2))
          (weakFieldConnDeriv2 A (2 * dΦ / c ^ 2) (2 * d2Φ / c ^ 2)) 0 0 =
        weakFieldRicci00 d2Φ c - dΦ ^ 2 / (c ^ 4 * A)
    ∧ weakFieldScalarCurvature2 A dΦ d2Φ c =
        2 / A * (weakFieldRicci00 d2Φ c - dΦ ^ 2 / (c ^ 4 * A))
    ∧ einsteinTensor (weakFieldRicciMatrix2 A dΦ d2Φ c)
          (weakFieldScalarCurvature2 A dΦ d2Φ c) (weakFieldMetric2 A) = 0
    ∧ einsteinFieldEquation (weakFieldRicciMatrix2 A dΦ d2Φ c)
        (weakFieldScalarCurvature2 A dΦ d2Φ c) (weakFieldMetric2 A) T
        (8 * Real.pi * G / c ^ 4)
    ∧ ricciFromConnection
          (weakFieldLeviCivita2 A (2 * dΦ / c ^ 2))
          (weakFieldConnDeriv2 A (2 * dΦ / c ^ 2) (2 * d2Φ / c ^ 2)) 0 0
        - weakFieldScalarCurvature2 A dΦ d2Φ c / 2 * weakFieldMetric2 A 0 0 =
          (8 * Real.pi * G / c ^ 4) * T 0 0
    ∧ T = 0
    ∧ T + gravitationalTensor (weakFieldRicciMatrix2 A dΦ d2Φ c)
        (weakFieldScalarCurvature2 A dΦ d2Φ c) (weakFieldMetric2 A)
        (8 * Real.pi * G / c ^ 4) = 0
    ∧ Λ = (8 * Real.pi * G / c ^ 4) • S := by
  have hComptonWavelength : 0 < comptonWavelength m c ℏ :=
    comptonWavelength_pos m c ℏ hm hc hℏ
  have hlogK : 0 < Real.log (schmidtNumber η) :=
    Real.log_pos (schmidtNumber_gt_one η hη)
  have hR : 0 < entropicProperDistance m c ℏ η := by
    unfold entropicProperDistance
    positivity
  have hNewton :=
    entropicNewtonConstant_converges G ℏ c N (entropicProperDistance m c ℏ η)
      d2Φ ρ M m kB Δx hℏ hkB hc hR hΔx hG hN hWeak
  have hClock :
      deBroglieFrequency (einsteinEnergy m c (m * c * Real.sinh θ)) ℏ =
        Real.cosh θ * comptonFrequency m c ℏ := by
    rw [einsteinEnergy_eq_rest_cosh_rapidity m c θ hm.le]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      deBroglie_eq_gamma_compton (Real.cosh θ) m c ℏ
  have hMassShell :
      nnLorentzForm (energyMomentumComplex m c (m * c * Real.sinh θ)) =
        (m * c) ^ 2 :=
    nnLorentzForm_energyMomentum m c (m * c * Real.sinh θ) hc.ne'
  have hConverges :
      nnConverges (energyMomentumComplex m c (m * c * Real.sinh θ)) :=
    (nnConverges_energyMomentum_iff m c (m * c * Real.sinh θ) hc.ne').2
      (mul_ne_zero hm.ne' hc.ne')
  have hSlope :
      (energyMomentumComplex m c (m * c * Real.sinh θ)).im /
          (energyMomentumComplex m c (m * c * Real.sinh θ)).re =
        Real.tan (massShellContourAngle θ) :=
    energyMomentumComplex_slope_eq_tan_massShellContourAngle m c θ hm hc
  have hRadius : 0 < massShellContourRadius m c θ :=
    massShellContourRadius_pos m c θ hm hc
  have hRay :
      energyMomentumComplex m c (m * c * Real.sinh θ) =
        Complex.exp (massShellContourAngle θ * Complex.I) *
          (massShellContourRadius m c θ : ℂ) :=
    energyMomentumComplex_eq_massShellContourRay m c θ hm hc
  have hContour :
      (∫ s : ℝ,
        deltaEpsC ε
            (Complex.exp (massShellContourAngle θ * Complex.I) * s) *
          Complex.exp (massShellContourAngle θ * Complex.I)) = 1 :=
    massShellContour_normalization θ ε hε
  have hConnection :=
    weakFieldLeviCivita2_eq_christoffelFromMetric
      A (2 * dΦ / c ^ 2) hA
  have hRicci :=
    weakField_ricci00_from_connection_newtonian A dΦ d2Φ c hA hc.ne'
  have hScalar :=
    weakFieldScalarCurvature2_eq A dΦ d2Φ c hA hc.ne'
  have hEinsteinZero :=
    weakFieldEinsteinTensor2_eq_zero A dΦ d2Φ c hA hc.ne'
  have hRealEinstein :
      einsteinFieldEquation (weakFieldRicciMatrix2 A dΦ d2Φ c)
        (weakFieldScalarCurvature2 A dΦ d2Φ c) (weakFieldMetric2 A) T
        (8 * Real.pi * G / c ^ 4) :=
    (complexEinsteinFieldEquation_iff_einstein
      (weakFieldRicciMatrix2 A dΦ d2Φ c)
        (weakFieldScalarCurvature2 A dΦ d2Φ c) (weakFieldMetric2 A) Λ T S
        (8 * Real.pi * G / c ^ 4)).mp hComplex |>.1
  have hκ : 8 * Real.pi * G / c ^ 4 ≠ 0 :=
    div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hG)
      (pow_ne_zero 4 hc.ne')
  have hLeviCivita :=
    complexEinstein_real_is_dAlembert
      (weakFieldRicciMatrix2 A dΦ d2Φ c)
      (weakFieldScalarCurvature2 A dΦ d2Φ c) (weakFieldMetric2 A) Λ T S
      (8 * Real.pi * G / c ^ 4) hκ hComplex
  have hTzero : T = 0 := by
    unfold einsteinFieldEquation at hRealEinstein
    rw [hEinsteinZero] at hRealEinstein
    exact (smul_eq_zero.mp hRealEinstein.symm).resolve_left hκ
  have h00 :
      ricciFromConnection
          (weakFieldLeviCivita2 A (2 * dΦ / c ^ 2))
          (weakFieldConnDeriv2 A (2 * dΦ / c ^ 2) (2 * d2Φ / c ^ 2)) 0 0
        - weakFieldScalarCurvature2 A dΦ d2Φ c / 2 * weakFieldMetric2 A 0 0 =
          (8 * Real.pi * G / c ^ 4) * T 0 0 := by
    exact einsteinFieldEquation_apply_00 0
      (weakFieldRicciMatrix2 A dΦ d2Φ c) (weakFieldMetric2 A) T
        (weakFieldScalarCurvature2 A dΦ d2Φ c)
        (8 * Real.pi * G / c ^ 4) hRealEinstein
  exact
    ⟨hNewton.1,
      hNewton.2.1,
      hNewton.2.2.1,
      hNewton.2.2.2,
      rfl,
      hClock,
      hMassShell,
      hConverges,
      hSlope,
      hRadius,
      hRay,
      hContour,
      hConnection,
      hRicci,
      hScalar,
      hEinsteinZero,
      hRealEinstein,
      h00,
      hTzero,
      hLeviCivita.1,
      hLeviCivita.2⟩

/-! # C. Sourced linearized `3+1` upgrade -/

/--
**Holographic `G`, the Compton/de Broglie clock, the Nagao–Nielsen contour,
and a sourced linearized `3+1` Einstein equation.**

This theorem upgrades the geometric end of the preceding `1+1` demonstrator.
The screen relation yields the same Poisson equation, which now implies a full
`Fin 4` rest-dust Einstein matrix equation through
`WeakFieldEinstein3Plus1.weakFieldLinearizedEFE4_of_poisson`.  The
source-bearing `R₀₀` is identified with the first-order connection contraction,
and the Newtonian acceleration Christoffel symbol is computed by the general
metric-to-Levi-Civita construction.  The complex equation is derived only after
the imaginary-sector relation `Λ = κS` is supplied explicitly.

The carrier is linearized and plane-symmetric: it is a genuine `3+1` tensor
equation, but it is not an exact nonlinear or general three-coordinate
solution.
-/
theorem holographicNewton_comptonNagaoLeviCivita_linearizedEinstein4_chain
    (G ℏ c N d2Φ ρ m η θ ε dΦ : ℝ)
    (Λ S : Matrix (Fin 4) (Fin 4) ℝ)
    (hℏ : 0 < ℏ) (hc : 0 < c) (hm : 0 < m) (hη : 0 < η)
    (hG : G ≠ 0) (hε : 0 < ε)
    (hN : N = holographicBits
      (sphereArea (entropicProperDistance m c ℏ η)) G ℏ c)
    (hWeak : weakFieldRicci00 d2Φ c = 4 * Real.pi * G * ρ / c ^ 2)
    (hImaginary : Λ = (8 * Real.pi * G / c ^ 4) • S) :
    G = sphereArea (entropicProperDistance m c ℏ η) * c ^ 3 / (ℏ * N)
    ∧ 8 * Real.pi * G / c ^ 4 =
        8 * Real.pi * (sphereArea (entropicProperDistance m c ℏ η) / N) / (ℏ * c)
    ∧ d2Φ = 4 * Real.pi * G * ρ
    ∧ deBroglieFrequency (einsteinEnergy m c (m * c * Real.sinh θ)) ℏ =
        Real.cosh θ * comptonFrequency m c ℏ
    ∧ energyMomentumComplex m c (m * c * Real.sinh θ) =
        Complex.exp (massShellContourAngle θ * Complex.I) *
          (massShellContourRadius m c θ : ℂ)
    ∧ (∫ s : ℝ,
        deltaEpsC ε (Complex.exp (massShellContourAngle θ * Complex.I) * s) *
          Complex.exp (massShellContourAngle θ * Complex.I)) = 1
    ∧ weakFieldLinearizedLeviCivita4 dΦ c 1 0 0 = dΦ / c ^ 2
    ∧ weakFieldLinearizedRicci4 d2Φ c 0 0 =
        ricciFromConnection (fun _ => 0) (weakFieldLinearizedConnDeriv4 d2Φ c) 0 0
    ∧ einsteinFieldEquation (weakFieldLinearizedRicci4 d2Φ c)
        (weakFieldLinearizedScalar4 d2Φ c) minkowskiMetric4
        (restDustStressEnergy4 ρ c) (8 * Real.pi * G / c ^ 4)
    ∧ complexEinsteinFieldEquation (weakFieldLinearizedEinstein4 d2Φ c) Λ
        (restDustStressEnergy4 ρ c) S (8 * Real.pi * G / c ^ 4) := by
  have hComptonWavelength : 0 < comptonWavelength m c ℏ :=
    comptonWavelength_pos m c ℏ hm hc hℏ
  have hlogK : 0 < Real.log (schmidtNumber η) :=
    Real.log_pos (schmidtNumber_gt_one η hη)
  have hR : 0 < entropicProperDistance m c ℏ η := by
    unfold entropicProperDistance
    positivity
  obtain ⟨hScreenG, hScreenKappa, hPoisson⟩ :=
    newtonG_is_area_per_bit_reproducing_newton G ℏ c N
      (entropicProperDistance m c ℏ η) d2Φ ρ hℏ.ne' hc.ne' hG hR.ne' hN hWeak
  have hClock :
      deBroglieFrequency (einsteinEnergy m c (m * c * Real.sinh θ)) ℏ =
        Real.cosh θ * comptonFrequency m c ℏ := by
    rw [einsteinEnergy_eq_rest_cosh_rapidity m c θ hm.le]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      deBroglie_eq_gamma_compton (Real.cosh θ) m c ℏ
  have hRay := energyMomentumComplex_eq_massShellContourRay m c θ hm hc
  have hContour := massShellContour_normalization θ ε hε
  have hConnection := weakFieldLinearizedLeviCivita4_100 dΦ c
  have hRicci := weakFieldLinearizedRicci4_apply_00_eq_connection d2Φ c
  have hEFE := weakFieldLinearizedEFE4_of_poisson G c ρ d2Φ hc.ne' hPoisson
  have hComplex := weakFieldLinearizedComplexEFE4_of_poisson
    G c ρ d2Φ Λ S hc.ne' hPoisson hImaginary
  exact ⟨hScreenG, hScreenKappa, hPoisson, hClock, hRay, hContour,
    hConnection, hRicci, hEFE, hComplex⟩

/-! # D. Full static spatial-Laplacian capstone -/

/--
**The holographic-Newton/clock/contour chain with a complete connection-derived static `Fin 4`
linearized Einstein carrier.**

This strengthens the plane-symmetric capstone to an arbitrary local static spatial gradient and
symmetric Hessian.  The screen relation yields the three-dimensional Poisson equation
`∂ₓ²Φ + ∂ᵧ²Φ + ∂𝓏²Φ = 4πGρ`.  All sixteen Ricci components are contracted from the explicit
linearized connection derivative; the mixed Hessian entries cancel, and the resulting Ricci matrix
feeds the real and complex Einstein equations.  The statement remains first-order and static: it is
not an exact nonlinear solution and makes no spherical-symmetry assumption.
-/
theorem holographicNewton_comptonNagaoLeviCivita_linearizedEinstein4Spatial_chain
    (G ℏ c N ρ m η θ ε dxΦ dyΦ dzΦ dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ : ℝ)
    (Λ S : Matrix (Fin 4) (Fin 4) ℝ)
    (hℏ : 0 < ℏ) (hc : 0 < c) (hm : 0 < m) (hη : 0 < η)
    (hG : G ≠ 0) (hε : 0 < ε)
    (hN : N = holographicBits
      (sphereArea (entropicProperDistance m c ℏ η)) G ℏ c)
    (hWeak : weakFieldRicci00 (spatialLaplacian3 dxxΦ dyyΦ dzzΦ) c =
      4 * Real.pi * G * ρ / c ^ 2)
    (hImaginary : Λ = (8 * Real.pi * G / c ^ 4) • S) :
    G = sphereArea (entropicProperDistance m c ℏ η) * c ^ 3 / (ℏ * N)
    ∧ 8 * Real.pi * G / c ^ 4 =
        8 * Real.pi * (sphereArea (entropicProperDistance m c ℏ η) / N) / (ℏ * c)
    ∧ spatialLaplacian3 dxxΦ dyyΦ dzzΦ = 4 * Real.pi * G * ρ
    ∧ deBroglieFrequency (einsteinEnergy m c (m * c * Real.sinh θ)) ℏ =
        Real.cosh θ * comptonFrequency m c ℏ
    ∧ energyMomentumComplex m c (m * c * Real.sinh θ) =
        Complex.exp (massShellContourAngle θ * Complex.I) *
          (massShellContourRadius m c θ : ℂ)
    ∧ (∫ s : ℝ,
        deltaEpsC ε (Complex.exp (massShellContourAngle θ * Complex.I) * s) *
          Complex.exp (massShellContourAngle θ * Complex.I)) = 1
    ∧ (weakFieldLinearizedLeviCivita4Spatial dxΦ dyΦ dzΦ c 1 0 0 = dxΦ / c ^ 2
      ∧ weakFieldLinearizedLeviCivita4Spatial dxΦ dyΦ dzΦ c 2 0 0 = dyΦ / c ^ 2
      ∧ weakFieldLinearizedLeviCivita4Spatial dxΦ dyΦ dzΦ c 3 0 0 = dzΦ / c ^ 2)
    ∧ weakFieldLinearizedLeviCivita4Spatial dxΦ dyΦ dzΦ c =
        weakFieldLinearizedConnection4Spatial dxΦ dyΦ dzΦ c
    ∧ ricciMatrixFromConnection (fun _ => 0)
        (weakFieldLinearizedLeviCivitaDeriv4Spatial
          dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c) =
      !![spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2, 0, 0, 0;
         0, spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2, 0, 0;
         0, 0, spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2, 0;
         0, 0, 0, spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2]
    ∧ einsteinFieldEquation
        (weakFieldLinearizedRicci4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c)
        (weakFieldLinearizedScalar4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c)
        minkowskiMetric4 (restDustStressEnergy4 ρ c) (8 * Real.pi * G / c ^ 4)
    ∧ complexEinsteinFieldEquation
        (weakFieldLinearizedEinstein4Spatial dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c) Λ
        (restDustStressEnergy4 ρ c) S (8 * Real.pi * G / c ^ 4) := by
  have hComptonWavelength : 0 < comptonWavelength m c ℏ :=
    comptonWavelength_pos m c ℏ hm hc hℏ
  have hlogK : 0 < Real.log (schmidtNumber η) :=
    Real.log_pos (schmidtNumber_gt_one η hη)
  have hR : 0 < entropicProperDistance m c ℏ η := by
    unfold entropicProperDistance
    positivity
  obtain ⟨hScreenG, hScreenKappa, hPoisson⟩ :=
    newtonG_is_area_per_bit_reproducing_newton G ℏ c N
      (entropicProperDistance m c ℏ η) (spatialLaplacian3 dxxΦ dyyΦ dzzΦ) ρ
      hℏ.ne' hc.ne' hG hR.ne' hN hWeak
  have hClock :
      deBroglieFrequency (einsteinEnergy m c (m * c * Real.sinh θ)) ℏ =
        Real.cosh θ * comptonFrequency m c ℏ := by
    rw [einsteinEnergy_eq_rest_cosh_rapidity m c θ hm.le]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      deBroglie_eq_gamma_compton (Real.cosh θ) m c ℏ
  have hRay := energyMomentumComplex_eq_massShellContourRay m c θ hm hc
  have hContour := massShellContour_normalization θ ε hε
  have hConnection :=
    weakFieldLinearizedLeviCivita4Spatial_acceleration dxΦ dyΦ dzΦ c
  have hFullConnection :=
    weakFieldLinearizedLeviCivita4Spatial_eq_connection dxΦ dyΦ dzΦ c
  have hRicci :
      ricciMatrixFromConnection (fun _ => 0)
          (weakFieldLinearizedLeviCivitaDeriv4Spatial
            dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c) =
        !![spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2, 0, 0, 0;
           0, spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2, 0, 0;
           0, 0, spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2, 0;
           0, 0, 0, spatialLaplacian3 dxxΦ dyyΦ dzzΦ / c ^ 2] := by
    simpa [weakFieldLinearizedRicci4Spatial] using
      weakFieldLinearizedRicci4Spatial_eq
        dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ c
  have hEFE := weakFieldLinearizedEFE4Spatial_of_poisson
    G c ρ dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ hc.ne' hPoisson
  have hComplex := weakFieldLinearizedComplexEFE4Spatial_of_poisson
    G c ρ dxxΦ dyyΦ dzzΦ dxyΦ dxzΦ dyzΦ Λ S hc.ne' hPoisson hImaginary
  exact ⟨hScreenG, hScreenKappa, hPoisson, hClock, hRay, hContour,
    hConnection, hFullConnection, hRicci, hEFE, hComplex⟩

/-! # E. Typed static-potential-jet capstone -/

/--
The full static spatial capstone expressed through one `StaticPotentialJet3`.

The jet packages the potential value, spatial gradient, and symmetric Hessian.  Its adapters feed
the same metric-derived connection and complete connection-derived Ricci carrier proved above.
This theorem is the intended downstream API: projects can construct or derive one jet and avoid
passing the individual Cartesian derivative components separately.
-/
theorem holographicNewton_comptonNagaoLeviCivita_staticPotentialJet3_chain
    (J : StaticPotentialJet3) (G ℏ c N ρ m η θ ε : ℝ)
    (Λ S : Matrix (Fin 4) (Fin 4) ℝ)
    (hℏ : 0 < ℏ) (hc : 0 < c) (hm : 0 < m) (hη : 0 < η)
    (hG : G ≠ 0) (hε : 0 < ε)
    (hN : N = holographicBits
      (sphereArea (entropicProperDistance m c ℏ η)) G ℏ c)
    (hWeak : weakFieldRicci00 J.laplacian c = 4 * Real.pi * G * ρ / c ^ 2)
    (hImaginary : Λ = (8 * Real.pi * G / c ^ 4) • S) :
    G = sphereArea (entropicProperDistance m c ℏ η) * c ^ 3 / (ℏ * N)
    ∧ 8 * Real.pi * G / c ^ 4 =
        8 * Real.pi * (sphereArea (entropicProperDistance m c ℏ η) / N) / (ℏ * c)
    ∧ J.SatisfiesPoisson G ρ
    ∧ deBroglieFrequency (einsteinEnergy m c (m * c * Real.sinh θ)) ℏ =
        Real.cosh θ * comptonFrequency m c ℏ
    ∧ energyMomentumComplex m c (m * c * Real.sinh θ) =
        Complex.exp (massShellContourAngle θ * Complex.I) *
          (massShellContourRadius m c θ : ℂ)
    ∧ (∫ s : ℝ,
        deltaEpsC ε (Complex.exp (massShellContourAngle θ * Complex.I) * s) *
          Complex.exp (massShellContourAngle θ * Complex.I)) = 1
    ∧ (J.leviCivita4 c 1 0 0 = J.gradient 0 / c ^ 2
      ∧ J.leviCivita4 c 2 0 0 = J.gradient 1 / c ^ 2
      ∧ J.leviCivita4 c 3 0 0 = J.gradient 2 / c ^ 2)
    ∧ J.leviCivita4 c =
        weakFieldLinearizedConnection4Spatial
          (J.gradient 0) (J.gradient 1) (J.gradient 2) c
    ∧ ricciMatrixFromConnection (fun _ => 0) (J.leviCivitaDeriv4 c) =
      !![J.laplacian / c ^ 2, 0, 0, 0;
         0, J.laplacian / c ^ 2, 0, 0;
         0, 0, J.laplacian / c ^ 2, 0;
         0, 0, 0, J.laplacian / c ^ 2]
    ∧ einsteinFieldEquation (J.ricci4 c) (J.scalar4 c) minkowskiMetric4
        (restDustStressEnergy4 ρ c) (8 * Real.pi * G / c ^ 4)
    ∧ complexEinsteinFieldEquation (J.einstein4 c) Λ
        (restDustStressEnergy4 ρ c) S (8 * Real.pi * G / c ^ 4) := by
  simpa [StaticPotentialJet3.SatisfiesPoisson, StaticPotentialJet3.laplacian,
    StaticPotentialJet3.leviCivita4, StaticPotentialJet3.leviCivitaDeriv4,
    StaticPotentialJet3.ricci4, StaticPotentialJet3.scalar4,
    StaticPotentialJet3.einstein4, spatialLaplacian3] using
    holographicNewton_comptonNagaoLeviCivita_linearizedEinstein4Spatial_chain
      G ℏ c N ρ m η θ ε
      (J.gradient 0) (J.gradient 1) (J.gradient 2)
      (J.hessian 0 0) (J.hessian 1 1) (J.hessian 2 2)
      (J.hessian 0 1) (J.hessian 0 2) (J.hessian 1 2)
      Λ S hℏ hc hm hη hG hε hN hWeak hImaginary

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.HolographicNewtonClockContourGravity

end
