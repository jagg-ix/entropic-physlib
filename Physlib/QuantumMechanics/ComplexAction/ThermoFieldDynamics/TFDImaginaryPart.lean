/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
meta import Zil

/-!
# The imaginary part in Thermo Field Dynamics (Fujimoto–Morikawa–Sasaki 1986)

Formalizes the algebraic core of *Y. Fujimoto, M. Morikawa, M. Sasaki, "Imaginary part in thermo field
dynamics", Phys. Rev. D 33 (1986) 590–593* — the sequel to `ThermoFieldDynamics.Basic` (Suzuki), computing the
imaginary part of self-energy Feynman diagrams in real-time finite-temperature TFD. Two structures carry the
result:

* the **thermo-Bogoliubov matrix** `U_B(θ) = [[cosh θ, sinh θ],[sinh θ, cosh θ]]` (Eq. 8) that diagonalizes
  the `2×2` thermo-propagator, with the thermal parametrization `sinh²θ = n_B = 1/(e^{βk₀}−1)` (Bose–Einstein);
  it is **unimodular** (`cosh²θ − sinh²θ = 1`) and sits on the Bogoliubov mass shell
  `cosh θ = bogoliubovEnergy(sinh θ, 1)`;
* the **hyperbolic imaginary-part relations** (Eqs. 13–14): `ImΣ̄ = tanh(βp₀/2)·ImΣ¹¹ = −sinh(βp₀/2)·ImΣ¹²`,
  whose consistency gives `ImΣ¹¹ = −cosh(βp₀/2)·ImΣ¹²` (Eq. 13) — the relation that makes the finite-`T`
  imaginary part computable in one short step.

* **§A — the thermo-Bogoliubov matrix** (`thermoBogoliubov`, `thermoBogoliubov_det`,
  `thermoBogoliubov_massShell`). The `U_B` of Eq. 8; unimodular; on the Bogoliubov mass shell.
* **§B — the Bose–Einstein parametrization** (`boseEinstein`, `thermal_cosh_sq`, `thermal_KMS_ratio`,
  `boseEinstein_eq_matsubara`). `sinh²θ = n_B ⟹ cosh²θ = 1 + n_B`; the detailed-balance/KMS ratio
  `cosh²θ/sinh²θ = e^{βk₀}`; and `n_B` in terms of the Matsubara/TFD Boltzmann weight.
* **§C — the imaginary-part relations** (`imaginaryPart_ratio`, `discontinuity`). Eqs. 13–14 and the
  discontinuity `disc Σ = −2i·ImΣ` (Eq. 6).
* **§D — the momentum and Matsubara contour layer** (`momentumGaussian_realAxis`,
  `momentum_wick_invariance`, `matsubaraFreq`, `bose_pole`, `bose_residue`). The Nagao-Nielsen
  Gaussian wedge supplies the loop Gaussian, while the Bose-factor poles give the Matsubara
  residue normalization used by the finite-temperature self-energy.

## References

* Y. Fujimoto, M. Morikawa, M. Sasaki, Phys. Rev. D 33 (1986) 590–593 (Eqs. 6, 8, 13–14).
* Repo carriers: `ThermoFieldDynamics.Basic` (the Suzuki TFD this extends; `matsubaraBoltzmannWeight`);
  `CausalDiamond.Helicity.diamond_horizon_energy` (`bogoliubovEnergy(sinh η,1) = cosh η`, the mass shell).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation


/-- **[Eq. 8] The thermo-Bogoliubov matrix** `U_B(θ) = [[cosh θ, sinh θ],[sinh θ, cosh θ]]` — the `2×2`
transformation diagonalizing the thermal propagator in the doubled TFD space. -/
noncomputable def thermoBogoliubov (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh θ, Real.sinh θ; Real.sinh θ, Real.cosh θ]

/-- **The thermo-Bogoliubov matrix is unimodular** `det U_B = cosh²θ − sinh²θ = 1` — a Lorentz boost (the
mass-shell relation). -/
lemma thermoBogoliubov_det (θ : ℝ) : (thermoBogoliubov θ).det = 1 := by
  rw [thermoBogoliubov, Matrix.det_fin_two_of]
  nlinarith [Real.cosh_sq_sub_sinh_sq θ]

/-- **The thermo-Bogoliubov angle sits on the Bogoliubov mass shell** `cosh θ = bogoliubovEnergy(sinh θ, 1)`
— the diagonal `cosh θ = √(sinh²θ + 1)` is the quasiparticle energy (`diamond_horizon_energy`), tying the
thermo-Bogoliubov to the diamond/mass-shell cluster. -/
lemma thermoBogoliubov_massShell (θ : ℝ) :
    Real.cosh θ = bogoliubovEnergy (Real.sinh θ) 1 :=
  (diamond_horizon_energy θ).symm


/-- **The Bose–Einstein occupation** `n_B(k) = 1/(e^{βk} − 1)` — the thermal weight `sinh²θ` of the
thermo-Bogoliubov. -/
noncomputable def boseEinstein (β k : ℝ) : ℝ := 1 / (Real.exp (β * k) - 1)

/-- **[Eq. 8] `cosh²θ = 1 + n_B`** — from the mass shell `cosh²θ − sinh²θ = 1` and `sinh²θ = n_B`. -/
lemma thermal_cosh_sq (θ β k : ℝ) (h : Real.sinh θ ^ 2 = boseEinstein β k) :
    Real.cosh θ ^ 2 = 1 + boseEinstein β k := by
  have := Real.cosh_sq_sub_sinh_sq θ
  rw [← h]; linarith

/-- **[Detailed balance / KMS] `cosh²θ = e^{βk}·sinh²θ`.** The ratio `cosh²θ/sinh²θ = (1+n_B)/n_B = e^{βk}` is
the KMS/detailed-balance condition of the thermal state. -/
lemma thermal_KMS_ratio (θ β k : ℝ) (h : Real.sinh θ ^ 2 = boseEinstein β k)
    (hk : Real.exp (β * k) ≠ 1) :
    Real.cosh θ ^ 2 = Real.exp (β * k) * Real.sinh θ ^ 2 := by
  have he : Real.exp (β * k) - 1 ≠ 0 := sub_ne_zero.mpr hk
  rw [thermal_cosh_sq θ β k h, h, boseEinstein]
  field_simp
  ring

/-- **`n_B` is the TFD/Matsubara Boltzmann weight** `n_B = w/(1 − w)`, `w = e^{−βk} = matsubaraBoltzmannWeight`
— the Bose–Einstein occupation in terms of the thermal weight of `ThermoFieldDynamics.Basic`. -/
lemma boseEinstein_eq_matsubara (β k : ℝ) (hk : Real.exp (β * k) ≠ 1) :
    boseEinstein β k = matsubaraBoltzmannWeight β k / (1 - matsubaraBoltzmannWeight β k) := by
  have he : Real.exp (β * k) - 1 ≠ 0 := sub_ne_zero.mpr hk
  have hpos : Real.exp (β * k) ≠ 0 := (Real.exp_pos _).ne'
  rw [boseEinstein, matsubaraBoltzmannWeight, Real.exp_neg]
  rw [div_eq_div_iff he (by
    rw [sub_ne_zero]; intro hc
    apply he
    field_simp at hc
    linarith [hc])]
  field_simp


/-- **[Eqs. 13–14] The imaginary-part ratio** `ImΣ¹¹ = −cosh(βp₀/2)·ImΣ¹²`. From `ImΣ̄ = tanh(x)·ImΣ¹¹`
(Eq. 14a) and `ImΣ̄ = −sinh(x)·ImΣ¹²` (Eq. 14b) with `x = βp₀/2`, consistency forces the component relation
(Eq. 13) — `tanh = sinh/cosh` cancels `sinh` to leave `cosh`. -/
lemma imaginaryPart_ratio (x imBar im11 im12 : ℝ)
    (h14a : imBar = Real.tanh x * im11) (h14b : imBar = -Real.sinh x * im12)
    (hsinh : Real.sinh x ≠ 0) :
    im11 = -Real.cosh x * im12 := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have htanh : Real.tanh x ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh]; exact div_ne_zero hsinh hc
  have h : Real.tanh x * im11 = -Real.sinh x * im12 := by rw [← h14a, h14b]
  have key : Real.tanh x * im11 = Real.tanh x * (-Real.cosh x * im12) := by
    rw [h, Real.tanh_eq_sinh_div_cosh]; field_simp
  exact mul_left_cancel₀ htanh key

/-- **[Eq. 6] The discontinuity** `disc Σ = −2i·ImΣ` — the imaginary part is half the discontinuity across the
cut, the physical content of the finite-`T` self-energy. -/
noncomputable def discontinuity (imPart : ℝ) : ℂ := -2 * Complex.I * imPart

end Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart

namespace Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDMatsubaraContour

open Real Complex
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourShift
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourGaussian


/-- **The real-time momentum Gaussian** `∫ e^{-ck²} dk = √(π/c)` — the Schwinger-parametrized
loop integral on the real-time contour, from the Nagao-Nielsen `gaussianContourIntegral`. -/
lemma momentumGaussian_realAxis (c : ℝ) (hc : 0 < c) :
    ∫ s : ℝ, contourIntegrand (gaussH c) 0 s = (Real.sqrt (π / c) : ℂ) :=
  gaussianContourIntegral hc (by rw [abs_zero]; positivity)

/-- **Real-time TFD = imaginary-time ITF for the loop Gaussian.** The real-time (`θ = 0`) and
Euclidean-rotated (`θ`) momentum Gaussians agree for any `|θ| < π / 4`. -/
lemma momentum_wick_invariance (c θ : ℝ) (hc : 0 < c) (hθ : |θ| < π / 4) :
    ∫ s : ℝ, contourIntegrand (gaussH c) 0 s = ∫ s : ℝ, contourIntegrand (gaussH c) θ s :=
  gaussianContourIntegral_indep hc (by rw [abs_zero]; positivity) hθ


/-- **The Matsubara frequency** `zₙ = 2πin/β`, the pole of the Bose factor
`1 / (e^{βz} - 1)` used to convert the frequency sum to a contour integral. -/
noncomputable def matsubaraFreq (β : ℝ) (n : ℤ) : ℂ := ((2 * π * n / β : ℝ) : ℂ) * Complex.I

/-- **Matsubara pole identity.** At every `zₙ = 2πin/β`, the Bose denominator satisfies
`e^{βzₙ} = 1`. -/
lemma bose_pole (β : ℝ) (n : ℤ) (hβ : β ≠ 0) :
    Complex.exp ((β : ℂ) * matsubaraFreq β n) = 1 := by
  unfold matsubaraFreq
  have h1 : β * (2 * π * (n : ℝ) / β) = 2 * π * (n : ℝ) := by field_simp
  have hcast : (β : ℂ) * (((2 * π * (n : ℝ) / β : ℝ) : ℂ) * Complex.I)
      = (n : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    rw [← mul_assoc, ← Complex.ofReal_mul, h1]; push_cast; ring
  rw [hcast, Complex.exp_int_mul_two_pi_mul_I]

/-- **Matsubara residue normalization.** The derivative of the Bose denominator
`e^{βz} - 1` at `zₙ` is `β`, so the residue of `1 / (e^{βz} - 1)` is `1 / β`. -/
lemma bose_residue (β : ℝ) (n : ℤ) (hβ : β ≠ 0) :
    HasDerivAt (fun z => Complex.exp ((β : ℂ) * z) - 1) (β : ℂ) (matsubaraFreq β n) := by
  have hexp : HasDerivAt (fun z : ℂ => Complex.exp ((β : ℂ) * z))
      (Complex.exp ((β : ℂ) * matsubaraFreq β n) * (β : ℂ)) (matsubaraFreq β n) := by
    exact ((Complex.hasDerivAt_exp ((β : ℂ) * matsubaraFreq β n)).comp (matsubaraFreq β n)
      ((hasDerivAt_id _).const_mul (β : ℂ))).congr_deriv (by ring)
  have hval : Complex.exp ((β : ℂ) * matsubaraFreq β n) * (β : ℂ) = (β : ℂ) := by
    rw [bose_pole β n hβ, one_mul]
  rw [hval] at hexp
  exact hexp.sub_const 1

end Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDMatsubaraContour

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart.imaginaryPart_ratio where
  formalizes @ "claim:the-thermofield-self-energy-imaginary-parts-satisfy-the-cosh-consistency-ratio",
  supported_by @ "paper:fujimoto-morikawa-sasaki-thermofield-self-energy"

zil attach Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart.thermoBogoliubov_massShell where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:the-thermo-bogoliubov-angle-sits-on-the-bogoliubov-causal-diamond-mass-shell"

zil attach Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart.thermal_KMS_ratio where
  formalizes @ "claim:the-thermal-occupation-satisfies-the-kms-detailed-balance-ratio-cosh-squared-equals-boltzmann-times-sinh-squared"

zil attach Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDMatsubaraContour.bose_residue where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDMatsubaraContour.bose_pole",
  supported_by @ "lean:HasVarAdjDerivAt.const_mul",
  formalizes @ "claim:the-matsubara-frequency-residue-of-the-bose-factor-is-one-over-beta"

zil_file_contract physlib.tfdImaginaryPart where
  promises "The thermofield imaginary-part and Matsubara-contour layer: the unimodular thermo-Bogoliubov matrix U_B diagonalizing the thermal propagator sits on the Bogoliubov causal-diamond mass shell; the Bose-Einstein occupation sinh^2 theta = n_B satisfies the KMS detailed-balance ratio cosh^2 = e^{beta k} sinh^2; the self-energy imaginary parts obey the cosh consistency ratio; and the Matsubara frequencies are the poles of the Bose factor with residue 1/beta, with real-time and imaginary-time loop Gaussians agreeing on the contour wedge."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart.thermoBogoliubov",
    "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart.boseEinstein"]
  forbids_substitutes ["the full Matsubara frequency sum, only the per-frequency pole and residue are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart.imaginaryPart_ratio,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart.thermoBogoliubov_massShell,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart.thermal_KMS_ratio,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart.thermal_cosh_sq,
    Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDMatsubaraContour.bose_residue]

/- ZIL-END -/
