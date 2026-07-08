/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The imaginary part in Thermo Field Dynamics (Fujimoto–Morikawa–Sasaki 1986)

Formalizes the algebraic core of *Y. Fujimoto, M. Morikawa, M. Sasaki, "Imaginary part in thermo field
dynamics", Phys. Rev. D 33 (1986) 590–593* — the sequel to `ThermoFieldDynamics.Basic` (Suzuki), computing the
imaginary part of self-energy Feynman diagrams in real-time finite-temperature TFD. Two structures include the
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

## References

* Y. Fujimoto, M. Morikawa, M. Sasaki, Phys. Rev. D 33 (1986) 590–593 (Eqs. 6, 8, 13–14).
* Repo dependencies: `ThermoFieldDynamics.Basic` (the Suzuki TFD this extends; `matsubaraBoltzmannWeight`);
  `CausalDiamond.Helicity.diamond_horizon_energy` (`bogoliubovEnergy(sinh η,1) = cosh η`, the mass shell).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation

/-! ## §A — the thermo-Bogoliubov matrix (Eq. 8) -/

/-- **[Eq. 8] The thermo-Bogoliubov matrix** `U_B(θ) = [[cosh θ, sinh θ],[sinh θ, cosh θ]]` — the `2×2`
transformation diagonalizing the thermal propagator in the doubled TFD space. -/
noncomputable def thermoBogoliubov (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh θ, Real.sinh θ; Real.sinh θ, Real.cosh θ]

/-- **The thermo-Bogoliubov matrix is unimodular** `det U_B = cosh²θ − sinh²θ = 1` — a Lorentz boost (the
mass-shell relation). -/
theorem thermoBogoliubov_det (θ : ℝ) : (thermoBogoliubov θ).det = 1 := by
  rw [thermoBogoliubov, Matrix.det_fin_two_of]
  nlinarith [Real.cosh_sq_sub_sinh_sq θ]

/-- **The thermo-Bogoliubov angle sits on the Bogoliubov mass shell** `cosh θ = bogoliubovEnergy(sinh θ, 1)`
— the diagonal `cosh θ = √(sinh²θ + 1)` is the quasiparticle energy (`diamond_horizon_energy`), tying the
thermo-Bogoliubov to the diamond/mass-shell cluster. -/
theorem thermoBogoliubov_massShell (θ : ℝ) :
    Real.cosh θ = bogoliubovEnergy (Real.sinh θ) 1 :=
  (diamond_horizon_energy θ).symm

/-! ## §B — the Bose–Einstein parametrization (Eq. 8) -/

/-- **The Bose–Einstein occupation** `n_B(k) = 1/(e^{βk} − 1)` — the thermal weight `sinh²θ` of the
thermo-Bogoliubov. -/
noncomputable def boseEinstein (β k : ℝ) : ℝ := 1 / (Real.exp (β * k) - 1)

/-- **[Eq. 8] `cosh²θ = 1 + n_B`** — from the mass shell `cosh²θ − sinh²θ = 1` and `sinh²θ = n_B`. -/
theorem thermal_cosh_sq (θ β k : ℝ) (h : Real.sinh θ ^ 2 = boseEinstein β k) :
    Real.cosh θ ^ 2 = 1 + boseEinstein β k := by
  have := Real.cosh_sq_sub_sinh_sq θ
  rw [← h]; linarith

/-- **[Detailed balance / KMS] `cosh²θ = e^{βk}·sinh²θ`.** The ratio `cosh²θ/sinh²θ = (1+n_B)/n_B = e^{βk}` is
the KMS/detailed-balance condition of the thermal state. -/
theorem thermal_KMS_ratio (θ β k : ℝ) (h : Real.sinh θ ^ 2 = boseEinstein β k)
    (hk : Real.exp (β * k) ≠ 1) :
    Real.cosh θ ^ 2 = Real.exp (β * k) * Real.sinh θ ^ 2 := by
  have he : Real.exp (β * k) - 1 ≠ 0 := sub_ne_zero.mpr hk
  rw [thermal_cosh_sq θ β k h, h, boseEinstein]
  field_simp
  ring

/-- **`n_B` is the TFD/Matsubara Boltzmann weight** `n_B = w/(1 − w)`, `w = e^{−βk} = matsubaraBoltzmannWeight`
— the Bose–Einstein occupation in terms of the thermal weight of `ThermoFieldDynamics.Basic`. -/
theorem boseEinstein_eq_matsubara (β k : ℝ) (hk : Real.exp (β * k) ≠ 1) :
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

/-! ## §C — the imaginary-part relations (Eqs. 6, 13–14) -/

/-- **[Eqs. 13–14] The imaginary-part ratio** `ImΣ¹¹ = −cosh(βp₀/2)·ImΣ¹²`. From `ImΣ̄ = tanh(x)·ImΣ¹¹`
(Eq. 14a) and `ImΣ̄ = −sinh(x)·ImΣ¹²` (Eq. 14b) with `x = βp₀/2`, consistency forces the component relation
(Eq. 13) — `tanh = sinh/cosh` cancels `sinh` to leave `cosh`. -/
theorem imaginaryPart_ratio (x imBar im11 im12 : ℝ)
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

end
