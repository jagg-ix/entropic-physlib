/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart
public import Mathlib.Data.Complex.Basic

/-!
# The self-energy integral-evaluation identities (Fujimoto–Morikawa–Sasaki 1986)

The momentum-integral evaluations of the TFD self-energy diagrams (`ThermoFieldDynamics.TFDImaginaryPart`, Eqs. 1–5, 15–25) rest
on a handful of purely *algebraic* identities — the analytic operations themselves (the `d³k` momentum
integrals and the Matsubara frequency-sum/contour integral Eq. 2) are genuine measure-theory/residue calculus
and stay outside scope, but the algebra they reduce to is formalized here:

* the **Sokhotski–Plemelj split** (Eq. 4) `1/(x+iε) = x/(x²+ε²) − i·ε/(x²+ε²)`, whose imaginary part is the
  Lorentzian nascent delta `(1/π)·ε/(x²+ε²) → δ(x)` that converts the energy denominators of Eq. 3 into the
  `δ`-functions of Eq. 5;
* the **Bose combinatorial identity** (Eq. 16) `(e^{β(E₁+E₂)}−1)·n_B(E₁)n_B(E₂) = 1 + n_B(E₁) + n_B(E₂)`, the
  statistics behind the `[1+n_B+n_B]` prefactors of Eqs. 5/15/17/18;
* the **fermion–boson combinatorial identity** (before Eq. 24)
  `e^{β(E₁+E₂)}+1 = (n_F(E₁)n_B(E₂))⁻¹ + n_F(E₁)⁻¹ − n_B(E₂)⁻¹`;
* the **thermal-prefactor hyperbolic forms** (Eqs. 14a/14b) `(e^x−1)/(e^x+1) = tanh(x/2)` and
  `(e^x−1)/(2e^{x/2}) = sinh(x/2)`, which justify the `tanh`/`sinh` coefficients used in
  `ThermoFieldDynamics.TFDImaginaryPart.imaginaryPart_ratio`.

* **§A — Sokhotski–Plemelj** (`sokhotski_re`, `sokhotski_im`, `lorentzian`). The `iε` split (Eq. 4).
* **§B — Bose statistics** (`bose_combinatorial`). Eq. 16.
* **§C — Fermi statistics** (`fermiDirac`, `fermion_boson_combinatorial`). The Eq. 24 identity.
* **§D — thermal prefactors** (`boltzmann_to_tanh`, `boltzmann_to_sinh`). Eqs. 14a/14b.

## References

* Y. Fujimoto, M. Morikawa, M. Sasaki, Phys. Rev. D 33 (1986) 590–593 (Eqs. 4, 14, 16, 24).
* Repo dependencies: `ThermoFieldDynamics.TFDImaginaryPart.boseEinstein` (`n_B`) and `imaginaryPart_ratio` (whose `tanh`/`sinh`
  coefficients §D supplies).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDSelfEnergyIdentities

open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDImaginaryPart

/-! ## §A — the Sokhotski–Plemelj split (Eq. 4) -/

/-- **[Eq. 4, real part] `Re 1/(x+iε) = x/(x²+ε²)`** — the principal-value precursor `P/x`. -/
theorem sokhotski_re (x ε : ℝ) : ((↑x + ↑ε * Complex.I)⁻¹).re = x / (x ^ 2 + ε ^ 2) := by
  rw [Complex.inv_re]; simp [Complex.normSq_apply]; ring

/-- **[Eq. 4, imaginary part] `Im 1/(x+iε) = −ε/(x²+ε²)`** — the Lorentzian whose `ε→0` limit is `−πδ(x)`. -/
theorem sokhotski_im (x ε : ℝ) : ((↑x + ↑ε * Complex.I)⁻¹).im = -ε / (x ^ 2 + ε ^ 2) := by
  rw [Complex.inv_im]; simp [Complex.normSq_apply]; ring

/-- **The Lorentzian nascent delta** `(1/π)·ε/(x²+ε²)` — `−Im 1/(x+iε)/π`; its `ε→0⁺` limit is the Dirac
`δ(x)` of Eq. 5 (the limit itself is the analytic step left aside). -/
noncomputable def lorentzian (ε x : ℝ) : ℝ := ε / (Real.pi * (x ^ 2 + ε ^ 2))

/-! ## §B — the Bose combinatorial identity (Eq. 16) -/

/-- **[Eq. 16] The Bose statistics identity** `(e^{β(E₁+E₂)}−1)·n_B(E₁)n_B(E₂) = 1 + n_B(E₁) + n_B(E₂)` — the
combinatorial source of the `[1+n_B+n_B]` prefactor in the imaginary part. -/
theorem bose_combinatorial (β E₁ E₂ : ℝ) (h1 : Real.exp (β * E₁) ≠ 1) (h2 : Real.exp (β * E₂) ≠ 1) :
    (Real.exp (β * (E₁ + E₂)) - 1) * boseEinstein β E₁ * boseEinstein β E₂
      = 1 + boseEinstein β E₁ + boseEinstein β E₂ := by
  unfold boseEinstein
  have ha : Real.exp (β * E₁) - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hb : Real.exp (β * E₂) - 1 ≠ 0 := sub_ne_zero.mpr h2
  rw [show β * (E₁ + E₂) = β * E₁ + β * E₂ from by ring, Real.exp_add]
  field_simp
  ring

/-! ## §C — Fermi statistics (the Eq. 24 identity) -/

/-- **The Fermi–Dirac occupation** `n_F(E) = 1/(e^{βE} + 1)`. -/
noncomputable def fermiDirac (β E : ℝ) : ℝ := 1 / (Real.exp (β * E) + 1)

/-- **[Before Eq. 24] The fermion–boson statistics identity**
`e^{β(E₁+E₂)}+1 = (n_F(E₁)n_B(E₂))⁻¹ + n_F(E₁)⁻¹ − n_B(E₂)⁻¹` — the combinatorial source of the fermion
self-energy prefactors (Fig. 4). -/
theorem fermion_boson_combinatorial (β E₁ E₂ : ℝ) (h2 : Real.exp (β * E₂) ≠ 1) :
    Real.exp (β * (E₁ + E₂)) + 1
      = 1 / (fermiDirac β E₁ * boseEinstein β E₂) + 1 / fermiDirac β E₁ - 1 / boseEinstein β E₂ := by
  unfold fermiDirac boseEinstein
  have ha : Real.exp (β * E₁) + 1 ≠ 0 := by positivity
  have hb : Real.exp (β * E₂) - 1 ≠ 0 := sub_ne_zero.mpr h2
  rw [show β * (E₁ + E₂) = β * E₁ + β * E₂ from by ring, Real.exp_add]
  field_simp
  ring

/-! ## §D — the thermal-prefactor hyperbolic forms (Eqs. 14a/14b) -/

/-- **[Eq. 14a coefficient] `(e^x−1)/(e^x+1) = tanh(x/2)`** — the thermal prefactor `tanh(βp₀/2)` in the
`ImΣ̄ = tanh(x)·ImΣ¹¹` relation. -/
theorem boltzmann_to_tanh (x : ℝ) : (Real.exp x - 1) / (Real.exp x + 1) = Real.tanh (x / 2) := by
  have hp : (0 : ℝ) < Real.exp (x / 2) := Real.exp_pos _
  have hu : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, hu]
  field_simp

/-- **[Eq. 14b coefficient] `(e^x−1)/(2e^{x/2}) = sinh(x/2)`** — the thermal prefactor `sinh(βp₀/2)` in the
`ImΣ̄ = −sinh(x)·ImΣ¹²` relation. -/
theorem boltzmann_to_sinh (x : ℝ) :
    (Real.exp x - 1) / (2 * Real.exp (x / 2)) = Real.sinh (x / 2) := by
  have hp : (0 : ℝ) < Real.exp (x / 2) := Real.exp_pos _
  have hu : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.sinh_eq, Real.exp_neg, hu]
  field_simp

end Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.TFDSelfEnergyIdentities

end
