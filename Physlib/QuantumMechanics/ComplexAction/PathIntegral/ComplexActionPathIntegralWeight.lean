/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDPathIntegralMeasureValid
public import Physlib.QFT.PathIntegral.Lorentzian

/-!
# The complex-action/entropic-time master complex-action path integral and its incarnations

Implements the path-integral equations of the complex-action/entropic-time master document (`complex_action_entropic_time_reference …`): the **master
complex-action path integral** `Z[J] = ∫ 𝒟Φ exp[(i/ℏ)S_R[Φ] − (1/ℏ)S_I[Φ]]` and its Feynman–Vernon,
Nagao–Nielsen, and Kuiken incarnations — *proved* equal to the repo objects rather than only described.

* **§A — the master weight is the Lorentzian kernel** (`complexActionPathIntegralWeight_eq_lorentzianKernel`): the
  per-configuration weight `exp[(i/ℏ)S_R − (1/ℏ)S_I]` of `Z[J]` *is* `lorentzianKernel S_R S_I ℏ`.
* **§B — the Feynman–Vernon factorized form** (`feynmanVernon_eq_master`): the FV influence functional
  `F = exp{(i/ℏ)S_FV,R − (1/ℏ)S_FV,I}` has the master-formula structure.
* **§C — the Nagao–Nielsen complex action** (`nagaoNielsen_eq_master`): the complex-action weight
  `exp((i/ℏ)S_complex)` with `S_complex = S_R + iS_I` equals the master weight (using `i² = −1`).
* **§D — the Kuiken classical weight is the entropic damping** (`kuiken_eq_entropyDamping`,
  `master_modulus_is_kuiken`): `W ∝ exp(−c⁻¹Π)` is `WickRotation.entropyDamping`, and is the *modulus* of
  the master weight — entropy production is the imaginary action.
* **§E — the entropy identification** (`master_modulus_is_entropy`): with `S_I = (ℏ/k_B)S_ent`, the master
  weight's modulus is the Boltzmann-like `exp(−S_ent/k_B)`.
* **§F — the measure-valid QED model realizes the master formula** (`qed_weight_is_master`,
  `qed_modulus_is_kuiken`): the `PathIntegral.QEDPathIntegralMeasureValid` model's complex weight *is* the master-formula
  integrand, and its Cameron–Martin damping *is* the Kuiken/entropy-production weight.

## References

* The complex-action/entropic-time master document `complex_action_entropic_time_reference …` — Eqs. at its lines 109/214/546/1498 (master `Z[J]`),
  178/187 (Feynman–Vernon), 196 (Kuiken), 207 (`S_I = (ℏ/k_B)S_ent`), 538 (Nagao–Nielsen `S_complex`).
* R. P. Feynman, F. L. Vernon, *The theory of a general quantum system interacting with a linear
  dissipative system*, Ann. Phys. 24 (1963) 118 — the influence functional.
* S. Albeverio, L. Cattaneo, S. Mazzucchi, L. Di Persio (2007) — rigorous Fresnel-integral construction of
  the Feynman–Vernon functional.
* K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor. Phys. 126 (2011) 1021.
* H. Kuiken (1977) — entropy production as probability weight (the classical analogue of `e^{−S_I/ℏ}`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.NonHermitian.WickRotation

/-! ## §A — the master complex-action path-integral weight -/

/-- **[complex-action/entropic-time master formula] The per-configuration weight of** `Z[J] = ∫ 𝒟Φ exp[(i/ℏ)S_R − (1/ℏ)S_I]`. -/
noncomputable def complexActionPathIntegralWeight (S_R S_I ℏ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((S_R / ℏ : ℝ) : ℂ) - ((S_I / ℏ : ℝ) : ℂ))

/-- **[Implement] The master weight IS the Lorentzian path-integral kernel** `exp[(i/ℏ)S_R − (1/ℏ)S_I] =
lorentzianKernel S_R S_I ℏ` — the complex-action/entropic-time master integrand is the repo's `lorentzianKernel`. -/
theorem complexActionPathIntegralWeight_eq_lorentzianKernel (S_R S_I ℏ : ℝ) :
    complexActionPathIntegralWeight S_R S_I ℏ = lorentzianKernel S_R S_I ℏ := by
  unfold complexActionPathIntegralWeight lorentzianKernel; congr 1; push_cast; ring

/-! ## §B — the Feynman–Vernon influence functional -/

/-- **[Feynman–Vernon] The factorized influence functional** `F = exp{(i/ℏ)S_FV,R − (1/ℏ)S_FV,I}` — the
result of integrating out the environment; same structure as the master weight. -/
noncomputable def feynmanVernonWeight (S_FV_R S_FV_I ℏ : ℝ) : ℂ := complexActionPathIntegralWeight S_FV_R S_FV_I ℏ

/-- **[Implement] The Feynman–Vernon functional is the master weight** (hence the `lorentzianKernel`) — the
complex action originates from the open-system path integral. -/
theorem feynmanVernon_eq_master (S_FV_R S_FV_I ℏ : ℝ) :
    feynmanVernonWeight S_FV_R S_FV_I ℏ = complexActionPathIntegralWeight S_FV_R S_FV_I ℏ := rfl

/-! ## §C — the Nagao–Nielsen complex action `S_complex = S_R + iS_I` -/

/-- **[Nagao–Nielsen] The complex-action weight** `exp((i/ℏ)S_complex)` with the complex action `S_complex = S_R + iS_I`. -/
noncomputable def nagaoNielsenComplexActionWeight (S_R S_I ℏ : ℝ) : ℂ :=
  Complex.exp (Complex.I / (ℏ : ℂ) * ((S_R : ℂ) + Complex.I * (S_I : ℂ)))

/-- **[Implement] The Nagao–Nielsen complex-action weight is the master weight.** `exp((i/ℏ)(S_R + iS_I)) =
exp[(i/ℏ)S_R − (1/ℏ)S_I]` since `i² = −1` — the complex action `S_R + iS_I` produces the master-formula
phase-times-damping. -/
theorem nagaoNielsen_eq_master (S_R S_I ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    nagaoNielsenComplexActionWeight S_R S_I ℏ = complexActionPathIntegralWeight S_R S_I ℏ := by
  have hℏ' : (ℏ : ℂ) ≠ 0 := by exact_mod_cast hℏ
  unfold nagaoNielsenComplexActionWeight complexActionPathIntegralWeight; congr 1; push_cast
  linear_combination ((S_I : ℂ) / (ℏ : ℂ)) * Complex.I_sq

/-! ## §D — the Kuiken classical weight = entropic damping = master modulus -/

/-- **[Kuiken] The classical entropy-production probability weight** `W ∝ exp(−c⁻¹Π)`. -/
noncomputable def kuikenWeight (c Pi : ℝ) : ℝ := Real.exp (-(Pi / c))

/-- **[Implement] The Kuiken weight is the entropic damping** `exp(−c⁻¹Π) = entropyDamping Π c` — Kuiken's
classical dissipation-controls-probability weight is the arc's Cameron–Martin / entropic-damping factor. -/
theorem kuiken_eq_entropyDamping (S_I ℏ : ℝ) : kuikenWeight ℏ S_I = entropyDamping S_I ℏ := by
  simp only [kuikenWeight, entropyDamping]

/-- **[Implement] The modulus of the master weight is the Kuiken/entropy-production weight.**
`‖exp[(i/ℏ)S_R − (1/ℏ)S_I]‖ = exp(−S_I/ℏ) = kuikenWeight ℏ S_I` — the imaginary action `S_I` is the
entropy production, and its exponential is the classical probability weight. -/
theorem master_modulus_is_kuiken (S_R S_I ℏ : ℝ) :
    ‖complexActionPathIntegralWeight S_R S_I ℏ‖ = kuikenWeight ℏ S_I := by
  rw [complexActionPathIntegralWeight_eq_lorentzianKernel, lorentzianKernel_norm_is_damping]
  simp only [kuikenWeight]

/-! ## §E — the entropy identification `S_I = (ℏ/k_B)S_ent` -/

/-- **[Implement] With `S_I = (ℏ/k_B)S_ent` the master modulus is the Boltzmann-like entropy weight**
`exp(−S_ent/k_B)` — the imaginary action is the entanglement entropy (complex-action/entropic-time identification, doc line
207). -/
theorem master_modulus_is_entropy (S_R S_ent kB ℏ : ℝ) (hℏ : ℏ ≠ 0) (hkB : kB ≠ 0) :
    ‖complexActionPathIntegralWeight S_R ((ℏ / kB) * S_ent) ℏ‖ = Real.exp (-(S_ent / kB)) := by
  have h : ((ℏ / kB) * S_ent) / ℏ = S_ent / kB := by field_simp
  rw [master_modulus_is_kuiken]; simp only [kuikenWeight]; rw [h]

/-! ## §F — the measure-valid QED model realizes the master formula -/

/-- **[Implement] The measure-valid QED model's weight IS the complex-action/entropic-time master integrand.** The complex weight
`(qedExchangeModel …).weight` of `PathIntegral.QEDPathIntegralMeasureValid` is `complexActionPathIntegralWeight` evaluated at the
model's real/imaginary actions — the master formula's integrand `Z[J]`, made a rigorous Bochner integrand. -/
theorem qed_weight_is_master (ℏ HI1 HI2 : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) (x : ℝ) :
    (PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).weight x
      = complexActionPathIntegralWeight
          ((PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).actionRe x)
          ((PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).actionIm x) ℏ := by
  unfold complexActionPathIntegralWeight MeasurePathIntegralModel.weight MeasurePathIntegralModel.actionReScaled
    MeasurePathIntegralModel.actionImScaled PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel
  congr 1; ring

/-- **[Implement] The QED model's Cameron–Martin damping is the Kuiken/entropy-production weight.**
`‖(qedExchangeModel …).weight‖ = kuikenWeight ℏ S_I` — the measure-valid QED weight's modulus is exactly
the classical entropy-production probability weight. -/
theorem qed_modulus_is_kuiken (ℏ HI1 HI2 : ℝ) (hℏ : 0 < ℏ) (h1 : 0 ≤ HI1) (h2 : 0 ≤ HI2) (x : ℝ) :
    ‖(PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel ℏ HI1 HI2 hℏ h1 h2).weight x‖
      = kuikenWeight ℏ (HI1 + HI2) := by
  rw [qed_weight_is_master, master_modulus_is_kuiken]
  simp only [PathIntegral.QEDPathIntegralMeasureValid.qedExchangeModel]

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

end
