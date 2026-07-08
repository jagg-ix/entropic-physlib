/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.LorentzianMatsubaraWick

/-!
# Consistency: the Bogoljubov order-parameter phase = Poincaré azimuth = complex-action phase

This file proves the **consistency** of one and the same phase `φ` appearing in three places:

1. the **Bogoljubov order parameter** `Δ = |Δ| e^{iφ}` (the pairing amplitude),
2. the **azimuthal angle** of the polarisation state on the **Poincaré sphere**
   (`Hopf.StokesSpinorIsomorphism`),
3. the phase of the **complex-action / Feynman–Kac / Matsubara path-integral weight**
   `e^{iS_R/ℏ}` (`QFT.Wick.Consistency.complexActionWeight`).

## The order parameter from the polarisation spinor

For the polarisation 2-spinor `χ = (χ₀, χ₁)`, the Bogoljubov pairing amplitude (order parameter)
is the off-diagonal combination `Δ = χ₀^* χ₁` (`orderParameter`). Its phase is the **relative
phase** of the two spinor components.

## Consistency 1 — Bogoljubov ↔ Poincaré

* `azimuthal_stokes_eq_orderParameter` — **`S₁ + i S₂ = 2 Δ`**. So `arg(S₁ + iS₂) = arg(Δ) = φ`:
  the order-parameter phase **is** the azimuthal angle (longitude) of the polarisation state on
  the Poincaré sphere.

## Consistency 2 — Bogoljubov ↔ complex action (Feynman–Kac / Matsubara)

* `orderParameter_phaseShift` — the **Bogoljubov U(1) gauge** `χ₁ → e^{iα} χ₁` shifts
  `Δ → e^{iα} Δ`, hence `φ → φ + α`.
* `bogoljubov_phase_eq_complexActionWeight` — **`e^{iα} = complexActionWeight (ℏα) 0 ℏ`**: the
  U(1) order-parameter phase is exactly the phase of the complex-action weight (the `S_I = 0`,
  entropy-free / unitary fiber of the Feynman–Kac/Matsubara weight). The order-parameter phase
  rotation is the action-phase rotation `e^{iS_R/ℏ}` with `S_R/ℏ = α`.

## The combined statement

* `bogoljubov_poincare_action_consistency` — both identities together: the order-parameter
  phase is simultaneously the Poincaré azimuth and the complex-action phase weight.

## References

* N. N. Bogoljubov (1958); BCS order parameter `Δ = |Δ|e^{iφ}`.
* S. Saito, Front. Phys. 11 (2024) 1225334 (Poincaré sphere); `QFT.Wick.Consistency`,
  `Hopf.StokesSpinorIsomorphism`, `ThermoFieldDynamics.LorentzianMatsubaraWick` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism
open Physlib.QFT.Wick.Consistency

namespace Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BogoljubovPoincareActionConsistency

/-! ## §A — the order parameter from the polarisation spinor -/

/-- **The Bogoljubov order parameter** `Δ = χ₀^* χ₁` — the off-diagonal pairing amplitude of the
polarisation spinor; its phase is the relative phase of the spinor components. -/
def orderParameter (χ : Fin 2 → ℂ) : ℂ := star (χ 0) * χ 1

/-! ## §B — consistency 1: Bogoljubov ↔ Poincaré (`S₁ + iS₂ = 2Δ`) -/

/-- **`S₁ + i S₂ = 2 Δ`**: the azimuthal Stokes combination equals twice the order parameter, so
the order-parameter phase `φ = arg Δ` is the azimuthal angle of the polarisation state on the
Poincaré sphere. -/
theorem azimuthal_stokes_eq_orderParameter (χ : Fin 2 → ℂ) :
    stokesS (Sum.inr 0) χ + Complex.I * stokesS (Sum.inr 1) χ = 2 * orderParameter χ := by
  rw [stokesS1_apply, stokesS2_apply]
  unfold orderParameter
  linear_combination (star (χ 1) * χ 0 - star (χ 0) * χ 1) * Complex.I_sq

/-! ## §C — consistency 2: Bogoljubov U(1) ↔ complex-action phase -/

/-- **The Bogoljubov U(1) gauge** `χ₁ → e^{iα} χ₁`. -/
def phaseShift (α : ℝ) (χ : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![χ 0, Complex.exp ((α : ℂ) * Complex.I) * χ 1]

/-- **The U(1) gauge shifts the order parameter by `e^{iα}`**: `Δ → e^{iα} Δ` (so `φ → φ + α`). -/
theorem orderParameter_phaseShift (α : ℝ) (χ : Fin 2 → ℂ) :
    orderParameter (phaseShift α χ) = Complex.exp ((α : ℂ) * Complex.I) * orderParameter χ := by
  unfold orderParameter phaseShift
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **The U(1) order-parameter phase is the complex-action phase weight**:
`e^{iα} = complexActionWeight (ℏα) 0 ℏ` — the `S_I = 0` (entropy-free, unitary) fiber of the
Feynman–Kac/Matsubara complex-action weight, with action phase `S_R/ℏ = α`. -/
theorem bogoljubov_phase_eq_complexActionWeight (α ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    Complex.exp ((α : ℂ) * Complex.I) = complexActionWeight (ℏ * α) 0 ℏ := by
  unfold complexActionWeight
  have hℏc : (ℏ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℏ
  congr 1
  push_cast
  field_simp
  ring

/-! ## §D — the combined consistency -/

/-- **Bogoljubov ↔ Poincaré ↔ complex action**: the order-parameter phase is simultaneously the
Poincaré azimuthal angle (`S₁ + iS₂ = 2Δ`) and the complex-action phase weight
(`e^{iα} = complexActionWeight (ℏα) 0 ℏ`, the Feynman–Kac/Matsubara `S_I = 0` fiber). -/
theorem bogoljubov_poincare_action_consistency (α ℏ : ℝ) (hℏ : ℏ ≠ 0) (χ : Fin 2 → ℂ) :
    stokesS (Sum.inr 0) χ + Complex.I * stokesS (Sum.inr 1) χ = 2 * orderParameter χ
      ∧ Complex.exp ((α : ℂ) * Complex.I) = complexActionWeight (ℏ * α) 0 ℏ :=
  ⟨azimuthal_stokes_eq_orderParameter χ, bogoljubov_phase_eq_complexActionWeight α ℏ hℏ⟩

end Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BogoljubovPoincareActionConsistency

end
