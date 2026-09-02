/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondBisognanoWichmannKMS
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra

/-!
# The three diamond clocks: modular (Bisognano–Wichmann), Misra, and Compton–de Broglie

The one diamond rapidity `θ` is read by three inequivalent notions of a clock, and they all agree — the
common reading is the diamond velocity `v = tanh θ = √(BCJ dual)` on the mass shell `E² − p² = 1`.

1. **Modular clock (Bisognano–Wichmann / KMS).**  The wedge modular flow is the boost by `θ`, KMS-periodic in
   imaginary rapidity at the Unruh `β = 2π` (`DiamondBisognanoWichmannKMS`).  By Connes–Rovelli this modular
   time *is* the Page–Wootters relational/conditional time (physlib `CausalDiamond.EntropicTime.
   pageWootters_connesRovelli_entropic_bridge`).
2. **Misra clock.**  The Misra internal-time / age vector is the Bogoliubov boost orbit
   `boostVector 1 θ = cosh θ + i·sinh θ` — which is *exactly* the diamond energy-momentum
   `diamondMomentum θ` (`diamondMomentum_eq_boostVector`).  Its polar velocity `ξ/E = tanh θ`
   (`HyperbolicPoincareLorentzMisra.boostVector_velocity`) is the BCJ dual velocity.
3. **Compton–de Broglie clock.**  The de Broglie phase frequency `ω_dB = E/ℏ = cosh θ · ω_C`
   (`FrequencyTrinity.deBroglie_eq_bogoliubovEnergy_compton`) is the diamond-boosted Compton clock
   (`ForceBCJDiamondEntropicClock`), whose squared rate is the Lorentz factor `1/(1 − BCJ dual)`.

* `diamondMomentum_eq_boostVector` — the diamond momentum **is** the Misra boost orbit vector at unit mass.
* `diamond_misra_velocity_sq_eq_bcj` — the Misra polar velocity² is the BCJ dual `tanh²θ`.
* `diamond_deBroglie_eq_boostedComptonClock` — the de Broglie frequency is the boosted Compton clock.
* `diamond_deBroglie_clockRate_sq_eq_lorentzFactor` — the de Broglie clock rate² is `1/(1 − BCJ dual)`.
* `diamond_threeClocks_common_velocity` — Misra velocity² = BCJ dual = (momentum/energy)²: one velocity.

Honest scope: algebraic identifications linking `diamondMomentum` to the Misra boost vector and the de
Broglie frequency to the boosted Compton clock, sharing the diamond velocity; the modular↔Page–Wootters
equivalence is cited (Connes–Rovelli), not reproved here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondThreeClocks

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamond
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamondMassShell
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamondEntropicClock
open Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondLorentzianEntropicClock
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra

/-- **[Misra bridge] The diamond momentum is the Misra boost orbit vector at unit rest mass.**
`diamondMomentum θ = boostVector 1 θ` — the diamond energy-momentum `cosh θ + i·sinh θ` is exactly the
Bogoliubov squeeze/boost vector that carries the Misra internal-time (age) structure. -/
theorem diamondMomentum_eq_boostVector (θ : ℝ) : diamondMomentum θ = boostVector 1 θ := by
  unfold diamondMomentum boostVector
  simp only [one_mul]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      zero_mul, sub_zero, add_zero, zero_add]

/-- **[Misra velocity is the BCJ dual] `(ξ/E)² = tanh²θ = lorentzForceDual`.**  The Misra clock's polar
Poincaré velocity `ξ/E` squared is the diamond gravitational dual. -/
theorem diamond_misra_velocity_sq_eq_bcj (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4)
    (θ : ℝ) (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    ((1 * Real.sinh θ) / (1 * Real.cosh θ)) ^ 2
      = lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2) := by
  rw [boostVector_velocity 1 θ one_ne_zero, ← lorentzForceDual_eq_diamond_velocity_sq F V μ θ hnum]

/-- **[de Broglie is the boosted Compton clock] `ω_dB = ω_C^{boosted}`.**  The de Broglie phase frequency of
the diamond mode `deBroglieFrequency (E_B·mc²) ℏ` equals the diamond-boosted Compton clock frequency
`comptonFrequency (m·E_B) c ℏ`. -/
theorem diamond_deBroglie_eq_boostedComptonClock (m c ħ θ : ℝ) :
    deBroglieFrequency (bogoliubovEnergy (Real.sinh θ) 1 * (m * c ^ 2)) ħ
      = comptonFrequency (m * bogoliubovEnergy (Real.sinh θ) 1) c ħ := by
  rw [deBroglie_eq_bogoliubovEnergy_compton, comptonFrequency_energy_scaling]

/-- **[de Broglie clock rate² is the Lorentz factor] `(ω_dB/ω_C)² = 1/(1 − lorentzForceDual)`.**  The de
Broglie clock's squared time-dilation is the Lorentz factor `γ² = cosh²θ`, the reciprocal of `1` minus the
BCJ gravitational dual. -/
theorem diamond_deBroglie_clockRate_sq_eq_lorentzFactor (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ)
    (μ : Fin 4) (m c ħ θ : ℝ) (hnum : (F *ᵥ V) μ = Real.sinh θ) (hω : comptonFrequency m c ħ ≠ 0) :
    (deBroglieFrequency (bogoliubovEnergy (Real.sinh θ) 1 * (m * c ^ 2)) ħ / comptonFrequency m c ħ) ^ 2
      = 1 / (1 - lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2)) := by
  rw [diamond_deBroglie_eq_boostedComptonClock]
  exact diamond_clockRate_sq_eq_lorentzFactor F V μ m c ħ θ hnum hω

/-- **[One velocity, three clocks] Misra velocity² = BCJ dual = (momentum/energy)².**  The Misra polar
velocity, the BCJ gravitational dual, and the diamond momentum-to-energy ratio all coincide — the three
clocks read the single diamond velocity `tanh²θ` on the mass shell. -/
theorem diamond_threeClocks_common_velocity (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4)
    (θ : ℝ) (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    ((1 * Real.sinh θ) / (1 * Real.cosh θ)) ^ 2
      = lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2)
    ∧ lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2)
      = (lorentzForceNum F V μ / bogoliubovEnergy (Real.sinh θ) 1) ^ 2 :=
  ⟨diamond_misra_velocity_sq_eq_bcj F V μ θ hnum,
    diamond_dual_eq_momentum_over_energy_sq F V μ θ hnum⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondThreeClocks

end
