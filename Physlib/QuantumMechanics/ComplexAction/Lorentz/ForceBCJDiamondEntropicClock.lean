/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamondMassShell
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-!
# The entropic Compton clock at the diamond mode — time quantization from the BCJ dual

The entropic Compton clock ticks at the frequency `ω = mc²/ℏ` (`ComptonClock.FrequencyTrinity.comptonFrequency`,
the Planck–Einstein `E = ℏω`), and its reciprocal `ℏ/(mc²)` is the quantized proper-time tick.  At the
Jacobson diamond mode the energy is boosted to `E = m·cosh θ` (`cosh θ = bogoliubovEnergy(sinh θ, 1)`, the
diamond horizon energy of `Lorentz.ForceBCJDiamondMassShell`), so the clock is boosted by the diamond Lorentz
factor and the quantized tick contracts.

The link to the BCJ double copy: the **squared clock-rate dilation is the Lorentz factor**

`(ω_boosted/ω_rest)² = cosh²θ = γ² = 1/(1 − lorentzForceDual)`,

so the entropic clock's time dilation is exactly the reciprocal of `1` minus the gravitational dual
`v² = tanh²θ`.  Time quantization (the Compton tick) is thereby read off the diamond BCJ kinematics.

* `comptonFrequency_energy_scaling` — `comptonFrequency (m·E) c ℏ = E · comptonFrequency m c ℏ`.
* `diamond_boostedComptonFrequency` — the diamond-boosted clock frequency `= cosh θ · ω_rest`.
* `diamond_clockRate_sq_eq_lorentzFactor` — `(ω_boosted/ω_rest)² = 1/(1 − lorentzForceDual)`.
* `diamond_boostedTimeQuantum` — the boosted quantized tick `= (1/cosh θ)·(rest tick)`.

Honest scope: the algebraic energy-scaling of the entropic clock and its identification with the diamond
Lorentz factor of `ForceBCJDiamondMassShell`; no quantum-clock dynamics or spectral quantization is
constructed beyond the Planck–Einstein `E = ℏω` proportionality.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamondEntropicClock

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamondMassShell
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-- **[Clock frequency scales with energy] `comptonFrequency (m·E) c ℏ = E · comptonFrequency m c ℏ`.**  The
entropic Compton clock frequency `ω = mc²/ℏ` is linear in the mass/energy (Planck–Einstein `E = ℏω`). -/
theorem comptonFrequency_energy_scaling (m E c ħ : ℝ) :
    comptonFrequency (m * E) c ħ = E * comptonFrequency m c ħ := by
  unfold comptonFrequency; ring

/-- **[Diamond-boosted clock] `ω_boosted = cosh θ · ω_rest`.**  At the diamond mode the energy is boosted to
`m·cosh θ` (the diamond horizon energy), so the entropic Compton clock frequency is the rest frequency times
the diamond Lorentz factor `cosh θ`. -/
theorem diamond_boostedComptonFrequency (m c ħ θ : ℝ) :
    comptonFrequency (m * bogoliubovEnergy (Real.sinh θ) 1) c ħ
      = bogoliubovEnergy (Real.sinh θ) 1 * comptonFrequency m c ħ :=
  comptonFrequency_energy_scaling m (bogoliubovEnergy (Real.sinh θ) 1) c ħ

/-- **[Clock-rate dilation = Lorentz factor] `(ω_boosted/ω_rest)² = 1/(1 − lorentzForceDual)`.**  The squared
time-dilation of the entropic Compton clock at the diamond mode is the Lorentz factor `γ² = cosh²θ`, which is
the reciprocal of `1` minus the BCJ gravitational dual `v² = tanh²θ` — time quantization read off the diamond
double-copy kinematics. -/
theorem diamond_clockRate_sq_eq_lorentzFactor (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4)
    (m c ħ θ : ℝ) (hnum : (F *ᵥ V) μ = Real.sinh θ) (hω : comptonFrequency m c ħ ≠ 0) :
    (comptonFrequency (m * bogoliubovEnergy (Real.sinh θ) 1) c ħ / comptonFrequency m c ħ) ^ 2
      = 1 / (1 - lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2)) := by
  rw [diamond_boostedComptonFrequency, mul_div_assoc, div_self hω, mul_one]
  exact diamond_lorentzFactor F V μ θ hnum

/-- **[Quantized tick contracts] `rest-tick·(1/cosh θ) = boosted tick`.**  The quantized proper-time tick of
the entropic clock (`1/ω = ℏ/(mc²)`) at the diamond-boosted energy is the rest tick divided by the diamond
Lorentz factor `cosh θ` — the proper-time quantum Lorentz-contracts along the boost. -/
theorem diamond_boostedTimeQuantum (m c ħ θ : ℝ) :
    1 / comptonFrequency (m * bogoliubovEnergy (Real.sinh θ) 1) c ħ
      = 1 / bogoliubovEnergy (Real.sinh θ) 1 * (1 / comptonFrequency m c ħ) := by
  rw [diamond_boostedComptonFrequency, one_div_mul_one_div]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamondEntropicClock

end
