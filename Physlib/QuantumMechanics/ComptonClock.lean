/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.WaveFunction

/-!
# The de Broglie / Compton internal clock and the phase gauge

The physical meaning of the normalization phase gauge. A particle at rest has de Broglie frequency
`ω_dB = E/ℏ = mc²/ℏ`, the **Compton clock** `ω_C = mc²/ℏ`. Advancing the entropic-dynamics wave function's phase
by the Compton-clock phase `ω_C·t` is exactly the phase-shift gauge `ψ ↦ e^{iω_C t}ψ` of `WaveFunction`: the
abstract `U(1)` gauge parameter *is* the particle's internal clock ticking. So Caticha's normalization gauge is
de Broglie's "periodic phenomenon", and the ray-space Killing flow (`phaseShift_born_isometry`) runs at the
Compton frequency `mc²/ℏ`.

References: L. de Broglie; A. Caticha, arXiv:2107.08502. No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.WaveFunction

@[expose] public section

namespace Physlib.QuantumMechanics.ComptonClock

/-- **The Compton clock frequency** `ω_C = mc²/ℏ`. -/
noncomputable def comptonFrequency (m c ħ : ℝ) : ℝ := m * c ^ 2 / ħ

/-- **The de Broglie frequency** `ω_dB = E/ℏ`. -/
noncomputable def deBroglieFrequency (E ħ : ℝ) : ℝ := E / ħ

/-- **The de Broglie frequency at rest is the Compton clock** `ω_dB(mc²) = ω_C`. For a particle at rest the total
energy is `mc²`, so its de Broglie frequency is exactly the Compton frequency. -/
theorem deBroglie_rest_is_comptonClock (m c ħ : ℝ) :
    deBroglieFrequency (m * c ^ 2) ħ = comptonFrequency m c ħ := by
  simp only [deBroglieFrequency, comptonFrequency]

/-- **The phase gauge is the de Broglie / Compton clock** `ψ(Φ + ω_dB(mc²)·t) = e^{i ω_C t} ψ(Φ)`. Advancing the
entropic-dynamics phase by the de Broglie rest phase `ω_dB(mc²)·t` — which is the Compton clock `ω_C·t = (mc²/ℏ)·t`
(`deBroglie_rest_is_comptonClock`) — multiplies the wave function by the Compton-clock phase `e^{i ω_C t}`. The
Hamilton–Killing normalization gauge is de Broglie's internal clock. -/
theorem phaseGauge_is_comptonClock (ρ Φ m c ħ t : ℝ) :
    edWaveFunction ρ (Φ + deBroglieFrequency (m * c ^ 2) ħ * t)
      = Complex.exp (((comptonFrequency m c ħ * t : ℝ) : ℂ) * Complex.I) * edWaveFunction ρ Φ := by
  rw [deBroglie_rest_is_comptonClock]
  exact phaseShift_gauge ρ Φ (comptonFrequency m c ħ * t)

end Physlib.QuantumMechanics.ComptonClock

end
