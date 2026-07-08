/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
public import Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope

/-!
# The Compton frequency trinity and the Compton-wavelength vacuum decay scale

Formalizes the **frequency trinity** (Compton, Zitterbewegung, de Broglie) and the **Compton
wavelength** as the decay scale of vacuum Bell correlations — the Reeh–Schlieder consequence reviewed in
Summers, *Yet More Ado About Nothing* (and Bennett, arXiv:1406.0750): *"violations of Bell's inequality
in the vacuum for a massive particle decay exponentially with spacelike separation, the decay scale
being the Compton wavelength."*

The unitary (phase) frequencies of a free massive particle are all proportional to `E/ħ`:

* **Compton** `ω_C = mc²/ħ` (rest energy, `comptonFrequency`);
* **Zitterbewegung** `ω_Z = 2√(p²c² + m²c⁴)/ħ`, which is `2 ω_C` in the rest frame
  (`zitterbewegung_rest_eq_two_compton`) — the `E_+ − E_−` splitting of the Dirac branches;
* **de Broglie** `ω_dB = E/ħ = γ ω_C` (`deBroglie_eq_gamma_compton`), with `γ = cosh η` the Lorentz
  factor / Bogoliubov energy (`deBroglie_eq_bogoliubovEnergy_compton`).

The **reduced Compton wavelength** is `λ_C = ħ/(mc) = c/ω_C` (`comptonWavelength`,
`comptonWavelength_mul_comptonFrequency`). It is the scale over which **vacuum Bell correlations decay**:
the concurrence falls as `C(r) = C₀·e^{−r/λ_C}`, so the CHSH envelope `S_CHSH(r) ≤ 2√(1 + C₀²e^{−2r/λ_C})`
decays monotonically toward the classical bound with spacelike separation `r`
(`vacuum_bell_compton_decay`, `vacuum_bell_compton_monotone`), always respecting Tsirelson — the
Reeh–Schlieder cluster decomposition realized through the CHSH entropic envelope
(`Bell.EntropicEnvelope`).

* **§A — the frequency trinity** (`comptonFrequency`, `zitterbewegung_rest_eq_two_compton`,
  `deBroglie_eq_gamma_compton`).
* **§B — the Compton wavelength** (`comptonWavelength`, `comptonWavelength_mul_comptonFrequency`).
* **§C — de Broglie = boosted Compton via the Bogoliubov energy**
  (`deBroglie_eq_bogoliubovEnergy_compton`).
* **§D — the Compton-wavelength vacuum Bell decay** (`vacuum_bell_compton_decay`,
  `vacuum_bell_compton_monotone`).

## References

* S. J. Summers, arXiv:0802.1854 (Reeh–Schlieder, exponential cluster decay over the Compton
  wavelength); A. F. Bennett, arXiv:1406.0750. Repo dependencies: `CausalDiamond.Helicity`
  (`bogoliubovEnergy`, `diamond_horizon_energy`), `Bell.EntropicEnvelope` (`chshEnvelope`,
  `chsh_dephasing_le_tsirelson`), `Bell.DeterministicBounds` (`tsirelsonWitness`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

open Real
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
open Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope

/-! ## §A — the frequency trinity -/

/-- **The Compton frequency** `ω_C = mc²/ħ` — the rest-energy angular frequency. -/
noncomputable def comptonFrequency (m c ħ : ℝ) : ℝ := m * c ^ 2 / ħ

/-- **The Zitterbewegung frequency** `ω_Z = 2√(p²c² + m²c⁴)/ħ` — the `E_+ − E_−` energy splitting of the
Dirac branches over `ħ`. -/
noncomputable def zitterbewegungFrequency (p m c ħ : ℝ) : ℝ :=
  2 * Real.sqrt (p ^ 2 * c ^ 2 + m ^ 2 * c ^ 4) / ħ

/-- **The de Broglie frequency** `ω_dB = E/ħ` — the phase frequency of a state of total energy `E`. -/
noncomputable def deBroglieFrequency (E ħ : ℝ) : ℝ := E / ħ

/-- **[Zitterbewegung is twice Compton in the rest frame] `ω_Z = 2 ω_C` at `p = 0`.** The Dirac
positive/negative-energy splitting `2√(m²c⁴) = 2mc²` is twice the rest energy. -/
theorem zitterbewegung_rest_eq_two_compton (m c ħ : ℝ) (hm : 0 ≤ m) :
    zitterbewegungFrequency 0 m c ħ = 2 * comptonFrequency m c ħ := by
  unfold zitterbewegungFrequency comptonFrequency
  rw [show (0 : ℝ) ^ 2 * c ^ 2 + m ^ 2 * c ^ 4 = (m * c ^ 2) ^ 2 from by ring,
    Real.sqrt_sq (by positivity)]
  ring

/-- **[de Broglie is `γ` times Compton] `ω_dB = γ ω_C`.** For total energy `E = γ mc²`, the de Broglie
frequency is the Lorentz factor `γ` times the Compton frequency; at `γ = 1` (rest frame) it is `ω_C`. -/
theorem deBroglie_eq_gamma_compton (γ m c ħ : ℝ) :
    deBroglieFrequency (γ * (m * c ^ 2)) ħ = γ * comptonFrequency m c ħ := by
  unfold deBroglieFrequency comptonFrequency; ring

/-! ## §B — the Compton wavelength -/

/-- **The reduced Compton wavelength** `λ_C = ħ/(mc)` — the natural length scale of a mass `m`. -/
noncomputable def comptonWavelength (m c ħ : ℝ) : ℝ := ħ / (m * c)

/-- **[`λ_C = c/ω_C`] `λ_C · ω_C = c`.** The reduced Compton wavelength is the speed of light over the
Compton frequency. -/
theorem comptonWavelength_mul_comptonFrequency (m c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonWavelength m c ħ * comptonFrequency m c ħ = c := by
  unfold comptonWavelength comptonFrequency; field_simp

/-- **[`λ_C > 0`].** -/
theorem comptonWavelength_pos (m c ħ : ℝ) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    0 < comptonWavelength m c ħ := by
  unfold comptonWavelength; positivity

/-! ## §C — de Broglie = boosted Compton via the Bogoliubov energy -/

/-- **[de Broglie at the Bogoliubov energy] `ω_dB = E_B·ω_C`.** With Lorentz factor
`γ = cosh η = bogoliubovEnergy (sinh η) 1` (`diamond_horizon_energy`), the de Broglie frequency of a
mode at rapidity `η` is the Bogoliubov energy times the Compton frequency — the boosted phase frequency
of the entanglement arc's energy. -/
theorem deBroglie_eq_bogoliubovEnergy_compton (η m c ħ : ℝ) :
    deBroglieFrequency (bogoliubovEnergy (Real.sinh η) 1 * (m * c ^ 2)) ħ
      = bogoliubovEnergy (Real.sinh η) 1 * comptonFrequency m c ħ :=
  deBroglie_eq_gamma_compton (bogoliubovEnergy (Real.sinh η) 1) m c ħ

/-! ## §D — the Compton-wavelength vacuum Bell decay (Reeh–Schlieder) -/

/-- **[Vacuum Bell correlations decay over `λ_C`] `S_CHSH(r) ≤ 2√2`.** With the concurrence decaying as
`C(r) = C₀·e^{−r/λ_C}` (Reeh–Schlieder cluster decomposition, decay scale the Compton wavelength), the
CHSH envelope at spacelike separation `r` still respects the Tsirelson bound — the vacuum Bell
correlation is bounded and falls toward the classical value with distance. -/
theorem vacuum_bell_compton_decay (C₀ r m c ħ : ℝ) (hC₀ : C₀ ^ 2 ≤ 1)
    (hr : 0 ≤ r / comptonWavelength m c ħ) :
    chshEnvelope (C₀ * Real.exp (-(r / comptonWavelength m c ħ))) ≤ tsirelsonWitness :=
  chsh_dephasing_le_tsirelson C₀ (r / comptonWavelength m c ħ) hC₀ hr

/-- **[The vacuum Bell violation decays with spacelike separation] monotone in `r`.** As the spacelike
separation `r` grows (in units of the Compton wavelength `λ_C > 0`), the vacuum CHSH envelope decreases
monotonically toward the classical bound — the exponential decay of vacuum entanglement over the Compton
wavelength (Reeh–Schlieder / Summers). -/
theorem vacuum_bell_compton_monotone (C₀ r₁ r₂ m c ħ : ℝ) (hC₀ : 0 ≤ C₀) (hr : r₁ ≤ r₂)
    (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    chshEnvelope (C₀ * Real.exp (-(r₂ / comptonWavelength m c ħ)))
      ≤ chshEnvelope (C₀ * Real.exp (-(r₁ / comptonWavelength m c ħ))) := by
  refine chsh_dephasing_monotone C₀ (r₁ / comptonWavelength m c ħ)
    (r₂ / comptonWavelength m c ħ) hC₀ ?_
  have hpos := comptonWavelength_pos m c ħ hm hc hħ
  gcongr

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

end
