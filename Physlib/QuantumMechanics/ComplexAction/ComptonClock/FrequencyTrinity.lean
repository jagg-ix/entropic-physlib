/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
public import Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope
meta import Zil

/-!
# The Compton frequency trinity and a conditional Compton-scale Bell envelope

Formalizes the **frequency trinity** (Compton, Zitterbewegung, de Broglie) and evaluates
a CHSH envelope under a supplied exponential concurrence profile. Summers' mass-gap
result motivates a Compton-scale exponential **upper bound** for vacuum Bell correlations,
but neither Reeh--Schlieder nor this file derives the exact concurrence equality
`C(r) = C₀ exp (-r/lambda_C)`.

The unitary (phase) frequencies of a free massive particle are all proportional to `E/ħ`:

* **Compton** `ω_C = mc²/ħ` (rest energy, `comptonFrequency`);
* **Zitterbewegung** `ω_Z = 2√(p²c² + m²c⁴)/ħ`, which is `2 ω_C` in the rest frame
  (`zitterbewegung_rest_eq_two_compton`) — the `E_+ − E_−` splitting of the Dirac branches;
* **de Broglie** `ω_dB = E/ħ = γ ω_C` (`deBroglie_eq_gamma_compton`), with `γ = cosh η` the Lorentz
  factor / Bogoliubov energy (`deBroglie_eq_bogoliubovEnergy_compton`).

The **reduced Compton wavelength** is `λ_C = ħ/(mc) = c/ω_C` (`comptonWavelength`,
`comptonWavelength_mul_comptonFrequency`). If one supplies the model profile
`C(r) = C₀ exp (-r/lambda_C)`, then the CHSH envelope decreases monotonically and
respects Tsirelson
(`vacuum_bell_compton_decay`, `vacuum_bell_compton_monotone`). The separate
`ComptonEuclideanVacuumCorrelation` module derives the same exponential for a specified Euclidean
vacuum--one-particle scalar mode; it does not identify that two-point function with
AQFT concurrence.

* **§A — the frequency trinity** (`comptonFrequency`, `zitterbewegung_rest_eq_two_compton`,
  `deBroglie_eq_gamma_compton`).
* **§B — the Compton wavelength** (`comptonWavelength`, `comptonWavelength_mul_comptonFrequency`).
* **§C — de Broglie = boosted Compton via the Bogoliubov energy**
  (`deBroglie_eq_bogoliubovEnergy_compton`).
* **§D — the conditional Compton-wavelength Bell envelope** (`vacuum_bell_compton_decay`,
  `vacuum_bell_compton_monotone`).

## References

* S. J. Summers, arXiv:0802.1854 (Reeh--Schlieder and mass-gap upper bounds on vacuum Bell
  correlations); A. F. Bennett, arXiv:1406.0750. Repo carriers: `CausalDiamond.Helicity`
  (`bogoliubovEnergy`, `diamond_horizon_energy`), `Bell.EntropicEnvelope` (`chshEnvelope`,
  `chsh_dephasing_le_tsirelson`), `Bell.DeterministicBounds` (`tsirelsonWitness`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

open Real
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
open Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope


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
lemma zitterbewegung_rest_eq_two_compton (m c ħ : ℝ) (hm : 0 ≤ m) :
    zitterbewegungFrequency 0 m c ħ = 2 * comptonFrequency m c ħ := by
  unfold zitterbewegungFrequency comptonFrequency
  rw [show (0 : ℝ) ^ 2 * c ^ 2 + m ^ 2 * c ^ 4 = (m * c ^ 2) ^ 2 from by ring,
    Real.sqrt_sq (by positivity)]
  ring

/-- **[de Broglie is `γ` times Compton] `ω_dB = γ ω_C`.** For total energy `E = γ mc²`, the de Broglie
frequency is the Lorentz factor `γ` times the Compton frequency; at `γ = 1` (rest frame) it is `ω_C`. -/
lemma deBroglie_eq_gamma_compton (γ m c ħ : ℝ) :
    deBroglieFrequency (γ * (m * c ^ 2)) ħ = γ * comptonFrequency m c ħ := by
  unfold deBroglieFrequency comptonFrequency; ring


/-- **The reduced Compton wavelength** `λ_C = ħ/(mc)` — the natural length scale of a mass `m`. -/
noncomputable def comptonWavelength (m c ħ : ℝ) : ℝ := ħ / (m * c)

/-- **[`λ_C = c/ω_C`] `λ_C · ω_C = c`.** The reduced Compton wavelength is the speed of light over the
Compton frequency. -/
lemma comptonWavelength_mul_comptonFrequency (m c ħ : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonWavelength m c ħ * comptonFrequency m c ħ = c := by
  unfold comptonWavelength comptonFrequency; field_simp

/-- **[`λ_C > 0`].** -/
lemma comptonWavelength_pos (m c ħ : ℝ) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    0 < comptonWavelength m c ħ := by
  unfold comptonWavelength; positivity

/-- **The reduced Compton wavelength identifies its mass scale.**  At fixed nonzero
`c` and `ħ`, two nonzero masses have the same reduced Compton wavelength exactly when
the masses agree. -/
lemma comptonWavelength_inj {m₁ m₂ c ħ : ℝ}
    (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    comptonWavelength m₁ c ħ = comptonWavelength m₂ c ħ ↔ m₁ = m₂ := by
  unfold comptonWavelength
  constructor
  · intro h
    rw [div_eq_div_iff (mul_ne_zero hm₁ hc) (mul_ne_zero hm₂ hc)] at h
    have hmc : m₂ * c = m₁ * c := mul_left_cancel₀ hħ h
    exact (mul_right_cancel₀ hc hmc).symm
  · rintro rfl
    rfl


/-- **[de Broglie at the Bogoliubov energy] `ω_dB = E_B·ω_C`.** With Lorentz factor
`γ = cosh η = bogoliubovEnergy (sinh η) 1` (`diamond_horizon_energy`), the de Broglie frequency of a
mode at rapidity `η` is the Bogoliubov energy times the Compton frequency — the boosted phase frequency
of the entanglement arc's energy. -/
lemma deBroglie_eq_bogoliubovEnergy_compton (η m c ħ : ℝ) :
    deBroglieFrequency (bogoliubovEnergy (Real.sinh η) 1 * (m * c ^ 2)) ħ
      = bogoliubovEnergy (Real.sinh η) 1 * comptonFrequency m c ħ :=
  deBroglie_eq_gamma_compton (bogoliubovEnergy (Real.sinh η) 1) m c ħ


/-- **[Conditional Compton-scale Bell envelope] `S_CHSH(r) ≤ 2√2`.** For the supplied profile
`C(r) = C₀ exp (-r/lambda_C)`, the CHSH envelope respects the Tsirelson bound. The proof
bounds this explicit real function; it does not derive the profile from a vacuum state or
local observables. -/
lemma vacuum_bell_compton_decay (C₀ r m c ħ : ℝ) (hC₀ : C₀ ^ 2 ≤ 1)
    (hr : 0 ≤ r / comptonWavelength m c ħ) :
    chshEnvelope (C₀ * Real.exp (-(r / comptonWavelength m c ħ))) ≤ tsirelsonWitness :=
  chsh_dephasing_le_tsirelson C₀ (r / comptonWavelength m c ħ) hC₀ hr

/-- **[The supplied Bell envelope is monotone in `r`.]** As `r` grows in units of a positive
Compton wavelength, the explicit model envelope decreases monotonically. -/
lemma vacuum_bell_compton_monotone (C₀ r₁ r₂ m c ħ : ℝ) (hC₀ : 0 ≤ C₀) (hr : r₁ ≤ r₂)
    (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    chshEnvelope (C₀ * Real.exp (-(r₂ / comptonWavelength m c ħ)))
      ≤ chshEnvelope (C₀ * Real.exp (-(r₁ / comptonWavelength m c ħ))) := by
  refine chsh_dephasing_monotone C₀ (r₁ / comptonWavelength m c ħ)
    (r₂ / comptonWavelength m c ħ) hC₀ ?_
  have hpos := comptonWavelength_pos m c ħ hm hc hħ
  gcongr

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglie_eq_gamma_compton where
  formalizes @ "claim:de-broglie-frequency-is-the-boosted-compton-clock-gamma-times-omega-c",
  supported_by @ "paper:summers-2008-reeh-schlieder-cluster-decay",
  caveat @ "claim:operational-identification-of-the-internal-clock-with-the-rest-energy-frequency"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegung_rest_eq_two_compton where
  formalizes @ "claim:rest-frame-zitterbewegung-is-twice-the-compton-frequency-dirac-branch-splitting",
  supported_by @ "paper:summers-2008-reeh-schlieder-cluster-decay"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength_mul_comptonFrequency where
  formalizes @ "claim:reduced-compton-wavelength-times-compton-frequency-is-the-speed-of-light",
  requires @ "claim:de-broglie-frequency-is-the-boosted-compton-clock-gamma-times-omega-c",
  caveat @ "claim:exact-kinematic-identity-lambda-c-equals-c-over-omega-c"

zil attach Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.vacuum_bell_compton_decay where
  formalizes @ "claim:a-supplied-exponential-concurrence-profile-at-the-compton-scale-\
produces-a-chsh-envelope-respecting-tsirelson",
  requires @ "claim:reduced-compton-wavelength-times-compton-frequency-is-the-speed-of-light",
  supported_by @ "paper:summers-2008-reeh-schlieder-cluster-decay",
  supported_by @ "paper:bennett-2014-vacuum-bell",
  caveat @ "claim:concurrence-exponential-decay-profile-is-supplied-not-derived-from-\
a-vacuum-state-and-local-observables"

zil_file_contract physlib.comptonFrequencyTrinity where
  promises "The Compton frequency trinity as one boosted internal clock: the de Broglie \
frequency is gamma times the Compton frequency, the rest-frame Zitterbewegung is twice \
the Compton frequency, and the reduced Compton wavelength times the Compton frequency \
is the speed of light. Under a separately supplied exponential concurrence profile at \
that scale, the corresponding CHSH envelope is monotone and respects the Tsirelson \
bound."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonFrequency",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bell.EntropicEnvelope.chshEnvelope"]
  forbids_substitutes ["a derivation of the concurrence exponential-decay law from \
Reeh-Schlieder or from specified AQFT local observables",
    "a numerical prediction of any particle mass or frequency, all left as free parameters"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.deBroglie_eq_gamma_compton,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.zitterbewegung_rest_eq_two_compton,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.comptonWavelength_mul_comptonFrequency,
    Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity.vacuum_bell_compton_decay]

/- ZIL-END -/
