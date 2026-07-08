/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The thermal entropy of a Hawking mode: `S = (n+1)ln(n+1) − n ln n = βω·n + ln(n+1)` (Kay–Wald)

Formalizes the **von Neumann (thermal) entropy** of a single bosonic Killing-horizon mode in the Hawking–KMS
state — the entropy encoded in Kay–Wald's thermal radiation. For mean occupation `n`,

`S(n) = (n+1) ln(n+1) − n ln n`,

and for the thermal (Bose–Einstein) occupation `n = 1/(e^{βω} − 1)` (`hawkingOccupation`) this collapses to the
**first-law / Gibbs relation**

`S = βω·n + ln(n+1) = β⟨E⟩ + ln Z`,

with `⟨E⟩ = ωn` the mean mode energy and `ln Z = ln(n+1)` the single-mode free-energy term (`Z = n+1`). The whole
identity rests on `ln(n+1) − ln n = βω`, the log of the detailed-balance ratio `(n+1)/n = e^{βω}`.

* the **occupation is positive** `n > 0` for `βω > 0` (`hawkingOccupation_pos`);
* the **log-occupation ratio** `ln(n+1) − ln n = βω` (`log_occupation_ratio`) — the log of the detailed-balance
 ratio `(n+1)/n = e^{βω}`, the exponent that reappears everywhere in the thermal state;
* the **first-law entropy identity** `S = βω·n + ln(n+1)` (`bosonicEntropy_thermal`) — the Gibbs entropy of the
 thermal mode written as `β⟨E⟩ + ln Z`, the thermodynamic entropy of the Hawking radiation;
* the **entropy is positive** `S > 0` (`bosonicEntropy_thermal_pos`) — the Hawking radiation records strictly
 positive entropy, the second-law content of the thermal state;
* the **Hawking specialization** `β = 2π/κ` (`hawking_radiation_entropy`) — at the Hawking inverse temperature the
 identity is the entropy of black-hole / Killing-horizon radiation.

So the Kay–Wald thermal state's entropy is the Gibbs entropy `S = β⟨E⟩ + ln Z` of a bosonic mode, strictly
positive, driven by the single exponent `βω = ln((n+1)/n)` that also governs the detailed balance and the KMS
periodicity — the entropy of Hawking radiation on the same thermal spine as the rest of the arc.

* **§A — the occupation and the log-ratio** (`hawkingOccupation_pos`, `bosonicEntropy`, `log_occupation_ratio`).
* **§B — the first-law entropy identity and its positivity** (`bosonicEntropy_thermal`,
 `bosonicEntropy_thermal_pos`).
* **§C — the Hawking specialization `β = 2π/κ`** (`hawking_radiation_entropy`).

The bosonic entropy function, the log-ratio, the first-law identity, and the positivity are
exact `Real.log`/`Real.exp` algebra for a single mode. The full field-mode sum (the Bekenstein–Hawking area law as
the integrated horizon entropy), the density-matrix derivation of the von Neumann entropy, and the KMS
characterization are the referenced content, not re-derived. This is the *bosonic* thermal entropy (an unbounded
occupation tower), distinct from the two-level binary entropy `sjModeEntropy` of `SorkinJohnstonEntanglementEntropy`.
No new axioms.

## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49; J.D. Bekenstein, S.W. Hawking (radiation entropy). Repo structure:
 `EntropicTime.KayWaldHawkingRadiationBoseEinstein` (`hawkingOccupation`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBosonicThermalEntropy

/-! ## §A — the occupation and the log-ratio -/

/-- **[The thermal occupation is positive] `n > 0` for `βω > 0`.** The Bose–Einstein occupation
`n = 1/(e^{βω} − 1)` is strictly positive whenever `βω > 0` (`e^{βω} > 1`). -/
theorem hawkingOccupation_pos (β ω : ℝ) (hβω : 0 < β * ω) : 0 < hawkingOccupation β ω := by
  have hE1 : 1 < Real.exp (β * ω) := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hβω
  unfold hawkingOccupation
  exact div_pos one_pos (by linarith)

/-- **The bosonic thermal entropy of a mode** `S(n) = (n+1) ln(n+1) − n ln n` — the von Neumann entropy of a single
bosonic oscillator mode with mean occupation `n`, the entropy encoded in a thermal Killing-horizon mode. -/
noncomputable def bosonicEntropy (n : ℝ) : ℝ := (n + 1) * Real.log (n + 1) - n * Real.log n

/-- **[The log-occupation ratio is the exponent] `ln(n+1) − ln n = βω`.** The detailed-balance ratio of the Bose
occupation is `(n+1)/n = e^{βω}`, so the difference of logs is the Boltzmann exponent `βω` — the same exponent
governing the detailed balance and the KMS periodicity. -/
theorem log_occupation_ratio (β ω : ℝ) (hβω : 0 < β * ω) :
    Real.log (hawkingOccupation β ω + 1) - Real.log (hawkingOccupation β ω) = β * ω := by
  have hE1 : 1 < Real.exp (β * ω) := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hβω
  have hd : (0 : ℝ) < Real.exp (β * ω) - 1 := by linarith
  have hn : 0 < hawkingOccupation β ω := hawkingOccupation_pos β ω hβω
  have hn1 : 0 < hawkingOccupation β ω + 1 := by linarith
  have hquot : (hawkingOccupation β ω + 1) / hawkingOccupation β ω = Real.exp (β * ω) := by
    unfold hawkingOccupation
    field_simp
    ring
  rw [← Real.log_div hn1.ne' hn.ne', hquot, Real.log_exp]

/-! ## §B — the first-law entropy identity and its positivity -/

/-- **[The first-law entropy identity] `S = βω·n + ln(n+1)`.** The Gibbs entropy of the thermal mode written as
`β⟨E⟩ + ln Z`: expanding `(n+1) ln(n+1) − n ln n = n(ln(n+1) − ln n) + ln(n+1)` and using `ln(n+1) − ln n = βω`
gives the mean-energy term `βω·n = β⟨E⟩` plus the free-energy term `ln(n+1) = ln Z`. -/
theorem bosonicEntropy_thermal (β ω : ℝ) (hβω : 0 < β * ω) :
    bosonicEntropy (hawkingOccupation β ω)
      = β * ω * hawkingOccupation β ω + Real.log (hawkingOccupation β ω + 1) := by
  unfold bosonicEntropy
  have hsplit : (hawkingOccupation β ω + 1) * Real.log (hawkingOccupation β ω + 1)
        - hawkingOccupation β ω * Real.log (hawkingOccupation β ω)
      = hawkingOccupation β ω
          * (Real.log (hawkingOccupation β ω + 1) - Real.log (hawkingOccupation β ω))
        + Real.log (hawkingOccupation β ω + 1) := by ring
  rw [hsplit, log_occupation_ratio β ω hβω]
  ring

/-- **[The Hawking radiation entropy is positive] `S > 0`.** From the first-law identity `S = βω·n + ln(n+1)` with
`βω > 0`, `n > 0`, and `ln(n+1) > 0` (as `n+1 > 1`), the thermal mode records strictly positive entropy — the
second-law content of the Kay–Wald thermal state. -/
theorem bosonicEntropy_thermal_pos (β ω : ℝ) (hβω : 0 < β * ω) :
    0 < bosonicEntropy (hawkingOccupation β ω) := by
  rw [bosonicEntropy_thermal β ω hβω]
  have hn : 0 < hawkingOccupation β ω := hawkingOccupation_pos β ω hβω
  have hlog : 0 < Real.log (hawkingOccupation β ω + 1) := Real.log_pos (by linarith)
  have henergy : 0 < β * ω * hawkingOccupation β ω := mul_pos hβω hn
  linarith

/-! ## §C — the Hawking specialization `β = 2π/κ` -/

/-- **[The entropy of Hawking radiation at `T_H = κ/2π`] `S = (2π/κ)ω·n + ln(n+1)`.** Specializing the first-law
entropy identity to the Hawking inverse temperature `β = hawkingBeta 1 κ 1 1 = 2π/κ`: the von Neumann entropy of a
bifurcate-Killing-horizon mode of frequency `ω` in the Hawking–KMS state. -/
theorem hawking_radiation_entropy (κ ω : ℝ) (hκω : 0 < hawkingBeta 1 κ 1 1 * ω) :
    bosonicEntropy (hawkingOccupation (hawkingBeta 1 κ 1 1) ω)
      = hawkingBeta 1 κ 1 1 * ω * hawkingOccupation (hawkingBeta 1 κ 1 1) ω
        + Real.log (hawkingOccupation (hawkingBeta 1 κ 1 1) ω + 1) :=
  bosonicEntropy_thermal (hawkingBeta 1 κ 1 1) ω hκω

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBosonicThermalEntropy

end
