/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Optics.MaterialTimescales
public import Mathlib.Tactic.NormNum

/-!
# Tirole / Galiffi ITO at Tirole's working pump intensity: an
explicit `EffectiveDampingDecomposition` in the Bender gain mode

This module instantiates
`Physlib.Optics.MaterialTimescales.EffectiveDampingDecomposition`
with the literal numerical rates measured in two independent
experiments on nominally identical ITO films:

* `γ_Drude = 1.30 × 10¹⁴ s⁻¹` — Galiffi et al. 2024,
 ellipsometry (Methods Sec. 1).

* `β = 2.34 × 10¹⁴ s⁻¹` — Pendry 2024 avalanche rate, eq. 3
 evaluated at Tirole's working pump intensity
 `I_pump = 124 GW/cm²` (numerical value from
 `catsim/scripts/pendry_avalanche_timescale.py` smoke-test 13).

The Pendry effective-damping decomposition (`γ_eff = γ_Drude −
β`, his eq. 6) then gives `γ_eff = −1.04 × 10¹⁴ s⁻¹`. The sign
of `γ_eff` is **negative**, which is the Bender complex-energy
"gain mode" condition `Im[ω] > 0`. This module proves that
fact, `tirole_is_gain_mode`, by direct application of
`isGainMode_iff_beta_gt_gammaDrude`.

The empirical content closes the chain:

 Bender 2008 algebraic Γ = ℏ/τ
 ↓
 Pendry 2024 eq. 6 γ_eff = γ_Drude − β
 ↓
 Galiffi 2024 ellipsometry γ_Drude = 1.30 × 10¹⁴ s⁻¹
 Pendry 2024 eq. 3 β = 2.34 × 10¹⁴ s⁻¹ at I=124 GW/cm²
 ↓
 γ_eff = −1.04 × 10¹⁴ s⁻¹ (this module's `IsGainMode`)
 ↓
 Galiffi 2024 observation up to 2600% parametric amplification

The Bender complex-energy gain mode is realised in the
laboratory, with both the Drude rate and the avalanche rate
empirically anchored to independent measurements, and the gain
condition derivable in Lean from the algebraic theorems in
`MaterialTimescales` §F.

## Provenance of the rate inputs

The numerical values used in this module come from three
independent measurements / derivations:

 **γ_Drude = 1.30 × 10¹⁴ s⁻¹**:
 Galiffi et al. 2024, *Optical coherent perfect absorption
 and amplification in a time-varying medium*, arXiv
 2410.16426, Methods Section 1 / Figure S1. Obtained by
 ellipsometric characterisation of a 310 nm ITO film
 nominally identical to the one used in Tirole 2022.
 Equivalent to `γ_Drude = 0.13 fs⁻¹` (their stated value),
 or `τ_Drude ≈ 7.7 fs`.

 **β at various I_pump**:
 Pendry 2024, *An avalanche model for femtosecond optical
 response*, arXiv 2407.08391, eq. 3:
 `β = E · e / √(U_G · m)`
 with `U_G = 3 eV` (band gap) and `m = m_e` (electron mass)
 per his eq. 9. The pump field amplitude `E` is converted
 from intensity I_pump via the standard plane-wave relation
 `I = (1/2) · ε_0 · c · E²`
 (free-space; the ITO refractive index dependence is small
 at the ENZ wavelength and is absorbed into Pendry's
 assumption).

 **I_pump values**:
 Galiffi 2024 Fig 5b reports a six-point pump-intensity
 sweep at: 18, 36, 73, 147, 294, 589 GW/cm². Tirole 2022
 reports the working pump intensity as 124 GW/cm² (Fig 1
 caption). The four instances in this module sit at:

 I = 18 GW/cm² `galiffiLowPumpDecomposition` DECAY
 I ≈ 38 GW/cm² `tiroleThresholdDecomposition` BOUNDARY
 I = 124 GW/cm² `tiroleDecomposition` GAIN
 I = 589 GW/cm² `galiffiHighPumpDecomposition` EXTREME GAIN

The β values are computed once-and-for-all in the Python
helper `catsim/scripts/pendry_avalanche_timescale.py` (smoke-
test 13 output) and recorded here as Lean literal constants.

## Cross-paper consistency

A numerical check that the framework is internally consistent:

 Tirole 2022 (envelope-fit τ_rise) ≈ 7 fs
 Pendry 2024 (τ_β at I = 50 GW/cm²) ≈ 6.7 fs
 Galiffi 2024 (1/γ_Drude) ≈ 7.7 fs

The Pendry-2024 avalanche τ_β at the *computed* threshold
intensity 38.3 GW/cm² (where β = γ_Drude, i.e.
`isAtThreshold_iff_beta_eq_gammaDrude`) is exactly 7.7 fs. At
Pendry's stated qualitative threshold of "~50 GW/cm²" it drops
to 6.7 fs, matching Tirole's envelope τ_rise to 5 %. The
numerical coincidence between τ_Drude (equilibrium) and τ_rise
(threshold avalanche) — within the same ITO film — is what
the Pendry-2024 mechanism resolves: they are different
physical quantities that happen to coincide at threshold.

## Scope

This file does **not** prove:

* that any specific observable in Tirole 2022 or Galiffi 2024 is
 governed by the Bender Γ identification used here;
* that the avalanche rate value used is exact (it depends on
 band-gap, effective-mass, and background-density inputs from
 Pendry 2024 eq. 9, which encode their own uncertainties);
* that the gain mode persists below the avalanche threshold
 (~50 GW/cm²);
* that the observable visibility in either experiment is an
 exponential function of `γ_eff` (it is not: visibility is
 governed by Pendry 2021's photon-conservation regime, see
 `IsPhotonConservationRegime` in `MaterialTimescales`).

What this file proves is the **microscopic** gain condition at
the rate level: `γ_Drude − β < 0` at Tirole's working pump
intensity, given the published Drude and avalanche rates.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Optics.ITOAvalancheCase

open Physlib.Optics.MaterialTimescales

/-- Galiffi 2024 ellipsometric Drude scattering rate for ITO at
the ENZ wavelength (~1196 nm).  Value: `1.3 × 10¹⁴ s⁻¹`
(equivalently `0.13 fs⁻¹`, or `τ_Drude ≈ 7.7 fs`). -/
def gammaDrudeITO : ℝ := 1.3e14

theorem gammaDrudeITO_pos : 0 < gammaDrudeITO := by
  unfold gammaDrudeITO; norm_num

/-- Pendry 2024 avalanche rate `β = E·e/√(U_G·m)` evaluated at
Tirole's working pump intensity `I_pump = 124 GW/cm²`.

Numerical value `2.34 × 10¹⁴ s⁻¹` (so `τ_β ≈ 4.27 fs`) is from
the Python computation in
`catsim/scripts/pendry_avalanche_timescale.py` smoke-test 13,
using Pendry's stated parameters `U_G = 3 eV`, `m = m_e`,
`n₀ = 10²⁴ m⁻³`. -/
def betaTiroleAtWorkingPump : ℝ := 2.34e14

theorem betaTiroleAtWorkingPump_pos : 0 < betaTiroleAtWorkingPump := by
  unfold betaTiroleAtWorkingPump; norm_num

/-- The **Tirole-ITO effective-damping decomposition**:
explicit instance of `EffectiveDampingDecomposition` with
Pendry's `γ_eff = γ_Drude − β` filled in numerically.

The `decomp` field reduces to `rfl` because the definition of
`γ_eff_inv_s` is literally `gammaDrudeITO - betaTiroleAtWorkingPump`. -/
def tiroleDecomposition : EffectiveDampingDecomposition where
  γ_Drude_inv_s := gammaDrudeITO
  γ_Drude_pos   := gammaDrudeITO_pos
  β_inv_s       := betaTiroleAtWorkingPump
  β_pos         := betaTiroleAtWorkingPump_pos
  γ_eff_inv_s   := gammaDrudeITO - betaTiroleAtWorkingPump
  decomp        := rfl

/-- **Avalanche exceeds Drude at Tirole's working pump intensity**:
`γ_Drude = 1.3 × 10¹⁴ < 2.34 × 10¹⁴ = β`. -/
theorem gammaDrudeITO_lt_betaTiroleAtWorkingPump :
    gammaDrudeITO < betaTiroleAtWorkingPump := by
  unfold gammaDrudeITO betaTiroleAtWorkingPump; norm_num

/-- **Tirole's working pump intensity is in the Bender gain
mode**: the effective Drude damping `γ_eff = γ_Drude − β` is
strictly negative, so the system exhibits exponential
amplification rather than damping.  This realises the Bender
complex-energy structure with `Im[ω] > 0` (gain) directly from
the avalanche dynamics, with no axiomatic input beyond the two
published rate measurements.

Proof: direct application of `isGainMode_iff_beta_gt_gammaDrude`
to `gammaDrudeITO_lt_betaTiroleAtWorkingPump`. -/
theorem tirole_is_gain_mode : IsGainMode tiroleDecomposition := by
  rw [isGainMode_iff_beta_gt_gammaDrude]
  exact gammaDrudeITO_lt_betaTiroleAtWorkingPump

/-- The effective damping at Tirole's working pump intensity
has numerical value `−1.04 × 10¹⁴ s⁻¹`.  This is the literal
Bender `Im[E]/ℏ` for the Tirole-ITO system in the avalanche
regime. -/
theorem tiroleDecomposition_gamma_eff_value :
    tiroleDecomposition.γ_eff_inv_s = -1.04e14 := by
  show gammaDrudeITO - betaTiroleAtWorkingPump = -1.04e14
  unfold gammaDrudeITO betaTiroleAtWorkingPump
  norm_num

/-! ## ITO at the Pendry avalanche threshold (computed) -/

/-- **Pendry avalanche rate at the threshold pump intensity**:
this is the value of `β` such that `β = γ_Drude`, i.e. the
decomposition sits exactly at threshold (`γ_eff = 0`).

Numerical value `1.30 × 10¹⁴ s⁻¹`, equal to `gammaDrudeITO` by
construction.  The corresponding pump intensity (computed in
`pendry_avalanche_timescale.pendry_threshold_intensity_GWcm2`)
is `≈ 38.3 GW/cm²`, within ~25 % of Pendry's stated qualitative
threshold of `≈ 50 GW/cm²`. -/
def betaAtThreshold : ℝ := 1.3e14

theorem betaAtThreshold_pos : 0 < betaAtThreshold := by
  unfold betaAtThreshold; norm_num

theorem betaAtThreshold_eq_gammaDrude :
    betaAtThreshold = gammaDrudeITO := by
  unfold betaAtThreshold gammaDrudeITO; rfl

/-- **At-threshold decomposition for the Tirole-ITO system**:
`γ_Drude = β = 1.30 × 10¹⁴ s⁻¹`, so `γ_eff = 0`.  This is the
boundary case between the gain and decay regimes. -/
def tiroleThresholdDecomposition : EffectiveDampingDecomposition where
  γ_Drude_inv_s := gammaDrudeITO
  γ_Drude_pos   := gammaDrudeITO_pos
  β_inv_s       := betaAtThreshold
  β_pos         := betaAtThreshold_pos
  γ_eff_inv_s   := gammaDrudeITO - betaAtThreshold
  decomp        := rfl

/-- **Tirole-ITO threshold decomposition is exactly at
threshold**.  Follows from `isAtThreshold_iff_beta_eq_gammaDrude`
applied to the equality `β = γ_Drude`. -/
theorem tirole_at_threshold : IsAtThreshold tiroleThresholdDecomposition := by
  rw [isAtThreshold_iff_beta_eq_gammaDrude]
  exact betaAtThreshold_eq_gammaDrude

/-- **At threshold the system is neither gain-mode nor
decay-mode**.  Composes the threshold theorem with the
mutual-exclusion lemma from `MaterialTimescales`. -/
theorem tirole_threshold_neither_gain_nor_decay :
    ¬ IsGainMode tiroleThresholdDecomposition ∧
    ¬ IsDecayMode tiroleThresholdDecomposition :=
  not_gain_and_not_decay_of_threshold tirole_at_threshold

/-! ## ITO at Galiffi's low pump (18 GW/cm²) — decay regime -/

/-- **Avalanche rate at Galiffi's low-pump operating point**:
`β = 8.92 × 10¹³ s⁻¹`, computed from Pendry 2024 eq. 3 with
`I_pump = 18 GW/cm²` (the lowest intensity in Galiffi's
Fig 5b sweep).  This is **below** the threshold `γ_Drude =
1.30 × 10¹⁴ s⁻¹`, so the decomposition is in the decay regime. -/
def betaGalliffiLowPump : ℝ := 8.92e13

theorem betaGalliffiLowPump_pos : 0 < betaGalliffiLowPump := by
  unfold betaGalliffiLowPump; norm_num

/-- **Below-threshold decomposition for the Tirole-ITO system at
Galiffi's low pump**: `β = 8.92 × 10¹³ s⁻¹ < γ_Drude = 1.30 ×
10¹⁴ s⁻¹`, so `γ_eff > 0` (decay mode). -/
def galiffiLowPumpDecomposition : EffectiveDampingDecomposition where
  γ_Drude_inv_s := gammaDrudeITO
  γ_Drude_pos   := gammaDrudeITO_pos
  β_inv_s       := betaGalliffiLowPump
  β_pos         := betaGalliffiLowPump_pos
  γ_eff_inv_s   := gammaDrudeITO - betaGalliffiLowPump
  decomp        := rfl

/-- **Avalanche below Drude at Galiffi's low pump**:
`8.92 × 10¹³ < 1.30 × 10¹⁴`. -/
theorem betaGalliffiLowPump_lt_gammaDrudeITO :
    betaGalliffiLowPump < gammaDrudeITO := by
  unfold betaGalliffiLowPump gammaDrudeITO; norm_num

/-- **Galiffi's low pump intensity is in the Bender decay
mode**: the effective Drude damping is positive (avalanche has
not ignited), so the system dissipates rather than amplifies. -/
theorem galiffi_low_pump_is_decay_mode :
    IsDecayMode galiffiLowPumpDecomposition := by
  rw [isDecayMode_iff_gammaDrude_gt_beta]
  exact betaGalliffiLowPump_lt_gammaDrudeITO

/-- The effective damping at Galiffi's low pump intensity has
numerical value `+4.08 × 10¹³ s⁻¹` (positive = ordinary Drude
decay). -/
theorem galiffiLowPumpDecomposition_gamma_eff_value :
    galiffiLowPumpDecomposition.γ_eff_inv_s = 4.08e13 := by
  show gammaDrudeITO - betaGalliffiLowPump = 4.08e13
  unfold gammaDrudeITO betaGalliffiLowPump
  norm_num

/-! ## ITO at Galiffi's high pump (589 GW/cm²) — extreme gain -/

/-- **Avalanche rate at Galiffi's high-pump operating point**:
`β = 5.10 × 10¹⁴ s⁻¹`, computed from Pendry 2024 eq. 3 with
`I_pump = 589 GW/cm²` (the highest intensity in Galiffi's
Fig 5b sweep).  This is `≈ 3.9 ×` the Drude rate, so the
decomposition is deep in the gain regime — consistent with
Galiffi's observation of up to 2600 % parametric amplification
at high pump intensity. -/
def betaGalliffiHighPump : ℝ := 5.10e14

theorem betaGalliffiHighPump_pos : 0 < betaGalliffiHighPump := by
  unfold betaGalliffiHighPump; norm_num

/-- **Extreme-gain decomposition for the Tirole-ITO system at
Galiffi's high pump**: `β = 5.10 × 10¹⁴ s⁻¹ >> γ_Drude = 1.30 ×
10¹⁴ s⁻¹`, so `γ_eff << 0`. -/
def galiffiHighPumpDecomposition : EffectiveDampingDecomposition where
  γ_Drude_inv_s := gammaDrudeITO
  γ_Drude_pos   := gammaDrudeITO_pos
  β_inv_s       := betaGalliffiHighPump
  β_pos         := betaGalliffiHighPump_pos
  γ_eff_inv_s   := gammaDrudeITO - betaGalliffiHighPump
  decomp        := rfl

/-- **Drude well below avalanche at Galiffi's high pump**:
`1.30 × 10¹⁴ < 5.10 × 10¹⁴`. -/
theorem gammaDrudeITO_lt_betaGalliffiHighPump :
    gammaDrudeITO < betaGalliffiHighPump := by
  unfold gammaDrudeITO betaGalliffiHighPump; norm_num

/-- **Galiffi's high pump intensity is in the Bender gain
mode**, with effective damping deep in the negative regime. -/
theorem galiffi_high_pump_is_gain_mode :
    IsGainMode galiffiHighPumpDecomposition := by
  rw [isGainMode_iff_beta_gt_gammaDrude]
  exact gammaDrudeITO_lt_betaGalliffiHighPump

/-- The effective damping at Galiffi's high pump intensity has
numerical value `−3.80 × 10¹⁴ s⁻¹` (large negative = extreme
gain).  In magnitude this is `≈ 3.65 ×` larger than the
working-pump value `−1.04 × 10¹⁴` from `tiroleDecomposition`. -/
theorem galiffiHighPumpDecomposition_gamma_eff_value :
    galiffiHighPumpDecomposition.γ_eff_inv_s = -3.80e14 := by
  show gammaDrudeITO - betaGalliffiHighPump = -3.80e14
  unfold gammaDrudeITO betaGalliffiHighPump
  norm_num

/-! ## ITO at Harwood's pump (200 GW/cm²) — deep gain

Harwood, Vezzoli, Raziman, Hooper, Tirole, Wu, Maier, Pendry,
Horsley, Sapienza (2024), *Space-Time Optical Diffraction from
Synthetic Motion*, arXiv 2407.10809, report a reflectivity
rise time **`<10 fs` at high pump powers** for their `200 GW/cm²`
pump intensity (their main text, p. 4).  Plugging this `I_pump`
into Pendry 2024 eq. 3 with the band-gap and mass values from
Pendry's own example gives `β ≈ 2.97 × 10¹⁴ s⁻¹` and
`τ_β ≈ 3.36 fs` — comfortably below the `<10 fs` observation,
i.e. the avalanche switching at Harwood's pump intensity is
fast enough to account for what they see.  The complex-action/entropic-time
framework's prediction at Harwood's pump intensity is therefore
**consistent with the reported rise time**.

(The diffraction pattern Harwood actually measures, and their
super-relativistic Doppler analysis of it, lie outside the
gain/decay/threshold scope of this Lean module — only the
rise-time anchor is checked here.) -/

/-- **Pendry avalanche rate at Harwood's pump intensity**
`I_pump = 200 GW/cm²`.  Numerical value `2.97 × 10¹⁴ s⁻¹` from
the Python computation in
`catsim/scripts/pendry_avalanche_timescale.py` smoke-test 13.
Implies `τ_β ≈ 3.36 fs`, consistent with Harwood's reported
`<10 fs` rise time. -/
def betaHarwoodPump : ℝ := 2.97e14

theorem betaHarwoodPump_pos : 0 < betaHarwoodPump := by
  unfold betaHarwoodPump; norm_num

/-- **Harwood-pump decomposition**: `γ_Drude = 1.30 × 10¹⁴ s⁻¹`,
`β = 2.97 × 10¹⁴ s⁻¹`, so `γ_eff = −1.67 × 10¹⁴ s⁻¹` —
intermediate between the Tirole working-pump value
(`−1.04 × 10¹⁴`) and the Galiffi high-pump value
(`−3.80 × 10¹⁴`), as expected for the intermediate pump
intensity `200 GW/cm²`. -/
def harwoodPumpDecomposition : EffectiveDampingDecomposition where
  γ_Drude_inv_s := gammaDrudeITO
  γ_Drude_pos   := gammaDrudeITO_pos
  β_inv_s       := betaHarwoodPump
  β_pos         := betaHarwoodPump_pos
  γ_eff_inv_s   := gammaDrudeITO - betaHarwoodPump
  decomp        := rfl

/-- **Drude well below avalanche at Harwood's pump**:
`1.30 × 10¹⁴ < 2.97 × 10¹⁴`. -/
theorem gammaDrudeITO_lt_betaHarwoodPump :
    gammaDrudeITO < betaHarwoodPump := by
  unfold gammaDrudeITO betaHarwoodPump; norm_num

/-- **Harwood's pump intensity is in the Bender gain mode**.
The avalanche rate exceeds the Drude damping by a factor of
~2.3, putting the system deep in the gain regime, consistent
with the high reflectivity contrast (~70 %) Harwood reports. -/
theorem harwood_is_gain_mode :
    IsGainMode harwoodPumpDecomposition := by
  rw [isGainMode_iff_beta_gt_gammaDrude]
  exact gammaDrudeITO_lt_betaHarwoodPump

/-- The effective damping at Harwood's pump intensity has
numerical value `−1.67 × 10¹⁴ s⁻¹`.  This sits between the
Tirole working-pump value (`−1.04 × 10¹⁴` at `I = 124 GW/cm²`)
and the Galiffi high-pump value (`−3.80 × 10¹⁴` at `I = 589
GW/cm²`), as expected for the intermediate pump intensity
`I = 200 GW/cm²`. -/
theorem harwoodPumpDecomposition_gamma_eff_value :
    harwoodPumpDecomposition.γ_eff_inv_s = -1.67e14 := by
  show gammaDrudeITO - betaHarwoodPump = -1.67e14
  unfold gammaDrudeITO betaHarwoodPump
  norm_num

/-! ## Regime summary

Five Tirole-ITO / Galiffi-ITO / Harwood-ITO instances together
span the pump-intensity range of the Pendry avalanche regime:

  Galiffi low pump   (18 GW/cm²)    β = 8.92e13   γ_eff = +4.08e13   decay
  computed threshold (~38 GW/cm²)   β = 1.30e14   γ_eff = 0          boundary
  Tirole working     (124 GW/cm²)   β = 2.34e14   γ_eff = -1.04e14   gain
  Harwood working    (200 GW/cm²)   β = 2.97e14   γ_eff = -1.67e14   gain
  Galiffi high pump  (589 GW/cm²)   β = 5.10e14   γ_eff = -3.80e14   extreme gain

All five cases are concrete `EffectiveDampingDecomposition`
instances; the regime conclusions are Lean theorems derived
from the abstract `isDecayMode_iff_gammaDrude_gt_beta`,
`isAtThreshold_iff_beta_eq_gammaDrude`, and
`isGainMode_iff_beta_gt_gammaDrude` of
`MaterialTimescales.lean` §F.  No axioms added.

Across the three Pendry-circle ITO experiments anchored here,
Pendry-2024's avalanche-corrected effective damping
`γ_eff = γ_Drude − β` is the consistent operational
identification of the Bender complex-energy regime. -/

end Physlib.Optics.ITOAvalancheCase

end
