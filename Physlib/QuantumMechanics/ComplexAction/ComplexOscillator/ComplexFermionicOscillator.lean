/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LorentzianPhase

/-!
# The complex fermionic oscillator (Pauli / Fermi–Dirac) and its inertial phase

This file expands the bosonic complex oscillator (`ComplexOscillator.ComplexHarmonicOscillatorBoson`) and the
inverted oscillator (`ComplexOscillator.PhaseDiagram`) to the **fermionic** case, leveraging the
inertial-mass / Lorentzian-phase machinery of `CollisionOperatorSl2.LorentzianPhase`.

## Bosonic ⟶ fermionic

A fermion is a two-level system (Pauli exclusion, `n ∈ {0, 1}`). The differences from the
boson are exactly the statistics sign:

* **Spectrum** — bosonic `E_n = ℏω(n+½)` (ground `+ℏω/2`) becomes fermionic `E_n = ℏω(n−½)`,
  with levels `{−ℏω/2, +ℏω/2}` (`fermionicEnergyReal`). The **ground energy is negative**
  (`fermionicEnergyReal_ground_neg`) — the inverted-oscillator / Dirac-sea feature — and the
  bosonic and fermionic zero-point energies **cancel** (`susy_zeropoint_cancellation`,
  `+ℏω/2 − ℏω/2 = 0`, SUSY).
* **Occupation** — Bose–Einstein `1/(e^{βℏω}−1)` (unbounded) becomes Fermi–Dirac
  `1/(e^{βℏω}+1)`, which is **bounded below 1** (`fermiDirac_lt_one`, Pauli exclusion).
* **Matsubara frequencies** — bosonic `2πn/β` (a zero mode at `n=0`) becomes fermionic
  `(2n+1)π/β` (antiperiodic, **no zero mode**, `fermionicMatsubaraFreq_ne_zero`).

## Inertial phase extends (leveraging `CollisionOperatorSl2.LorentzianPhase`)

The fermionic frequency is still `ω = √(k_spring/m_eff)`, so the inertial mass slows the
fermionic Lorentzian phase exactly as for the boson (`fermionicPhaseRate_le_bare`), and the
fermionic Lorentzian kernel is a pure phase (`fermionic_lorentzian_phase_unimodular`).

## References

* Fermionic harmonic oscillator / Fermi–Dirac statistics; Matsubara antiperiodicity.
* `ComplexOscillator.ComplexHarmonicOscillatorBoson`, `ComplexOscillator.PhaseDiagram`,
  `CollisionOperatorSl2.LorentzianPhase` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LorentzianPhase
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.LorentzianMatsubaraWick

namespace Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator

/-! ## §A — the fermionic spectrum `E_n = ℏω(n−½)` (Pauli, two levels) -/

/-- **The fermionic oscillator spectrum** `E_n = ℏω(n−½)` (`n ∈ {0,1}`: levels `{−ℏω/2, +ℏω/2}`).
Contrast the bosonic `oscillatorEnergyReal = ℏω(n+½)`. -/
def fermionicEnergyReal (ℏ ω : ℝ) (n : ℕ) : ℝ := ℏ * ω * (n - 1 / 2)

/-- **The fermionic ground level** `E_0 = −ℏω/2`. -/
theorem fermionicEnergyReal_ground (ℏ ω : ℝ) : fermionicEnergyReal ℏ ω 0 = -(ℏ * ω / 2) := by
  unfold fermionicEnergyReal; push_cast; ring

/-- **The fermionic excited level** `E_1 = +ℏω/2`. -/
theorem fermionicEnergyReal_excited (ℏ ω : ℝ) : fermionicEnergyReal ℏ ω 1 = ℏ * ω / 2 := by
  unfold fermionicEnergyReal; push_cast; ring

/-- **The fermionic ground energy is negative** (`ℏ, ω > 0`) — the inverted-oscillator /
Dirac-sea feature, unlike the bosonic `+ℏω/2 > 0`. -/
theorem fermionicEnergyReal_ground_neg (ℏ ω : ℝ) (hℏ : 0 < ℏ) (hω : 0 < ω) :
    fermionicEnergyReal ℏ ω 0 < 0 := by
  rw [fermionicEnergyReal_ground]
  have : 0 < ℏ * ω / 2 := by positivity
  linarith

/-- **Level spacing is the quantum** `E_1 − E_0 = ℏω` (same as the boson). -/
theorem fermionic_level_spacing (ℏ ω : ℝ) :
    fermionicEnergyReal ℏ ω 1 - fermionicEnergyReal ℏ ω 0 = ℏ * ω := by
  unfold fermionicEnergyReal; push_cast; ring

/-- **SUSY zero-point cancellation**: the bosonic (`+ℏω/2`) and fermionic (`−ℏω/2`) ground-state
energies cancel, `E_0^B + E_0^F = 0`. -/
theorem susy_zeropoint_cancellation (ℏ ω : ℝ) :
    oscillatorEnergyReal ℏ ω 0 + fermionicEnergyReal ℏ ω 0 = 0 := by
  unfold oscillatorEnergyReal fermionicEnergyReal; push_cast; ring

/-! ## §B — Fermi–Dirac occupation (Pauli exclusion, bounded) -/

/-- **Fermi–Dirac occupation** `n_F = 1/(e^{βℏω}+1)` — the `+1` (vs Bose–Einstein's `−1`) is the
fermionic statistics sign. -/
def fermiDirac (x : ℝ) : ℝ := 1 / (Real.exp x + 1)

/-- The Fermi–Dirac occupation is positive. -/
theorem fermiDirac_pos (x : ℝ) : 0 < fermiDirac x := by
  unfold fermiDirac; positivity

/-- **Pauli exclusion**: `n_F < 1` always — at most one fermion per mode (unlike the unbounded
Bose–Einstein occupation `ThermoFieldDynamics.MatsubaraThermalOscillator.boseEinstein`). -/
theorem fermiDirac_lt_one (x : ℝ) : fermiDirac x < 1 := by
  unfold fermiDirac
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos x]

/-! ## §C — fermionic Matsubara frequencies (antiperiodic, no zero mode) -/

/-- **Fermionic Matsubara frequencies** `ω_n = (2n+1)π/β` (antiperiodic), vs the bosonic
`2nπ/β` (`ThermoFieldDynamics.MatsubaraThermalOscillator.matsubaraFreqBoson`). -/
def fermionicMatsubaraFreq (β : ℝ) (n : ℤ) : ℝ := (2 * n + 1) * Real.pi / β

/-- **No fermionic zero mode**: `ω_n ≠ 0` for all `n` (the odd numerator `2n+1 ≠ 0`) — the
antiperiodicity, contrasting the bosonic static mode `matsubaraFreqBoson β 0 = 0`. -/
theorem fermionicMatsubaraFreq_ne_zero (β : ℝ) (hβ : β ≠ 0) (n : ℤ) :
    fermionicMatsubaraFreq β n ≠ 0 := by
  unfold fermionicMatsubaraFreq
  apply div_ne_zero _ hβ
  apply mul_ne_zero _ Real.pi_ne_zero
  have h : (2 * (n : ℝ) + 1) = ((2 * n + 1 : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.cast_ne_zero]
  omega

/-! ## §D — the inertial mass slows the fermionic Lorentzian phase (leverage) -/

/-- **The fermionic Lorentzian phase rate** `ω(m_eff)·½` (`|E_1|/ℏ`), on the Nagao–Nielsen
inertial mass. -/
def fermionicPhaseRate (kSpring m_R m_I : ℝ) : ℝ :=
  oscillatorFrequency kSpring (effectiveMass m_R m_I) * (1 / 2)

/-- **The imaginary mass slows the fermionic phase** too (`phaseRate(m_eff) ≤ phaseRate(m_R)`),
exactly as for the boson. -/
theorem fermionicPhaseRate_le_bare (kSpring m_R m_I : ℝ) (hk : 0 < kSpring) (hm_R : 0 < m_R) :
    fermionicPhaseRate kSpring m_R m_I ≤ oscillatorFrequency kSpring m_R * (1 / 2) := by
  unfold fermionicPhaseRate
  have hfreq : oscillatorFrequency kSpring (effectiveMass m_R m_I)
      ≤ oscillatorFrequency kSpring m_R :=
    oscillatorFrequency_antitone kSpring m_R (effectiveMass m_R m_I) hk hm_R
      (effectiveMass_ge m_R m_I hm_R)
  exact mul_le_mul_of_nonneg_right hfreq (by norm_num)

/-- **The fermionic Lorentzian real-time kernel is a pure phase** (unitary): the inertial mass
changes the fermionic phase *rate*, not the magnitude. -/
theorem fermionic_lorentzian_phase_unimodular (kSpring m_R m_I ℏ t : ℝ) :
    ‖wickKernel (ℏ * fermionicPhaseRate kSpring m_R m_I) ℏ (t : ℂ)‖ = 1 :=
  norm_wickKernel_real_time _ ℏ t

end Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator

end
