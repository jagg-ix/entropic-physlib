/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.MassInertial
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.LorentzianMatsubaraWick

/-!
# The inertial mass and the Lorentzian real-time phase

`CollisionOperatorSl2.MassInertial` showed the Nagao–Nielsen inertial mass `m_eff = m_R + m_I²/m_R`
slows the collision operator's *imaginary-time* diffusion (`D = k/2m_eff`). This file leverages
that to the **Lorentzian real-time** side: the same `m_eff` sets the oscillator frequency
`ω = √(k_spring/m_eff)`, which is the **rotation rate of the Lorentzian phase** `e^{−iEt/ℏ}`.

So the inertial mass acts on real time and imaginary time in dual ways:

* **Imaginary time (diffusion):** `D = k/2m_eff` — heavier `m_eff` ⟹ slower thermalization
  (`collisionInertialDiffusivity_le_bare`).
* **Real time (phase):** `ω = √(k_spring/m_eff)` — heavier `m_eff` ⟹ slower phase rotation
  (`inertialPhaseRate_le_bare`), while the Lorentzian kernel stays a **pure phase**
  (`‖e^{−iEt/ℏ}‖ = 1`, `oscillator_lorentzian_phase_unimodular`): the inertial mass changes the
  phase *rate*, not the magnitude.

## Main results

* `oscillatorFrequency k_spring m = √(k_spring/m)`; `oscillatorFrequency_antitone` /
  `oscillatorFrequency_lt` — heavier mass ⟹ lower frequency.
* `inertialPhaseRate = ω(m_eff)·(n+½)` — the Lorentzian phase rate (energy/ℏ) of the n-th mode
  on the inertial mass; `inertialPhaseRate_le_bare` / `_lt_bare` — the imaginary mass `m_I`
  slows it (strictly when `m_I ≠ 0`).
* `oscillator_lorentzian_phase_unimodular` — the Lorentzian real-time kernel
  `wickKernel (ℏ·phaseRate) ℏ t` is unimodular (pure phase, unitary).
* `inertialMass_slows_phase_and_diffusion` — **the capstone**: one inertial mass `m_eff` slows
  *both* the Lorentzian real-time phase and the imaginary-time diffusion; both reduce to the
  bare-mass values at `m_I = 0` (the reversible / no-information point).

## References

* V. Saveliev, J. Math. Phys. 37 (1996) 6139 (diffusivity `k/2m`); K. Nagao, H. B. Nielsen,
  arXiv:1304.4017 (`m_eff`), arXiv:1902.01424 (oscillator `ω`).
* `CollisionOperatorSl2.MassInertial`, `ThermoFieldDynamics.LorentzianMatsubaraWick` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.BoltzmannThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.MassInertial
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.LorentzianMatsubaraWick

namespace Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LorentzianPhase

/-! ## §A — the oscillator frequency from the inertial mass `ω = √(k/m)` -/

/-- **The oscillator angular frequency** `ω = √(k_spring/m)` — set by the inertial mass `m`. -/
def oscillatorFrequency (kSpring m : ℝ) : ℝ := Real.sqrt (kSpring / m)

/-- **Heavier mass ⟹ lower frequency** (`m₁ ≤ m₂ ⟹ ω(m₂) ≤ ω(m₁)`). -/
theorem oscillatorFrequency_antitone (kSpring m₁ m₂ : ℝ) (hk : 0 < kSpring) (hm₁ : 0 < m₁)
    (h : m₁ ≤ m₂) : oscillatorFrequency kSpring m₂ ≤ oscillatorFrequency kSpring m₁ := by
  unfold oscillatorFrequency
  have hk' : (0 : ℝ) ≤ kSpring := hk.le
  apply Real.sqrt_le_sqrt
  gcongr

/-- **Strictly heavier mass ⟹ strictly lower frequency** (`m₁ < m₂ ⟹ ω(m₂) < ω(m₁)`). -/
theorem oscillatorFrequency_lt (kSpring m₁ m₂ : ℝ) (hk : 0 < kSpring) (hm₁ : 0 < m₁)
    (h : m₁ < m₂) : oscillatorFrequency kSpring m₂ < oscillatorFrequency kSpring m₁ := by
  unfold oscillatorFrequency
  have hm₂ : 0 < m₂ := lt_trans hm₁ h
  apply Real.sqrt_lt_sqrt (by positivity)
  gcongr

/-! ## §B — the Lorentzian real-time phase rate on the inertial mass -/

/-- **The Lorentzian phase rate** (energy/ℏ) of the n-th mode: `ω(m_eff)·(n+½)` — the rotation
rate of the Lorentzian phase `e^{−iEt/ℏ}` for the oscillator on the Nagao–Nielsen inertial mass
`m_eff = m_R + m_I²/m_R`. -/
def inertialPhaseRate (kSpring m_R m_I : ℝ) (n : ℕ) : ℝ :=
  oscillatorFrequency kSpring (effectiveMass m_R m_I) * (n + 1 / 2)

/-- **The imaginary mass slows the Lorentzian phase** (`phaseRate(m_eff) ≤ phaseRate(m_R)`). -/
theorem inertialPhaseRate_le_bare (kSpring m_R m_I : ℝ) (n : ℕ) (hk : 0 < kSpring)
    (hm_R : 0 < m_R) :
    inertialPhaseRate kSpring m_R m_I n ≤ oscillatorFrequency kSpring m_R * (n + 1 / 2) := by
  unfold inertialPhaseRate
  have hfreq : oscillatorFrequency kSpring (effectiveMass m_R m_I)
      ≤ oscillatorFrequency kSpring m_R :=
    oscillatorFrequency_antitone kSpring m_R (effectiveMass m_R m_I) hk hm_R
      (effectiveMass_ge m_R m_I hm_R)
  have hn : (0 : ℝ) ≤ (n + 1 / 2) := by positivity
  exact mul_le_mul_of_nonneg_right hfreq hn

/-- **A nonzero imaginary mass strictly slows the Lorentzian phase**: `m_I ≠ 0 ⟹
phaseRate(m_eff) < phaseRate(m_R)`. -/
theorem inertialPhaseRate_lt_bare (kSpring m_R m_I : ℝ) (n : ℕ) (hk : 0 < kSpring)
    (hm_R : 0 < m_R) (hm_I : m_I ≠ 0) :
    inertialPhaseRate kSpring m_R m_I n < oscillatorFrequency kSpring m_R * (n + 1 / 2) := by
  unfold inertialPhaseRate
  have hgt : m_R < effectiveMass m_R m_I := by
    unfold effectiveMass
    have : (0 : ℝ) < m_I ^ 2 / m_R := by positivity
    linarith
  have hfreq := oscillatorFrequency_lt kSpring m_R (effectiveMass m_R m_I) hk hm_R hgt
  have hn : (0 : ℝ) < (n + 1 / 2) := by positivity
  exact mul_lt_mul_of_pos_right hfreq hn

/-! ## §C — the Lorentzian kernel is a pure phase; the mass affects only its rate -/

/-- **The Lorentzian real-time energy** `E = ℏ·ω(m_eff)·(n+½)` of the n-th oscillator mode. -/
def inertialEnergy (kSpring m_R m_I ℏ : ℝ) (n : ℕ) : ℝ :=
  ℏ * inertialPhaseRate kSpring m_R m_I n

/-- **The oscillator's Lorentzian real-time kernel is a pure phase** (unitary): for the real
energy `E = ℏ·ω(m_eff)·(n+½)`, `‖e^{−iEt/ℏ}‖ = 1`. The inertial mass changes the phase *rate*
(`inertialPhaseRate`, slowed by `m_I`), not the magnitude. -/
theorem oscillator_lorentzian_phase_unimodular (kSpring m_R m_I ℏ : ℝ) (n : ℕ) (t : ℝ) :
    ‖wickKernel (inertialEnergy kSpring m_R m_I ℏ n) ℏ (t : ℂ)‖ = 1 :=
  norm_wickKernel_real_time _ ℏ t

/-- **Capstone — one inertial mass, two slowdowns.** The Nagao–Nielsen inertial mass `m_eff`
slows *both* the Lorentzian real-time phase (`ω = √(k_spring/m_eff)`) and the imaginary-time
diffusion (`D = k_B/2m_eff`); both reduce to the bare-mass values at `m_I = 0` (the reversible /
no-information point). -/
theorem inertialMass_slows_phase_and_diffusion (kSpring kB m_R m_I : ℝ) (n : ℕ)
    (hk : 0 < kSpring) (hkB : 0 < kB) (hm_R : 0 < m_R) :
    inertialPhaseRate kSpring m_R m_I n ≤ oscillatorFrequency kSpring m_R * (n + 1 / 2)
      ∧ collisionInertialDiffusivity kB m_R m_I ≤ thermalDiffusivity kB m_R :=
  ⟨inertialPhaseRate_le_bare kSpring m_R m_I n hk hm_R,
   collisionInertialDiffusivity_le_bare kB m_R m_I hkB hm_R⟩

end Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.LorentzianPhase

end
