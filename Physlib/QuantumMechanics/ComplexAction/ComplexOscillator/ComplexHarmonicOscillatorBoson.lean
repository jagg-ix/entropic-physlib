/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.BosonicInertialMass
public import Physlib.QuantumMechanics.Schrodinger.SpectralDynamics

/-!
# The complex harmonic oscillator: bosonic inertia from frequency, and the massless Wick rotation

This file extends `MassOrigin.BosonicInertialMass` using Nagao–Nielsen's *Formalism of a harmonic
oscillator in the future-included complex action theory* (arXiv:1902.01424). The harmonic
oscillator is the prototypical **boson** (its quanta are bosons), here with **complex mass
`m = m_R + i m_I`** and **complex angular frequency `ω = ω_R + i ω_I`** (Eqs. 3.12–3.15).
Three results connect directly to the massless-boson inertial mass of the last step.

## §A — The kinetic-convergence condition `m_I ≥ 0` (Eq. 3.22)

For the oscillator's FPI to be sensible the kinetic term must not blow up: `m_I ≥ 0`
(Eq. 3.22). This is *exactly* the convergence condition of
`PathIntegral.MomentumPathIntegral.momentum_integral_converges_iff` (`0 < Re b ⟺ 0 < Im m`), so the
oscillator's "sensible-boson" region is the Feynman–Kac/Euclidean-damping region of the
momentum integral. (`oscillatorKineticConverges`, `oscillator_kinetic_converges_iff`.)

## §B — The massless boson is a Wick-rotated imaginary mass (Eqs. 3.30, 3.36, case θ_m = π/2)

At `θ_m = π/2` the rest mass vanishes (`m_R = 0`), so `m = i m_I` is **purely imaginary** — a
massless boson. Nagao–Nielsen restore a positive real mass by `m_new = a·m` with `a = −i`
(and imaginary time `t_new = −i t`): `m_new = (−i)(i m_I) = m_I`. So the massless boson's
inertia is the imaginary mass `m_I` *Wick-rotated to a real inertial mass*
(`massless_inertialMass`) — the precise origin of the "generated scale" `μ` of
`MassOrigin.BosonicInertialMass`. With it, the Nagao–Nielsen effective mass is just `m_I`
(`massless_bosonicEffectiveMass`).

## §C — Bosonic inertia comes from frequency, not rest mass (`E_n = ℏω(n+½)`)

The oscillator energy spectrum is `E_n = ℏω(n+½)` (`oscillatorEnergy`), with level spacing
`E_{n+1} − E_n = ℏω` (the quantum) and zero-point energy `E_0 = ℏω/2`. A boson's energy is
set by its **frequency**, so via `E = m_inert c²` the n-th quantum records inertial mass
`ℏω(n+½)/c² > 0` **even when the rest mass is zero** (`quantum_inertialMass_pos`): a massless
boson is inertial because it oscillates.

## Link to reversibility / no information

`m_I` (the Wick-rotated mass) and `ω` (the spectral inertia) both have to be nonzero for a
massless boson to encode inertia. In the reversible / `T = 0` / no-information limit the
imaginary sector vanishes (`m_I → 0`): the kinetic term — and with it the massless boson's
inertia — disappears, consistent with `MassOrigin.BosonicInertialMass.thermalInertialMass_zero_iff`.

## References

* K. Nagao, H. B. Nielsen, arXiv:1902.01424, Eqs. 3.12–3.36 (complex `m`, `ω`; phase
  diagram; mass positivization `m_new = a m`); arXiv:1304.4017 (`m_eff`).
* `MassOrigin.BosonicInertialMass` (this development) — generated inertial scales `E/c²`, `k_B T/c²`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.BosonicInertialMass
open Physlib.QuantumMechanics.Schrodinger.SpectralDynamics

namespace Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson

/-! ## §A — the kinetic-convergence condition `m_I ≥ 0` (Eq. 3.22) -/

/-- **Eq. 3.22**: the sensible-boson condition `m_I ≥ 0` — the oscillator's kinetic term
does not blow up. -/
def oscillatorKineticConverges (m : ℂ) : Prop := 0 ≤ m.im

/-- **Eq. 3.23**: the potential-convergence condition `Im(mω²) ≤ 0`. -/
def oscillatorPotentialConverges (m ω : ℂ) : Prop := (m * ω ^ 2).im ≤ 0

/-- **The oscillator kinetic Gaussian converges iff `Im m > 0`** — the same Feynman–Kac /
Euclidean-damping condition as the momentum integral (`momentum_integral_converges_iff`). So
the oscillator's sensible-boson region (Eq. 3.22) is the momentum integral's convergence
region. -/
theorem oscillator_kinetic_converges_iff (m : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt)
    (hm : m ≠ 0) : 0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im :=
  momentum_integral_converges_iff m hℏ hdt hm

/-! ## §B — the massless boson as a Wick-rotated imaginary mass (Eqs. 3.30, 3.36) -/

/-- **Mass positivization** `m_new = a·m` (Nagao–Nielsen Eq. 3.30): the unit-modulus factor
`a` rotating the complex mass to a positive real part. -/
def massPositivized (a m : ℂ) : ℂ := a * m

/-- **The massless boson's Wick-rotated inertial mass** (Eq. 3.30/3.36, case `θ_m = π/2`):
the purely-imaginary mass `m = i m_I` (rest mass `m_R = 0`) is rotated by `a = −i` to the
**real** inertial mass `m_I`. -/
theorem massless_inertialMass (m_I : ℝ) :
    massPositivized (-Complex.I) (((0 : ℝ) : ℂ) + (m_I : ℂ) * Complex.I) = (m_I : ℂ) := by
  unfold massPositivized
  rw [Complex.ofReal_zero, zero_add]
  have h : (-Complex.I) * ((m_I : ℂ) * Complex.I) = (m_I : ℂ) * (-(Complex.I * Complex.I)) := by
    ring
  rw [h, Complex.I_mul_I]
  ring

/-- **The massless boson's Nagao–Nielsen effective mass is just `m_I`**: with the
Wick-rotated real scale `μ = m_I` and no residual imaginary mass, `m_eff = m_I` — the
generated inertial scale of `MassOrigin.BosonicInertialMass`, supplied here by the harmonic-oscillator
construction. -/
theorem massless_bosonicEffectiveMass (m_I : ℝ) :
    bosonicEffectiveMass m_I 0 = m_I := by
  unfold bosonicEffectiveMass effectiveMass
  simp

/-! ## §C — bosonic inertia from frequency: `E_n = ℏ ω (n + ½)` -/

/-- **The oscillator energy spectrum** `E_n = ℏ ω (n + ½)` (complex `ω` in general). -/
def oscillatorEnergy (ℏ : ℝ) (ω : ℂ) (n : ℕ) : ℂ := (ℏ : ℂ) * ω * ((n : ℂ) + 1 / 2)

/-- **The level spacing is the quantum** `E_{n+1} − E_n = ℏ ω`. -/
theorem oscillatorEnergy_succ_sub (ℏ : ℝ) (ω : ℂ) (n : ℕ) :
    oscillatorEnergy ℏ ω (n + 1) - oscillatorEnergy ℏ ω n = (ℏ : ℂ) * ω := by
  unfold oscillatorEnergy
  push_cast
  ring

/-- **The zero-point energy** `E_0 = ℏ ω / 2`. -/
theorem oscillatorEnergy_zero (ℏ : ℝ) (ω : ℂ) :
    oscillatorEnergy ℏ ω 0 = (ℏ : ℂ) * ω / 2 := by
  unfold oscillatorEnergy
  push_cast
  ring

/-- **Real-frequency energy spectrum** `E_n = ℏ ω (n + ½) ∈ ℝ` for real `ω`. -/
def oscillatorEnergyReal (ℏ ω : ℝ) (n : ℕ) : ℝ := ℏ * ω * (n + 1 / 2)

/-- For real `ω` the complex spectrum is the real spectrum. -/
theorem oscillatorEnergy_ofReal (ℏ ω : ℝ) (n : ℕ) :
    oscillatorEnergy ℏ (ω : ℂ) n = ((oscillatorEnergyReal ℏ ω n : ℝ) : ℂ) := by
  unfold oscillatorEnergy oscillatorEnergyReal
  push_cast
  ring

/-! ## §C.1 — Spectral-dynamics reuse for oscillator levels -/

/-- The real-frequency oscillator level includes the shared Facchi spectral phase
`exp(-i E_n t / ℏ)`. -/
noncomputable def oscillatorSpectralPhase (ℏ ω : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  spectralPhase (oscillatorEnergyReal ℏ ω n) ℏ t

/-- The oscillator spectral phase has unit norm by the common spectral-dynamics
phase theorem. -/
theorem oscillatorSpectralPhase_norm (ℏ ω : ℝ) (n : ℕ) (t : ℝ) :
    ‖oscillatorSpectralPhase ℏ ω n t‖ = 1 := by
  simpa [oscillatorSpectralPhase] using
    spectralPhase_norm (oscillatorEnergyReal ℏ ω n) ℏ t

/-- Oscillator spectral phases preserve scalar Born weights. -/
theorem oscillatorSpectralPhase_probability_preserved
    (ℏ ω : ℝ) (n : ℕ) (t : ℝ) (c : ℂ) :
    ‖oscillatorSpectralPhase ℏ ω n t * c‖ ^ 2 = ‖c‖ ^ 2 := by
  simpa [oscillatorSpectralPhase] using
    spectralAmplitude_probability_preserved (oscillatorEnergyReal ℏ ω n) ℏ t c

/-- A finite oscillator spectral packet preserves the total Born weight by the
shared finite pure-point spectral-evolution theorem. -/
theorem oscillatorFiniteSpectralEvolution_total_probability
    (N : ℕ) (ℏ ω t : ℝ) (c : Fin N → ℂ) :
    (∑ i, ‖finiteSpectralEvolution
      (fun j : Fin N => oscillatorEnergyReal ℏ ω (j : ℕ)) ℏ t c i‖ ^ 2)
      = ∑ i, ‖c i‖ ^ 2 := by
  simpa using
    finiteSpectralEvolution_total_probability
      (fun j : Fin N => oscillatorEnergyReal ℏ ω (j : ℕ)) ℏ t c

/-- **Bosonic inertia from frequency**: the n-th oscillator quantum records positive
inertial mass `ℏ ω (n + ½)/c² > 0` (via `E = m_inert c²`) **even with zero rest mass** — a
massless boson is inertial because it oscillates. -/
theorem quantum_inertialMass_pos (ℏ ω c : ℝ) (hℏ : 0 < ℏ) (hω : 0 < ω) (hc : 0 < c) (n : ℕ) :
    0 < relativisticInertialMass (oscillatorEnergyReal ℏ ω n) c := by
  apply relativisticInertialMass_pos _ c _ hc
  unfold oscillatorEnergyReal
  positivity

/-- **The quantum inertial mass explicitly** `m_inert,n = ℏ ω (n + ½)/c²`. -/
theorem quantum_inertialMass_eq (ℏ ω c : ℝ) (n : ℕ) :
    relativisticInertialMass (oscillatorEnergyReal ℏ ω n) c = ℏ * ω * (n + 1 / 2) / c ^ 2 := by
  unfold relativisticInertialMass oscillatorEnergyReal
  rfl

end Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson

end

end
