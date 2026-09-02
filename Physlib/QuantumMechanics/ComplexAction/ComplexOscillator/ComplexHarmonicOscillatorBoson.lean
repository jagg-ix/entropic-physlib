/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.BosonicInertialMass
public import Physlib.QuantumMechanics.OneDimension.HarmonicOscillator.TISE
public import Physlib.QuantumMechanics.Schrodinger.SpectralDynamics
public import Mathlib.Order.Filter.AtTopBot.Field

/-!
# The complex harmonic oscillator: bosonic inertia from frequency, and the massless Wick rotation

This file extends `MassOrigin.BosonicInertialMass` using Nagao–Nielsen's *Formalism of a harmonic
oscillator in the future-included complex action theory* (arXiv:1902.01424). The harmonic
oscillator is the prototypical **boson** (its quanta are bosons), here with **complex mass
`m = m_R + i m_I`** and **complex angular frequency `ω = ω_R + i ω_I`** (Eqs. 3.12–3.15).
Three results connect directly to the massless-boson inertial mass of the last step.


For the oscillator's FPI to be sensible the kinetic term must not blow up: `m_I ≥ 0`
(Eq. 3.22). This is *exactly* the convergence condition of
`PathIntegral.MomentumPathIntegral.momentum_integral_converges_iff` (`0 < Re b ⟺ 0 < Im m`), so the
oscillator's "sensible-boson" region is the Feynman–Kac/Euclidean-damping region of the
momentum integral. (`oscillatorKineticConverges`, `oscillator_kinetic_converges_iff`.)


At `θ_m = π/2` the rest mass vanishes (`m_R = 0`), so `m = i m_I` is **purely imaginary** — a
massless boson. Nagao–Nielsen restore a positive real mass by `m_new = a·m` with `a = −i`
(and imaginary time `t_new = −i t`): `m_new = (−i)(i m_I) = m_I`. So the massless boson's
inertia is the imaginary mass `m_I` *Wick-rotated to a real inertial mass*
(`massless_inertialMass`) — the precise origin of the "generated scale" `μ` of
`MassOrigin.BosonicInertialMass`. With it, the Nagao–Nielsen effective mass is just `m_I`
(`massless_bosonicEffectiveMass`).


The oscillator energy spectrum is `E_n = ℏω(n+½)` (`oscillatorEnergy`), with level spacing
`E_{n+1} − E_n = ℏω` (the quantum) and zero-point energy `E_0 = ℏω/2`. A boson's energy is
set by its **frequency**, so via `E = m_inert c²` the n-th quantum carries inertial mass
`ℏω(n+½)/c² > 0` **even when the rest mass is zero** (`quantum_inertialMass_pos`): a massless
boson is inertial because it oscillates.

## Link to reversibility / no information

`m_I` (the Wick-rotated mass) and `ω` (the spectral inertia) both have to be nonzero for a
massless boson to carry inertia. In the reversible / `T = 0` / no-information limit the
imaginary sector vanishes (`m_I → 0`): the kinetic term — and with it the massless boson's
inertia — disappears, consistent with `MassOrigin.BosonicInertialMass.thermalInertialMass_zero_iff`.

## References

* K. Nagao, H. B. Nielsen, arXiv:1902.01424, Eqs. 3.12–3.36 (complex `m`, `ω`; phase
  diagram; mass positivization `m_new = a m`); arXiv:1304.4017 (`m_eff`).
* `MassOrigin.BosonicInertialMass` (this development) — generated inertial scales `E/c²`, `k_B T/c²`.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.BosonicInertialMass
open Physlib.QuantumMechanics.Schrodinger.SpectralDynamics

namespace Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson


/-- **Eq. 3.22**: the sensible-boson condition `m_I ≥ 0` — the oscillator's kinetic term
does not blow up. -/
def oscillatorKineticConverges (m : ℂ) : Prop := 0 ≤ m.im

/-- **Eq. 3.23**: the potential-convergence condition `Im(mω²) ≤ 0`. -/
def oscillatorPotentialConverges (m ω : ℂ) : Prop := (m * ω ^ 2).im ≤ 0

/-- **The oscillator kinetic Gaussian converges iff `Im m > 0`** — the same Feynman–Kac /
Euclidean-damping condition as the momentum integral (`momentum_integral_converges_iff`). So
the oscillator's sensible-boson region (Eq. 3.22) is the momentum integral's convergence
region. -/
lemma oscillator_kinetic_converges_iff (m : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt)
    (hm : m ≠ 0) : 0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im :=
  momentum_integral_converges_iff m hℏ hdt hm


/-- **Mass positivization** `m_new = a·m` (Nagao–Nielsen Eq. 3.30): the unit-modulus factor
`a` rotating the complex mass to a positive real part. -/
def massPositivized (a m : ℂ) : ℂ := a * m

/-- **The massless boson's Wick-rotated inertial mass** (Eq. 3.30/3.36, case `θ_m = π/2`):
the purely-imaginary mass `m = i m_I` (rest mass `m_R = 0`) is rotated by `a = −i` to the
**real** inertial mass `m_I`. -/
lemma massless_inertialMass (m_I : ℝ) :
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
lemma massless_bosonicEffectiveMass (m_I : ℝ) :
    bosonicEffectiveMass m_I 0 = m_I := by
  unfold bosonicEffectiveMass effectiveMass
  simp


/-- **The oscillator energy spectrum** `E_n = ℏ ω (n + ½)` (complex `ω` in general). -/
def oscillatorEnergy (ℏ : ℝ) (ω : ℂ) (n : ℕ) : ℂ := (ℏ : ℂ) * ω * ((n : ℂ) + 1 / 2)

/-- **The level spacing is the quantum** `E_{n+1} − E_n = ℏ ω`. -/
lemma oscillatorEnergy_succ_sub (ℏ : ℝ) (ω : ℂ) (n : ℕ) :
    oscillatorEnergy ℏ ω (n + 1) - oscillatorEnergy ℏ ω n = (ℏ : ℂ) * ω := by
  unfold oscillatorEnergy
  push_cast
  ring

/-- **The zero-point energy** `E_0 = ℏ ω / 2`. -/
lemma oscillatorEnergy_zero (ℏ : ℝ) (ω : ℂ) :
    oscillatorEnergy ℏ ω 0 = (ℏ : ℂ) * ω / 2 := by
  unfold oscillatorEnergy
  push_cast
  ring

/-- **Real-frequency energy spectrum** `E_n = ℏ ω (n + ½) ∈ ℝ` for real `ω`. -/
def oscillatorEnergyReal (ℏ ω : ℝ) (n : ℕ) : ℝ := ℏ * ω * (n + 1 / 2)

/-- For real `ω` the complex spectrum is the real spectrum. -/
lemma oscillatorEnergy_ofReal (ℏ ω : ℝ) (n : ℕ) :
    oscillatorEnergy ℏ (ω : ℂ) n = ((oscillatorEnergyReal ℏ ω n : ℝ) : ℂ) := by
  unfold oscillatorEnergy oscillatorEnergyReal
  push_cast
  ring


/-- The real-frequency oscillator level carries the shared Facchi spectral phase
`exp(-i E_n t / ℏ)`. -/
noncomputable def oscillatorSpectralPhase (ℏ ω : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  spectralPhase (oscillatorEnergyReal ℏ ω n) ℏ t

/-- The oscillator spectral phase has unit norm by the common spectral-dynamics
phase theorem. -/
lemma oscillatorSpectralPhase_norm (ℏ ω : ℝ) (n : ℕ) (t : ℝ) :
    ‖oscillatorSpectralPhase ℏ ω n t‖ = 1 := by
  simpa [oscillatorSpectralPhase] using
    spectralPhase_norm (oscillatorEnergyReal ℏ ω n) ℏ t

/-- Oscillator spectral phases preserve scalar Born weights. -/
lemma oscillatorSpectralPhase_probability_preserved
    (ℏ ω : ℝ) (n : ℕ) (t : ℝ) (c : ℂ) :
    ‖oscillatorSpectralPhase ℏ ω n t * c‖ ^ 2 = ‖c‖ ^ 2 := by
  simpa [oscillatorSpectralPhase] using
    spectralAmplitude_probability_preserved (oscillatorEnergyReal ℏ ω n) ℏ t c

/-- A finite oscillator spectral packet preserves the total Born weight by the
shared finite pure-point spectral-evolution theorem. -/
lemma oscillatorFiniteSpectralEvolution_total_probability
    (N : ℕ) (ℏ ω t : ℝ) (c : Fin N → ℂ) :
    (∑ i, ‖finiteSpectralEvolution
      (fun j : Fin N => oscillatorEnergyReal ℏ ω (j : ℕ)) ℏ t c i‖ ^ 2)
      = ∑ i, ‖c i‖ ^ 2 := by
  simpa using
    finiteSpectralEvolution_total_probability
      (fun j : Fin N => oscillatorEnergyReal ℏ ω (j : ℕ)) ℏ t c

/-! ## B.1. One-dimensional QHO spectral lines and response filters -/

/-- The QHO energy line supplied by the existing one-dimensional harmonic
oscillator TISE API. -/
def qhoEigenSpectrum
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (n : ℕ) : ℝ :=
  Q.eigenValue n

/-- The QHO TISE eigenvalue is the real Nagao-Nielsen oscillator-energy line. -/
lemma qhoEigenSpectrum_eq_oscillatorEnergyReal
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (n : ℕ) :
    qhoEigenSpectrum Q n = oscillatorEnergyReal (Constants.ℏ : ℝ) Q.ω n := by
  simp [qhoEigenSpectrum, QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue,
    oscillatorEnergyReal]
  ring

/-- The QHO spectral spacing is `hbar * omega`, reusing the TISE spacing lemma. -/
lemma qhoEigenSpectrum_succ_sub
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (n : ℕ) :
    qhoEigenSpectrum Q (n + 1) - qhoEigenSpectrum Q n =
      (Constants.ℏ : ℝ) * Q.ω := by
  simpa [qhoEigenSpectrum] using Q.eigenValue_succ_sub n

/-- The QHO spectral phase attached to the `n`-th energy line. -/
def qhoSpectralPhase
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (n : ℕ) (t : ℝ) : ℂ :=
  spectralPhase (qhoEigenSpectrum Q n) (Constants.ℏ : ℝ) t

/-- QHO spectral phases have unit norm. -/
lemma qhoSpectralPhase_norm
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (n : ℕ) (t : ℝ) :
    ‖qhoSpectralPhase Q n t‖ = 1 := by
  simpa [qhoSpectralPhase] using
    spectralPhase_norm (qhoEigenSpectrum Q n) (Constants.ℏ : ℝ) t

/-- QHO spectral phases preserve scalar Born weights. -/
lemma qhoSpectralPhase_probability_preserved
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (n : ℕ) (t : ℝ)
    (c : ℂ) :
    ‖qhoSpectralPhase Q n t * c‖ ^ 2 = ‖c‖ ^ 2 := by
  simpa [qhoSpectralPhase] using
    spectralAmplitude_probability_preserved
      (qhoEigenSpectrum Q n) (Constants.ℏ : ℝ) t c

/-- A finite QHO spectral packet preserves total Born weight. -/
lemma qhoFiniteSpectralEvolution_total_probability
    (N : ℕ) (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (t : ℝ) (c : Fin N → ℂ) :
    (∑ i, ‖finiteSpectralEvolution
      (fun j : Fin N => qhoEigenSpectrum Q (j : ℕ)) (Constants.ℏ : ℝ) t c i‖ ^ 2)
      = ∑ i, ‖c i‖ ^ 2 := by
  simpa using
    finiteSpectralEvolution_total_probability
      (fun j : Fin N => qhoEigenSpectrum Q (j : ℕ)) (Constants.ℏ : ℝ) t c

/-- The driven QHO linear-response denominator
`m * (omega0^2 - omega^2) + i gamma omega`. -/
def qhoResponseDenominator
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (gamma driveOmega : ℝ) : ℂ :=
  ((Q.m * (Q.ω ^ 2 - driveOmega ^ 2) : ℝ) : ℂ)
    + ((gamma * driveOmega : ℝ) : ℂ) * Complex.I

/-- The QHO linear-response transfer function. -/
def qhoResponseTransfer
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (gamma driveOmega : ℝ) : ℂ :=
  (qhoResponseDenominator Q gamma driveOmega)⁻¹

/-- White-noise output spectrum of the QHO linear-response filter. -/
def qhoNoiseSpectrum
    (sigma2 : ℝ) (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (gamma driveOmega : ℝ) : ℝ :=
  whiteNoiseOutputSpectrum sigma2 (qhoResponseTransfer Q gamma driveOmega)

/-- The QHO response spectrum is white-noise power times transfer power. -/
lemma qhoNoiseSpectrum_eq_whiteNoise_mul_transfer
    (sigma2 : ℝ) (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (gamma driveOmega : ℝ) :
    qhoNoiseSpectrum sigma2 Q gamma driveOmega =
      whiteNoiseSpectrum sigma2 * Complex.normSq
        (qhoResponseTransfer Q gamma driveOmega) := by
  rfl

/-- The QHO response spectrum is nonnegative for nonnegative input variance. -/
lemma qhoNoiseSpectrum_nonneg
    {sigma2 : ℝ} (hsigma : 0 ≤ sigma2)
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator)
    (gamma driveOmega : ℝ) :
    0 ≤ qhoNoiseSpectrum sigma2 Q gamma driveOmega := by
  exact whiteNoiseOutputSpectrum_nonneg hsigma
    (qhoResponseTransfer Q gamma driveOmega)

/-- At QHO resonance, the real part of the response denominator vanishes. -/
lemma qhoResponseDenominator_re_at_resonance
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (gamma : ℝ) :
    (qhoResponseDenominator Q gamma Q.ω).re = 0 := by
  simp [qhoResponseDenominator]

/-- At QHO resonance, the response denominator is purely imaginary. -/
lemma qhoResponseDenominator_at_resonance
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (gamma : ℝ) :
    qhoResponseDenominator Q gamma Q.ω =
      ((gamma * Q.ω : ℝ) : ℂ) * Complex.I := by
  simp [qhoResponseDenominator]

/-- The IQHO line obtained by Wick-rotating a QHO energy line:
`E_IQHO,n = -i E_QHO,n`. -/
def iqhoWickRotatedEigenValue
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (n : ℕ) : ℂ :=
  -Complex.I * (qhoEigenSpectrum Q n : ℂ)

/-- The IQHO Wick-rotated line is the complex oscillator energy at
`omega -> -i omega`. -/
lemma iqhoWickRotatedEigenValue_eq_oscillatorEnergy
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (n : ℕ) :
    iqhoWickRotatedEigenValue Q n =
      oscillatorEnergy (Constants.ℏ : ℝ) (-Complex.I * (Q.ω : ℂ)) n := by
  simp [iqhoWickRotatedEigenValue, qhoEigenSpectrum,
    QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue,
    oscillatorEnergy]
  ring

/-- IQHO Wick-rotated lines are purely imaginary. -/
@[simp] lemma iqhoWickRotatedEigenValue_re
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (n : ℕ) :
    (iqhoWickRotatedEigenValue Q n).re = 0 := by
  simp [iqhoWickRotatedEigenValue]

/-- The imaginary part of an IQHO Wick-rotated line is minus the QHO energy. -/
@[simp] lemma iqhoWickRotatedEigenValue_im
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (n : ℕ) :
    (iqhoWickRotatedEigenValue Q n).im = -qhoEigenSpectrum Q n := by
  simp [iqhoWickRotatedEigenValue]

/-- The IQHO Wick-rotated spacing is `-i hbar omega`. -/
lemma iqhoWickRotatedEigenValue_succ_sub
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) (n : ℕ) :
    iqhoWickRotatedEigenValue Q (n + 1) - iqhoWickRotatedEigenValue Q n =
      -Complex.I * (((Constants.ℏ : ℝ) * Q.ω : ℝ) : ℂ) := by
  have h : ((qhoEigenSpectrum Q (n + 1) : ℝ) : ℂ)
      - (qhoEigenSpectrum Q n : ℂ) =
      (((Constants.ℏ : ℝ) * Q.ω : ℝ) : ℂ) := by
    exact_mod_cast qhoEigenSpectrum_succ_sub Q n
  unfold iqhoWickRotatedEigenValue
  rw [← mul_sub, h]

/-- **Bosonic inertia from frequency**: the n-th oscillator quantum carries positive
inertial mass `ℏ ω (n + ½)/c² > 0` (via `E = m_inert c²`) **even with zero rest mass** — a
massless boson is inertial because it oscillates. -/
lemma quantum_inertialMass_pos (ℏ ω c : ℝ) (hℏ : 0 < ℏ) (hω : 0 < ω) (hc : 0 < c) (n : ℕ) :
    0 < relativisticInertialMass (oscillatorEnergyReal ℏ ω n) c := by
  apply relativisticInertialMass_pos _ c _ hc
  unfold oscillatorEnergyReal
  positivity

/-- **The quantum inertial mass explicitly** `m_inert,n = ℏ ω (n + ½)/c²`. -/
lemma quantum_inertialMass_eq (ℏ ω c : ℝ) (n : ℕ) :
    relativisticInertialMass (oscillatorEnergyReal ℏ ω n) c = ℏ * ω * (n + 1 / 2) / c ^ 2 := by
  unfold relativisticInertialMass oscillatorEnergyReal
  rfl

/-! ## The maximization principle: survival overlap selects the least-decaying mode (§6)

The **maximization principle** of the future-included theory (Nagao–Nielsen 2019, PTEP 073B01,
§6; *Reality from maximizing overlap*, arXiv:2203.07795) selects the past/future states
`|A⟩, |B⟩` that maximize the transition overlap `|⟨B|A⟩|`.  Its algebraic core: a stationary
mode of complex energy `E` develops with survival amplitude `e^{−iEt/ℏ}`, whose **modulus is
`e^{(Im E)·t/ℏ}`**, so for `t > 0` maximizing the survival overlap is exactly maximizing
`Im E` — selecting the **least-decaying** mode (`PeriodicQHermitian.Basic` flags this
maximization step as not formalized there).  For the oscillator `E_n = ℏω(n+½)` with `Im ω > 0`
the higher level always survives more, so the principle picks the **utmost-energy** level (no
true ground state, §6): the surviving mode is the one that has undergone the least entropic
(imaginary-action) damping over the period. -/

/-- **The survival modulus** `|e^{−iEt/ℏ}| = e^{(Im E)·t/ℏ}` of a stationary mode of complex
energy `E`: the imaginary energy sets the (entropic) decay/growth of the overlap. -/
noncomputable def survivalModulus (ℏ : ℝ) (E : ℂ) (t : ℝ) : ℝ := Real.exp (E.im * t / ℏ)

/-- **The survival modulus is the norm of the survival amplitude** `e^{−iEt/ℏ}` — its magnitude
depends only on the imaginary part of the energy. -/
theorem survivalModulus_eq_norm (ℏ : ℝ) (E : ℂ) (t : ℝ) :
    ‖Complex.exp (-Complex.I * E * ((t / ℏ : ℝ) : ℂ))‖ = survivalModulus ℏ E t := by
  rw [Complex.norm_exp, survivalModulus]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Maximizing the overlap ⟺ maximizing `Im E`** — for `t, ℏ > 0`, one survival modulus
dominates another exactly when its imaginary energy is larger: the maximization principle
selects the mode of maximal `Im E`, the least-decaying (least entropically-damped) one. -/
theorem survivalModulus_le_iff (ℏ t : ℝ) (E₁ E₂ : ℂ) (hℏ : 0 < ℏ) (ht : 0 < t) :
    survivalModulus ℏ E₁ t ≤ survivalModulus ℏ E₂ t ↔ E₁.im ≤ E₂.im := by
  unfold survivalModulus
  rw [Real.exp_le_exp, mul_div_assoc, mul_div_assoc]
  have hc : 0 < t / ℏ := div_pos ht hℏ
  constructor
  · intro h; exact le_of_mul_le_mul_right h hc
  · intro h; exact mul_le_mul_of_nonneg_right h hc.le

/-- **The oscillator level's imaginary energy** `Im E_n = ℏ(n+½)·Im ω` — the entropic decay
rate of the `n`-th complex-oscillator level. -/
theorem oscillatorEnergy_im (ℏ : ℝ) (ω : ℂ) (n : ℕ) :
    (oscillatorEnergy ℏ ω n).im = ℏ * ((n : ℝ) + 1 / 2) * ω.im := by
  have h : oscillatorEnergy ℏ ω n = ((ℏ * ((n : ℝ) + 1 / 2) : ℝ) : ℂ) * ω := by
    unfold oscillatorEnergy; push_cast; ring
  rw [h]
  simp [Complex.mul_im]

/-- **The maximization principle picks the utmost-energy level** (Nagao–Nielsen 2019 §6) — for
`Im ω > 0` the survival modulus increases with the level `n`, so higher levels dominate the
overlap: the "ground" state is the utmost-energy one and there is no true ground state (that
requires real positive `ω`). -/
theorem oscillator_survival_utmost (ℏ t : ℝ) (ω : ℂ) (hℏ : 0 < ℏ) (ht : 0 < t)
    (hω : 0 < ω.im) {n m : ℕ} (hnm : n ≤ m) :
    survivalModulus ℏ (oscillatorEnergy ℏ ω n) t ≤ survivalModulus ℏ (oscillatorEnergy ℏ ω m) t := by
  rw [survivalModulus_le_iff ℏ t _ _ hℏ ht, oscillatorEnergy_im, oscillatorEnergy_im]
  have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by linarith) hℏ.le) hω.le

/-- **The ratio of two survival moduli is a single exponential** in the imaginary-energy gap:
`e^{(Im E₁ − Im E₂)·t/ℏ}`. -/
theorem survivalModulus_ratio (ℏ : ℝ) (E₁ E₂ : ℂ) (t : ℝ) :
    survivalModulus ℏ E₁ t / survivalModulus ℏ E₂ t = Real.exp ((E₁.im - E₂.im) * t / ℏ) := by
  unfold survivalModulus
  rw [← Real.exp_sub]
  congr 1
  ring

/-- **A sub-dominant mode is suppressed at every period** — for `Im E₁ < Im E₂` and `t, ℏ > 0`
its survival modulus is strictly smaller, `‖amp₁‖/‖amp₂‖ < 1`: the less-imaginary mode always
weighs less in the overlap. -/
theorem survivalModulus_ratio_lt_one (ℏ : ℝ) (E₁ E₂ : ℂ) (t : ℝ) (hℏ : 0 < ℏ) (ht : 0 < t)
    (h : E₁.im < E₂.im) :
    survivalModulus ℏ E₁ t / survivalModulus ℏ E₂ t < 1 := by
  rw [survivalModulus_ratio, Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) ht) hℏ

/-- **Asymptotic dominance** (the analytic core of Nagao–Nielsen Theorem 1, arXiv:2203.07795):
as the period `t → ∞`, the relative weight of any sub-dominant mode (`Im E₁ < Im E₂`) tends to
`0` — only the modes of maximal imaginary part (the subset `A`) survive the maximization, which
is what reduces the periodic-time expectation to the dominant-subset sum (Eq. 8). -/
theorem survivalModulus_ratio_tendsto_zero (ℏ : ℝ) (E₁ E₂ : ℂ) (hℏ : 0 < ℏ)
    (h : E₁.im < E₂.im) :
    Filter.Tendsto (fun t => survivalModulus ℏ E₁ t / survivalModulus ℏ E₂ t)
      Filter.atTop (nhds 0) := by
  have hslope : (E₁.im - E₂.im) / ℏ < 0 := div_neg_of_neg_of_pos (by linarith) hℏ
  have heq : (fun t => survivalModulus ℏ E₁ t / survivalModulus ℏ E₂ t)
      = fun t => Real.exp ((E₁.im - E₂.im) / ℏ * t) := by
    funext t
    rw [survivalModulus_ratio]
    congr 1
    ring
  rw [heq]
  exact Real.tendsto_exp_atBot.comp
    ((Filter.tendsto_const_mul_atBot_of_neg hslope).mpr Filter.tendsto_id)

/-! ## The survival modulus is the entropic-damping weight (link to Caticha ED, Fokker–Planck, Hadamard)

The survival modulus that the maximization principle maximizes is the **entropic-damping weight**
`e^{−S_I/ℏ}` with accumulated imaginary (entropic) action `S_I = −(Im E)·t` — the modulus
`|e^{iS/ℏ}|` of the complex-action weight (`S = S_R + i S_I`), i.e. exactly
`PathIntegral.ComplexActionPathIntegralWeight.kuikenWeight ℏ (imaginaryAction E t)`.  This single
form unifies the entropic-time arc (stated here without the upstream import, which would cycle):

* **Caticha entropic dynamics.** The Ipek–Caticha transition weight
  `EntropicTime.EntropicDynamicsTransitionProbability.edTransitionWeight = e^{−(entropic action)}`
  has the *same* `e^{−S_I/ℏ}` shape; maximizing the NN survival overlap (least imaginary-action
  damping, `survivalModulus_le_iff`) is the complex-action face of maximizing the ED transition
  probability (least entropic action).
* **Fokker–Planck.** At the reversible point `S_I = 0` the damping is `1`, and the dynamics reduce
  to the conservative continuity equation of the local-time Fokker–Planck ensemble Hamiltonian
  (`EntropicTime.EntropicDynamicsFokkerPlanckHamiltonian`, Ipek–Abedi–Caticha) — the same conserved
  probability current as the future-included Ehrenfest theorem
  (`PeriodicQHermitian.Ehrenfest.probability_conserved`).
* **Hadamard.** The imaginary energy `Im E` that sets the damping is the vacuum two-point /
  causal-Green data of the quasifree Hadamard net (`AlgebraicQFTQuasifree.HadamardTypeIIIAQFT`,
  `SorkinJohnstonCausalGreen`): the entropic-time arrow read off the same complex analytic structure. -/

/-- **The accumulated imaginary (entropic) action** `S_I = −(Im E)·t` of a stationary mode of
complex energy `E` over time `t` — non-negative (net damping) exactly for a decaying mode
`Im E ≤ 0`. -/
def imaginaryAction (E : ℂ) (t : ℝ) : ℝ := -(E.im * t)

/-- **The survival modulus is the entropic-damping weight** — `survivalModulus ℏ E t =
e^{−S_I/ℏ}` with `S_I = imaginaryAction E t`: the `|e^{iS/ℏ}| = e^{−S_I/ℏ}` face, identical in
shape to `kuikenWeight ℏ (imaginaryAction E t)`, the Caldeira–Leggett decoherence weight, and the
Caticha ED transition weight.  Maximizing the survival overlap is minimizing `S_I`. -/
theorem survivalModulus_eq_entropicDamping (ℏ : ℝ) (E : ℂ) (t : ℝ) :
    survivalModulus ℏ E t = Real.exp (-(imaginaryAction E t) / ℏ) := by
  unfold survivalModulus imaginaryAction
  congr 1
  ring

end Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson

end

end
