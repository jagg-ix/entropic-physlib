/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Clock.Phase
public import Physlib.QuantumMechanics.OneDimension.HarmonicOscillator.TISE
public import Physlib.QuantumMechanics.Schrodinger.SpectralDynamics

/-!
# Quantum harmonic oscillator as a phase clock

Rather than redefine an oscillator, the metric clock layer **wraps** Physlib's
1D quantum harmonic oscillator `QuantumMechanics.OneDimension.HarmonicOscillator`:
its proper angular frequency `ω` supplies a `PhaseClock`, and its energy
eigenvalues supply stationary quantum phase rates `E_n/ℏ = (n + 1/2)·ω`.

-/

@[expose] public section

noncomputable section


open Physlib.QuantumMechanics.Clock.Phase
namespace QuantumMechanics.OneDimension.HarmonicOscillator

open Constants
open Physlib.QuantumMechanics.Schrodinger.SpectralDynamics

/-- Stationary-state **phase rate** of the `n`-th energy eigenstate:
`E_n / ℏ`, the rate at which `exp(-i E_n τ / ℏ)` accumulates phase. -/
noncomputable def eigenPhaseRate (Q : HarmonicOscillator) (n : ℕ) : ℝ :=
  Q.eigenValue n / ℏ

/-- The eigenstate phase rate is `(n + 1/2)·ω`. -/
theorem eigenPhaseRate_eq (Q : HarmonicOscillator) (n : ℕ) :
    Q.eigenPhaseRate n = (n + 1 / 2) * Q.ω := by
  unfold eigenPhaseRate eigenValue
  field_simp [ℏ_ne_zero]

/-! ## Spectral-dynamics link -/

/-- The stationary phase factor of the `n`-th oscillator eigenstate, expressed
through the shared Facchi spectral-dynamics phase. -/
noncomputable def eigenSpectralPhase (Q : HarmonicOscillator) (n : ℕ) (t : ℝ) : ℂ :=
  spectralPhase (Q.eigenValue n) ℏ t

@[simp] theorem eigenSpectralPhase_zero (Q : HarmonicOscillator) (n : ℕ) :
    Q.eigenSpectralPhase n 0 = 1 := by
  simp [eigenSpectralPhase]

/-- Oscillator eigenstate phases compose by the spectral one-parameter group law. -/
theorem eigenSpectralPhase_add (Q : HarmonicOscillator) (n : ℕ) (s t : ℝ) :
    Q.eigenSpectralPhase n (s + t) =
      Q.eigenSpectralPhase n s * Q.eigenSpectralPhase n t := by
  simpa [eigenSpectralPhase] using spectralPhase_add (Q.eigenValue n) ℏ s t

/-- The oscillator eigenstate phase has unit norm, by the shared spectral
phase theorem. -/
theorem eigenSpectralPhase_norm (Q : HarmonicOscillator) (n : ℕ) (t : ℝ) :
    ‖Q.eigenSpectralPhase n t‖ = 1 := by
  simpa [eigenSpectralPhase] using spectralPhase_norm (Q.eigenValue n) ℏ t

/-- Multiplication by the oscillator eigenstate phase preserves Born weight. -/
theorem eigenSpectralPhase_probability_preserved
    (Q : HarmonicOscillator) (n : ℕ) (t : ℝ) (c : ℂ) :
    ‖Q.eigenSpectralPhase n t * c‖ ^ 2 = ‖c‖ ^ 2 := by
  simpa [eigenSpectralPhase] using
    spectralAmplitude_probability_preserved (Q.eigenValue n) ℏ t c

end QuantumMechanics.OneDimension.HarmonicOscillator

namespace QuantumMechanics.OneDimension.HarmonicOscillator

/-- Physlib's 1D quantum harmonic oscillator becomes a `PhaseClock` via its
proper angular frequency `ω`. -/
def PhaseClock.ofQuantumHarmonicOscillator
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) : PhaseClock where
  omega0 := Q.ω
  omega0_pos := Q.hω

@[simp] theorem PhaseClock.ofQuantumHarmonicOscillator_omega0
    (Q : QuantumMechanics.OneDimension.HarmonicOscillator) :
    (PhaseClock.ofQuantumHarmonicOscillator Q).omega0 = Q.ω := rfl

end QuantumMechanics.OneDimension.HarmonicOscillator

end
