/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic

/-!
# Damped-oscillator entropy-production proxy

Reuses Physlib's damped harmonic oscillator as the classical analogue of the
non-Hermitian entropy-production layer. Its mechanical-energy dissipation rate
`γ‖ẋ‖²` is a nonnegative entropy-production proxy, and along a solution it
equals the negative energy-dissipation rate.

-/

@[expose] public section

noncomputable section


namespace Physlib.StatisticalMechanics.DampedEntropy

open ClassicalMechanics Real InnerProductSpace ContDiff Time
open scoped RealInnerProductSpace

/-- An entropy-production proxy for a damped harmonic oscillator: the
dissipation power `γ‖ẋ‖²`. -/
structure DampedOscillatorEntropyProxy
    (S : DampedHarmonicOscillator)
    (xₜ : Time → EuclideanSpace ℝ (Fin 1)) where
  /-- The entropy-production rate as a function of time. -/
  entropyRate : Time → ℝ
  /-- It is the damping dissipation power `γ‖ẋ‖²`. -/
  entropyRate_eq_dissipation :
    ∀ t, entropyRate t = S.γ * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ

namespace DampedOscillatorEntropyProxy

variable {S : DampedHarmonicOscillator} {xₜ : Time → EuclideanSpace ℝ (Fin 1)}

/-- The entropy-production proxy is nonnegative (`γ ≥ 0` and `⟪ẋ,ẋ⟫ ≥ 0`). -/
theorem entropyRate_nonneg (P : DampedOscillatorEntropyProxy S xₜ) (t : Time) :
    0 ≤ P.entropyRate t := by
  rw [P.entropyRate_eq_dissipation t]
  exact mul_nonneg S.γ_nonneg real_inner_self_nonneg

/-- Along a smooth solution, the entropy-production rate equals minus the
mechanical-energy dissipation rate: `entropyRate = −d/dt(energy)`. -/
theorem entropyRate_eq_neg_energy_dissipation
    (P : DampedOscillatorEntropyProxy S xₜ) (t : Time)
    (h1 : S.EquationOfMotion xₜ) (hx : ContDiff ℝ ∞ xₜ) :
    P.entropyRate t = -(∂ₜ (S.energy xₜ) t) := by
  rw [P.entropyRate_eq_dissipation t, S.energy_dissipation_rate xₜ t h1 hx]
  ring

end DampedOscillatorEntropyProxy

end Physlib.StatisticalMechanics.DampedEntropy

end
