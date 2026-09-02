/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockMatsubaraZeta
public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour

/-!
# The Nagao–Nielsen complex oscillator and contour as the analytic continuation of the ζ-regularized Fock vacuum

The thermal Fock oscillator's ζ-regularized vacuum energy (`SciamaFockMatsubaraZeta`,
`Σₙ (ω(n+½))^{−s} = ω^{−s} ζ(s,½)`) sits at the real point of the **Nagao–Nielsen complex oscillator**
(`ComplexOscillator.ComplexHarmonicOscillatorBoson`, `Dunkl.NagaoNielsenOscillator`), whose frequency
`ω = |ω|e^{iθ}` is analytically continued onto the **convergence contour** of `ComplexDelta.Contour`.  This
module ties the three together:

* `oscillatorEnergyReal_spectralZeta_eq_hurwitz` — the NN oscillator's real energy `oscillatorEnergyReal ℏ ω n
  = ℏω(n+½)` has spectral zeta `(ℏω)^{−s} ζ(s,½)`: the Fock ζ-regularization *is* the NN oscillator's, read off
  `ComplexHarmonicOscillatorBoson.oscillatorEnergyReal`.
* `dunkl_spectralZeta_eq_hurwitz` — the **Wigner–Dunkl / Nagao–Nielsen deformation** `ν` shifts the Hurwitz
  parameter: the deformed spectrum `ℏω(n+ν+½)` (the real `dunklOscillatorEnergy`) has spectral zeta
  `(ℏω)^{−s} ζ(s, ν+½)`.  At `ν = 0` (`dunkl_spectralZeta_zero_param`) it collapses to the canonical Fock
  oscillator (`Dunkl.NagaoNielsenOscillator.dunklOscE_zero_param`); the reflection parameter `ν` moves the
  zero-point along the Hurwitz-zeta `a`-line.
* `nagaoNielsen_contour_real_permitted` — the real oscillator is the `θ = 0` centre of the NN contour:
  `L(e^{i·0}) = cos 0 = 1 > 0`, deep in the permitted cone `|θ| < π/4` (`cos 2θ > 0`,
  `ComplexDelta.Contour.lorentzianForm_rayDir`) where the rotated complex Gaussian still converges.

So the ζ-regularized thermal Fock oscillator, the Nagao–Nielsen complex oscillator, its Wigner–Dunkl
deformation, and the convergence contour are one object: the Fock zero-point energy analytically continued in
the complex frequency `ω = |ω|e^{iθ}`, regularized by the Hurwitz zeta `ζ(s, ν+½)` and convergent on the
timelike cone `cos 2θ > 0` around the real axis where the physical thermal state lives.

Honest scope: the real-spectrum spectral-zeta identities (Fock `a = ½`, Dunkl `a = ν+½`) and the real-axis
permittedness of the NN contour.  The full complex-`ω` analytic continuation of `spectralZeta` and the contour
deformation of the path integral are contextualized, not carried out here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockNagaoNielsenZeta

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HurwitzZetaRegularization
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour

/-- **[Linear-spectrum ζ-regularization] `Σₙ (c(n+a))^{−s} = c^{−s} ζ(s, a)`.**  The spectral zeta of any
uniformly-spaced tower `c(n+a)` factorizes into the scale `c^{−s}` and the Hurwitz zeta at the ground offset
`a`. -/
theorem linear_spectralZeta_eq_hurwitz (c a s : ℝ) (hc : 0 < c) (ha : 0 ≤ a) :
    spectralZeta (fun n => c * ((n : ℝ) + a)) s = c ^ (-s) * hurwitzZetaSeries s a := by
  rw [← spectralZeta_linear_eq_hurwitz a s ha, spectralZeta, spectralZeta, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [Real.mul_rpow hc.le (add_nonneg (Nat.cast_nonneg n) ha)]

/-- **[NN oscillator vacuum ζ] `Σₙ (ℏω(n+½))^{−s} = (ℏω)^{−s} ζ(s, ½)`.**  The Fock ζ-regularization read off the
Nagao–Nielsen complex oscillator's real energy `ComplexHarmonicOscillatorBoson.oscillatorEnergyReal`. -/
theorem oscillatorEnergyReal_spectralZeta_eq_hurwitz (ℏ ω s : ℝ) (hℏ : 0 < ℏ) (hω : 0 < ω) :
    spectralZeta (fun n => oscillatorEnergyReal ℏ ω n) s
      = (ℏ * ω) ^ (-s) * hurwitzZetaSeries s (1 / 2) := by
  have hf : (fun n => oscillatorEnergyReal ℏ ω n) = (fun n : ℕ => (ℏ * ω) * ((n : ℝ) + 1 / 2)) := by
    funext n; rw [oscillatorEnergyReal]
  rw [hf]
  exact linear_spectralZeta_eq_hurwitz (ℏ * ω) (1 / 2) s (mul_pos hℏ hω) (by norm_num)

/-- **[Wigner–Dunkl deformation shifts the Hurwitz parameter] `Σₙ (ℏω(n+ν+½))^{−s} = (ℏω)^{−s} ζ(s, ν+½)`.**
The Nagao–Nielsen / Wigner–Dunkl reflection parameter `ν` moves the zero-point offset from `½` to `ν+½`, so the
ζ-regularized vacuum is the Hurwitz zeta at `a = ν+½` (the real `dunklOscillatorEnergy ℏ ω ν n = ℏω(n+ν+½)`). -/
theorem dunkl_spectralZeta_eq_hurwitz (ℏ ω ν s : ℝ) (hℏ : 0 < ℏ) (hω : 0 < ω) (hν : 0 ≤ ν) :
    spectralZeta (fun n => ℏ * ω * ((n : ℝ) + ν + 1 / 2)) s
      = (ℏ * ω) ^ (-s) * hurwitzZetaSeries s (ν + 1 / 2) := by
  have hf : (fun n : ℕ => ℏ * ω * ((n : ℝ) + ν + 1 / 2))
      = (fun n : ℕ => (ℏ * ω) * ((n : ℝ) + (ν + 1 / 2))) := by funext n; ring
  rw [hf]
  exact linear_spectralZeta_eq_hurwitz (ℏ * ω) (ν + 1 / 2) s (mul_pos hℏ hω) (by linarith)

/-- **[Dunkl `ν = 0` is the Fock oscillator] the deformed vacuum ζ collapses to the canonical one at `ν = 0`.**
Mirrors `Dunkl.NagaoNielsenOscillator.dunklOscE_zero_param` at the spectral-zeta level. -/
theorem dunkl_spectralZeta_zero_param (ℏ ω s : ℝ) (hℏ : 0 < ℏ) (hω : 0 < ω) :
    spectralZeta (fun n => ℏ * ω * ((n : ℝ) + 0 + 1 / 2)) s
      = spectralZeta (fun n => oscillatorEnergyReal ℏ ω n) s := by
  rw [dunkl_spectralZeta_eq_hurwitz ℏ ω 0 s hℏ hω le_rfl,
    oscillatorEnergyReal_spectralZeta_eq_hurwitz ℏ ω s hℏ hω]
  norm_num

/-- **[Real oscillator = NN contour centre] `L(e^{i·0}) = 1 > 0`.**  The real (physical, thermal) oscillator is
the `θ = 0` ray, at the centre of the Nagao–Nielsen convergence cone `cos 2θ > 0` (`|θ| < π/4`) where the
rotated complex Gaussian converges. -/
theorem nagaoNielsen_contour_real_permitted :
    0 < lorentzianForm (Complex.exp ((0 : ℝ) * Complex.I)) := by
  rw [lorentzianForm_rayDir, mul_zero, Real.cos_zero]
  norm_num

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockNagaoNielsenZeta

end
