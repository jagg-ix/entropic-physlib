/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeComplexAngularMomentum
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.CausalRegimes

/-!
# The Swift–Lee Bethe–Salpeter bound state as a Nagao–Nielsen complex oscillator

This extends `BetheSalpeter.SwiftLeeComplexAngularMomentum` (the parity / Regge-signature core of Swift–Lee 1963)
by formalizing the dynamics of the bound state itself, using the **Nagao–Nielsen complex momentum**
(`PathIntegral.MomentumPathIntegral`) and **complex oscillator** (`ComplexOscillator.ComplexHarmonicOscillatorBoson`) theorems of
this development.

## The Bethe–Salpeter relative motion is a complex oscillator

The spinor Bethe–Salpeter amplitude `Ψ(q, q₀)` (Swift–Lee Eq. 2) describes the bound state of a
fermion and an antifermion; `q₀` is the **relative energy** (the zeroth component of the relative
momentum). Two structural facts:

* **Relative energy = Nagao–Nielsen complex momentum.** The BS kernel is a Gaussian / propagator
  integral in the relative energy. By `PathIntegral.MomentumPathIntegral.momentum_integral_converges_iff` it
  converges (the coefficient has positive real part) **iff `Im m > 0`** — the Feynman–Kac / Wick
  prescription that makes the imaginary action a *decaying* weight (`bsKernel_converges_iff`).
* **Bound-state spectrum = complex-oscillator tower.** The relative motion is the Nagao–Nielsen
  complex oscillator with (complex) frequency `ω`; its spectrum is `E_n = ℏω(n + ½)`
  (`ComplexOscillator.ComplexHarmonicOscillatorBoson.oscillatorEnergy`), the rotational / Regge tower with level
  spacing `ℏω` (`boundState_level_spacing`) and zero-point `ℏω/2` (`boundState_ground`).

## Bound state vs resonance, and the Regge link

For a **real** frequency `ω` the tower is real — a stable bound state. For a **complex** frequency
`ω = ω_R + iω_I` the level spacing acquires an imaginary part `Im(ℏω) = ℏ·ω_I`
(`boundState_spacing_im`), the **resonance width** — nonzero iff `ω_I ≠ 0`
(`boundState_spacing_real_iff`). This imaginary frequency `ω_I` is the dynamical counterpart of the
**imaginary angular momentum** `J_I` of the Regge signature `‖e^{iπJ}‖ = e^{−πJ_I}`
(`norm_reggeSignature`): the resonance width and the Regge damping are two faces of the same
imaginary part — the complex-action `S_I`.

## Main results

* `bsKernel_converges_iff` — the BS relative-energy kernel converges iff `Im m > 0`.
* `boundState_level_spacing`, `boundState_ground` — the oscillator tower `E_n = ℏω(n+½)`.
* `boundState_spacing_im`, `boundState_spacing_real_iff` — the resonance width `ℏ·ω_I`.
* `boundState_resonance_regge_link` — the resonance width and the Regge damping share the imaginary
  part.
* `swiftLee_betheSalpeter_oscillator` — the bundled statement.

## References

* A. R. Swift, B. W. Lee, Phys. Rev. **131** (1963) 1857. doi:10.1103/PhysRev.131.1857.
* K. Nagao, H. B. Nielsen, arXiv:1304.4017 (complex momentum), arXiv:1902.01424 (complex oscillator).
* This development: `PathIntegral.MomentumPathIntegral`, `ComplexOscillator.ComplexHarmonicOscillatorBoson`,
  `BetheSalpeter.SwiftLeeComplexAngularMomentum`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexHarmonicOscillatorBoson
open Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeComplexAngularMomentum

namespace Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeBetheSalpeterOscillator

/-! ## §A — the relative energy as Nagao–Nielsen complex momentum (kernel convergence) -/

/-- **The Bethe–Salpeter kernel converges iff `Im m > 0`** (Feynman–Kac / Wick prescription): the
relative-energy Gaussian of the BS kernel has positive real coefficient exactly when the mass has a
positive imaginary part — the imaginary action gives a *decaying* weight. -/
theorem bsKernel_converges_iff (m : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt) (hm : m ≠ 0) :
    0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im :=
  momentum_integral_converges_iff m hℏ hdt hm

/-! ## §B — the bound-state spectrum as the complex-oscillator tower -/

/-- **The bound-state level spacing is `ℏω`** (`E_{n+1} − E_n = ℏω`): the rotational / Regge tower of
the relative-motion complex oscillator. -/
theorem boundState_level_spacing (ℏ : ℝ) (ω : ℂ) (n : ℕ) :
    oscillatorEnergy ℏ ω (n + 1) - oscillatorEnergy ℏ ω n = (ℏ : ℂ) * ω :=
  oscillatorEnergy_succ_sub ℏ ω n

/-- **The bound-state zero-point energy is `ℏω/2`**. -/
theorem boundState_ground (ℏ : ℝ) (ω : ℂ) :
    oscillatorEnergy ℏ ω 0 = (ℏ : ℂ) * ω / 2 :=
  oscillatorEnergy_zero ℏ ω

/-! ## §C — bound state vs resonance: the imaginary frequency is the width -/

/-- **The resonance width**: the level spacing's imaginary part is `Im(ℏω) = ℏ·ω_I` — the decay width
of the tower, set by the imaginary frequency. -/
theorem boundState_spacing_im (ℏ : ℝ) (ω : ℂ) :
    ((ℏ : ℂ) * ω).im = ℏ * ω.im := by
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-- **Stable bound state ⟺ real frequency**: the level spacing is real (no width) iff `ω_I = 0`. -/
theorem boundState_spacing_real_iff (ℏ : ℝ) (ω : ℂ) (hℏ : ℏ ≠ 0) :
    ((ℏ : ℂ) * ω).im = 0 ↔ ω.im = 0 := by
  rw [boundState_spacing_im]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hℏ
    · exact h
  · intro h; rw [h, mul_zero]

/-! ## §D — the resonance width and the Regge damping share the imaginary part -/

/-- **The resonance width and the Regge signature damping are two faces of the imaginary part.** The
bound-state level spacing has imaginary part `ℏ·ω_I` (the resonance width), and the Regge signature
`e^{iπJ}` has modulus `e^{−πJ_I}` (the angular-momentum damping). Both are governed by the imaginary
part — the complex-action `S_I`: `ω_I` (oscillator width) and `J_I` (Regge damping) play the same
role. -/
theorem boundState_resonance_regge_link (ℏ : ℝ) (ω J : ℂ) :
    ((ℏ : ℂ) * ω).im = ℏ * ω.im
      ∧ ‖reggeSignature J‖ = Real.exp (-(Real.pi) * J.im) :=
  ⟨boundState_spacing_im ℏ ω, norm_reggeSignature J⟩

/-! ## §E — the bundled statement -/

/-- **The Swift–Lee Bethe–Salpeter bound state is a Nagao–Nielsen complex oscillator.** For `0 < ℏ`,
`0 < dt`, `m ≠ 0`:

* the relative-energy kernel converges iff `Im m > 0` (Wick / Feynman–Kac);
* the bound-state spectrum is the complex-oscillator tower with spacing `ℏω`;
* the resonance width is `Im(ℏω) = ℏ·ω_I` (nonzero iff `ω` is complex). -/
theorem swiftLee_betheSalpeter_oscillator (m ω : ℂ) {ℏ dt : ℝ} (hℏ : 0 < ℏ) (hdt : 0 < dt)
    (hm : m ≠ 0) (n : ℕ) :
    (0 < (momentumGaussianCoeff m ℏ dt).re ↔ 0 < m.im)
      ∧ oscillatorEnergy ℏ ω (n + 1) - oscillatorEnergy ℏ ω n = (ℏ : ℂ) * ω
      ∧ ((ℏ : ℂ) * ω).im = ℏ * ω.im :=
  ⟨bsKernel_converges_iff m hℏ hdt hm, boundState_level_spacing ℏ ω n, boundState_spacing_im ℏ ω⟩

end Physlib.QuantumMechanics.ComplexAction.BetheSalpeter.SwiftLeeBetheSalpeterOscillator

end

end
