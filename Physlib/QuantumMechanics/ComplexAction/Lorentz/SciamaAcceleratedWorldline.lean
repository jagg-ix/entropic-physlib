/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondLorentzianEntropicClock

/-!
# The Sciama accelerated detector worldline is the diamond mode

Sciama–Candelas–Deutsch (1981), Eq. (2): the uniformly accelerated detector's space–time path is

`x = α⁻¹ cosh τ,  t = α⁻¹ sinh τ`   (α = constant proper acceleration, α⁻¹τ = proper time).

This is exactly the diamond energy–momentum `diamondMomentum τ = (cosh τ, sinh τ)`
(`DiamondLorentzianEntropicClock`) scaled by `α⁻¹`: the detector's worldline **is** the boost orbit on the
mass-shell hyperbola.  This grounds the whole Sciama/Unruh detector arc — the redshift, the Unruh
temperature, the KMS period — in the diamond geometry, rather than merely asserting "the detector is at
rapidity θ."

* `sciamaWorldline` — the accelerated path `α⁻¹·diamondMomentum τ` (`.re = x`, `.im = t`).
* `sciamaWorldline_re`, `sciamaWorldline_im` — `x = α⁻¹ cosh τ`, `t = α⁻¹ sinh τ`.
* `lorentzianForm_ofReal_mul` — `L(c·q) = c²·L(q)` (the Lorentzian form is real-quadratic-homogeneous).
* `sciamaWorldline_massShell` — `x² − t² = α⁻²`: the worldline is the mass-shell hyperbola of proper
  acceleration `α` (its Lorentzian invariant is the squared inverse acceleration).

Honest scope: the algebraic identification of the accelerated worldline with the diamond mode and its
mass-shell invariant; the detector response is elsewhere in the Sciama arc.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAcceleratedWorldline

open Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondLorentzianEntropicClock
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

/-- **The Sciama uniformly-accelerated detector worldline** `α⁻¹·diamondMomentum τ` — real part the spatial
position `x = α⁻¹ cosh τ`, imaginary part the time `t = α⁻¹ sinh τ` (Eq. 2). -/
def sciamaWorldline (α τ : ℝ) : ℂ := (α⁻¹ : ℂ) * diamondMomentum τ

/-- **The spatial position** `x = α⁻¹ cosh τ`. -/
@[simp] theorem sciamaWorldline_re (α τ : ℝ) : (sciamaWorldline α τ).re = α⁻¹ * Real.cosh τ := by
  simp [sciamaWorldline, Complex.mul_re]

/-- **The time coordinate** `t = α⁻¹ sinh τ`. -/
@[simp] theorem sciamaWorldline_im (α τ : ℝ) : (sciamaWorldline α τ).im = α⁻¹ * Real.sinh τ := by
  simp [sciamaWorldline, Complex.mul_im]

/-- **The Lorentzian form is real-quadratic-homogeneous** `L(c·q) = c²·L(q)`. -/
theorem lorentzianForm_ofReal_mul (c : ℝ) (q : ℂ) :
    lorentzianForm ((c : ℂ) * q) = c ^ 2 * lorentzianForm q := by
  unfold lorentzianForm
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- **[Worldline mass shell] `x² − t² = α⁻²`.**  The accelerated worldline lies on the mass-shell hyperbola
of proper acceleration `α` — its Lorentzian invariant is `α⁻²`, the diamond mass shell (`= 1`) scaled by the
inverse acceleration. -/
theorem sciamaWorldline_massShell (α τ : ℝ) :
    lorentzianForm (sciamaWorldline α τ) = (α⁻¹) ^ 2 := by
  unfold lorentzianForm
  simp only [sciamaWorldline_re, sciamaWorldline_im]
  nlinarith [Real.cosh_sq_sub_sinh_sq τ]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAcceleratedWorldline

end
