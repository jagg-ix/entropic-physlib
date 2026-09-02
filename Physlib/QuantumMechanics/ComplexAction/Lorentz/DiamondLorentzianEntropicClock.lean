/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamondEntropicClock
public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

/-!
# The diamond entropic clock on the Lorentzian metric, not the Euclidean

The diamond-mode energy `E = cosh θ` came from the Euclidean combination `bogoliubovEnergy(sinh θ, 1) =
√(sinh²θ + 1)` (a sum of squares).  But the quantity actually preserved under the boost — and the one the
entropic Compton clock's invariant tick is read off — is the **Lorentzian** (Minkowski) form, not the
Euclidean modulus.

Packaging the diamond energy-momentum as the complex number `q = E + i p = cosh θ + i·sinh θ` (real part the
energy, imaginary part the momentum), the two metrics diverge:

* **Lorentzian** `lorentzianForm q = E² − p² = cosh²θ − sinh²θ = 1` — the boost-**invariant** rest mass²
  (`ComplexDelta.Convergence.lorentzianForm`, the Nagao–Nielsen convergence cone `p² − q²`).
* **Euclidean** `|q|² = E² + p² = cosh²θ + sinh²θ = cosh 2θ` — boost-**dependent**, growing with `θ`.

The entropic clock's **rest tick** is therefore Lorentz-invariant (set by `√(lorentzianForm q) = 1`, the
Minkowski rest mass), while its **time-dilation²** is read directly off the Lorentzian metric and equals the
BCJ double-copy dual:

`E²/lorentzianForm q = cosh²θ = γ² = 1/(1 − lorentzForceDual)`.

* `diamond_lorentzianForm_eq_restMassSq` — `lorentzianForm q = 1` (Lorentzian invariant).
* `diamond_euclideanNormSq_eq_cosh_two` — `|q|² = cosh 2θ` (Euclidean, boost-dependent).
* `diamond_lorentzian_le_euclidean` — `lorentzianForm q ≤ |q|²`.
* `diamond_restClock_lorentzInvariant` — the rest Compton tick is set by `√(lorentzianForm q)`, boost-free.
* `diamond_lorentzian_timeDilation_sq` — `E²/lorentzianForm q = 1/(1 − lorentzForceDual)`.

Honest scope: algebraic identities packaging the diamond kinematics on the Lorentzian form and linking its
time-dilation to `ForceBCJDiamondEntropicClock`; the Wick rotation Euclidean↔Lorentzian itself is not
constructed here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondLorentzianEntropicClock

open Matrix
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDiamondMassShell
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

/-- **The diamond energy-momentum** as a complex number `q = E + i p = cosh θ + i·sinh θ` — real part the
diamond horizon energy, imaginary part the diamond momentum. -/
def diamondMomentum (θ : ℝ) : ℂ := ⟨Real.cosh θ, Real.sinh θ⟩

@[simp] theorem diamondMomentum_re (θ : ℝ) : (diamondMomentum θ).re = Real.cosh θ := rfl
@[simp] theorem diamondMomentum_im (θ : ℝ) : (diamondMomentum θ).im = Real.sinh θ := rfl

/-- **[Lorentzian invariant] `lorentzianForm q = 1`.**  The Minkowski form `E² − p² = cosh²θ − sinh²θ = 1` is
the boost-invariant rest mass² of the diamond mode — the Nagao–Nielsen convergence cone value. -/
theorem diamond_lorentzianForm_eq_restMassSq (θ : ℝ) : lorentzianForm (diamondMomentum θ) = 1 := by
  unfold lorentzianForm
  rw [diamondMomentum_re, diamondMomentum_im]
  exact Real.cosh_sq_sub_sinh_sq θ

/-- **[Euclidean modulus] `|q|² = cosh 2θ`.**  The Euclidean form `E² + p² = cosh²θ + sinh²θ = cosh 2θ` is
boost-*dependent*, growing with the rapidity — unlike the Lorentzian invariant. -/
theorem diamond_euclideanNormSq_eq_cosh_two (θ : ℝ) :
    Complex.normSq (diamondMomentum θ) = Real.cosh (2 * θ) := by
  rw [Complex.normSq_apply, diamondMomentum_re, diamondMomentum_im, Real.cosh_two_mul]
  nlinarith [Real.cosh_sq_sub_sinh_sq θ]

/-- **[Lorentzian ≤ Euclidean] `lorentzianForm q ≤ |q|²`.**  The Minkowski invariant is bounded by the
boost-dependent Euclidean modulus, with equality only at rest (`θ = 0`, `p = 0`). -/
theorem diamond_lorentzian_le_euclidean (θ : ℝ) :
    lorentzianForm (diamondMomentum θ) ≤ Complex.normSq (diamondMomentum θ) := by
  unfold lorentzianForm
  rw [Complex.normSq_apply, diamondMomentum_re, diamondMomentum_im]
  nlinarith [sq_nonneg (Real.sinh θ)]

/-- **[Lorentz-invariant rest tick] The entropic Compton clock's rest tick is set by the Lorentzian rest
mass** `√(lorentzianForm q) = 1`, so it is boost-independent — `comptonFrequency (m·√(lorentzianForm q)) c ℏ
= comptonFrequency m c ℏ`.  (Contrast the boosted, coordinate frequency `cosh θ · ω_rest`.) -/
theorem diamond_restClock_lorentzInvariant (m c ħ θ : ℝ) :
    comptonFrequency (m * Real.sqrt (lorentzianForm (diamondMomentum θ))) c ħ = comptonFrequency m c ħ := by
  rw [diamond_lorentzianForm_eq_restMassSq, Real.sqrt_one, mul_one]

/-- **[Time-dilation² from the Lorentzian metric] `E²/lorentzianForm q = 1/(1 − lorentzForceDual)`.**  The
entropic clock's squared time-dilation is the diamond energy² over the *Lorentzian* rest mass² — read off the
Minkowski metric — and equals the Lorentz factor `γ² = cosh²θ`, i.e. the reciprocal of `1` minus the BCJ
gravitational dual `v² = tanh²θ`. -/
theorem diamond_lorentzian_timeDilation_sq (F : Matrix (Fin 4) (Fin 4) ℝ) (V : Fin 4 → ℝ) (μ : Fin 4)
    (θ : ℝ) (hnum : (F *ᵥ V) μ = Real.sinh θ) :
    (diamondMomentum θ).re ^ 2 / lorentzianForm (diamondMomentum θ)
      = 1 / (1 - lorentzForceDual F V μ (bogoliubovEnergy (Real.sinh θ) 1 ^ 2)) := by
  rw [diamond_lorentzianForm_eq_restMassSq, div_one, diamondMomentum_re, ← diamond_horizon_energy]
  exact diamond_lorentzFactor F V μ θ hnum

end Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondLorentzianEntropicClock

end
