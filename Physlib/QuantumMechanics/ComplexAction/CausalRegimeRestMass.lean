/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ActionAngleCausalRegimes
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency

/-!
# The causal regime is the rest-mass sign: timelike = massive (rest frame exists)

This links the Nagao–Nielsen causal regimes (`ActionAngleCausalRegimes` / `ComplexOscillator.CausalRegimes`) to the
rest-frame / Bogoliubov-boost / QIF-consistency structure of `Bogoliubov.RestFrameQIFConsistency`. They are the same
metric: the `restMassSq t x = t² − x²` (the `symplecticS = diag(1,−1)` norm of `(E/c, p)`,
`restMass_is_metric_norm`) is exactly the `lorentzianForm` of the complex energy-momentum `t + i·x`.

So the causal regime *is* the rest-mass sign:

* **timelike** ⟺ `restMassSq > 0` ⟺ **massive** — a rest frame exists (`boost_to_rest_frame`, condition `|p| < E/c`)
  ⟺ **harmonic oscillator**;
* **spacelike** ⟺ `restMassSq < 0` ⟺ **tachyonic** — no rest frame ⟺ **inverted harmonic oscillator**.

The Bogoliubov boost `boostFrame θ` is a Lorentz boost precisely when it preserves the metric `S`
(`metric_condition`, `𝒱ᵀ S 𝒱 = S ⟺ u² − v² = 1`); it preserves `restMassSq` (`boostFrame_restMass`, the same
`lorentzBoost_preserves_form` used for `CausalRegimes.boost_preserves_underdamped`), so the causal regime is
**boost-invariant** — the metric `S` is the common root of both the rest-mass and the causal-regime invariance,
alongside the transverse entropic rate `λ` (`boostFrame_entropicRate`).

For the action-angle momentum, the radicand `R = 2I/τ − q^{α+1}/τ²` *is* the rest mass² of the momentum viewed as an
energy-momentum: the classically-allowed (`R > 0`, real momentum) region is massive/timelike (its own rest frame,
`p = 0`), the forbidden region is tachyonic/spacelike.

* **`restMassSq_eq_lorentzianForm`** (`t² − x² = lorentzianForm(t + i·x)`); **`massive_iff_timelike`**,
  **`massive_isHarmonicOscillator`**.
* **`boostFrame_massive_iff`** (the boost preserves the massive/timelike regime).
* **`reducedMomentum_restMassSq`** (the action-angle radicand `R` is the momentum's rest mass²).

**Honest layering.** Exact `restMassSq` / `lorentzianForm` identities; reuses `restMass_is_metric_norm`,
`boostFrame_restMass`, `lorentzBoost_preserves_form`, `reducedMomentum_sq` and the `CausalRegimes` trichotomy..

## References

* Links `ActionAngleCausalRegimes` / `ComplexOscillator.CausalRegimes` to `Bogoliubov.RestFrameQIFConsistency`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearGeneralizedTrig
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.CausalRegimes
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrameQIFConsistency

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CausalRegimeRestMass

/-- **The rest mass² is the Lorentzian form of the complex energy-momentum** `restMassSq t x = t² − x² =
lorentzianForm(t + i·x)` — the `symplecticS = diag(1,−1)` metric norm of `(E/c, p)` (`restMass_is_metric_norm`) is
the `(Re)² − (Im)²` causal form. -/
lemma restMassSq_eq_lorentzianForm (t x : ℝ) :
    restMassSq t x = lorentzianForm ((t : ℂ) + Complex.I * (x : ℂ)) := by
  unfold restMassSq lorentzianForm
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

/-- **Massive ⟺ timelike** `0 < restMassSq t x ↔ timelike(t + i·x)` — a positive rest mass² is the timelike
(underdamped) regime; a rest frame exists (`boost_to_rest_frame`, `|p| < E/c`). -/
lemma massive_iff_timelike (t x : ℝ) :
    0 < restMassSq t x ↔ timelike ((t : ℂ) + Complex.I * (x : ℂ)) := by
  rw [restMassSq_eq_lorentzianForm]; rfl

/-- **A massive energy-momentum is a harmonic oscillator** `0 < restMassSq → IsHarmonicOscillator 1 (t + i·x)` —
the physical (timelike, rest-frame-admitting) regime is the harmonic oscillator. -/
lemma massive_isHarmonicOscillator (t x : ℝ) (h : 0 < restMassSq t x) :
    IsHarmonicOscillator 1 ((t : ℂ) + Complex.I * (x : ℂ)) :=
  (timelike_iff_isHarmonicOscillator _).mp ((massive_iff_timelike t x).mp h)

/-- **The Bogoliubov boost preserves the massive/timelike regime** — since `boostFrame` preserves `restMassSq`
(`boostFrame_restMass = lorentzBoost_preserves_form`), the causal regime is boost-invariant: the metric `S` is the
common root of the rest-mass and causal-regime invariances. -/
lemma boostFrame_massive_iff (θ : ℝ) (F : FrameData) :
    0 < restMassSq (boostFrame θ F).energy (boostFrame θ F).momentum
      ↔ 0 < restMassSq F.energy F.momentum := by
  rw [boostFrame_restMass]

/-- **The action-angle radicand is the momentum's rest mass²** `restMassSq (reducedMomentum) 0 = R` — the
classically-allowed (`R ≥ 0`, real) momentum, viewed as an energy-momentum with vanishing spatial part, has rest
mass² equal to the turning-point radicand `R = 2I/τ − q^{α+1}/τ²`: allowed = massive (at rest). -/
lemma reducedMomentum_restMassSq (I α τ q : ℝ) (h : 0 ≤ 2 * I / τ - q ^ (α + 1) / τ ^ 2) :
    restMassSq (reducedMomentum I α τ q) 0 = 2 * I / τ - q ^ (α + 1) / τ ^ 2 := by
  unfold restMassSq
  rw [reducedMomentum_sq I α τ q h]
  ring

end Physlib.QuantumMechanics.ComplexAction.CausalRegimeRestMass
