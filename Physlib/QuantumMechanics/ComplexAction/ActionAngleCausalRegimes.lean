/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ActionAngleNagaoNielsenComplexAction
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.CausalRegimes

/-!
# The action-angle turning points are the Nagao–Nielsen causal regimes (HO / IHO)

This extends the action-angle / Nagao–Nielsen complex-momentum arc
(`ActionAngleNagaoNielsenComplexAction`) by relating it to the **causal-regime trichotomy** of the complex
oscillator (`ComplexOscillator.CausalRegimes`) — timelike/spacelike = harmonic/inverted-harmonic =
underdamped/overdamped, the Three Faces.

The bridge is exact: the Lorentzian form `lorentzianForm p = (Re p)² − (Im p)² = Re(p²)` of the action-angle
momentum equals the radicand `R = 2I/τ − q^{α+1}/τ²` (via `reducedMomentum_sq` / `nnReducedMomentum_sq`). So the
classical turning point `R = 0` is exactly the light-cone `lorentzianForm = 0`:

* **classically-allowed region** `R > 0` — the momentum `p = √R` is **real** ⟹ **timelike** ⟹ a harmonic
  oscillator (underdamped, oscillatory motion);
* **classically-forbidden region** `R < 0` — the momentum `p = i√(−R)` is **imaginary** ⟹ **spacelike** ⟹ an
  inverted harmonic oscillator (overdamped, runaway = tunneling under the barrier).

The Nagao–Nielsen Wick rotation `p ↦ i·p` (`CausalRegimes.wick_swaps_HO_IHO`) sends the allowed (timelike/HO)
momentum to the forbidden (spacelike/IHO) one — the real-time ↔ imaginary-time exchange, i.e. crossing the turning
point. So the action-angle turning-point structure *is* the causal trichotomy: the oscillatory / critical /
tunneling regimes are the timelike / lightlike / spacelike Nagao–Nielsen oscillator regimes (the Three Faces).

* **§A — the forbidden region is spacelike / IHO.** **`nnReducedMomentum_lorentzianForm`** (`= R`),
  `nnReducedMomentum_spacelike`, **`nnReducedMomentum_isInvertedHarmonicOscillator`**.
* **§B — the allowed region is timelike / HO.** `reducedMomentum_lorentzianForm` (`= R`),
  `reducedMomentum_timelike`, **`reducedMomentum_isHarmonicOscillator`**, `reducedMomentum_wick_isInverted`
  (the Wick rotation of the allowed momentum is the forbidden regime).

**Honest layering.** Exact `lorentzianForm` / `Complex` identities; reuses `reducedMomentum`, `nnReducedMomentum`
and the `CausalRegimes` trichotomy. ## References

* A. Ghosh, C. Bhamidipati, arXiv:1905.08062; K. Nagao, H. B. Nielsen. Links `ActionAngleNagaoNielsenComplexAction`
  to `ComplexOscillator.CausalRegimes`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearGeneralizedTrig
open Physlib.QuantumMechanics.ComplexAction.ActionAngleNagaoNielsenComplexAction
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.CausalRegimes

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ActionAngleCausalRegimes


/-- **The forbidden-region momentum's Lorentzian form is the radicand** `lorentzianForm(p) = 2I/τ − q^{α+1}/τ²`
(`= R < 0` in the forbidden region) — the imaginary Nagao–Nielsen momentum's `(Re p)² − (Im p)² = Re(p²)` is the
on-shell `R`. -/
lemma nnReducedMomentum_lorentzianForm (I α τ q : ℝ) (h : 2 * I / τ - q ^ (α + 1) / τ ^ 2 ≤ 0) :
    lorentzianForm (nnReducedMomentum I α τ q) = 2 * I / τ - q ^ (α + 1) / τ ^ 2 := by
  rw [lorentzianForm_eq_re_sq, nnReducedMomentum_sq I α τ q h, Complex.ofReal_re]

/-- **The forbidden-region momentum is spacelike** — where `R < 0` the action-angle momentum lies outside the
`45°` light cone. -/
lemma nnReducedMomentum_spacelike (I α τ q : ℝ) (h : 2 * I / τ - q ^ (α + 1) / τ ^ 2 < 0) :
    spacelike (nnReducedMomentum I α τ q) := by
  unfold spacelike
  rw [nnReducedMomentum_lorentzianForm I α τ q h.le]
  simpa using h

/-- **The forbidden region is an inverted harmonic oscillator** — under the barrier (`R < 0`, imaginary momentum)
the action-angle motion is overdamped/runaway, the Nagao–Nielsen `IsInvertedHarmonicOscillator` regime (tunneling).
-/
lemma nnReducedMomentum_isInvertedHarmonicOscillator (I α τ q : ℝ)
    (h : 2 * I / τ - q ^ (α + 1) / τ ^ 2 < 0) :
    IsInvertedHarmonicOscillator 1 (nnReducedMomentum I α τ q) :=
  (spacelike_iff_isInvertedHarmonicOscillator _).mp (nnReducedMomentum_spacelike I α τ q h)


/-- **The allowed-region momentum's Lorentzian form is the radicand** `lorentzianForm(p) = 2I/τ − q^{α+1}/τ²`
(`= R > 0` in the allowed region) — the real momentum `√R` has `(Re p)² − (Im p)² = R`. -/
lemma reducedMomentum_lorentzianForm (I α τ q : ℝ) (h : 0 ≤ 2 * I / τ - q ^ (α + 1) / τ ^ 2) :
    lorentzianForm ((reducedMomentum I α τ q : ℝ) : ℂ) = 2 * I / τ - q ^ (α + 1) / τ ^ 2 := by
  rw [lorentzianForm_eq_re_sq, ← Complex.ofReal_pow, reducedMomentum_sq I α τ q h, Complex.ofReal_re]

/-- **The allowed-region momentum is timelike** — where `R > 0` the action-angle momentum lies inside the `45°`
light cone. -/
lemma reducedMomentum_timelike (I α τ q : ℝ) (h : 0 < 2 * I / τ - q ^ (α + 1) / τ ^ 2) :
    timelike ((reducedMomentum I α τ q : ℝ) : ℂ) := by
  unfold timelike
  rw [reducedMomentum_lorentzianForm I α τ q h.le]
  simpa using h

/-- **The allowed region is a harmonic oscillator** — with real momentum (`R > 0`) the action-angle motion is
underdamped/oscillatory, the Nagao–Nielsen `IsHarmonicOscillator` regime. -/
lemma reducedMomentum_isHarmonicOscillator (I α τ q : ℝ)
    (h : 0 < 2 * I / τ - q ^ (α + 1) / τ ^ 2) :
    IsHarmonicOscillator 1 ((reducedMomentum I α τ q : ℝ) : ℂ) :=
  (timelike_iff_isHarmonicOscillator _).mp (reducedMomentum_timelike I α τ q h)

/-- **The Wick rotation of the allowed momentum is the forbidden regime** — Wick-rotating the real (timelike/HO)
action-angle momentum `p ↦ i·p` gives an inverted harmonic oscillator (spacelike), the Nagao–Nielsen
real-time ↔ imaginary-time exchange: crossing the classical turning point. -/
lemma reducedMomentum_wick_isInverted (I α τ q : ℝ) (h : 0 < 2 * I / τ - q ^ (α + 1) / τ ^ 2) :
    IsInvertedHarmonicOscillator 1 (Complex.I * ((reducedMomentum I α τ q : ℝ) : ℂ)) :=
  (wick_swaps_HO_IHO _).mp (reducedMomentum_isHarmonicOscillator I α τ q h)

end Physlib.QuantumMechanics.ComplexAction.ActionAngleCausalRegimes
