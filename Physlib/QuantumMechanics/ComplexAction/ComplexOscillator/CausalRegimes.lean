/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram

/-!
# Timelike and spacelike: the causal regimes of the Nagao–Nielsen complex oscillator

`Rapidity.LightCone45RapidityUnification` formalized the **lightlike** boundary (the `45°` light cone). This
file completes the causal trichotomy with **timelike** and **spacelike** theorems and links them to
the **Nagao–Nielsen complex oscillator** (`ComplexOscillator.PhaseDiagram`).

## The bridge

For a complex angular frequency `ω = ω_R + i ω_I` (mode `e^{−iωt} = e^{−iω_R t} e^{ω_I t}`), the
Minkowski form of `ω` is the real part of `ω²`:

  `lorentzianForm ω = (Re ω)² − (Im ω)² = Re(ω²)`   (`lorentzianForm_eq_re_sq`).

This is *exactly* the Nagao–Nielsen oscillator discriminant `Re(m ω²)` at unit mass `m = 1`. Hence
the causal character of the frequency **is** the oscillator regime:

* **Timelike** `L(ω) > 0` ⟺ `Re(ω²) > 0` ⟺ `IsHarmonicOscillator 1 ω` — the **underdamped /
  oscillatory** regime (`|Im ω| < |Re ω|`, inside the `45°` cone): the real frequency dominates, the
  mode oscillates.
* **Spacelike** `L(ω) < 0` ⟺ `Re(ω²) < 0` ⟺ `IsInvertedHarmonicOscillator 1 ω` — the **overdamped
  / runaway** regime (`|Re ω| < |Im ω|`, outside the cone): the imaginary frequency dominates, the
  mode grows/decays exponentially (inverted oscillator).
* **Lightlike** `L(ω) = 0` ⟺ `|Re ω| = |Im ω|` — the **critically damped** `45°` boundary.

## Main results

* `timelike_iff_isHarmonicOscillator` — timelike ⟺ HO (underdamped).
* `spacelike_iff_isInvertedHarmonicOscillator` — spacelike ⟺ IHO (overdamped).
* `timelike_iff_abs_im_lt`, `spacelike_iff_abs_re_lt` — the cone interior/exterior characterizations.
* `oscillator_causal_trichotomy` — every frequency is timelike (HO) / lightlike (critical) /
  spacelike (IHO).
* `wick_swaps_HO_IHO` — the Wick rotation `ω ↦ iω` swaps HO and IHO (timelike ↔ spacelike).
* `boost_preserves_underdamped` — a Lorentz boost preserves the oscillator regime.
* `massive_energyVector_isHarmonicOscillator` — the massive Bogoliubov energy vector is timelike (HO).

## References

* K. Nagao, H. B. Nielsen, arXiv:1902.01424 (complex `m, ω` oscillator phase diagram).
* `ComplexOscillator.PhaseDiagram`, `Rapidity.LightCone45RapidityUnification`, `Rapidity.FutureIncludedLorentzian`,
  `ComplexDelta.Convergence`, `TimeOperator.HyperbolicPoincareLorentzMisra` (this development).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.HyperbolicPoincareLorentzMisra
open Physlib.QuantumMechanics.ComplexAction.Rapidity.LightCone45RapidityUnification
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram

namespace Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.CausalRegimes

/-! ## §A — the cone interior/exterior in coordinates -/

/-- **Spacelike in coordinates** `L(q) < 0 ⟺ |Re q| < |Im q|` (outside the `45°` cone): the
imaginary part dominates. Complements `lorentzian_pos_iff_timelike` (the timelike interior). -/
theorem lorentzian_neg_iff_abs_re_lt (q : ℂ) : lorentzianForm q < 0 ↔ |q.re| < |q.im| := by
  unfold lorentzianForm
  constructor
  · intro h; nlinarith [sq_abs q.re, sq_abs q.im, abs_nonneg q.re, abs_nonneg q.im, h]
  · intro h; nlinarith [sq_abs q.re, sq_abs q.im, abs_nonneg q.re, abs_nonneg q.im, h]

/-- **Timelike interior** `timelike ω ⟺ |Im ω| < |Re ω|` (inside the `45°` cone) — the underdamped
condition. -/
theorem timelike_iff_abs_im_lt (ω : ℂ) : timelike ω ↔ |ω.im| < |ω.re| :=
  lorentzian_pos_iff_timelike ω

/-- **Spacelike exterior** `spacelike ω ⟺ |Re ω| < |Im ω|` (outside the cone) — the overdamped
condition. -/
theorem spacelike_iff_abs_re_lt (ω : ℂ) : spacelike ω ↔ |ω.re| < |ω.im| :=
  lorentzian_neg_iff_abs_re_lt ω

/-! ## §B — timelike ⟺ harmonic oscillator (underdamped), spacelike ⟺ inverted (overdamped) -/

/-- **Timelike ⟺ harmonic oscillator** `timelike ω ⟺ IsHarmonicOscillator 1 ω`: the frequency is
timelike iff the unit-mass oscillator is a genuine (underdamped) HO, because
`lorentzianForm ω = Re(ω²) = Re(1·ω²)`. -/
theorem timelike_iff_isHarmonicOscillator (ω : ℂ) :
    timelike ω ↔ IsHarmonicOscillator 1 ω := by
  unfold timelike IsHarmonicOscillator
  rw [lorentzianForm_eq_re_sq, one_mul]

/-- **Spacelike ⟺ inverted harmonic oscillator** `spacelike ω ⟺ IsInvertedHarmonicOscillator 1 ω`:
the frequency is spacelike iff the unit-mass oscillator is inverted (overdamped / runaway). -/
theorem spacelike_iff_isInvertedHarmonicOscillator (ω : ℂ) :
    spacelike ω ↔ IsInvertedHarmonicOscillator 1 ω := by
  unfold spacelike IsInvertedHarmonicOscillator
  rw [lorentzianForm_eq_re_sq, one_mul]

/-! ## §C — the causal trichotomy = the oscillator regime trichotomy -/

/-- **The causal trichotomy of the complex frequency = the oscillator regimes.** Every complex
frequency `ω` is exactly one of:

* **timelike** — `IsHarmonicOscillator 1 ω` and `|Im ω| < |Re ω|` (underdamped, oscillatory);
* **lightlike** — `lorentzianForm ω = 0` and `|Re ω| = |Im ω|` (critically damped, `45°`);
* **spacelike** — `IsInvertedHarmonicOscillator 1 ω` and `|Re ω| < |Im ω|` (overdamped, runaway). -/
theorem oscillator_causal_trichotomy (ω : ℂ) :
    (IsHarmonicOscillator 1 ω ∧ |ω.im| < |ω.re|)
      ∨ (lorentzianForm ω = 0 ∧ |ω.re| = |ω.im|)
      ∨ (IsInvertedHarmonicOscillator 1 ω ∧ |ω.re| < |ω.im|) := by
  rcases lt_trichotomy (lorentzianForm ω) 0 with h | h | h
  · exact Or.inr (Or.inr ⟨(spacelike_iff_isInvertedHarmonicOscillator ω).mp h,
      (lorentzian_neg_iff_abs_re_lt ω).mp h⟩)
  · exact Or.inr (Or.inl ⟨h, (lightlike_iff_abs_eq ω).mp h⟩)
  · exact Or.inl ⟨(timelike_iff_isHarmonicOscillator ω).mp h,
      (lorentzian_pos_iff_timelike ω).mp h⟩

/-! ## §D — Wick rotation swaps the regimes, the boost preserves them -/

/-- **The Wick rotation `ω ↦ iω` swaps HO and IHO** (timelike ↔ spacelike): multiplying the
frequency by `i` (the rotation to imaginary time) turns an underdamped oscillator into an inverted
(overdamped) one, since `(iω)² = −ω²` flips `Re(ω²)`. The Nagao–Nielsen real-time ↔ imaginary-time
exchange. -/
theorem wick_swaps_HO_IHO (ω : ℂ) :
    IsHarmonicOscillator 1 ω ↔ IsInvertedHarmonicOscillator 1 (Complex.I * ω) := by
  rw [← timelike_iff_isHarmonicOscillator, ← spacelike_iff_isInvertedHarmonicOscillator,
    timelike_mul_I_iff_spacelike]

/-- **A Lorentz boost preserves the oscillator regime**: if `ω` is underdamped (`|Im ω| < |Re ω|`,
timelike) then the boosted frequency is still underdamped, because the boost preserves `Re² − Im²`
(`lorentzBoost_preserves_form`). The regime is boost-invariant. -/
theorem boost_preserves_underdamped (θ : ℝ) (ω : ℂ) (h : ω.im ^ 2 < ω.re ^ 2) :
    (lorentzBoost θ ω.re ω.im).2 ^ 2 < (lorentzBoost θ ω.re ω.im).1 ^ 2 := by
  have hpres := lorentzBoost_preserves_form θ ω.re ω.im
  linarith [hpres, h]

/-! ## §E — link to the last reply: the massive energy vector is an underdamped oscillator -/

/-- **The massive Bogoliubov energy vector is a harmonic oscillator** (timelike / underdamped): for a
genuine gap `Δ ≠ 0` the energy vector `(E, ξ)` is timelike, hence `IsHarmonicOscillator 1 (E + iξ)` —
the rest mass makes the "real frequency" dominate. (At `Δ = 0`, massless, it is lightlike /
critically damped: `massless_energyVector_lightlike`.) -/
theorem massive_energyVector_isHarmonicOscillator (ξ Δ : ℝ) (hΔ : Δ ≠ 0) :
    IsHarmonicOscillator 1 ((bogoliubovEnergy ξ Δ : ℂ) + (ξ : ℂ) * Complex.I) :=
  (timelike_iff_isHarmonicOscillator _).mp (bogoliubov_energyVector_timelike ξ Δ hΔ)

/-- **Summary: the three causal characters are the three oscillator regimes.** Timelike ⟺ HO
(underdamped), spacelike ⟺ IHO (overdamped), lightlike ⟺ critically damped; and the massive energy
vector of the last reply is timelike (HO). -/
theorem complexOscillator_regimes_summary (ξ Δ : ℝ) (hΔ : Δ ≠ 0) (ω : ℂ) :
    (timelike ω ↔ IsHarmonicOscillator 1 ω)
      ∧ (spacelike ω ↔ IsInvertedHarmonicOscillator 1 ω)
      ∧ (lightlike ω ↔ |ω.re| = |ω.im|)
      ∧ IsHarmonicOscillator 1 ((bogoliubovEnergy ξ Δ : ℂ) + (ξ : ℂ) * Complex.I) :=
  ⟨timelike_iff_isHarmonicOscillator ω, spacelike_iff_isInvertedHarmonicOscillator ω,
   lightlike_iff_abs_eq ω, massive_energyVector_isHarmonicOscillator ξ Δ hΔ⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.CausalRegimes

end

end
