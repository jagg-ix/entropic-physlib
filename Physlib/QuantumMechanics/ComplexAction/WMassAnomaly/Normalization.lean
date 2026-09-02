/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.CrossCheck

/-!
# Isolating and identifying the entropic normalization `c = (S_I/ħ)/(α/2π)`

The entire entropic-time W-mass analysis (`WMassAnomaly.EntropicLagrangian`, `…CrossCheck`) leaves **one**
undetermined number: the normalization of the muon imaginary action `S_I/ħ` (equivalently the proportionality
`c` between it and the muon QED anomaly `α/2π`). This file **isolates** that number and **identifies** its
value.

* **§A — isolation.** `entropicNormalization c = (S_I/ħ)/(α/2π)`, the single coefficient, with the **defining
  identity** `S_I/ħ = c · (α/2π)` (`impliedAction_eq_normalization_mul_anomaly`) — the W-mass-required entropic
  action *is* `c` times the verified muon anomaly.
* **§B — identification of the value.** `entropicNormalization_bounds`: `4.43 < c < 4.46`, from the CDF inputs
  and the *verified* `α/2π` bound (`MuonAnomaly.AnomalousMagneticMoment.muonSchwingerAnomaly_bounds`). So `c ≈ 4.445`,
  pinned to a `0.03`-wide window.
* **§C — a candidate closed form.** `piSqrt2_in_window`: `π√2 ≈ 4.4429` lands in the same window
  (`4.43 < π√2 < 4.46`) — a **compatible** candidate (`c = π√2` would make `S_I/ħ = √2·α` parameter-free).

**Honest verdict — this is the boundary.** Isolated: `c` is a single, precisely-defined number, pinned to
`(4.43, 4.46)` and identified physically as the muon's imaginary action per unit QED anomaly. Identified only
up to that window: `π√2` is compatible, but the window is `~1%` wide and the electroweak inputs (`sin²θ_W`,
`M_W`) have uncertainty of that order — so this **does not derive** `c`; it identifies its *scale* (`O(1)`,
near `π√2`), not a proven closed form. A first-principles value of `c` still requires deriving `S_I` from a
microscopic entropic Lagrangian `L_I` — the one remaining open step.

## References

* CDF Collaboration, *Science* **376** (2022) 170; M. Endo, S. Mishima, Phys. Rev. D **106** (2022) 115005.
  `Physlib` (`WMassAnomaly.CrossCheck`, `MuonAnomaly.AnomalousMagneticMoment`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.GFShift
open Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.CrossCheck

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.Normalization


/-- The **entropic normalization** `c = (S_I/ħ)/(α/2π)` — the single undetermined coefficient of the entropic
W-mass interpretation: the muon imaginary action per unit QED anomaly. -/
noncomputable def entropicNormalization : ℝ :=
  impliedEntropicAction / schwingerAnomaly ((1 : ℝ) / 137)

/-- **[The defining identity]** `S_I/ħ = c · (α/2π)` — the entropic action required by the CDF W-mass excess is
exactly `c` times the verified muon anomaly. This is what isolates `c`. -/
lemma impliedAction_eq_normalization_mul_anomaly :
    impliedEntropicAction = entropicNormalization * schwingerAnomaly ((1 : ℝ) / 137) := by
  have ha : schwingerAnomaly ((1 : ℝ) / 137) ≠ 0 :=
    ne_of_gt (by linarith [muonSchwingerAnomaly_bounds.1])
  unfold entropicNormalization
  rw [div_mul_cancel₀ _ ha]


/-- **[Tightened required action]** `0.00516 < S_I/ħ < 0.00517` (≈ `5.163×10⁻³`). -/
lemma impliedEntropicAction_bounds_tight :
    0.00516 < impliedEntropicAction ∧ impliedEntropicAction < 0.00517 := by
  unfold impliedEntropicAction wMassShiftRatio weinbergKappa gfShiftCoefficient
  constructor <;> norm_num

/-- **[The normalization is pinned to `c ≈ 4.445`]** `4.43 < c < 4.46` — from the CDF inputs and the verified
`α/2π` bound, the single entropic coefficient is fixed to a `0.03`-wide window. -/
lemma entropicNormalization_bounds : 4.43 < entropicNormalization ∧ entropicNormalization < 4.46 := by
  obtain ⟨ha_lo, ha_hi⟩ := muonSchwingerAnomaly_bounds
  obtain ⟨hI_lo, hI_hi⟩ := impliedEntropicAction_bounds_tight
  have ha_pos : 0 < schwingerAnomaly ((1 : ℝ) / 137) := by linarith
  unfold entropicNormalization
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ ha_pos]; linarith
  · rw [div_lt_iff₀ ha_pos]; linarith


/-- **[The candidate `π√2` is compatible]** `4.43 < π√2 < 4.46` — `π√2 ≈ 4.4429` lands inside the window for
`c`, so `c = π√2` (i.e. `S_I/ħ = √2·α`) is a viable closed form. This is *compatibility*, not derivation: the
window is `~1%` wide and admits other `O(1)` constants. -/
lemma piSqrt2_in_window :
    4.43 < Real.pi * Real.sqrt 2 ∧ Real.pi * Real.sqrt 2 < 4.46 := by
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have hs_lo : (1.41421 : ℝ) < Real.sqrt 2 := by
    rw [show (1.41421 : ℝ) = Real.sqrt (1.41421 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs_hi : Real.sqrt 2 < (1.41422 : ℝ) := by
    rw [show (1.41422 : ℝ) = Real.sqrt (1.41422 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  constructor
  · nlinarith [hpi_lo, hs_lo, Real.pi_pos, Real.sqrt_nonneg 2]
  · nlinarith [hpi_hi, hs_hi, Real.pi_pos, Real.sqrt_nonneg 2]

end Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.Normalization

end
