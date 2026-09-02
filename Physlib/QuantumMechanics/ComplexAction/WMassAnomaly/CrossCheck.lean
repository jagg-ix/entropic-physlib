/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.EntropicLagrangian
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment

/-!
# Cross-check: the entropic action for the W-mass anomaly vs. the muon g-2 scale

A numerical cross-check of the entropic-time interpretation (`WMassAnomaly.EntropicLagrangian`,
`δ_{G_F} = e^{−S_I/ħ} − 1`). The W-mass derivation and the muon `g−2` are claimed to share one entropic
source. This file **tests the magnitudes against each other**, reusing the *verified* muon Schwinger bound
(`MuonAnomaly.AnomalousMagneticMoment.muonSchwingerAnomaly_bounds`, `0.001161 < α/2π < 0.001162`).

**The two numbers.**
* From CDF (Endo–Mishima Eq. 11): `ΔM_W/M_{W,SM} = (80.4335 − 80.3500)/80.3500 ≈ 1.039×10⁻³`, and with the
  electroweak coefficient `κ = s_W²/(2(c_W²−s_W²)) ≈ 0.201`, the implied entropic action (leading order
  `δ_{G_F} ≈ −S_I/ħ`) is `S_I/ħ = (ΔM_W/M_{W,SM})/κ ≈ 5.16×10⁻³` (`impliedEntropicAction`).
* The muon's verified leading anomaly is `α/2π ≈ 1.161×10⁻³` (`schwingerAnomaly (1/137)`).

**The cross-check result.** The proportionality `c = (S_I/ħ)/(α/2π)` lands at `≈ 4.45`, an `O(1)` number
(`crosscheck_proportionality_O1`: `4 < c < 5`). So the two anomalies require entropic content of the **same
`10⁻³` scale**, related by an `O(1)` constant — *order-of-magnitude consistent and not fine-tuned*.

**Honest verdict.** Positive: the magnitudes are mutually consistent up to `c ≈ 4.4 = O(1)`; the sign is exact;
both anomalies sit at the `α/2π ∼ 10⁻³` entropic scale. Negative / caveat: `c ≠ 1`, so this is a *consistency
check*, not a parameter-free prediction — `c` (the ratio of the muon's imaginary action to its QED anomaly)
remains the one undetermined number. Crucially, the cross-check supports identifying `S_I/ħ` with the **full**
anomaly scale `α/2π`, **not** the `g−2` *discrepancy* `Δa_μ ∼ 2.5×10⁻⁹` (which would force an absurd
`c ∼ 10⁶`).

## References

* CDF Collaboration, *Science* **376** (2022) 170; M. Endo, S. Mishima, Phys. Rev. D **106** (2022) 115005.
  `Physlib` (`WMassAnomaly.EntropicLagrangian`, `MuonAnomaly.AnomalousMagneticMoment` — the verified `α/2π` bound).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.GFShift

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.CrossCheck


/-- The fractional W-mass excess `ΔM_W/M_{W,SM} = (80.4335 − 80.3500)/80.3500` (CDF vs SM, in GeV). -/
noncomputable def wMassShiftRatio : ℝ := (80.4335 - 80.3500) / 80.3500

/-- The electroweak coefficient `κ = s_W²/(2(c_W²−s_W²))` of Eq. (11), the repo's
`WMassAnomaly.GFShift.gfShiftCoefficient` evaluated at `s_W² ≈ 0.223`, `c_W² ≈ 0.777`. -/
noncomputable def weinbergKappa : ℝ := gfShiftCoefficient 0.223 0.777

/-- The **implied entropic action** `S_I/ħ = (ΔM_W/M_{W,SM})/κ` that the CDF excess requires (leading order,
`δ_{G_F} ≈ −S_I/ħ`). -/
noncomputable def impliedEntropicAction : ℝ := wMassShiftRatio / weinbergKappa


/-- **[The required entropic action]** `0.005 < S_I/ħ < 0.0053` (≈ `5.16×10⁻³`). -/
lemma impliedEntropicAction_bounds : 0.005 < impliedEntropicAction ∧ impliedEntropicAction < 0.0053 := by
  unfold impliedEntropicAction wMassShiftRatio weinbergKappa gfShiftCoefficient
  constructor <;> norm_num


/-- **[Cross-check: `O(1)` consistency between the W-mass and g-2 entropic scales]** the proportionality
`c = (S_I/ħ)/(α/2π)` between the W-mass-implied entropic action and the *verified* muon Schwinger anomaly
satisfies `4 < c < 5` — an `O(1)` constant. The two anomalies require entropic content of the same `10⁻³`
scale (consistent, not fine-tuned), related by `c ≈ 4.4`. -/
lemma crosscheck_proportionality_O1 :
    4 < impliedEntropicAction / schwingerAnomaly ((1 : ℝ) / 137)
      ∧ impliedEntropicAction / schwingerAnomaly ((1 : ℝ) / 137) < 5 := by
  obtain ⟨ha_lo, ha_hi⟩ := muonSchwingerAnomaly_bounds
  obtain ⟨hI_lo, hI_hi⟩ := impliedEntropicAction_bounds
  have ha_pos : 0 < schwingerAnomaly ((1 : ℝ) / 137) := by linarith
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ ha_pos]; linarith
  · rw [div_lt_iff₀ ha_pos]; linarith

end Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.CrossCheck

end
