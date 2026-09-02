/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
meta import Zil

/-!
# The muon anomalous magnetic moment (g − 2) at leading order

Applies the Bennett / Schwinger anomalous-magnetic-moment formalization
(`FirstQuantizedQED.AnomalousMagneticMoment`) to the **muon `g − 2`**. The leading one-loop QED contribution to the
anomalous moment is **lepton-mass-independent**, `a = α/(2π)` (Schwinger), so the muon's leading anomaly
is the *same function of `α`* as the electron's (`schwingerAnomaly`); the muon differs only at higher
order (mass-dependent QED, hadronic, and electroweak contributions).

Evaluated at the empirical fine-structure constant `α ≈ 1/137`, the leading Schwinger term is

  `a_μ^{(2)} = α/(2π) ≈ 0.001161`   (`muonSchwingerAnomaly_bounds`),

with muon `g`-factor `g_μ = 2 + α/π ≈ 2.00232` (`muonGFactor_bounds`), above the Dirac value `2`
(`gFactor_dirac`, `muonGFactor_gt_two`). The leading term lies **below** the measured
`a_μ ≈ 0.00116592` (`muonSchwingerAnomaly_lt_measured`) — the difference is the higher-order QED,
hadronic, and weak contributions.

> **Note.** `α` is taken as an input (its empirical value `≈ 1/137`). The source material proposes
> *deriving* `α` from a vacuum-structure (icosahedral packing) ansatz; that derivation is speculative and
> is **not** formalized here — only the standard QED Schwinger term `a = α/(2π)`, which is real physics.

* **§A — the leading muon anomaly** (`muonSchwingerAnomaly_bounds`, `schwingerAnomaly_pos`,
  `muonSchwingerAnomaly_lt_measured`).
* **§B — the muon g-factor** (`muonGFactor_bounds`, `muonGFactor_gt_two`).
* **§C — the assembly** (`muon_g2_leading`).

## References

* J. Schwinger, Phys. Rev. **73** (1948) 416 (`a = α/2π`); A. F. Bennett, arXiv:1406.0750v3, §VI. Measured
  `a_μ`: Muon `g − 2` Collaboration. Repo carrier: `FirstQuantizedQED.AnomalousMagneticMoment` (`gFactor`,
  `schwingerAnomaly`, `gFactor_schwinger`, `gFactor_dirac`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment

open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment


/-- **[The anomalous moment is positive] `a = α/(2π) > 0`** for `α > 0` — the radiative correction raises
`g` above the Dirac value `2`. -/
lemma schwingerAnomaly_pos (α : ℝ) (hα : 0 < α) : 0 < schwingerAnomaly α := by
  unfold schwingerAnomaly; positivity

/-- **[The leading muon anomaly at `α ≈ 1/137`] `0.001161 < a_μ^{(2)} < 0.001162`.** The one-loop
Schwinger term `α/(2π)` at the empirical fine-structure constant. -/
lemma muonSchwingerAnomaly_bounds :
    0.001161 < schwingerAnomaly ((1 : ℝ) / 137) ∧ schwingerAnomaly ((1 : ℝ) / 137) < 0.001162 := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  unfold schwingerAnomaly
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hpos]; nlinarith [Real.pi_lt_d4]
  · rw [div_lt_iff₀ hpos]; nlinarith [Real.pi_gt_d4]

/-- **[The leading term is below the measured value] `a_μ^{(2)} < a_μ ≈ 0.00116592`.** The one-loop
Schwinger contribution is the dominant part of the measured muon anomaly; the remainder is the
higher-order QED, hadronic, and electroweak contributions. -/
lemma muonSchwingerAnomaly_lt_measured : schwingerAnomaly ((1 : ℝ) / 137) < 0.00116592 := by
  have h := muonSchwingerAnomaly_bounds.2
  linarith


/-- **[The muon g-factor exceeds the Dirac value] `g_μ > 2`** for `α > 0` (`gFactor_dirac` gives the
Dirac value `g = 2` at `a = 0`). -/
lemma muonGFactor_gt_two (α : ℝ) (hα : 0 < α) : 2 < gFactor (schwingerAnomaly α) := by
  rw [gFactor_schwinger]
  have : 0 < α / Real.pi := div_pos hα Real.pi_pos
  linarith

/-- **[The muon g-factor at `α ≈ 1/137`] `2.00232 < g_μ < 2.00233`.** -/
lemma muonGFactor_bounds :
    2.00232 < gFactor (schwingerAnomaly ((1 : ℝ) / 137))
      ∧ gFactor (schwingerAnomaly ((1 : ℝ) / 137)) < 2.00233 := by
  rw [gFactor_schwinger]
  have hpos : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨?_, ?_⟩
  · rw [show (2.00232 : ℝ) = 2 + 0.00232 from by norm_num, add_lt_add_iff_left, lt_div_iff₀ hpos]
    nlinarith [Real.pi_lt_d4]
  · rw [show (2.00233 : ℝ) = 2 + 0.00233 from by norm_num, add_lt_add_iff_left, div_lt_iff₀ hpos]
    nlinarith [Real.pi_gt_d4]


/-- **[The muon g − 2 at leading order, assembled].** Using the Bennett/Schwinger formalization for the
muon at the empirical `α ≈ 1/137`: the leading anomalous moment is `a_μ^{(2)} = α/(2π) ∈ (0.001161,
0.001162)`, below the measured `a_μ ≈ 0.00116592`; the muon g-factor is `g_μ = 2 + α/π`, above the Dirac
value `g = 2` (`gFactor_dirac`). The leading muon anomaly is the *same* Schwinger function of `α` as the
electron's — lepton-mass-independent at one loop. -/
lemma muon_g2_leading :
    (0.001161 < schwingerAnomaly ((1 : ℝ) / 137) ∧ schwingerAnomaly ((1 : ℝ) / 137) < 0.001162)
      ∧ schwingerAnomaly ((1 : ℝ) / 137) < 0.00116592
      ∧ gFactor 0 = 2
      ∧ gFactor (schwingerAnomaly ((1 : ℝ) / 137)) = 2 + ((1 : ℝ) / 137) / Real.pi
      ∧ 2 < gFactor (schwingerAnomaly ((1 : ℝ) / 137)) :=
  ⟨muonSchwingerAnomaly_bounds, muonSchwingerAnomaly_lt_measured, gFactor_dirac,
    gFactor_schwinger ((1 : ℝ) / 137), muonGFactor_gt_two ((1 : ℝ) / 137) (by positivity)⟩

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment.schwingerAnomaly_pos where
  formalizes @ "claim:the-schwinger-one-loop-anomaly-alpha-over-two-pi-is-positive",
  supported_by @ "paper:schwinger-1948"

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment.muonGFactor_gt_two where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment.gFactor_schwinger",
  formalizes @ "claim:the-muon-g-factor-exceeds-the-dirac-value-two-by-the-anomaly",
  requires @ "claim:the-schwinger-one-loop-anomaly-alpha-over-two-pi-is-positive"

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment.muonSchwingerAnomaly_lt_measured where
  formalizes @ "claim:the-schwinger-one-loop-value-is-below-the-measured-muon-anomaly-leaving-the-higher-order-remainder",
  requires @ "claim:the-muon-g-factor-exceeds-the-dirac-value-two-by-the-anomaly",
  supported_by @ "measurement:fermilab-muon-g-2-final-2025",
  caveat @ "claim:one-loop-schwinger-only-the-full-value-needs-hadronic-and-higher-loop-contributions"

zil_file_contract physlib.anomalousMagneticMoment where
  promises "The muon anomalous magnetic moment at one loop: the Schwinger anomaly alpha over two pi is positive, the muon g-factor exceeds the Dirac value two by the anomaly, and the one-loop Schwinger value sits below the measured anomaly, leaving the higher-order hadronic and multi-loop remainder."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment.schwingerAnomaly",
    "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment.gFactor"]
  forbids_substitutes ["the hadronic vacuum-polarization and higher-loop contributions, not computed here"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment.schwingerAnomaly_pos,
    Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment.muonGFactor_gt_two,
    Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalousMagneticMoment.muonSchwingerAnomaly_lt_measured]

/- ZIL-END -/
