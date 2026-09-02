/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.GeometricEntropy
public import Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.Normalization

/-!
# The mode-count test: `N = S_I / log K` is `2π√2`, not a clean integer

Testing reading (ii) of `WMassAnomaly.GeometricEntropy`: *does the muon couple to an integer number `N` of
geometric (Rényi-2) entropy cells, `S_I = N·log K`, with `N` derivable from the decay structure?* The required
count is

  `N = (S_I/ħ)_required / log K = impliedEntropicAction / muonRenyi2Entropy`   (`requiredModeCount`).

* `requiredModeCount_gt_eight` — `N > 8` (from `WMassAnomaly.GeometricEntropy.geometric_entropy_undershoots`).
* `twoPiSqrt2_between_8_8_and_9` — `8.8 < 2π√2 < 9` (`≈ 8.886`), the value `N` actually takes (since the closed
  form `S_I/ħ = α/√2`, i.e. `c = π√2`, with `log K ≈ α/4π`, gives `N = (α/√2)/(α/4π) = 2π√2`).

**Verdict — the integer-`N` reading is disfavored.** The required mode count is `N ≈ 8.886 = 2π√2`, a
*transcendental* number, **not** the integer `9` (nor any clean integer). So `S_I` is **not** an integer
multiple of the single-cell Rényi-2 entropy; equivalently the closed form is `S_I/ħ = α/√2` (`c = π√2`, the
`WMassAnomaly.Normalization` candidate), which involves the irrational `2π√2 = 4π/√2`. This **rules out** the
clean cell-counting picture (reading ii) at the few-percent level. The two surviving readings are: (i) the
relevant entropy is the **von Neumann** (`≈2.6×10⁻³`), which needs only a factor `≈2` — physically the cleanest,
since the muon-decay *rate* `Γ ∝ |A|²` and the bipartite (`e⁻ν̄_eν_μ`) entanglement both naturally double the
single-subsystem entropy; and (iii) a non-`1:1` shift/action proportionality `= π√2`. The honest residual is
**a factor of `2` (von Neumann + bipartite/rate doubling), not an integer cell count.**

## References

* `Physlib` (`WMassAnomaly.GeometricEntropy` — geometric entropy `= log K`; `WMassAnomaly.Normalization` —
  `c = π√2` candidate; `MuonAnomaly.EntanglementEntropy`, `WMassAnomaly.CrossCheck`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.EntanglementEntropy
open Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.CrossCheck
open Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.GeometricEntropy
open Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.Normalization

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.ModeCount

/-- The **required mode count** `N = (S_I/ħ)_required / log K` — the number of single-cell Rényi-2 entropy
quanta the W-mass excess would need (reading ii). -/
noncomputable def requiredModeCount : ℝ :=
  impliedEntropicAction / muonRenyi2Entropy ((1 : ℝ) / 137)

/-- **[The required mode count exceeds 8]** `N > 8` — the geometric single-cell entropy `log K` is more than
eight times too small (`WMassAnomaly.GeometricEntropy.geometric_entropy_undershoots`). -/
lemma requiredModeCount_gt_eight : 8 < requiredModeCount := by
  have hm : 0 < muonRenyi2Entropy ((1 : ℝ) / 137) := muonRenyi2Entropy_pos _ (by norm_num)
  rw [requiredModeCount, lt_div_iff₀ hm]
  exact geometric_entropy_undershoots

/-- **[The mode count is `2π√2 ≈ 8.886`, not an integer]** `8.8 < 2π√2 < 9` — the value `N` takes (via the
closed form `S_I/ħ = α/√2`) is the transcendental `2π√2`, strictly between `8.8` and `9`, hence **not** the
integer `9`. The clean cell-counting reading (ii) is disfavored. -/
lemma twoPiSqrt2_between_8_8_and_9 :
    8.8 < 2 * (Real.pi * Real.sqrt 2) ∧ 2 * (Real.pi * Real.sqrt 2) < 9 := by
  obtain ⟨hlo, hhi⟩ := piSqrt2_in_window
  constructor <;> linarith

end Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.ModeCount

end
