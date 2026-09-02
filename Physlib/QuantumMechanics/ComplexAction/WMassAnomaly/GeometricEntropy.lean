/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.EntanglementEntropy
public import Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.CrossCheck

/-!
# Penrose / horizon-cell analysis of the W-mass entropic action: the geometry undershoots

Does the repo's **Penrose / horizon-cell geometry** close the factor-of-`2` between the muon entanglement
entropy and the W-mass requirement? This file inspects the geometric theorems and finds — **no, it sharpens
the tension**.

The horizon-cell arc (`HorizonCell.CellThreeFacesAssembly`) fixes the quasifree (Verch) suppression weight as
`e^{−S_I/ħ} = tanh η`, so the **geometric imaginary action is**

  `S_I/ħ = −log tanh η = log(coth η) = log K`   (`quasifree_imaginaryAction_eq_renyi2`),

i.e. the **Rényi-2 entropy** `log K` (the area-law / bond-dimension entropy: a horizon cell has `log(e^{1/4}) =
1/4` per cell, `N` cells → `S = A/4`). And `AdSCFT.PenroseHolographicMassEntropyBound` proves the Penrose bound
`S_I = A/4 ≤ 4π m²`.

**The finding.** The geometry unambiguously selects the **Rényi-2** entropy `log K`, which for the muon is
`< 5.81×10⁻⁴` (`MuonAnomaly.EntanglementEntropy.muonRenyi2Entropy_bound`) — the *smaller* of the two candidates, **not**
the von Neumann `≈ 2.6×10⁻³`. So against the W-mass requirement `S_I/ħ ≈ 5.16×10⁻³`, the geometric value
undershoots by **more than `8×`** (`geometric_entropy_undershoots`).

* `quasifree_imaginaryAction_eq_renyi2` — the geometric (quasifree/horizon) imaginary action *is* `log K`.
* `geometric_entropy_undershoots` — `8 · S₂(muon) < S_I/ħ(required)`: the geometric entropy is `> 8×` too small.

**Honest verdict — the Penrose geometry does NOT close the gap.** It does the opposite: by pinning the geometric
entropy to the Rényi-2 `log K` (the quasifree/area-law value), it makes the single-cell geometric prediction
**undershoot by ~9×**, not ~2×. Three consistent readings remain: (i) the relevant `S_ent` is the **von
Neumann** entropy (`≈2.6×10⁻³`, factor-2), which the area-law geometry does *not* supply — area-law is Rényi-2;
(ii) the muon couples to **`N ≈ 9` cells/modes** (`S_I = N·log K`), a definite integer to be derived, not
fitted; (iii) the proportionality between the W-mass `G_F` shift and the muon imaginary action is not `1:1`.
The Penrose mass bound `S_I = A/4 ≤ 4π m²` is the *gravitational* face (with `m_μ` in Planck units it is
astronomically below `10⁻³`), so it does **not** constrain the QED-entanglement scale. The geometry's role is
to make the residual a **definite, falsifiable factor** (`log K` vs von Neumann vs `N`), not to remove it.

## References

* R. Penrose (cosmic-censorship inequality); Bekenstein–Hawking `S = A/4`. `Physlib`
  (`HorizonCell.CellThreeFacesAssembly` — quasifree `e^{−S_I/ħ}=tanh η`, `AdSCFT.PenroseHolographicMassEntropyBound`,
  `MuonAnomaly.EntanglementEntropy`, `WMassAnomaly.CrossCheck`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.EntanglementEntropy
open Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.CrossCheck
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.GeometricEntropy


/-- The **quasifree (horizon-cell) imaginary action** `S_I/ħ = −log tanh η` — from the Verch suppression weight
`e^{−S_I/ħ} = tanh η` (`HorizonCell.CellThreeFacesAssembly`). -/
noncomputable def quasifreeImaginaryAction (η : ℝ) : ℝ := -Real.log (Real.tanh η)

/-- **[The geometric imaginary action is the Rényi-2 entropy] `S_I/ħ = −log tanh η = log K`** — the
quasifree/horizon entropic action is exactly the Rényi-2 entanglement entropy `log(schmidtNumber η)` (the
area-law / bond-dimension entropy, `1/4` per Bekenstein–Hawking cell). -/
lemma quasifree_imaginaryAction_eq_renyi2 (η : ℝ) :
    quasifreeImaginaryAction η = renyi2Entropy (schmidtNumber η) := by
  unfold quasifreeImaginaryAction renyi2Entropy schmidtNumber
  rw [← Real.log_inv, Real.tanh_eq_sinh_div_cosh, inv_div]


/-- **[The geometric entropy undershoots by more than `8×`]** `8 · S₂(muon) < S_I/ħ(required)` — the
area-law / Rényi-2 entropy `log K ≈ 5.8×10⁻⁴` that the Penrose / horizon-cell geometry selects is more than
eight times too small to supply the W-mass-required imaginary action `≈ 5.16×10⁻³`. The geometry does not close
the factor-of-2; it makes a single-cell geometric prediction undershoot by `~9×`. -/
lemma geometric_entropy_undershoots :
    8 * muonRenyi2Entropy ((1 : ℝ) / 137) < impliedEntropicAction := by
  have h1 := muonRenyi2Entropy_bound.2
  have h2 := impliedEntropicAction_bounds.1
  linarith

end Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.GeometricEntropy

end
