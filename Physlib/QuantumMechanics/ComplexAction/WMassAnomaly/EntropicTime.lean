/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.GFShift

/-!
# Entropic-time re-evaluation of the W-mass anomaly: the common muon-sector source

A re-evaluation of the CDF W-mass anomaly through the repo's **entropic-time / rapidity** lens, the same one
used for the muon `g − 2`. There the anomaly is reframed (`MuonAnomaly.AnomalyRapidity.anomaly_eq_schmidt_sq_sub_one`)
as an **entanglement defect**

  `a_μ = K² − 1`,

with `K = coth η` the **Schmidt number** (the entropic/rapidity measure); the Schwinger value is recovered as
`K² = 1 + α/2π`, so `K > 1` *is* the anomaly.

**The isolation.** The Fermi constant `G_F` that fixes `M_W` (Endo–Mishima Eq. 11, `WMassAnomaly.GFShift`) is
extracted from **muon decay** — the *same* muon. So the `M_W` calculation, re-evaluated, must include the muon's
entropic factor. The proposed entropic-time term is

  `δ_{G_F} = −c (K² − 1)`   (`c > 0`),

an **entropic attenuation** of the effective muon coupling (the `e^{−S_I/ħ}`-type weight of the dynamics
files), proportional to the *same* entanglement defect that gives `g − 2`. Then a single condition — the muon
being entropically entangled, `K > 1` — produces **both** excesses at once:

* the `g − 2` excess `a_μ = K² − 1 > 0`, and
* the `W`-mass excess `M_W > M_W,SM` (because `δ_{G_F} < 0`, the CDF direction).

* **§A — the shared entropic defect** `entropicDefect K = K² − 1` (`entropicDefect_pos`, `K>1 ⇒ > 0`).
* **§B — the entropic `G_F` shift** `entropicGFShift c K = −c(K²−1)`, negative for `K>1`, `c>0`
  (`entropicGFShift_neg`).
* **§C — one source, two anomalies** `wMass_raised_by_entropic_muon`, and the main result
  `joint_anomaly_same_entropic_source` (the `g−2` and `W`-mass excesses follow from the single `K>1`).

**Honest layering — strong caveat.** This is a *proposed entropic ansatz*, not a derivation. Proven: the
**sign/structure** — that the muon entanglement `K>1` makes `δ_{G_F}<0` and hence raises `M_W`, the *same* `K`
that makes `g−2` positive, so the two anomalies share one source with a definite sign correlation (a
*relation*, the genuine falsifiable content, in the spirit of the rapidity-defect g-2 file). NOT proven / NOT
claimed: the functional form `δ_{G_F} = −c(K²−1)` and the constant `c` are an **input ansatz**, not derived
from a Lagrangian; the numerical coincidence (`a_μ ∼ 10⁻³`, `δ_{G_F} ∼ −5×10⁻³`, i.e. `c` a few) is suggestive
only. The claim is structural: *if* the W-mass `G_F` inherits the muon's entropic defect, the CDF sign follows
and ties to `g−2`.

## References

* M. Endo, S. Mishima, Phys. Rev. D **106** (2022) 115005 (`δ_{G_F}` → `M_W`). `Physlib`
  (`WMassAnomaly.GFShift`, `MuonAnomaly.AnomalyRapidity` — the `a = K²−1` Schmidt defect,
  `QuantumChemistry.TimeEvolution` — the entropic weight `e^{−S_I/ħ}`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.GFShift

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.EntropicTime


/-- The **entropic defect** `K² − 1` — the muon's entanglement defect from the unentangled value `K = 1`. In
the repo's g-2 formalization this *is* the muon anomaly (`a_μ = K² − 1`, Schmidt number `K`). -/
def entropicDefect (K : ℝ) : ℝ := K ^ 2 - 1

/-- **[An entangled muon has a positive defect]** `K > 1 ⇒ K² − 1 > 0` — the `g − 2` excess. -/
lemma entropicDefect_pos (K : ℝ) (hK : 1 < K) : 0 < entropicDefect K := by
  unfold entropicDefect; nlinarith


/-- The **entropic `G_F` shift** `δ_{G_F} = −c (K² − 1)` — an entropic attenuation (`c > 0`) of the effective
muon coupling, proportional to the same entanglement defect that produces `g − 2`. -/
def entropicGFShift (c K : ℝ) : ℝ := -c * entropicDefect K

/-- **[The entropic shift is negative for an entangled muon]** `c > 0`, `K > 1 ⇒ δ_{G_F} < 0` — exactly the
sign (`WMassAnomaly.GFShift`) that raises `M_W` to the CDF value. -/
lemma entropicGFShift_neg (c K : ℝ) (hc : 0 < c) (hK : 1 < K) : entropicGFShift c K < 0 := by
  unfold entropicGFShift; nlinarith [mul_pos hc (entropicDefect_pos K hK)]


/-- **[The W-mass excess from the muon's entropic defect]** for `K > 1` (entangled muon), `c > 0`, and the
positive electroweak coefficient `κ > 0`, the entropic `G_F` shift raises the W mass above its SM value,
`M_W > M_W,SM` — the CDF anomaly, sourced by the muon entanglement. -/
lemma wMass_raised_by_entropic_muon (mWsm κ c K : ℝ)
    (hm : 0 < mWsm) (hκ : 0 < κ) (hc : 0 < c) (hK : 1 < K) :
    mWsm < correctedWMass mWsm κ (entropicGFShift c K) :=
  (wMass_raised_iff_negative_gfShift mWsm κ (entropicGFShift c K) hm hκ).mpr
    (entropicGFShift_neg c K hc hK)

/-- **[One source, two anomalies]** the single condition `K > 1` — the muon being entropically entangled
(Schmidt number above the unentangled value) — produces simultaneously the `g − 2` excess `a_μ = K² − 1 > 0`
**and** the `W`-mass excess `M_W > M_W,SM`. The proposed entropic-time re-evaluation isolates the W-mass
`δ_{G_F}` to the very same muon entropic defect as the muon anomalous moment. -/
lemma joint_anomaly_same_entropic_source (mWsm κ c K : ℝ)
    (hm : 0 < mWsm) (hκ : 0 < κ) (hc : 0 < c) (hK : 1 < K) :
    0 < entropicDefect K ∧ mWsm < correctedWMass mWsm κ (entropicGFShift c K) :=
  ⟨entropicDefect_pos K hK, wMass_raised_by_entropic_muon mWsm κ c K hm hκ hc hK⟩

/-- **[Full electroweak form]** the joint result with the explicit electroweak coefficient
`κ = s_W²/(2(c_W²−s_W²))` (positive since `0 < s_W² < c_W²`): one muon entropic defect `K>1` drives both the
`g−2` and the CDF `W`-mass excess. -/
lemma joint_anomaly_electroweak (mWsm c K sW2 cW2 : ℝ)
    (hm : 0 < mWsm) (hc : 0 < c) (hK : 1 < K) (hs : 0 < sW2) (hsc : sW2 < cW2) :
    0 < entropicDefect K
      ∧ mWsm < correctedWMass mWsm (gfShiftCoefficient sW2 cW2) (entropicGFShift c K) :=
  ⟨entropicDefect_pos K hK,
    wMass_raised_by_entropic_muon mWsm (gfShiftCoefficient sW2 cW2) c K hm
      (gfShiftCoefficient_pos sW2 cW2 hs hsc) hc hK⟩

end Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.EntropicTime

end
