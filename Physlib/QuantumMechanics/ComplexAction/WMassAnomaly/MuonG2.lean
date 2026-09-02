/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.EntropicTime
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity

/-!
# Bridge: a conditional muon g-2/W-mass cross-observable law

Replaces the docstring-only "common source" claim of `WMassAnomaly.EntropicTime` with a **theorem-level link**
into the repo's muon `g − 2` arc (`MuonAnomaly.AnomalyRapidity`, `MuonAnomaly.SchmidtRapidityHyperbolicUnification`). There the
muon anomaly is `anomaly η = (schmidtNumber η)² − 1` with the Schmidt number `K = coth η` — which is
*literally* the W-mass file's `entropicDefect K = K² − 1`. So the two are the **same object**:

  `entropicDefect (schmidtNumber η) = anomaly η`   (`entropicDefect_eq_muon_g2`).

A single muon rapidity `η > 0` (entangled, `schmidtNumber η > 1` — `schmidtNumber_gt_one`) then enters **both**
observables through one Schmidt number `K = schmidtNumber η`:

* the positive muon magnetic anomaly `a_μ = anomaly η > 0`, and
* the CDF W-mass excess `M_W > M_W,SM` (the entropic `G_F` shift `−c·entropicDefect(K) < 0`).

`joint_anomaly_fractional_wMass_shift` is the strongest assembled result: the model's fractional W-mass
shift is exactly `κ c a_μ`. This is a potentially testable cross-observable *form*, but it is not a
parameter-free numerical W-mass prediction because `c` (and the electroweak coefficient `κ`) must be fixed
independently. In particular, using the CDF-2022 W mass to choose `c` is a fit, not a prediction.

**Honest layering.** Proven: that the W-mass `entropicDefect` and the muon `anomaly` are the same `K² − 1`
(a consistency identity in the repo's definitions), and that the stated positive-coefficient ansatz yields
the W-shift sign and the exact fractional cross-law. Unchanged from
`WMassAnomaly.EntropicTime` / `…EntropicLagrangian`: the entropic-shift *form* `−c(K²−1)` (or its derived
`e^{−S_I/ħ}−1`) and the proportionality `c` remain the ansatz/derivation already discussed — this file only
*identifies the entropic defect with the muon anomaly*, it does not change the normalization caveat.
`MuonAnomaly.AnomalyRapidity.fermilabMagicGamma_determines_schmidtNumber` operationally reconstructs `K`
from storage-ring kinematics. Because the magic operating point is anomaly-dependent, this is not an
independent prediction of `a_μ`, nor is it a direct QFT Schmidt-spectrum measurement. In light of
the 2025 Theory Initiative update, “muon anomaly” here means the magnetic quantity `(g−2)/2`, not an asserted
unresolved Standard-Model discrepancy.

## References

* M. Endo, S. Mishima, Phys. Rev. D **106** (2022) 115005. `Physlib` (`WMassAnomaly.EntropicTime`,
  `MuonAnomaly.AnomalyRapidity` — `anomaly_eq_schmidt_sq_sub_one`,
  `MuonAnomaly.SchmidtRapidityHyperbolicUnification.schmidtNumber_gt_one`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.EntropicTime
open Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.GFShift
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.MuonG2

/-- **[The W-mass entropic defect is the muon g-2 anomaly]** `entropicDefect (schmidtNumber η) = anomaly η`
— the `K² − 1` that the W-mass `G_F` shift uses is *identically* the muon anomalous moment (Schmidt number
`K = coth η`). The "common entropic source" is an identity in the repo's definitions, not an assumption. -/
lemma entropicDefect_eq_muon_g2 (η : ℝ) (hη : 0 < η) :
    entropicDefect (schmidtNumber η) = anomaly η := by
  unfold entropicDefect
  exact (anomaly_eq_schmidt_sq_sub_one η hη).symm

/-- **[One muon rapidity enters both observables]** for a muon rapidity `η > 0` (entangled, Schmidt number
`> 1`), the **same** Schmidt number `K = schmidtNumber η` produces the muon `g − 2` excess
`a_μ = anomaly η > 0` **and**, conditionally on the entropic `G_F` ansatz, a positive W-mass shift
`M_W > M_W,SM` (with `κ > 0`, `c > 0`, `M_W,SM > 0`). This proves the direction of the shift, not its
CDF-2022 magnitude. -/
lemma joint_anomaly_muon_rapidity (mWsm κ c η : ℝ)
    (hm : 0 < mWsm) (hκ : 0 < κ) (hc : 0 < c) (hη : 0 < η) :
    0 < anomaly η
      ∧ mWsm < correctedWMass mWsm κ (entropicGFShift c (schmidtNumber η)) :=
  ⟨anomaly_pos η hη,
    wMass_raised_by_entropic_muon mWsm κ c (schmidtNumber η) hm hκ hc (schmidtNumber_gt_one η hη)⟩

/-- **[Exact conditional muon/W cross-law]** under the repository's entropic `G_F` ansatz, the fractional
W-mass shift is exactly `κ c` times the muon magnetic anomaly:

`(M_W - M_W,SM) / M_W,SM = κ c a_μ`.

Unlike `entropicDefect_eq_muon_g2`, this relates two observables. Its normalization is nevertheless
ansatz-loaded: it becomes a numerical prediction only after `κ` and especially `c` are fixed without using
the W-mass datum being tested. -/
lemma joint_anomaly_fractional_wMass_shift (mWsm κ c η : ℝ)
    (hm : 0 < mWsm) (hκ : 0 < κ) (hc : 0 < c) (hη : 0 < η) :
    0 < anomaly η
      ∧ mWsm < correctedWMass mWsm κ (entropicGFShift c (schmidtNumber η))
      ∧ (correctedWMass mWsm κ (entropicGFShift c (schmidtNumber η)) - mWsm) / mWsm =
        κ * c * anomaly η := by
  have hjoint := joint_anomaly_muon_rapidity mWsm κ c η hm hκ hc hη
  refine ⟨hjoint.1, hjoint.2, ?_⟩
  rw [← entropicDefect_eq_muon_g2 η hη]
  unfold correctedWMass entropicGFShift
  field_simp [hm.ne']
  ring

end Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.MuonG2

end
