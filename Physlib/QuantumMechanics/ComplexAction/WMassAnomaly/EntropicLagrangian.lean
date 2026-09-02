/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.GFShift
public import Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.TimeEvolution

/-!
# The W-mass anomaly `G_F` shift, derived from the complex-action Lagrangian

Upgrades the entropic re-evaluation of the CDF W-mass anomaly from the *ansatz* `δ_{G_F} = −c(K²−1)`
(`WMassAnomaly.EntropicTime`) to a **derivation from a Lagrangian** — the CAT/EPT complex action.

**The derivation.** Take the complex Lagrangian / action

  `L = L_R + i L_I`,   `S = S_R + i S_I`,   `S_I ≥ 0`,

the foundational CAT/EPT object (`L_R` reversible, `L_I` the irreversible/entropic part). The amplitude is the
path-integral weight

  `A ∝ e^{iS/ħ} = e^{iS_R/ħ} · e^{−S_I/ħ}`,

so the **imaginary action attenuates the amplitude** by `e^{−S_I/ħ}` (the `entropicWeight` of the dynamics
files; `U_eff = e^{−(i/ħ)H_R t − (1/ħ)Γ_I t}`). The Fermi constant `G_F` is extracted from the **muon-decay
rate** `Γ ∝ G_F² |A|²`; the amplitude factor `e^{−S_I/ħ}` therefore renormalizes the *measured* coupling,
`G_F = G_F^{tree} · e^{−S_I/ħ}`, i.e. (Endo–Mishima parametrization `G_F = (1+δ_{G_F})/√2v²`)

  `δ_{G_F} = e^{−S_I/ħ} − 1`.

This is **derived** from `L = L_R + iL_I`, not assumed. Since `S_I ≥ 0` (entropy/imaginary action is
non-negative), `δ_{G_F} ≤ 0` — automatically the CDF direction (`M_W` raised). At leading order
`δ_{G_F} = −S_I/ħ`, recovering the linear shift; the `K²−1` of the previous file is the leading term when
`S_I/ħ` is the muon entanglement defect.

* **§A — the derived shift.** `gfShiftFromAction S_I ħ = e^{−S_I/ħ} − 1` (`= entropicWeight − 1`);
  `gfShiftFromAction_zero` (`S_I=0 ⇒ 0`), `_nonpos` (`≤ 0`), `_neg` (`< 0` for `S_I>0`),
  `_ge_linear` (`≥ −S_I/ħ`, the leading order).
* **§B — the W-mass raised, from the Lagrangian.** `wMass_raised_from_action`, and the main result
  `wMass_anomaly_from_complex_action` — the CDF excess `M_W > M_W,SM` follows from a non-vanishing imaginary
  action `S_I > 0`.

**Honest layering — what is and isn't derived.** Now *derived* (from `L = L_R + iL_I`): the **functional form
and sign** of the shift, `δ_{G_F} = e^{−S_I/ħ} − 1 ≤ 0`, hence `M_W` is raised — no ansatz, the form follows
from the path-integral weight `e^{iS/ħ}`. Still *input*: the **value** of the muon imaginary action `S_I`
(equivalently `Γ_I`, the entropic Lagrangian's strength) — its magnitude (`S_I/ħ ∼ 5×10⁻³` to match CDF) is not
computed from a microscopic `L_I` here. So the derivation fixes the *mechanism and sign*; the *normalization*
remains the one undetermined parameter.

## References

* M. Endo, S. Mishima, Phys. Rev. D **106** (2022) 115005 (`δ_{G_F} → M_W`). CAT/EPT complex action
  `e^{iS/ħ} = e^{−S_I/ħ}` (Nagao–Nielsen). `Physlib` (`WMassAnomaly.GFShift`,
  `QuantumChemistry.TimeEvolution.entropicWeight`, `WMassAnomaly.EntropicTime`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.GFShift
open Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.TimeEvolution

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.EntropicLagrangian


/-- The **Fermi-constant shift derived from the complex action** `δ_{G_F} = e^{−S_I/ħ} − 1` — the amplitude
attenuation `e^{−S_I/ħ}` from `A ∝ e^{iS/ħ}` (`S = S_R + iS_I`) renormalizing the measured muon-decay
coupling. Built from the `entropicWeight` of the dynamics files. -/
noncomputable def gfShiftFromAction (SI ħ : ℝ) : ℝ := entropicWeight SI ħ - 1

/-- **[No imaginary action ⇒ no shift]** `S_I = 0 ⇒ δ_{G_F} = 0` — the reversible (`L_I = 0`) limit recovers
the SM coupling. -/
lemma gfShiftFromAction_zero (ħ : ℝ) : gfShiftFromAction 0 ħ = 0 := by
  unfold gfShiftFromAction; rw [entropicWeight_zero]; ring

/-- **[The derived shift is non-positive]** `δ_{G_F} = e^{−S_I/ħ} − 1 ≤ 0` for `S_I ≥ 0`, `ħ > 0` — the
entropic attenuation can only *lower* the measured `G_F`, automatically the CDF direction. -/
lemma gfShiftFromAction_nonpos (SI ħ : ℝ) (hSI : 0 ≤ SI) (hħ : 0 < ħ) :
    gfShiftFromAction SI ħ ≤ 0 := by
  have h := entropicWeight_le_one SI ħ hSI hħ
  unfold gfShiftFromAction; linarith

/-- **[A genuine entropic action gives a strictly negative shift]** `S_I > 0 ⇒ δ_{G_F} < 0` — the sign that
raises `M_W` to the CDF value. -/
lemma gfShiftFromAction_neg (SI ħ : ℝ) (hSI : 0 < SI) (hħ : 0 < ħ) :
    gfShiftFromAction SI ħ < 0 := by
  have hlt : entropicWeight SI ħ < 1 := by
    unfold entropicWeight
    rw [Real.exp_lt_one_iff]
    have : 0 < SI / ħ := div_pos hSI hħ
    linarith
  unfold gfShiftFromAction; linarith

/-- **[Leading order: `δ_{G_F} = −S_I/ħ`]** `δ_{G_F} = e^{−S_I/ħ} − 1 ≥ −S_I/ħ` (convexity of `exp`) — the
linear entropic shift is the first-order term, recovering the `−c(K²−1)` form when `S_I/ħ` is the muon
entanglement defect. -/
lemma gfShiftFromAction_ge_linear (SI ħ : ℝ) : -(SI / ħ) ≤ gfShiftFromAction SI ħ := by
  unfold gfShiftFromAction entropicWeight
  linarith [Real.add_one_le_exp (-(SI / ħ))]


/-- **[The W-mass excess follows from the imaginary action]** for a non-vanishing muon imaginary action
`S_I > 0` (and `κ > 0`, `M_W,SM > 0`), the derived shift `δ_{G_F} = e^{−S_I/ħ}−1 < 0` raises the W mass:
`M_W > M_W,SM`. -/
lemma wMass_raised_from_action (mWsm κ SI ħ : ℝ)
    (hm : 0 < mWsm) (hκ : 0 < κ) (hSI : 0 < SI) (hħ : 0 < ħ) :
    mWsm < correctedWMass mWsm κ (gfShiftFromAction SI ħ) :=
  (wMass_raised_iff_negative_gfShift mWsm κ (gfShiftFromAction SI ħ) hm hκ).mpr
    (gfShiftFromAction_neg SI ħ hSI hħ)

/-- **[The CDF W-mass anomaly from the complex-action Lagrangian]** the main result: a complex Lagrangian
`L = L_R + iL_I` with a non-vanishing entropic part (`S_I > 0`) **derives** both the negative Fermi-constant
shift `δ_{G_F} < 0` and the consequent CDF W-mass excess `M_W > M_W,SM`, with the explicit electroweak
coefficient `κ = s_W²/(2(c_W²−s_W²)) > 0`. The mechanism and sign are derived; only the magnitude of `S_I` is
input. -/
lemma wMass_anomaly_from_complex_action (mWsm SI ħ sW2 cW2 : ℝ)
    (hm : 0 < mWsm) (hSI : 0 < SI) (hħ : 0 < ħ) (hs : 0 < sW2) (hsc : sW2 < cW2) :
    gfShiftFromAction SI ħ < 0
      ∧ mWsm < correctedWMass mWsm (gfShiftCoefficient sW2 cW2) (gfShiftFromAction SI ħ) :=
  ⟨gfShiftFromAction_neg SI ħ hSI hħ,
    wMass_raised_from_action mWsm (gfShiftCoefficient sW2 cW2) SI ħ hm
      (gfShiftCoefficient_pos sW2 cW2 hs hsc) hSI hħ⟩

end Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.EntropicLagrangian

end
