/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.WBosonMassElectroweak

/-!
# The CDF-II W-mass anomaly: the Fermi-constant-shift mechanism

The CDF Collaboration measured `M_W = 80.4335 ± 0.0094 GeV`, a `7σ` excess over the Standard-Model prediction
`M_W,SM = 80.3500 ± 0.0056 GeV`. M. Endo and S. Mishima, *New physics interpretation of W-boson mass anomaly*,
Phys. Rev. D **106** (2022) 115005, interpret this as new physics shifting the **Fermi coupling constant**
`G_F` (measured from muon decay) — the "third possibility", distinct from the oblique `S, T` parameters. Their
Eq. (11) gives the corrected mass

  `M_W = (M_W)_SM · [ 1 − (s_W²/(2(c_W²−s_W²))) δ_{G_F} ]`,

where `δ_{G_F}` is the fractional `G_F` shift from the dimension-six operators `O_{φℓ}^{(3)}` and `O_{ℓℓ}`.

**Verdict on the base model.** The tree-level electroweak model (`WMassAnomaly.WBosonMassElectroweak`) proves the exact SM
relation `M_W = M_Z cos θ_W` and `ρ = 1` (`rho_parameter_one`) — which is *precisely* the relation the CDF
value deviates from. So the unextended model predicts `M_W,SM` and does **not** explain the excess. It can
**accommodate** it only via the `G_F`-shift correction below — and this file proves the **sign/structure**
condition: the excess (`M_W > M_W,SM`) requires `δ_{G_F} < 0` (matching the paper's `C_{φℓ}^{(3)} < 0`).

* **§A — the correction.** `gfShiftCoefficient s_W² c_W² = s_W²/(2(c_W²−s_W²))`, `correctedWMass`, and the SM
  limit `correctedWMass_sm_limit` (`δ_{G_F}=0 ⇒ M_W = M_W,SM`).
* **§B — the anomaly direction.** `gfShiftCoefficient_pos` (`κ > 0` since `c_W² > s_W²`) and
  `wMass_raised_iff_negative_gfShift` (`M_W > M_W,SM ⟺ δ_{G_F} < 0`); the main result
  `cdf_anomaly_requires_negative_gfShift`.

**Honest layering.** Proven: the *algebra and sign* of the `G_F`-shift correction — that a negative `δ_{G_F}`
(with `κ>0`) raises `M_W`, the only direction that fits CDF. NOT proven / NOT claimed: `δ_{G_F}` is the free
new-physics Wilson coefficient (an input, here arbitrary), *not* derived from CAT/EPT or any first principle;
its numerical value (`δ_{G_F} ≈ −5×10⁻³`), the multi-TeV mediators, and the global SMEFT fit are the paper's
content. So the model **parametrizes** the anomaly with the correct structure; it does not **predict** or
uniquely explain its origin.

## References

* M. Endo, S. Mishima, *New physics interpretation of W-boson mass anomaly*, Phys. Rev. D **106** (2022)
  115005, doi:10.1103/PhysRevD.106.115005 (Eq. 11; `δ_{G_F}` from `O_{φℓ}^{(3)}`, `O_{ℓℓ}`). CDF
  Collaboration, *Science* **376** (2022) 170. `Physlib` (`WMassAnomaly.WBosonMassElectroweak`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.GFShift


/-- The **`G_F`-shift coefficient** `κ = s_W²/(2(c_W²−s_W²))` of Eq. (11) (`s_W² = sin²θ_W`,
`c_W² = cos²θ_W`). -/
noncomputable def gfShiftCoefficient (sW2 cW2 : ℝ) : ℝ := sW2 / (2 * (cW2 - sW2))

/-- The **corrected W-boson mass** `M_W = (M_W)_SM · (1 − κ δ_{G_F})` (Eq. 11), with `κ` the `G_F`-shift
coefficient and `δ_{G_F}` the fractional shift of the Fermi constant. -/
def correctedWMass (mWsm κ δGF : ℝ) : ℝ := mWsm * (1 - κ * δGF)

/-- **[SM limit]** `δ_{G_F} = 0 ⇒ M_W = M_W,SM` — no `G_F` shift recovers the Standard-Model prediction (the
relation `ρ=1`, `WMassAnomaly.WBosonMassElectroweak.rho_parameter_one`, that the CDF value deviates from). -/
lemma correctedWMass_sm_limit (mWsm κ : ℝ) : correctedWMass mWsm κ 0 = mWsm := by
  simp [correctedWMass]


/-- **[The shift coefficient is positive]** `κ = s_W²/(2(c_W²−s_W²)) > 0` since `0 < s_W² < c_W²`
(physically `sin²θ_W ≈ 0.223 < 0.777 ≈ cos²θ_W`). -/
lemma gfShiftCoefficient_pos (sW2 cW2 : ℝ) (hs : 0 < sW2) (h : sW2 < cW2) :
    0 < gfShiftCoefficient sW2 cW2 := by
  unfold gfShiftCoefficient
  exact div_pos hs (by linarith)

/-- **[The CDF excess requires a negative `G_F` shift] `M_W > M_W,SM ⟺ δ_{G_F} < 0`** (for `κ > 0`,
`M_W,SM > 0`) — the only direction of the Fermi-constant shift that can lift the W mass above its SM value, in
agreement with the paper's `C_{φℓ}^{(3)} < 0`. -/
lemma wMass_raised_iff_negative_gfShift (mWsm κ δGF : ℝ) (hm : 0 < mWsm) (hκ : 0 < κ) :
    mWsm < correctedWMass mWsm κ δGF ↔ δGF < 0 := by
  unfold correctedWMass
  constructor
  · intro hlt; nlinarith [mul_pos hm hκ]
  · intro hδ; nlinarith [mul_pos hm hκ]

/-- **[The CDF W-mass anomaly is accommodated exactly when `δ_{G_F} < 0`]** the model fits the excess
`M_W > M_W,SM` if and only if the new-physics Fermi-constant shift is negative (with `κ > 0` guaranteed by
`s_W² < c_W²`). The W mass is *parametrized* by `δ_{G_F}` with the correct sign; the value of `δ_{G_F}` is the
free new-physics input, not derived here. -/
lemma cdf_anomaly_requires_negative_gfShift
    (mWsm δGF sW2 cW2 : ℝ) (hm : 0 < mWsm) (hs : 0 < sW2) (h : sW2 < cW2) :
    mWsm < correctedWMass mWsm (gfShiftCoefficient sW2 cW2) δGF ↔ δGF < 0 :=
  wMass_raised_iff_negative_gfShift mWsm (gfShiftCoefficient sW2 cW2) δGF hm
    (gfShiftCoefficient_pos sW2 cW2 hs h)

end Physlib.QuantumMechanics.ComplexAction.WMassAnomaly.GFShift

end
