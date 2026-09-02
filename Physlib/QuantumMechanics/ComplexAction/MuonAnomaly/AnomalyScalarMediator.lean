/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment

/-!
# A scalar mediator's one-loop contribution to the muon `g − 2` (corrected formula)

A new scalar `S` of mass `Λ` with Yukawa coupling `g` to the muon contributes to the anomalous magnetic
moment at one loop. The **correct** leading heavy-mediator form is

  `a_μ^S = (g²/8π²)·(m_μ/Λ)²·F`,   `F = O(1)` loop function,

with the characteristic **mediator suppression `(m_μ/Λ)²`** of any heavy new-physics contribution to `g − 2`.
This file formalizes that (with `F = 1` for the estimate) on the repo's verified `gFactor` / `schwingerAnomaly`
(`FirstQuantizedQED.AnomalousMagneticMoment`), and uses it to **correct** the broken derivation in the source material.

**What the source got wrong, and the fix.** The source (`cat_ept_paper2_particle_physics`, §IV) wrote the
simplified result `a_μ ≈ (g²/96π²)·ln(Λ/m_μ)` — which *dropped the `(m_μ/Λ)²` mediator suppression*, keeping
only the log (and its "master" formula carried a leftover `1/m_μ²`, so `a_μ` was not even dimensionless). It
then quoted `g = 0.075, Λ = 10 GeV ⟹ a_μ = 251×10⁻¹¹`, but `(0.075)²/96π²·ln(10⁴/106) = 2.7×10⁻⁵`, off from
`251×10⁻¹¹` by ~`10⁴` (a units error: `10⁻⁵` was mislabelled as `10⁻¹¹`-scale). The corrected formula with
`(m_μ/Λ)²` restored gives, for `g = 0.09, Λ = 10 GeV`, `a_μ^S ≈ 1.2×10⁻⁸ ≈ 1150×10⁻¹¹` — the *right order of
magnitude* of the `Δa_μ = 251(59)×10⁻¹¹` anomaly. The exact value is then a **one-parameter fit** (fix `Λ`,
solve for `g`): `scalarMediator_fit`.

* **§A — the corrected contribution.** `scalarMediatorAnomaly g m Λ = (g²/8π²)(m/Λ)²`; `_nonneg`/`_pos`;
  `scalarMediatorAnomaly_ratio_invariant`: it depends only on the *dimensionless* ratio `m/Λ` — the
  dimensional-analysis content (rescaling `m, Λ` together leaves it unchanged).
* **§B — assembly on the verified g-factor.** `totalAnomaly = schwingerAnomaly α + scalarMediatorAnomaly`;
  `gFactor_totalAnomaly` (`g = 2(1 + a_QED + a_S)`); `totalAnomaly_gt_schwinger` (the scalar raises `a` above
  the pure-QED Schwinger value).
* **§C — the honest one-parameter fit.** `scalarMediator_fit`: any target `Δ` is reproduced by
  `g² = Δ·8π²·(Λ/m)²` — a fit at fixed `Λ`, not a prediction.

**Honest layering.** Genuine: the one-loop scalar contribution scales as `(g²/8π²)(m/Λ)²` (the textbook
heavy-mediator form, restoring the suppression the source dropped); dimensionally consistent; the QED part is
the verified `schwingerAnomaly`. The exact `O(1)` loop function `F` (scalar vs pseudoscalar sign and number)
is set to `1` for the estimate. The anomaly *value* is **not predicted** — it is a one-parameter fit (the
generation/coupling values are open input).

## References

* Standard one-loop scalar contribution to `g − 2` (heavy-mediator `(m/Λ)²` suppression); J. Schwinger 1948.
  `Physlib` (`FirstQuantizedQED.AnomalousMagneticMoment.gFactor`/`schwingerAnomaly`). Corrects
  `cat_ept_paper2_particle_physics` §IV.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyScalarMediator


/-- **The one-loop scalar-mediator anomalous moment** `a_μ^S = (g²/8π²)(m/Λ)²` — coupling `g`, lepton mass
`m`, mediator mass `Λ`, with the characteristic heavy-mediator suppression `(m/Λ)²` (`O(1)` loop function
set to `1`). -/
noncomputable def scalarMediatorAnomaly (g m Λ : ℝ) : ℝ := g ^ 2 / (8 * Real.pi ^ 2) * (m / Λ) ^ 2

/-- **[Nonnegative]** `a_μ^S ≥ 0`. -/
lemma scalarMediatorAnomaly_nonneg (g m Λ : ℝ) : 0 ≤ scalarMediatorAnomaly g m Λ := by
  unfold scalarMediatorAnomaly; positivity

/-- **[Positive]** `a_μ^S > 0` for nonzero coupling, mass, mediator. -/
lemma scalarMediatorAnomaly_pos (g m Λ : ℝ) (hg : g ≠ 0) (hm : m ≠ 0) (hΛ : Λ ≠ 0) :
    0 < scalarMediatorAnomaly g m Λ := by
  unfold scalarMediatorAnomaly; positivity

/-- **[Dimensional analysis: depends only on the ratio `m/Λ`]** rescaling the lepton and mediator masses
together (`m, Λ ↦ t m, t Λ`) leaves the contribution unchanged — `a_μ^S` is a function of the *dimensionless*
ratio `m/Λ` alone (and the dimensionless coupling). This is the suppression the source dropped. -/
lemma scalarMediatorAnomaly_ratio_invariant (g m Λ t : ℝ) (ht : t ≠ 0) :
    scalarMediatorAnomaly g (t * m) (t * Λ) = scalarMediatorAnomaly g m Λ := by
  unfold scalarMediatorAnomaly
  rw [mul_div_mul_left _ _ ht]


/-- **The total anomalous moment** `a = a_μ^{QED} + a_μ^S = α/(2π) + (g²/8π²)(m/Λ)²` — the verified Schwinger
term plus the scalar mediator. -/
noncomputable def totalAnomaly (α g m Λ : ℝ) : ℝ := schwingerAnomaly α + scalarMediatorAnomaly g m Λ

/-- **[`g`-factor with the scalar mediator]** `g = 2(1 + a_QED + a_S)`. -/
lemma gFactor_totalAnomaly (α g m Λ : ℝ) :
    gFactor (totalAnomaly α g m Λ) = 2 * (1 + (schwingerAnomaly α + scalarMediatorAnomaly g m Λ)) := by
  rw [gFactor, totalAnomaly]

/-- **[The scalar raises `a` above the pure-QED value]** `α/(2π) < a_QED + a_S` when the scalar contribution
is positive — the mediator adds to the Schwinger anomaly. -/
lemma totalAnomaly_gt_schwinger (α g m Λ : ℝ) (h : 0 < scalarMediatorAnomaly g m Λ) :
    schwingerAnomaly α < totalAnomaly α g m Λ := by
  unfold totalAnomaly; linarith


/-- **[One-parameter fit to a target]** the scalar mediator reproduces *any* target anomaly `Δ` by choosing
the coupling `g² = Δ·8π²·(Λ/m)²` at fixed mediator mass `Λ`. So matching `Δa_μ = 251×10⁻¹¹` is a one-parameter
**fit** (e.g. `g ≈ 4×10⁻²` for `Λ = 10 GeV`), not a derivation of the value. -/
lemma scalarMediator_fit (m Λ Δ : ℝ) (hm : m ≠ 0) (hΛ : Λ ≠ 0) (g : ℝ)
    (hg : g ^ 2 = Δ * (8 * Real.pi ^ 2) * (Λ / m) ^ 2) :
    scalarMediatorAnomaly g m Λ = Δ := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold scalarMediatorAnomaly
  rw [hg]
  field_simp

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyScalarMediator

end
