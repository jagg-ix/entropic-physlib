/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
meta import Zil

/-!
# The quark mass runs with the coupling: `γ_m = −α_s/π`, pole↔MS̄ shift `= C_F` (PDG 2026 §9.1.2)

Extends `QCDBetaFunctionAsymptoticFreedom` with the **running of the quark mass** (PDG 2026 §9.1.2, Eq. 9.6):
just as the coupling runs (`μ² dα_s/dμ² = β`), the `MS̄` quark mass runs,
`μ² dm̄/dμ² = [−α_s/π + O(α_s²)] m̄ = γ_m · m̄`, with the one-loop **mass anomalous dimension** `γ_m = −α_s/π`.

Two things tie this to the color/coupling module already built:

* the mass runs **down** at high scale (`mass_running_negative`) — the same negative sign as asymptotic freedom,
  driven by the same `α_s`, and it **freezes in the UV** `α_s → 0` (`mass_running_uv_free`);
* the **pole↔MS̄ conversion** `m_pole = m̄(1 + (4/3)(α_s/π) + …)` has leading coefficient `4/3 = C_F`, the
  **fundamental color Casimir** (`poleMassShift_casimir`): the same `casimirFundamental 3 = 4/3` of the β-function.
  The pole mass equals the running mass in the UV (`poleMassShift_uv`).

So the quark mass is not a fixed number but a scale-dependent quantity governed by the same `α_s` and the same
`C_F` as the coupling — the mass sector of the running QCD Lagrangian.

* **§A — the mass anomalous dimension** (`massAnomalousDimension`, `massBeta`).
* **§B — the mass runs down (asymptotic)** (`mass_running_negative`, `mass_running_uv_free`).
* **§C — pole↔MS̄ shift is `C_F`** (`poleMassShift`, `poleMassShift_casimir`, `poleMassShift_uv`).
* **§D — assembled** (`quarkMassRunning`).
* **§E — the running-mass RG solution** (`runningMass`, `runningMass_solves_massRG`): `m̄(t) = m₀ e^{γ_m t}`
  is the integral curve of the mass `β`-function — the RGE integrated, not merely recorded.

**Honest layering.** `γ_m = −α_s/π` and the pole↔MS̄ leading coefficient `4/3 = C_F` are exact (`norm_num`);
the sign lemmas are exact `mul_neg`/`div_neg`. The leading-log RGE solution `m̄(t) = m₀ e^{γ_m t}` at fixed
`γ_m` is now integrated (`runningMass_solves_massRG`); the full running-`γ_m` solution and higher-order
series are recorded, not integrated. ## References

* Particle Data Group, PDG 2026 Review, §9.1.2, Eq. 9.6 (`μ² dm̄/dμ² = [−α_s/π]m̄`; `m_pole = m̄(1+4α_s/3π+…)`).
  Repo carrier: `HorizonCell.QCDBetaFunctionAsymptoticFreedom` (`casimirFundamental`, `betaFunction`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDQuarkMassRunning


/-- **The one-loop mass anomalous dimension** `γ_m = −α_s/π` (PDG Eq. 9.6, leading term). -/
noncomputable def massAnomalousDimension (αs : ℝ) : ℝ := -αs / Real.pi

/-- **The mass `β`-function** `μ² dm̄/dμ² = γ_m · m̄` (PDG Eq. 9.6) — the running-mass analogue of the coupling
`β`-function. -/
noncomputable def massBeta (αs m : ℝ) : ℝ := massAnomalousDimension αs * m


/-- **[The quark mass runs down at high scale] `μ² dm̄/dμ² < 0`.** For a positive coupling and positive mass, the
mass `β`-function is negative — the running mass *decreases* with the renormalization scale, the same negative
sign as asymptotic freedom, driven by the same `α_s`. -/
lemma mass_running_negative (αs m : ℝ) (ha : 0 < αs) (hm : 0 < m) : massBeta αs m < 0 := by
  unfold massBeta massAnomalousDimension
  have h1 : -αs / Real.pi < 0 := div_neg_of_neg_of_pos (by linarith) Real.pi_pos
  exact mul_neg_of_neg_of_pos h1 hm

/-- **[The mass running freezes in the UV] `γ_m·m̄ → 0` as `α_s → 0`.** At vanishing coupling (the ultraviolet
limit of asymptotic freedom) the mass anomalous dimension switches off: the running mass becomes scale-independent
in the deep UV. -/
lemma mass_running_uv_free (m : ℝ) : massBeta 0 m = 0 := by
  unfold massBeta massAnomalousDimension; simp


/-- **The pole↔MS̄ mass conversion** `m_pole = m̄ · (1 + (4/3)(α_s/π))` (PDG §9.1.2, leading term) — the factor
relating the pole mass to the running `MS̄` mass. -/
noncomputable def poleMassShift (αs : ℝ) : ℝ := 1 + (4 / 3) * (αs / Real.pi)

/-- **[The pole↔MS̄ shift coefficient is the fundamental Casimir] `4/3 = C_F`.** The leading coefficient of the
pole–`MS̄` conversion is exactly `casimirFundamental 3 = 4/3`, the same `C_F` that governs gluon emission from a
quark in the β-function: `m_pole = m̄(1 + C_F α_s/π + …)`. -/
lemma poleMassShift_casimir (αs : ℝ) :
    poleMassShift αs = 1 + casimirFundamental 3 * (αs / Real.pi) := by
  unfold poleMassShift
  rw [show casimirFundamental 3 = 4 / 3 from by unfold casimirFundamental; norm_num]

/-- **[Pole mass = running mass in the UV] `m_pole/m̄ → 1` as `α_s → 0`.** At vanishing coupling the pole–`MS̄`
shift is unity: the two mass definitions coincide in the deep ultraviolet. -/
lemma poleMassShift_uv : poleMassShift 0 = 1 := by
  unfold poleMassShift; simp


/-- **[The running quark mass, assembled].** For a positive coupling and mass:

* the mass runs down `μ² dm̄/dμ² = γ_m m̄ < 0` (`γ_m = −α_s/π`), freezing as `α_s → 0`;
* the pole↔MS̄ shift is `1 + C_F(α_s/π)` with `C_F = casimirFundamental 3 = 4/3`, becoming unity as `α_s → 0`.

The quark mass is a scale-dependent quantity run by the same `α_s` and the same fundamental Casimir `C_F` as the
coupling — the mass sector of the running QCD Lagrangian. -/
lemma quarkMassRunning (αs m : ℝ) (ha : 0 < αs) (hm : 0 < m) :
    massBeta αs m < 0
      ∧ massBeta 0 m = 0
      ∧ poleMassShift αs = 1 + casimirFundamental 3 * (αs / Real.pi)
      ∧ poleMassShift 0 = 1 :=
  ⟨mass_running_negative αs m ha hm, mass_running_uv_free m,
    poleMassShift_casimir αs, poleMassShift_uv⟩


/-! ### §E — the running-mass RG solution -/

/-- **The one-loop running mass** `m̄(t) = m₀ · e^{γ_m t}`, `t` the renormalization scale time — the integral
curve of the mass RG flow `dm̄/dt = γ_m m̄` at fixed anomalous dimension `γ_m` (leading-log). -/
noncomputable def runningMass (m0 γm t : ℝ) : ℝ := m0 * Real.exp (γm * t)

/-- **[The running mass solves the mass RG flow] `dm̄/dt = γ_m m̄`.** The *integrated* form of the mass
`β`-function: `m̄(t) = m₀ e^{γ_m t}` is the integral curve of `massBeta`, with `γ_m = massAnomalousDimension
α_s` — the mass RGE solved, not merely recorded (the exact analogue of `runningCoupling_solves_rg`). -/
lemma runningMass_solves_massRG (αs m0 t : ℝ) :
    HasDerivAt (runningMass m0 (massAnomalousDimension αs))
      (massBeta αs (runningMass m0 (massAnomalousDimension αs) t)) t := by
  have hlin : HasDerivAt (fun s => massAnomalousDimension αs * s) (massAnomalousDimension αs) t := by
    simpa using (hasDerivAt_id t).const_mul (massAnomalousDimension αs)
  have hm := (hlin.exp).const_mul m0
  have hval : massBeta αs (runningMass m0 (massAnomalousDimension αs) t)
      = m0 * (Real.exp (massAnomalousDimension αs * t) * massAnomalousDimension αs) := by
    unfold massBeta runningMass; ring
  rw [hval]
  exact hm

/-- **[The running mass stays positive] `m̄(t) > 0`** for `m₀ > 0`: the exponential RG flow preserves a
positive mass. -/
lemma runningMass_pos (m0 γm t : ℝ) (hm : 0 < m0) : 0 < runningMass m0 γm t := by
  unfold runningMass; positivity

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDQuarkMassRunning

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDQuarkMassRunning.poleMassShift_casimir where
  formalizes @ "claim:the-pole-to-msbar-quark-mass-shift-leading-coefficient-is-the-fundamental-color-casimir-four-thirds",
  supported_by @ "paper:pdg-2026-review-qcd"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDQuarkMassRunning.runningMass_solves_massRG where
  formalizes @ "claim:the-running-quark-mass-m0-exp-gamma-m-t-solves-the-mass-rg-flow-dm-dt-equals-gamma-m-times-m",
  supported_by @ "paper:pdg-2026-review-qcd",
  caveat @ "claim:the-leading-log-solution-at-fixed-anomalous-dimension-the-full-running-gamma-m-is-not-integrated"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDQuarkMassRunning.quarkMassRunning where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDQuarkMassRunning.poleMassShift_casimir",
  formalizes @ "claim:the-quark-mass-runs-down-with-scale-and-freezes-in-the-uv-driven-by-the-same-alpha-s-and-color-casimir-as-the-coupling",
  requires @ "claim:the-pole-to-msbar-quark-mass-shift-leading-coefficient-is-the-fundamental-color-casimir-four-thirds"

zil_file_contract physlib.qcdQuarkMassRunning where
  promises "The quark mass runs with the coupling: the one-loop mass anomalous dimension is gamma_m = -alpha_s/pi so the mass runs down at high scale and freezes in the UV; the pole-to-MSbar conversion has leading coefficient the fundamental color Casimir four-thirds; and the leading-log RGE is integrated, the running mass m0*exp(gamma_m*t) solving dm/dt = gamma_m*m."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDQuarkMassRunning.massAnomalousDimension",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDQuarkMassRunning.massBeta",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom.casimirFundamental"]
  forbids_substitutes ["the loop computation of the mass anomalous dimension, taken as the PDG input",
    "the full running-gamma_m RGE solution or higher-order series, only the leading-log solution is integrated"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDQuarkMassRunning.poleMassShift_casimir,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDQuarkMassRunning.runningMass_solves_massRG,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDQuarkMassRunning.quarkMassRunning]

/- ZIL-END -/
