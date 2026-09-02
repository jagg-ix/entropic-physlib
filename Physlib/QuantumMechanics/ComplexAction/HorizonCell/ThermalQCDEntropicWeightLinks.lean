/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator

/-!
# The thermal QCD coupling on the entropic-weight hub: Boltzmann = kuiken = confinement (repo links)

Binds `ThermalQCDRunningCoupling` (van Eijck–Stephens–van Weert, hep-ph/9308227) into the rest of the repository
so other modules can reuse it. The finite-temperature QCD coupling was previously chained only to the vacuum
β-function module; here its **temperature** is connected to the repository's thermofield / Matsubara machinery and
its **high-temperature = infrared** limit to the confinement hub, all through one identity.

**The unifying identity.** The Matsubara Gibbs weight `matsubaraBoltzmannWeight β E = e^{−βE}`
(`ThermoFieldDynamics.MatsubaraThermalOscillator`) is *exactly* the entropic weight
`kuikenWeight c Π = e^{−Π/c}` at temperature `c = 1/β` (`boltzmann_is_kuiken`). The confinement area law is the
*same* `kuikenWeight` (`areaLaw_is_kuikenWeight`, `wilsonAreaLaw = kuikenWeight 1 (σA)`). So the thermal Gibbs
weight, the confinement suppression, and the complex-action master weight all live on one `e^{−·/·}` hub — and the
finite-`T` QCD coupling is wired onto it.

Reusable consequences:

* the **Boltzmann weight obeys the generalized second law** (`thermal_boltzmann_le_one`,
  `thermal_boltzmann_antitone`) — reusing the arc's `kuikenWeight_le_one`/`kuikenWeight_antitone`;
* **raising the temperature weakens the suppression** (`kuikenWeight_monotone_in_temperature`) — a new, generally
  useful monotonicity of `e^{−E/T}` in `T`, complementary to the `Π`-monotonicity of the GSL;
* the **high-`T` = infrared = confinement** regime is exhibited together (`high_temp_is_confinement_regime`): the
  thermal coupling's β is strongly-coupled negative while the confinement area law tightens — one IR;
* the **vacuum / thermal / confinement weights sit on one hub** (`thermal_qcd_on_entropic_hub`).

* **§A — Boltzmann weight = kuiken weight** (`boltzmann_is_kuiken`).
* **§B — higher temperature weakens the weight** (`kuikenWeight_monotone_in_temperature`).
* **§C — the Boltzmann weight obeys the GSL** (`thermal_boltzmann_le_one`, `thermal_boltzmann_antitone`).
* **§D — high-`T` = IR = confinement** (`high_temp_is_confinement_regime`).
* **§E — assembled on the entropic hub** (`thermal_qcd_on_entropic_hub`).

**Honest layering.** `boltzmann_is_kuiken` and the temperature monotonicity are exact `Real.exp` identities; the
GSL reuses `ElectronExclusionEntropyProduction`. `high_temp_is_confinement_regime` juxtaposes the two exact IR
facts (`betaHighTemp_neg`, `confinement_obeys_gsl`) — it is an identification of regimes, not a derivation of the
deconfinement transition (no `T_c` is constructed). ## References

* van Eijck–Stephens–van Weert, hep-ph/9308227. Repo carriers: `HorizonCell.ThermalQCDRunningCoupling`,
  `ThermoFieldDynamics.MatsubaraThermalOscillator`, `HorizonCell.ConfinementAreaLawEntropicWeight`,
  `PathIntegral.ComplexActionPathIntegralWeight`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDRunningCoupling
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ConfinementAreaLawEntropicWeight
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionEntropyProduction
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDEntropicWeightLinks


/-- **[The Matsubara Gibbs weight is the entropic weight at temperature `1/β`] `e^{−βE} = kuikenWeight (1/β) E`.**
The thermofield Boltzmann/Gibbs weight `matsubaraBoltzmannWeight β E` is exactly the complex-action entropic
weight `kuikenWeight c Π = e^{−Π/c}` with `c = 1/β = k_B T` (the temperature) and `Π = E`. The thermal weight of
finite-`T` QCD lives on the same `e^{−·/·}` hub as confinement and the master path-integral weight. -/
lemma boltzmann_is_kuiken (β E : ℝ) : matsubaraBoltzmannWeight β E = kuikenWeight (1 / β) E := by
  unfold matsubaraBoltzmannWeight kuikenWeight
  congr 1
  rw [one_div, div_inv_eq_mul]
  ring


/-- **[Higher temperature weakens the entropic weight] `T₁ ≤ T₂ ⟹ e^{−E/T₁} ≤ e^{−E/T₂}`.** For non-negative
energy `E` and positive temperatures, `kuikenWeight c E = e^{−E/c}` is monotone *increasing* in the temperature
`c`: raising `T` moves the Boltzmann/confinement weight toward `1` (weaker suppression). Complementary to the
`Π`-monotonicity of the generalized second law (`kuikenWeight_antitone`). -/
lemma kuikenWeight_monotone_in_temperature (E c1 c2 : ℝ) (hE : 0 ≤ E) (hc1 : 0 < c1) (h : c1 ≤ c2) :
    kuikenWeight c1 E ≤ kuikenWeight c2 E := by
  unfold kuikenWeight
  apply Real.exp_le_exp.mpr
  rw [neg_le_neg_iff]
  gcongr


/-- **[The thermal Boltzmann weight is bounded by one] `e^{−βE} ≤ 1`.** For positive inverse temperature and
non-negative energy, the Gibbs weight is a bona-fide suppression — the arc's `kuikenWeight_le_one` transported to
the thermofield weight via `boltzmann_is_kuiken`. -/
lemma thermal_boltzmann_le_one (β E : ℝ) (hβ : 0 < β) (hE : 0 ≤ E) :
    matsubaraBoltzmannWeight β E ≤ 1 := by
  rw [boltzmann_is_kuiken]
  exact kuikenWeight_le_one (1 / β) E (by positivity) hE

/-- **[The thermal Boltzmann weight decreases with energy] `E₁ ≤ E₂ ⟹ e^{−βE₂} ≤ e^{−βE₁}`.** At fixed
temperature the Gibbs weight is antitone in the energy — the generalized second law (`kuikenWeight_antitone`)
transported to the thermofield weight. -/
lemma thermal_boltzmann_antitone (β : ℝ) (hβ : 0 < β) {E1 E2 : ℝ} (h : E1 ≤ E2) :
    matsubaraBoltzmannWeight β E2 ≤ matsubaraBoltzmannWeight β E1 := by
  rw [boltzmann_is_kuiken, boltzmann_is_kuiken]
  exact kuikenWeight_antitone (1 / β) (by positivity) h


/-- **[High temperature is the infrared confinement regime].** The finite-`T` QCD coupling's β-function is
strongly-coupled negative at high temperature (`betaHighTemp_neg`) while, in the *same* infrared, the confinement
area-law Wilson loop tightens as the area grows (`confinement_obeys_gsl`). Raising `T` at fixed momentum is going
into the infrared, where the coupling is strong and confinement suppresses — one regime, both faces. -/
lemma high_temp_is_confinement_regime (N_c αs τ κ σ : ℝ) (hNc : 0 < N_c) (ha : αs ≠ 0)
    (hτ : 0 < τ) (hκ : 0 < κ) (hσ : 0 ≤ σ) {A1 A2 : ℝ} (hA : A1 ≤ A2) :
    betaHighTemp N_c αs τ κ < 0 ∧ wilsonAreaLaw σ A2 ≤ wilsonAreaLaw σ A1 :=
  ⟨betaHighTemp_neg N_c αs τ κ hNc ha hτ hκ, confinement_obeys_gsl σ hσ hA⟩


/-- **[The finite-`T` QCD coupling on the entropic-weight hub, assembled].**

* the **vacuum** limit is the ordinary one-loop coefficient `betaCoeffFT 3 N_f = 2π betaZeroCoeff N_f`;
* the **thermal** Gibbs weight is the entropic weight `matsubaraBoltzmannWeight β E = kuikenWeight (1/β) E`;
* the **confinement** area law is the *same* entropic weight `wilsonAreaLaw σ A = kuikenWeight 1 (σA)`.

Vacuum coupling, thermal Boltzmann weight, and confinement suppression are one `e^{−·/·}` entropic-weight hub —
the finite-temperature QCD coupling is wired into the repository through it. -/
lemma thermal_qcd_on_entropic_hub (N_f β E σ A : ℝ) :
    betaCoeffFT 3 N_f = 2 * Real.pi * betaZeroCoeff N_f
      ∧ matsubaraBoltzmannWeight β E = kuikenWeight (1 / β) E
      ∧ wilsonAreaLaw σ A = kuikenWeight 1 (σ * A) :=
  ⟨betaCoeffFT_eq_vacuum N_f, boltzmann_is_kuiken β E, areaLaw_is_kuikenWeight σ A⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ThermalQCDEntropicWeightLinks

end
