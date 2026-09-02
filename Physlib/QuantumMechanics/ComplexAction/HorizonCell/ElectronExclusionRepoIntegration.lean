/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionEntropyProduction
public import Physlib.QuantumMechanics.ComplexAction.Fermion.StructuredElectronFermionRegion
public import Physlib.QuantumMechanics.ComplexAction.SimplicialCausalSetGravityUnification

/-!
# Integrating the electron-exclusion-cell arc into the repository

The electron-exclusion-cell arc (`HorizonCell.ElectronExclusion*`, `ElectronMadelung*`, …) reuses a great deal
of existing infrastructure but nothing downstream referenced it — it was a leaf. This module ties it back into
the two repository hubs it most naturally belongs to.

* **the electron aggregator** — the arc's electron *is* the repository's canonical structured electron
  (`Fermion.StructuredElectronFermionRegion`): the arc's Compton/Zitterbewegung clock discharges that
  aggregator's `HasRestZitterbewegungCompton` predicate (`exclusionCell_hasRestZitterbewegungCompton`), so the
  exclusion cell is a realization of the repo's assembled electron, not a parallel construction;
* **the quantum-gravity entropic-weight hub** — the arc's generalized second law (`kuikenWeight_antitone`, the
  monotonicity of `kuikenWeight = e^{−S_I/ℏ}`) governs the repository's whole complex-action weight family: the
  Ambjørn–Savvidy / Regge **sum-over-triangulations** quantum-gravity weight
  (`SimplicialCausalSetGravityUnification.reggeEinsteinHilbert_weight_modulus_is_kuiken`) obeys it
  (`reggeGravityWeight_obeys_arc_gsl`) — as the gravitational imaginary action grows the weight decreases. The
  same generalized second law the arc proved for the electron's emitting boundary is the second law of the
  simplicial quantum-gravity path integral.

So the arc is woven in on both sides: its electron is the repo's structured electron, and its generalized second
law is the second law of the repo's quantum-gravity sum. Both are exact reuse — the bridge only *names* the
connections.

* **§A — the arc's electron is the structured electron** (`exclusionCell_hasRestZitterbewegungCompton`).
* **§B — the arc's GSL governs the quantum-gravity weight** (`reggeGravityWeight_obeys_arc_gsl`).
* **§C — assembled** (`electron_exclusion_repo_integration`).

**Honest layering.** §A is exactly `zitterbewegung_rest_eq_two_compton` (the predicate's definitional content);
§B composes `reggeEinsteinHilbert_weight_modulus_is_kuiken` with the arc's `kuikenWeight_antitone`. No new
axioms.

## References

* Ties `HorizonCell.ElectronExclusion*` to `Fermion.StructuredElectronFermionRegion` and
  `SimplicialCausalSetGravityUnification`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.Fermion.StructuredElectronFermionRegion
open Physlib.QuantumMechanics.ComplexAction.AmbjornSavvidySteinerWeyl
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.SimplicialCausalSetGravityUnification
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionEntropyProduction

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionRepoIntegration


/-- **[The exclusion-cell electron discharges the structured-electron Zitterbewegung–Compton predicate].** The
arc's electron clock — `ω_Z = 2ω_C` at rest, the basis of `ElectronExclusionMutex`'s Margolus–Levitin
saturation — is exactly `Fermion.StructuredElectronFermionRegion.HasRestZitterbewegungCompton`: the exclusion
cell is a realization of the repository's canonical assembled electron, not an isolated parallel construction. -/
lemma exclusionCell_hasRestZitterbewegungCompton (m c ħ : ℝ) (hm : 0 ≤ m) :
    HasRestZitterbewegungCompton m c ħ :=
  zitterbewegung_rest_eq_two_compton m c ħ hm


/-- **[The Ambjørn–Savvidy / Regge quantum-gravity weight obeys the arc's generalized second law].** The
simplicial (sum-over-triangulations) quantum-gravity path-integral weight modulus is `kuikenWeight ℏ S_I`
(`reggeEinsteinHilbert_weight_modulus_is_kuiken`); by the arc's `kuikenWeight_antitone` it *decreases* as the
gravitational imaginary action grows, `S_{I,1} ≤ S_{I,2} ⟹ ‖W(S_{I,2})‖ ≤ ‖W(S_{I,1})‖`. The generalized second
law the arc proved for the electron's emitting boundary is the second law of the quantum-gravity sum. -/
lemma reggeGravityWeight_obeys_arc_gsl {ι : Type*} (σ ω : ι → ℝ) (s : Finset ι) (ħ : ℝ)
    (hħ : 0 < ħ) {S_I1 S_I2 : ℝ} (h : S_I1 ≤ S_I2) :
    ‖complexActionPathIntegralWeight (reggeEinsteinHilbert σ ω s) S_I2 ħ‖
      ≤ ‖complexActionPathIntegralWeight (reggeEinsteinHilbert σ ω s) S_I1 ħ‖ := by
  rw [reggeEinsteinHilbert_weight_modulus_is_kuiken, reggeEinsteinHilbert_weight_modulus_is_kuiken]
  exact kuikenWeight_antitone ħ hħ h


/-- **[The electron-exclusion-cell arc, integrated].** For the exclusion-cell electron and the simplicial
quantum-gravity weight:

* the electron discharges the structured-electron `HasRestZitterbewegungCompton` predicate (it *is* the repo's
  assembled electron);
* the Regge sum-over-triangulations weight obeys the arc's generalized second law (`kuikenWeight` monotone).

The arc is a node of the repository web: its electron is the structured electron, and its second law is the
second law of the quantum-gravity path integral. -/
lemma electron_exclusion_repo_integration
    {ι : Type*} (σ ω : ι → ℝ) (s : Finset ι) (m c ħ : ℝ) (hm : 0 ≤ m) (hħ : 0 < ħ)
    {S_I1 S_I2 : ℝ} (h : S_I1 ≤ S_I2) :
    HasRestZitterbewegungCompton m c ħ
      ∧ ‖complexActionPathIntegralWeight (reggeEinsteinHilbert σ ω s) S_I2 ħ‖
          ≤ ‖complexActionPathIntegralWeight (reggeEinsteinHilbert σ ω s) S_I1 ħ‖ :=
  ⟨exclusionCell_hasRestZitterbewegungCompton m c ħ hm,
    reggeGravityWeight_obeys_arc_gsl σ ω s ħ hħ h⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionRepoIntegration

end
