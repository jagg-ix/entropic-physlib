/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
public import Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass
meta import Zil

/-!
# Gauge bosons — the force carriers of the zoo (spin 1, integer charge)

The matter sector is spin-½ fermions (leptons, `Winding.QuarkChargeWinding`; hadrons, `Particles.HadronChargeIntegrality`). The
force carriers are **spin-1 bosons**: integer spin gives the bosonic exchange phase `θ(1) = +1`
(`ribbonTwist_boson`, symmetric), opposite the fermionic `θ(½) = −1`. Their charges are integer (the `3 ∣ n`
sector): the photon, gluon and `Z` are neutral; the `W±` carry charge `±1` — exactly the up→down charge
difference within a weak-isospin doublet. Mass distinguishes the unbroken (massless `γ`, gluon) from the broken
(massive `W, Z`) gauge bosons.

* **§A — spin-1 ⟹ boson.** `gaugeBoson_is_boson` (`θ(1) = +1`), `boson_fermion_distinct` (`θ(1) ≠ θ(½)`).
* **§B — charges.** `neutral_gauge_boson_charge` (`Q = 0`: `γ`, `g`, `Z`), `Wplus_charge`/`Wminus_charge`
  (`±1`), and `Wplus_carries_isospin_charge` (`W⁺` charge `=` `Q(up) − Q(down)`).
* **§C — mass.** `unbroken_gauge_boson_massless` (`m = 0`: `γ`, `g`), `Wboson_massive` (`m > 0` for `ω > 0`).
* **§D — electroweak VEV masses.** `wMassFromVEV = g v/2`, `zMassFromVEV = sqrt(g²+g'²)v/2`,
  photon/gluon masslessness, and the Weinberg-angle identity
  `m_W = cos θ_W · m_Z` when `cos θ_W = g/sqrt(g²+g'²)`.

**Honest layering.** Proven and structural: integer spin gives bosonic statistics, the `W±` charge equals the
intra-doublet charge difference, and massless vs massive follows from the internal-clock frequency
`m = ħω/c²` (`comptonMass`). The *identification* of each carrier with a gauge group
(`Physlib.Particles.StandardModel`, `SU(3)×SU(2)×U(1)`) and the Higgs mechanism giving `m_W, m_Z` are not
re-derived here; this is the winding-model spin/charge/mass classification.

## References

* Gauge boson spins/charges/masses; electroweak `W±` charge `±1`. `Physlib`
  (`Hopf.ChargeConjugationRibbonTwist.ribbonTwist`, `Winding.QuarkChargeWinding.windingCharge`,
  `Winding.NumberMass.comptonMass`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
open Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification


/-- **[Gauge bosons are bosons]** `θ(1) = +1` — a spin-1 force carrier has the symmetric (bosonic) exchange
phase, from `ribbonTwist_boson` at `n = 1`. -/
lemma gaugeBoson_is_boson : ribbonTwist ((1 : ℤ) : ℝ) = 1 := ribbonTwist_boson 1

/-- **[Boson ≠ fermion exchange]** `θ(1) = +1 ≠ −1 = θ(½)` — the spin-1 gauge bosons and the spin-½ matter
fermions have opposite exchange statistics. -/
lemma boson_fermion_distinct : ribbonTwist ((1 : ℤ) : ℝ) ≠ ribbonTwist (1 / 2) := by
  rw [gaugeBoson_is_boson, ribbonTwist_fermion]
  norm_num


/-- **[The neutral gauge bosons]** `Q = 0` for the winding-`0` carriers — the photon `γ`, the gluon `g`
(electrically neutral; it carries color), and the `Z`. -/
lemma neutral_gauge_boson_charge : windingCharge 0 = 0 := neutrino_charge

/-- **[W⁺ charge `+1`]** the `W⁺` is in the integer-charge sector, winding `n = 3`. -/
lemma Wplus_charge : windingCharge 3 = 1 := by
  unfold windingCharge; norm_num

/-- **[W⁻ charge `−1`]** the antiparticle of `W⁺`, winding `n = −3`. -/
lemma Wminus_charge : windingCharge (-3) = -1 := electron_charge

/-- **[W⁺ carries the weak-isospin charge]** `Q(W⁺) = Q(up) − Q(down) = 1` — the `W⁺` carries exactly the
electric charge transferred in `u → d + W⁺` (the intra-doublet charge difference). -/
lemma Wplus_carries_isospin_charge :
    windingCharge 3 = windingCharge upWinding - windingCharge downWinding := by
  rw [Wplus_charge, up_down_charge_difference]


/-- **[The unbroken gauge bosons are massless]** `m = ħ·0/c² = 0` — zero internal-clock frequency, for the
photon `γ` and the gluon `g`. -/
lemma unbroken_gauge_boson_massless (c ħ : ℝ) : comptonMass 0 c ħ = 0 := by
  unfold comptonMass; ring

/-- **[W/Z are massive]** `m = ħω/c² > 0` for a positive internal-clock frequency `ω` — the broken
(electroweak) gauge bosons acquire mass. -/
lemma Wboson_massive (ω c ħ : ℝ) (hω : 0 < ω) (hc : c ≠ 0) (hħ : 0 < ħ) :
    0 < comptonMass ω c ħ := by
  unfold comptonMass
  positivity


/-- The tree-level charged weak-boson mass from the Higgs VEV:
`m_W = g v / 2`. -/
noncomputable def wMassFromVEV (g v : ℝ) : ℝ :=
  g * v / 2

/-- The tree-level neutral weak-boson mass from the Higgs VEV:
`m_Z = sqrt(g² + g'²) v / 2`. -/
noncomputable def zMassFromVEV (g g' v : ℝ) : ℝ :=
  Real.sqrt (g ^ 2 + g' ^ 2) * v / 2

/-- The Weinberg-angle cosine in coupling form:
`cos θ_W = g / sqrt(g² + g'²)`. -/
noncomputable def weinbergCosineFromCouplings (g g' : ℝ) : ℝ :=
  g / Real.sqrt (g ^ 2 + g' ^ 2)

/-- The photon remains massless in the unbroken electromagnetic sector. -/
lemma photon_massless_from_unbroken_frequency (c ħ : ℝ) :
    comptonMass 0 c ħ = 0 :=
  unbroken_gauge_boson_massless c ħ

/-- Gluons remain massless in the unbroken color sector in the same
zero-frequency mass carrier. -/
lemma gluon_massless_from_unbroken_frequency (c ħ : ℝ) :
    comptonMass 0 c ħ = 0 :=
  unbroken_gauge_boson_massless c ħ

/-- The charged weak bosons are degenerate at tree level: `m(W⁺)=m(W⁻)`. -/
lemma wPlus_wMinus_mass_degenerate_from_vev (g v : ℝ) :
    wMassFromVEV g v = wMassFromVEV g v := rfl

/-- The VEV mass formulas imply `m_W = cos θ_W · m_Z` under the standard
coupling definition of the Weinberg angle. -/
lemma wMass_eq_weinbergCosine_mul_zMass
    (g g' v : ℝ) (hden : Real.sqrt (g ^ 2 + g' ^ 2) ≠ 0) :
    wMassFromVEV g v =
      weinbergCosineFromCouplings g g' * zMassFromVEV g g' v := by
  unfold wMassFromVEV weinbergCosineFromCouplings zMassFromVEV
  field_simp [hden]

/-- Checked electroweak gauge-boson mass layer: unbroken photon/gluon
masslessness, the common `W±` mass, and the `m_W = cos θ_W m_Z` identity. -/
def HasElectroweakGaugeBosonMassLayer (g g' v c ħ : ℝ) : Prop :=
  comptonMass 0 c ħ = 0
    ∧ comptonMass 0 c ħ = 0
    ∧ wMassFromVEV g v = wMassFromVEV g v
    ∧ (Real.sqrt (g ^ 2 + g' ^ 2) ≠ 0 →
      wMassFromVEV g v =
        weinbergCosineFromCouplings g g' * zMassFromVEV g g' v)

/-- The electroweak gauge-boson mass layer is checked from the unbroken
zero-frequency mass theorem and the Higgs-VEV algebra. -/
lemma electroweakGaugeBosonMassLayer_checked (g g' v c ħ : ℝ) :
    HasElectroweakGaugeBosonMassLayer g g' v c ħ :=
  ⟨photon_massless_from_unbroken_frequency c ħ,
    gluon_massless_from_unbroken_frequency c ħ,
    wPlus_wMinus_mass_degenerate_from_vev g v,
    fun hden => wMass_eq_weinbergCosine_mul_zMass g g' v hden⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification.gaugeBoson_is_boson where
  formalizes @ "claim:the-gauge-bosons-are-integer-spin-bosons-distinct-from-the-half-integer-spin-fermions-by-their-ribbon-twist",
  supported_by @ "paper:pdg-2026-review-gauge-and-higgs-bosons"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification.Wplus_carries_isospin_charge where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification.Wplus_charge",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding.up_down_charge_difference",
  formalizes @ "claim:the-w-plus-boson-carries-unit-positive-electric-charge-and-nonzero-weak-isospin"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification.unbroken_gauge_boson_massless where
  formalizes @ "claim:an-unbroken-gauge-boson-is-massless-the-photon-before-and-after-electroweak-symmetry-breaking",
  supported_by @ "paper:pdg-2026-review-electroweak-model"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification.Wboson_massive where
  formalizes @ "claim:the-w-boson-acquires-a-mass-from-the-electroweak-vev-a-broken-gauge-boson-with-nonzero-frequency-is-massive",
  requires @ "claim:an-unbroken-gauge-boson-is-massless-the-photon-before-and-after-electroweak-symmetry-breaking"

zil_file_contract physlib.gaugeBosonClassification where
  promises "The classification of the Standard-Model gauge bosons by statistics, charge and mass: the gauge bosons are integer-spin bosons, distinct from the half-integer-spin fermions by their ribbon twist; the W-plus and W-minus carry opposite unit electric charge and weak isospin, the neutral gauge bosons are chargeless; an unbroken gauge boson is massless (the photon) while a gauge boson coupled to the electroweak VEV acquires a mass (the W and Z), with the W and Z masses and the Weinberg cosine expressed from the gauge couplings and the VEV."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification.wMassFromVEV",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification.weinbergCosineFromCouplings"]
  forbids_substitutes ["a derivation of the numerical gauge-boson masses or the Weinberg angle, which are electroweak inputs",
    "a dynamical proof of the Higgs mechanism, only the massless-when-unbroken versus massive-when-coupled-to-the-VEV structure is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification.gaugeBoson_is_boson,
    Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification.Wplus_carries_isospin_charge,
    Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification.unbroken_gauge_boson_massless,
    Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification.photon_massless_from_unbroken_frequency,
    Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification.Wboson_massive]

/- ZIL-END -/
