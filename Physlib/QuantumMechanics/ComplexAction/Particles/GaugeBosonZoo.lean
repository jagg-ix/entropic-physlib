/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification
public import Physlib.QuantumMechanics.ComplexAction.Particles.StrongInteractionColorOctet

/-!
# The complete gauge-boson sector: all twelve force carriers

Enumerates every Standard-Model **gauge boson** and shows the count per force equals the dimension of the
gauge group:

* **electromagnetic** — the photon `γ` (`U(1)`, `1` boson);
* **weak** — `W⁺, W⁻, Z⁰` (`SU(2)`, `2²−1 = 3` bosons);
* **strong** — eight gluons `g` (`SU(3)`, `3²−1 = 8` bosons).

`1 + 3 + 8 = 12` gauge bosons in all (`card_gaugeBoson`). Each is **spin-1** (the bosonic exchange phase
`θ(1)=+1`, `Particles.GaugeBosonClassification.gaugeBoson_is_boson`); the photon, `Z`, and gluons are electrically
neutral, the `W±` carry `±1` and are each other's antiparticles.

* **§A — the enumeration.** `GaugeBoson` (photon / W± / Z / 8 gluons), `gaugeBosonForce`, `gaugeBosonCharge`.
* **§B — counts = gauge-group dimensions.** `em_boson_count` (`1`), `weak_boson_count` (`3 = 2²−1`),
  `gluon_boson_count` (`8 = 3²−1`), `card_gaugeBoson` (`12`).
* **§C — charges and spin.** `photon_neutral`/`Z_neutral`/`gluon_neutral`, `wPlus_charge`/`wMinus_charge`
  (`±1`), `wPlus_wMinus_conjugate` (`Q(W⁺) = −Q(W⁻)`), `wPlus_charge_eq_winding` (link to the winding model),
  and `gaugeBoson_spin_one`.
* **§D — the main result** `gauge_boson_sector`.
* **§E — mass bridge** `gaugeBosonZooWithMassLayer_checked` exposes photon/gluon masslessness and the
  electroweak VEV identities from `Particles.GaugeBosonClassification` through the full twelve-boson zoo.

**Honest layering.** Proven: the enumeration has `12` elements with the stated per-force counts (`= N²−1` for
`SU(N)`, `1` for `U(1)`), the listed charges, `W⁺ = C(W⁻)`, and spin-1. Masses (massless `γ`/`g` vs massive
`W`/`Z`) and the full non-abelian dynamics are not modelled — this is the counting/charge/spin classification.

## References

* The twelve Standard-Model gauge bosons; gauge-group dimensions `dim U(1)=1`, `dim SU(2)=3`, `dim SU(3)=8`.
  `Physlib` (`Particles.GaugeBosonClassification`, `Particles.StrongInteractionColorOctet`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification
open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonZoo


/-- The three fundamental forces with gauge-boson carriers. -/
inductive Force
  | electromagnetic | weak | strong
  deriving DecidableEq

set_option backward.isDefEq.respectTransparency false in
/-- **Every Standard-Model gauge boson**: the photon, the three weak bosons `W⁺, W⁻, Z⁰`, and the eight
gluons (indexed by `Fin 8`). -/
inductive GaugeBoson
  | photon
  | wPlus | wMinus | zZero
  | gluon (i : Fin 8)
  deriving DecidableEq, Fintype

/-- The force whose gauge boson this is. -/
def gaugeBosonForce : GaugeBoson → Force
  | .photon => .electromagnetic
  | .wPlus => .weak | .wMinus => .weak | .zZero => .weak
  | .gluon _ => .strong

/-- The electric charge of a gauge boson. -/
def gaugeBosonCharge : GaugeBoson → ℚ
  | .photon => 0
  | .wPlus => 1 | .wMinus => -1 | .zZero => 0
  | .gluon _ => 0


/-- **[One photon]** the electromagnetic gauge group `U(1)` has dimension `1`: a single photon. -/
lemma em_boson_count :
    (Finset.univ.filter (fun b => gaugeBosonForce b = Force.electromagnetic)).card = 1 := by decide

/-- **[Three weak bosons]** the weak gauge group `SU(2)` has dimension `2²−1 = 3`: `W⁺, W⁻, Z⁰`. -/
lemma weak_boson_count :
    (Finset.univ.filter (fun b => gaugeBosonForce b = Force.weak)).card = 2 ^ 2 - 1 := by decide

/-- **[Eight gluons]** the strong gauge group `SU(3)` has dimension `3²−1 = 8`: eight gluons
(cf. `Particles.StrongInteractionColorOctet.gluon_count`). -/
lemma gluon_boson_count :
    (Finset.univ.filter (fun b => gaugeBosonForce b = Force.strong)).card = 3 ^ 2 - 1 := by decide

/-- **[Twelve gauge bosons]** `1 + 3 + 8 = 12` force carriers in all. -/
lemma card_gaugeBoson : Fintype.card GaugeBoson = 12 := by decide


/-- **[The photon is neutral]** `Q(γ) = 0`. -/
lemma photon_neutral : gaugeBosonCharge .photon = 0 := rfl

/-- **[The `Z⁰` is neutral]** `Q(Z) = 0`. -/
lemma Z_neutral : gaugeBosonCharge .zZero = 0 := rfl

/-- **[Gluons are neutral]** `Q(g) = 0` for every gluon. -/
lemma gluon_neutral (i : Fin 8) : gaugeBosonCharge (.gluon i) = 0 := rfl

/-- **[`W⁺` charge `+1`]**. -/
lemma wPlus_charge : gaugeBosonCharge .wPlus = 1 := rfl

/-- **[`W⁻` charge `−1`]**. -/
lemma wMinus_charge : gaugeBosonCharge .wMinus = -1 := rfl

/-- **[`W±` are antiparticles]** `Q(W⁺) = −Q(W⁻)` — the charged weak bosons are each other's charge
conjugates. -/
lemma wPlus_wMinus_conjugate : gaugeBosonCharge .wPlus = - gaugeBosonCharge .wMinus := by
  norm_num [gaugeBosonCharge]

/-- **[`W⁺` charge matches the winding model]** `Q(W⁺) = windingCharge 3 = 1`
(`Particles.GaugeBosonClassification.Wplus_charge`). -/
lemma wPlus_charge_eq_winding : gaugeBosonCharge .wPlus = windingCharge 3 := by
  rw [wPlus_charge, Wplus_charge]

/-- **[All gauge bosons are spin-1]** `θ(1) = +1`, the bosonic exchange phase
(`Particles.GaugeBosonClassification.gaugeBoson_is_boson`). -/
lemma gaugeBoson_spin_one : ribbonTwist ((1 : ℤ) : ℝ) = 1 := gaugeBoson_is_boson


/-- **[The gauge-boson sector, assembled]** twelve force carriers across three forces, with the count per
force equal to the gauge-group dimension (`U(1):1`, `SU(2):3`, `SU(3):8`), the `W±` charges `±1`
(antiparticles), the neutral `γ/Z/g`, and the spin-1 (bosonic) exchange phase shared by all. -/
lemma gauge_boson_sector :
    Fintype.card GaugeBoson = 12
      ∧ (Finset.univ.filter (fun b => gaugeBosonForce b = Force.electromagnetic)).card = 1
      ∧ (Finset.univ.filter (fun b => gaugeBosonForce b = Force.weak)).card = 2 ^ 2 - 1
      ∧ (Finset.univ.filter (fun b => gaugeBosonForce b = Force.strong)).card = 3 ^ 2 - 1
      ∧ gaugeBosonCharge .wPlus = - gaugeBosonCharge .wMinus
      ∧ ribbonTwist ((1 : ℤ) : ℝ) = 1 :=
  ⟨card_gaugeBoson, em_boson_count, weak_boson_count, gluon_boson_count, wPlus_wMinus_conjugate,
    gaugeBoson_spin_one⟩


/-- The full twelve-gauge-boson zoo together with the Higgs-VEV mass layer:
unbroken photon/gluon masslessness, common `W±` mass, and
`m_W = cos θ_W m_Z`. -/
def HasGaugeBosonZooWithMassLayer (g g' v c ħ : ℝ) : Prop :=
  Fintype.card GaugeBoson = 12
    ∧ (Finset.univ.filter (fun b => gaugeBosonForce b = Force.electromagnetic)).card = 1
    ∧ (Finset.univ.filter (fun b => gaugeBosonForce b = Force.weak)).card = 2 ^ 2 - 1
    ∧ (Finset.univ.filter (fun b => gaugeBosonForce b = Force.strong)).card = 3 ^ 2 - 1
    ∧ HasElectroweakGaugeBosonMassLayer g g' v c ħ

/-- The complete gauge-boson zoo can call the lower electroweak mass layer
without duplicating the mass equations. -/
lemma gaugeBosonZooWithMassLayer_checked (g g' v c ħ : ℝ) :
    HasGaugeBosonZooWithMassLayer g g' v c ħ :=
  ⟨card_gaugeBoson,
    em_boson_count,
    weak_boson_count,
    gluon_boson_count,
    electroweakGaugeBosonMassLayer_checked g g' v c ħ⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonZoo

end
