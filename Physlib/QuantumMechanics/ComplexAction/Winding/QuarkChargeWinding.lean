/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
public import Mathlib.Tactic

/-!
# Quarks as fractional-winding fermions — completing the matter zoo

The charged leptons are integer-winding states (`Winding.NumberMass`/`Particles.ChargedLeptonGenerations`, electric charge
= winding number, `Hopf.ChargeConjugationRibbonTwist.chargeState (q : ℤ)`). Quarks extend this to **thirds of a
winding**: electric charge `Q = n/3` for an integer winding `n` (`windingCharge`), the fractional-charge sector
that the integer `chargeState` cannot reach. This file builds the quark charge taxonomy and the boson/fermion
status on the existing winding/ribbon-twist infrastructure.

The organizing principle is the winding residue mod 3:

* `n ≡ 0 (mod 3)` — **integer charge**: charged leptons (`e: n = −3`, `Q = −1`), neutrinos (`n = 0`, `Q = 0`),
  and (downstream) color-singlet hadrons.
* `n ≡ 2 ≡ −1 (mod 3)` — **fractional charge**: quarks (up-type `n = 2`, `Q = +2/3`; down-type `n = −1`,
  `Q = −1/3`), never integer ⟹ confined (`Particles.HadronChargeIntegrality`).

* **§A — fractional electric charge.** `windingCharge n = n/3`; additivity/conjugation
  (`windingCharge_add`, `windingCharge_neg`); `windingCharge_integer_iff` (integer charge ⟺ `3 ∣ n`).
* **§B — the quark/lepton charge table.** `upQuark_charge` (`+2/3`), `downQuark_charge` (`−1/3`),
  `electron_charge` (`−1`), `neutrino_charge` (`0`); `quark_charge_fractional` (quark charge is not an integer).
* **§C — spin-statistics.** `quark_is_fermion` (`ribbonTwist ½ = −1`), `antiquark_charge` (conjugation flips
  the sign), generation charge universality (`up_charm_top_charge_universal`).

**Honest layering.** What is structural and proven: charge is quantized in thirds of a winding, charge
conjugation flips it, quarks are spin-½ fermions, and (the key downstream result) only `3 ∣ n` combinations are
integer-charged. The *assignment* of which winding to which flavor (`up = 2`, `down = −1`) is the empirical
input matching observed charges; quark *masses* are inputs (Yukawa, `Yukawa.StandardModelYukawaCoupling`), not
predicted here. The rigorous gauge/anomaly content lives in `Physlib.Particles.StandardModel`; this is the
winding-model charge taxonomy.

## References

* Quark electric charges `+2/3, −1/3`; color triality. `Physlib`
  (`Hopf.ChargeConjugationRibbonTwist.ribbonTwist`/`chargeState`, `Winding.NumberMass`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding


/-- **Electric charge from a winding number, in thirds** `Q = n/3` — the fractional-charge generalization of
the integer `chargeState (q : ℤ)`: a quark carries a third of a winding, `n ≡ 2 (mod 3)`. -/
def windingCharge (n : ℤ) : ℚ := (n : ℚ) / 3

/-- **[Charge additivity]** `Q(m) + Q(n) = Q(m + n)` — charge is additive in the winding (the composite-state
charge law). -/
lemma windingCharge_add (m n : ℤ) : windingCharge m + windingCharge n = windingCharge (m + n) := by
  unfold windingCharge; push_cast; ring

/-- **[Charge conjugation]** `Q(−n) = −Q(n)` — the antiparticle has opposite charge (`chargeState` antipode). -/
lemma windingCharge_neg (n : ℤ) : windingCharge (-n) = -windingCharge n := by
  unfold windingCharge; push_cast; ring

/-- **[Integer charge ⟺ `3 ∣ winding`]** the charge `n/3` is an integer exactly when the winding is a multiple
of three — the divide between integer-charged states (leptons, hadrons) and fractional quarks. -/
lemma windingCharge_integer_iff (n : ℤ) :
    (∃ k : ℤ, windingCharge n = (k : ℚ)) ↔ (3 : ℤ) ∣ n := by
  unfold windingCharge
  constructor
  · rintro ⟨k, hk⟩
    rw [div_eq_iff (by norm_num)] at hk
    have hn : (n : ℤ) = k * 3 := by exact_mod_cast hk
    exact ⟨k, by rw [hn]; ring⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; ring⟩


/-- The **up-type** quark winding (`up, charm, top`): `n = 2`, electric charge `+2/3`. -/
def upWinding : ℤ := 2

/-- The **down-type** quark winding (`down, strange, bottom`): `n = −1`, electric charge `−1/3`. -/
def downWinding : ℤ := -1

/-- **[Up-type charge `+2/3`]**. -/
lemma upQuark_charge : windingCharge upWinding = 2 / 3 := by
  unfold windingCharge upWinding; norm_num

/-- **[Down-type charge `−1/3`]**. -/
lemma downQuark_charge : windingCharge downWinding = -1 / 3 := by
  unfold windingCharge downWinding; norm_num

/-- **[Electron charge `−1`]** the charged lepton is the integer-winding `n = −3` state — leptons live in the
`3 ∣ n` (integer-charge) sector. -/
lemma electron_charge : windingCharge (-3) = -1 := by
  unfold windingCharge; norm_num

/-- **[Neutrino charge `0`]** the neutral lepton is the `n = 0` state. -/
lemma neutrino_charge : windingCharge 0 = 0 := by
  unfold windingCharge; norm_num

/-- **[Quark charge is fractional]** an up-type quark's charge `2/3` is not an integer (`¬ 3 ∣ 2`) — the
hallmark of a single quark, never seen free. -/
lemma quark_charge_fractional : ¬ ∃ k : ℤ, windingCharge upWinding = (k : ℚ) := by
  rw [windingCharge_integer_iff]
  decide


/-- **[Quarks are spin-½ fermions]** `θ(½) = −1` — quarks carry the fermionic exchange sign, like the leptons
(`ribbonTwist_fermion`). -/
lemma quark_is_fermion : ribbonTwist (1 / 2) = -1 := ribbonTwist_fermion

/-- **[Antiquark charge]** the antiquark of winding `n` has charge `−Q(n)`: anti-up `−2/3`, anti-down `+1/3`. -/
lemma antiquark_charge (n : ℤ) : windingCharge (-n) = -windingCharge n := windingCharge_neg n

/-- **[Up−down charge difference is `1`]** `Q(up) − Q(down) = 2/3 − (−1/3) = 1` — the electric charge raised
within a weak-isospin doublet, i.e. the charge `+1` carried off by the `W⁺` boson (`u → d + W⁺`). -/
lemma up_down_charge_difference : windingCharge upWinding - windingCharge downWinding = 1 := by
  unfold windingCharge upWinding downWinding; norm_num

end Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding

end
