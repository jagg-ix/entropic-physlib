/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
meta import Zil

/-!
# Hadron spin-statistics and baryon number from quark content

`Particles.HadronChargeIntegrality` gave hadron *charge* (proton `+1`, neutron `0`, `π⁺ +1`, confinement signature). The
composite model is completed here by the two quantum numbers that follow from a hadron being a bound state of
spin-½ quarks:

* **Spin-statistics from the quark count.** Each quark is a spin-½ fermion with exchange phase `θ(½) = −1`
  (`ribbonTwist_fermion`). The exchange phase of an `n`-quark composite is the product `(−1)ⁿ`
  (`compositeTwist`). So an **odd** number of quarks is a **fermion** and an **even** number a **boson**:
  baryons (`qqq`, `n = 3`) are fermions (`baryon_is_fermion`, hence proton/neutron obey Pauli — nuclear shell
  structure), mesons (`q q̄`, `n = 2`) are bosons (`meson_is_boson`).

* **Baryon number from quark content.** Each quark carries `B = 1/3`, so a baryon (`qqq`) has `B = 1`
  (`baryonNumber_baryon`) and a meson (`q q̄`) has `B = 0` (`baryonNumber_meson`).

* **§A — spin-statistics.** `compositeTwist`, `compositeTwist_eq` (`= (−1)ⁿ`), `baryon_is_fermion`,
  `meson_is_boson`, `odd_quarkCount_fermion` / `even_quarkCount_boson` (the general count rule).
* **§B — baryon number.** `quarkBaryonNumber` (`= 1/3`), `baryonNumber_baryon` (`= 1`), `baryonNumber_meson`
  (`= 0`).

**Honest layering.** Proven: a composite of `n` spin-½ quarks has exchange phase `(−1)ⁿ` (so odd ⟹ fermion,
even ⟹ boson), and the quark `B = 1/3` gives baryons `B = 1`, mesons `B = 0`. The multiplicativity of the
exchange phase across constituents (composite twist `= ∏` of constituent twists) is the standard composite
spin-statistics rule, taken as the definition of `compositeTwist`; the constituent value `θ(½) = −1` is the
verified `ribbonTwist_fermion`. Hadron masses/magnetic-moments are dynamics, not derived here.

## References

* Composite spin-statistics (baryon = fermion, meson = boson); baryon number `B = 1/3` per quark. `Physlib`
  (`Hopf.ChargeConjugationRibbonTwist.ribbonTwist`, `Winding.QuarkChargeWinding`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics


/-- **The exchange phase of an `n`-quark composite** `θ_total = θ(½)ⁿ = (−1)ⁿ` — the product of the `n`
constituent spin-½ fermion exchange phases. -/
noncomputable def compositeTwist (n : ℕ) : ℂ := (ribbonTwist (1 / 2)) ^ n

/-- **[Composite exchange phase is `(−1)ⁿ`]** with `θ(½) = −1` (`ribbonTwist_fermion`). -/
lemma compositeTwist_eq (n : ℕ) : compositeTwist n = (-1) ^ n := by
  rw [compositeTwist, ribbonTwist_fermion]

/-- **[Baryons are fermions]** `θ(qqq) = (−1)³ = −1` — a three-quark baryon (proton, neutron, …) is a fermion,
hence obeys the Pauli principle (nuclear shell structure). -/
lemma baryon_is_fermion : compositeTwist 3 = -1 := by
  rw [compositeTwist_eq]; norm_num

/-- **[Mesons are bosons]** `θ(q q̄) = (−1)² = +1` — a quark–antiquark meson (pion, kaon, …) is a boson. -/
lemma meson_is_boson : compositeTwist 2 = 1 := by
  rw [compositeTwist_eq]; norm_num

/-- **[Odd quark count ⟹ fermion]** any composite of an odd number of quarks has exchange phase `−1`. -/
lemma odd_quarkCount_fermion (n : ℕ) (h : Odd n) : compositeTwist n = -1 := by
  rw [compositeTwist_eq, h.neg_one_pow]

/-- **[Even quark count ⟹ boson]** any composite of an even number of quarks has exchange phase `+1`. -/
lemma even_quarkCount_boson (n : ℕ) (h : Even n) : compositeTwist n = 1 := by
  rw [compositeTwist_eq, h.neg_one_pow]


/-- **The baryon number of a single quark** `B = 1/3`. -/
def quarkBaryonNumber : ℚ := 1 / 3

/-- **[Baryon number of a baryon]** `B(qqq) = 3 · (1/3) = 1`. -/
lemma baryonNumber_baryon : 3 * quarkBaryonNumber = 1 := by
  unfold quarkBaryonNumber; norm_num

/-- **[Baryon number of a meson]** `B(q q̄) = 1/3 + (−1/3) = 0` (the antiquark carries `B = −1/3`). -/
lemma baryonNumber_meson : quarkBaryonNumber + (-quarkBaryonNumber) = 0 := by
  ring

end Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.compositeTwist_eq where
  formalizes @ "claim:the-composite-ribbon-twist-of-n-quarks-is-minus-one-to-the-n-so-parity-of-the-quark-count-fixes-the-exchange-statistics",
  supported_by @ "paper:spin-statistics-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.baryon_is_fermion where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.compositeTwist_eq",
  formalizes @ "claim:a-baryon-with-three-quarks-is-a-fermion-the-composite-twist-is-minus-one",
  requires @ "claim:the-composite-ribbon-twist-of-n-quarks-is-minus-one-to-the-n-so-parity-of-the-quark-count-fixes-the-exchange-statistics"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.meson_is_boson where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.compositeTwist_eq",
  formalizes @ "claim:a-meson-with-a-quark-and-an-antiquark-is-a-boson-the-composite-twist-is-plus-one",
  requires @ "claim:the-composite-ribbon-twist-of-n-quarks-is-minus-one-to-the-n-so-parity-of-the-quark-count-fixes-the-exchange-statistics"

zil_file_contract physlib.hadronSpinStatistics where
  promises "The spin-statistics connection for composite hadrons: the composite ribbon twist of n quarks is minus one to the n, so the parity of the quark count fixes the exchange statistics -- an odd number of quarks (a three-quark baryon) is a fermion with composite twist minus one, and an even number (a quark-antiquark meson) is a boson with composite twist plus one; a single quark carries baryon number one-third, so three quarks make a baryon and a quark-antiquark pair a meson with baryon number zero."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.compositeTwist",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.quarkBaryonNumber"]
  forbids_substitutes ["a field-theoretic proof of the spin-statistics theorem, whose single-quark spin-half input is taken from the ribbon twist",
    "a derivation of the quark spin, taken as one-half"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.compositeTwist_eq,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.baryon_is_fermion,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.meson_is_boson,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.odd_quarkCount_fermion,
    Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics.even_quarkCount_boson]

/- ZIL-END -/
