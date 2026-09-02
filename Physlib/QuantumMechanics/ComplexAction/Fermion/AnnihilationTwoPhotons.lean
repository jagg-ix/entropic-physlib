/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics
public import Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification

/-!
# Electron–positron annihilation as an unknotting into two photons

In the topological-soliton / winding picture, a fermion is a **knot**: a wound loop characterized by its
winding (writhe) `q`, realized as the group-like state `chargeState q` (`Hopf.ChargeConjugationRibbonTwist`; the
trefoil `B₃` word of `ChernSimons.BraidRelationTrefoilTorus` is the concrete knot). The **positron** is the *mirror* knot —
the charge-conjugate, i.e. the antipode `chargeState (−q)`. Their annihilation is the **unknotting**: the knot
composed with its anti-knot collapses to the trivial element,

  `chargeState q · chargeState (−q) = chargeState 0 = 1`   (`fermion_antifermion_unknots`),

the unknot/vacuum, with the windings cancelling `q + (−q) = 0` (`annihilation_winding_zero`).

**The radiation — the standard channel.** The energy is carried off as **two photons** `e⁺e⁻ → γγ` (standard
QED; a single photon is forbidden by momentum conservation in the CM frame). The identification is consistent
on both conserved channels:

* **charge** — the photon is neutral (`windingCharge 0 = 0`), matching the net charge `q + (−q) = 0` of the
  annihilated pair (`annihilation_to_neutral_photons`);
* **spin-statistics** — the `e⁺e⁻` pair is a boson (`compositeTwist 2 = +1`), and each photon is a spin-1 boson
  (`ribbonTwist 1 = +1`); a fermion pair can therefore radiate spin-1 bosons
  (`annihilation_photon_spin_consistent`).

* **§A — the unknotting.** `fermion_antifermion_unknots`, `annihilation_winding_zero`.
* **§B — into two photons.** `photon_is_boson`, `photon_neutral`, `fermionPair_is_boson`,
  `annihilation_photon_spin_consistent`, `annihilation_to_neutral_photons`, and the bundled
  `annihilation_unknots_to_photons`.

**Honest layering.** Proven: the unknotting (knot and its mirror compose to the unit; windings cancel) and that
the standard two-photon final state is charge- and spin-statistics-consistent with the annihilating pair (the
photon is neutral and a spin-1 boson; the pair is a boson). The knot/winding picture is the soliton-model
*representation* of the electron; the *products* `e⁺e⁻ → γγ` are the **standard** QED channel. The "two photons,
not one" follows from energy–momentum conservation (kinematics, not formalized here).

## References

* Standard QED `e⁺e⁻ → γγ`; charge conjugation as the antipode; spin-statistics. `Physlib`
  (`Hopf.ChargeConjugationRibbonTwist.chargeState`/`ribbonTwist`, `Particles.HadronSpinStatistics.compositeTwist`,
  `Particles.GaugeBosonClassification`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
open Physlib.QuantumMechanics.ComplexAction.Particles.HadronSpinStatistics
open Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Fermion.AnnihilationTwoPhotons


/-- **[Knot · anti-knot = unknot]** the electron knot `chargeState q` composed with the positron mirror
`chargeState (−q)` (its charge-conjugate antipode) collapses to the trivial element `1` — the unknot / vacuum.
This is `e⁻ + e⁺ → (vacuum)` as the unknotting of the wound fermion structure. -/
lemma fermion_antifermion_unknots (q : ℤ) :
    chargeState q * chargeState (-q) = 1 := by
  rw [chargeState_mul, add_neg_cancel, chargeState_zero]

/-- **[The windings cancel]** `q + (−q) = 0` — the writhe of the knot and its mirror sum to zero, the signature
of the unknot. -/
lemma annihilation_winding_zero (q : ℤ) : q + (-q) = 0 := add_neg_cancel q


/-- **[The photon is a spin-1 boson]** `ribbonTwist 1 = +1` (`Particles.GaugeBosonClassification`). -/
lemma photon_is_boson : ribbonTwist ((1 : ℤ) : ℝ) = 1 := gaugeBoson_is_boson

/-- **[The photon is neutral]** `Q(γ) = 0` — the photon carries no electric charge. -/
lemma photon_neutral : windingCharge 0 = 0 := neutral_gauge_boson_charge

/-- **[The fermion pair is a boson]** `compositeTwist 2 = (−1)² = +1` — the `e⁺e⁻` pair of two spin-½ fermions
has a bosonic exchange phase. -/
lemma fermionPair_is_boson : compositeTwist 2 = 1 := by
  rw [compositeTwist_eq]; norm_num

/-- **[Spin-statistics allows the photon channel]** the `e⁺e⁻` pair's exchange phase `compositeTwist 2 = +1`
equals a photon's `ribbonTwist 1 = +1`: a fermion pair can radiate spin-1 bosons (photons). -/
lemma annihilation_photon_spin_consistent :
    compositeTwist 2 = ribbonTwist ((1 : ℤ) : ℝ) := by
  rw [fermionPair_is_boson, photon_is_boson]

/-- **[Charge conservation into neutral photons]** the windings cancel (`q + (−q) = 0`) and the photons are
neutral (`Q(γ) = 0`): electric charge is conserved in `e⁺e⁻ → γγ`. -/
lemma annihilation_to_neutral_photons (q : ℤ) :
    q + (-q) = 0 ∧ windingCharge 0 = 0 :=
  ⟨annihilation_winding_zero q, photon_neutral⟩

/-- **[Annihilation: an unknotting into two neutral spin-1 photons]** the electron knot and positron anti-knot
unknot to the vacuum (`chargeState q · chargeState (−q) = 1`); the products are photons — neutral
(`windingCharge 0 = 0`) and spin-1 bosons sharing the pair's exchange phase (`compositeTwist 2 = ribbonTwist 1`)
— the standard QED channel `e⁺e⁻ → γγ`. -/
lemma annihilation_unknots_to_photons (q : ℤ) :
    chargeState q * chargeState (-q) = 1
      ∧ windingCharge 0 = 0
      ∧ compositeTwist 2 = ribbonTwist ((1 : ℤ) : ℝ) :=
  ⟨fermion_antifermion_unknots q, photon_neutral, annihilation_photon_spin_consistent⟩

end Physlib.QuantumMechanics.ComplexAction.Fermion.AnnihilationTwoPhotons

end
