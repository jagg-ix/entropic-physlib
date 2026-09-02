/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronComplexEinsteinCPTChirality
public import Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor

/-!
# Charge = chirality = sign of Im E: the electron/positron as conjugate SU(5) representations

Completes the charge–chirality story of `ElectronComplexEinsteinCPTChirality` at the representation-theoretic
root. There the sign of the imaginary Einstein energy `Im E = m_I c²` was shown to be the electric charge sign,
and CPT `= −iγ⁵` (chirality) flips it. Here that sign is identified with the **`SU(5)` representation**: the
electron sits in the `5̄` (left-Weyl, antifundamental) and the positron in the `5` (right-Weyl, fundamental =
conjugate), so the electric charge *is* the chirality of the representation.

* the **electron's charge is the `5̄` charge** `Q(e⁻) = su5AntifundCharge 3 = −1`
  (`electron_charge_is_antifund`) — the charged-lepton entry of the left-Weyl antifundamental;
* the **positron's charge is the `5` charge** `Q(e⁺) = su5FundCharge 3 = +1` (`positron_charge_is_fund`) — the
  conjugate (opposite-chirality) fundamental;
* the **chirality flip `5̄ ↔ 5` is the charge conjugation** `Q(5) + Q(5̄) = 0` (`chirality_flip_is_charge_conjugation`,
  `su5_particle_antiparticle_charge`) — exactly the `positron.electric = −electron.electric` of the CPT module;
* so the **`SU(5)` chirality is the sign of `Im E`** (`su5_chirality_is_imEinstein_sign`): the `5̄`/`5` (left/right
  Weyl) label of the complex-Einstein electron is the sign of its imaginary Einstein energy, and CPT `= −iγ⁵`
  exchanges them.

The chain closes: **charge = chirality (`5̄`/`5` SU(5) rep) = sign of `Im E`** (imaginary Einstein sector),
electron and positron the two conjugate representations exchanged by CPT.

* **§A — the electron is the `5̄`** (`electron_charge_is_antifund`).
* **§B — the positron is the `5`** (`positron_charge_is_fund`).
* **§C — chirality flip = charge conjugation** (`chirality_flip_is_charge_conjugation`).
* **§D — SU(5) chirality is the sign of Im E** (`su5_chirality_is_imEinstein_sign`).

**Honest layering.** §A is definitional (`su5AntifundCharge 3 = −1 = electron.electric`, both `ℚ`); §B/§C reuse
`su5_particle_antiparticle_charge`; §D composes with `imEinstein_charge_conjugation_odd`. No claim that `SU(5)`
is derived; the electron/positron charges are *identified* with the `5̄`/`5` entries. ## References

* Georgi–Glashow `SU(5)`; the CPT theorem. Repo carriers: `Su5ChargeQuantizationCartanTensor`,
  `AntiparticleConjugation`, `HorizonCell.ElectronComplexEinsteinCPTChirality`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor
open Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation
open Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronComplexEinsteinCPTChirality

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronChargeChiralitySU5


/-- **[The electron's charge is the `5̄` (antifundamental) charge] `Q(e⁻) = su5AntifundCharge 3 = −1`.** The
electron's electric charge is exactly the charged-lepton entry (index `3`) of the `SU(5)` left-Weyl
antifundamental `5̄ = (1/3,1/3,1/3,−1,0)` — the electron *is* that representation's lepton. -/
lemma electron_charge_is_antifund : electron.electric = su5AntifundCharge 3 := rfl


/-- **[The positron's charge is the `5` (fundamental) charge] `Q(e⁺) = su5FundCharge 3 = +1`.** The positron's
electric charge is the conjugate (opposite-chirality) fundamental entry `su5FundCharge 3 = +1`: the positron is
the `5`, the CPT/charge-conjugate representation of the electron's `5̄`. -/
lemma positron_charge_is_fund : positron.electric = su5FundCharge 3 := by
  have h := su5_particle_antiparticle_charge 3
  have ha : su5AntifundCharge 3 = -1 := rfl
  have hp : positron.electric = -electron.electric := conjugate_electric electron
  have he : electron.electric = -1 := rfl
  rw [hp, he]; linarith


/-- **[The `5̄ ↔ 5` chirality flip is the charge conjugation] `Q(5) + Q(5̄) = 0`.** Componentwise the fundamental
and antifundamental charges cancel — the conjugation of the `SU(5)` representation (the chirality flip) is
exactly the electric-charge conjugation `positron.electric = −electron.electric` of the CPT module. -/
lemma chirality_flip_is_charge_conjugation (i : Fin 5) :
    su5FundCharge i + su5AntifundCharge i = 0 :=
  su5_particle_antiparticle_charge i


/-- **[The `SU(5)` chirality is the sign of `Im E`].** The electron's charge is the `5̄` entry and the positron's
is the `5` entry (`electron_charge_is_antifund`, `positron_charge_is_fund`); charge conjugation flips the
imaginary Einstein energy `Im E(−m_I) = −Im E(m_I)` (`imEinstein_charge_conjugation_odd`). So the `5̄`/`5`
(left/right-Weyl) chirality label of the complex-Einstein electron is the sign of its imaginary Einstein energy,
and CPT `= −iγ⁵` exchanges them: **charge = chirality (`SU(5)` rep) = sign of `Im E`**. -/
lemma su5_chirality_is_imEinstein_sign (m_R m_I c : ℝ) :
    electron.electric = su5AntifundCharge 3
      ∧ positron.electric = su5FundCharge 3
      ∧ (complexEinsteinEnergy m_R (-m_I) c).im = -(complexEinsteinEnergy m_R m_I c).im :=
  ⟨electron_charge_is_antifund, positron_charge_is_fund,
    imEinstein_charge_conjugation_odd m_R m_I c⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronChargeChiralitySU5

end
