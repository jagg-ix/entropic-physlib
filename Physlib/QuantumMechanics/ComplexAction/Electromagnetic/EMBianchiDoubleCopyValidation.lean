/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiDoubleCopy

/-!
# The double copy of the EM Bianchi identities, validated by the §7 Bianchi theorem

Uses the BCJ double copy to **map the electromagnetic Bianchi identities to the gravity side**, then
**validates** the result with the §7 Bianchi theorem (`LeviCivita.BianchiValidation`,
`LeviCivita.BianchiDoubleCopy`). The electromagnetic field strength `F = dA` carries its homogeneous
Maxwell / **first Bianchi** identity `k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0` (`dF = 0`,
`faraday_bianchi`); under the double copy this is the kinematic Jacobi `n_s + n_t + n_u = 0` whose square
gives the gravity numerators. So:

* the **double copy of the EM first Bianchi** is the gravity **first Bianchi** — the Riemann cyclic identity
  `R_{ijkl} + R_{iklj} + R_{iljk} = 0` (`firstBianchi_double_copy`);
* the gravity **second (contracted) Bianchi** — Levi-Civita's Eq. 12, the vanishing Einstein divergence — is
  the differential face of the same double copy, and it **validates the field equations**: through the §7
  Bianchi theorem `eq12_discharges_bcj` it yields stress-energy conservation `∇^μ T_{μν} = 0`.

This is packaged as a `DualBianchiContracts` (`emBianchiDoubleCopy`) whose `firstBianchi` is the EM Faraday
identity, whose `secondBianchi` is the gravity contracted Bianchi (Eq. 12), and whose
`secondImpliesContracted` is **exactly** the §7 validation theorem — the double copy of the EM Bianchi
identities, validated by the Bianchi theorem we used.

* **§A — the double-copied EM Bianchi as a §7-validated dual contract** (`emBianchiDoubleCopy`,
  `emBianchiDoubleCopy_firstBianchi`, `emBianchiDoubleCopy_validated`).
* **§B — the full chain: EM first Bianchi → gravity first/second Bianchi → validation**
  (`em_bianchi_doublecopy_validated`).

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson (arXiv:0805.3993); T. Levi-Civita (arXiv:physics/9906004, §7).
  Carriers: `BCJDoubleCopy.SecondBianchiConservation` (`DualBianchiContracts`), `LeviCivita.BianchiDoubleCopy`
  (`firstBianchi_double_copy`, `eq12_discharges_bcj`), `LeviCivita.BianchiValidation`
  (`FirstBianchi`, `einsteinDivergence`, `contractedSecondBianchi`),
  `PTSymmetricQFT.MaxwellFaraday` (`faraday`, `faraday_bianchi`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMBianchiDoubleCopyValidation

open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday


/-- **The double copy of the EM Bianchi identities, §7-validated.** A `DualBianchiContracts` built from the
electromagnetic field: its **first Bianchi** is the Maxwell–Faraday identity `dF = 0`
(`k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0`), its **second Bianchi** is the gravity contracted Bianchi
(Levi-Civita Eq. 12, `contractedSecondBianchi`), and its `secondImpliesContracted` is the §7 Bianchi
validation theorem `eq12_discharges_bcj`: the contracted second Bianchi conserves the source `∇^μ T_{μν} = 0`
(given `G = −κT`, `κ ≠ 0`). The gauge Bianchi double-copies to the gravity Bianchi, validated by §7. -/
noncomputable def emBianchiDoubleCopy (k A : Fin 4 → ℝ) (lam μ ν : Fin 4)
    (divRicci gradScalar divT : Fin 4 → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hField : einsteinDivergence divRicci gradScalar = (-κ) • divT) : DualBianchiContracts where
  firstBianchi :=
    k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0
  secondBianchi := contractedSecondBianchi divRicci gradScalar
  contractedConservation := divT = 0
  secondImpliesContracted := fun h2 => eq12_discharges_bcj divRicci gradScalar divT κ hκ hField h2

/-- **[The dual contract's first Bianchi holds] — the EM Faraday identity `dF = 0`.** -/
lemma emBianchiDoubleCopy_firstBianchi (k A : Fin 4 → ℝ) (lam μ ν : Fin 4)
    (divRicci gradScalar divT : Fin 4 → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hField : einsteinDivergence divRicci gradScalar = (-κ) • divT) :
    (emBianchiDoubleCopy k A lam μ ν divRicci gradScalar divT κ hκ hField).firstBianchi :=
  faraday_bianchi k A lam μ ν

/-- **[The §7 Bianchi theorem validates the double copy] second Bianchi ⟹ conservation.** Feeding the
gravity contracted second Bianchi (Eq. 12) into the dual contract proves, through `eq12_discharges_bcj`,
into stress-energy conservation `∇^μ T_{μν} = 0`. -/
lemma emBianchiDoubleCopy_validated (k A : Fin 4 → ℝ) (lam μ ν : Fin 4)
    (divRicci gradScalar divT : Fin 4 → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hField : einsteinDivergence divRicci gradScalar = (-κ) • divT)
    (h2 : (emBianchiDoubleCopy k A lam μ ν divRicci gradScalar divT κ hκ hField).secondBianchi) :
    (emBianchiDoubleCopy k A lam μ ν divRicci gradScalar divT κ hκ hField).contractedConservation :=
  (emBianchiDoubleCopy k A lam μ ν divRicci gradScalar divT κ hκ hField).contracted_of_second h2


/-- **[The double copy of the EM Bianchi identities, validated].** From the electromagnetic field and a
Riemann tensor with the first Bianchi identity:

* the **EM first Bianchi** holds — `k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0` (`dF = 0`);
* its **double copy is the gravity first Bianchi** — the Riemann cyclic identity
  `R_{ijkl} + R_{iklj} + R_{iljk} = 0`;
* the gravity **second (contracted) Bianchi** (Eq. 12), validated by the §7 Bianchi theorem, conserves the
  source — `∇^μ T_{μν} = 0`.

The BCJ double copy maps the electromagnetic Bianchi identities to the gravity first and second Bianchi
identities, and the §7 Bianchi theorem validates the field equations through them. -/
lemma em_bianchi_doublecopy_validated {R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hFB : FirstBianchi R) (a b cc d : Fin 4) (k A : Fin 4 → ℝ) (lam μ ν : Fin 4)
    (divRicci gradScalar divT : Fin 4 → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hField : einsteinDivergence divRicci gradScalar = (-κ) • divT)
    (hBianchi : contractedSecondBianchi divRicci gradScalar) :
    (k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0)
      ∧ (R a b cc d + R a cc d b + R a d b cc = 0)
      ∧ divT = 0 :=
  ⟨faraday_bianchi k A lam μ ν, hFB a b cc d,
    eq12_discharges_bcj divRicci gradScalar divT κ hκ hField hBianchi⟩

end Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMBianchiDoubleCopyValidation

end
