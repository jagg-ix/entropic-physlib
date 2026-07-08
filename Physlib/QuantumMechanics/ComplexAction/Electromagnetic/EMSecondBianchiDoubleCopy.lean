/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMBianchiDoubleCopyValidation
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant

/-!
# The EM second Bianchi (current conservation) and its double copy to gravity conservation

Completes the double copy of the electromagnetic Bianchi identities
(`Electromagnetic.EMBianchiDoubleCopyValidation` handled the *first*) by formalizing the **second** Bianchi on the EM
field and its gravity double copy. The electromagnetic field has two Bianchi-type identities:

* the **first Bianchi** — the homogeneous Maxwell equation `dF = 0`
  (`k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0`, `faraday_bianchi`), double-copied to the gravity **first
  Bianchi** (Riemann cyclic) in `Electromagnetic.EMBianchiDoubleCopyValidation`;
* the **second Bianchi** — the contracted Maxwell identity `∂_ν J^ν = 0` (`fourCurrent_conserved`,
  `Electromagnetic.MaxwellContinuityCovariant`), the **current conservation** that follows from `J^ν = ∂_μ F^{μν}` because a
  symmetric derivative pair contracts an antisymmetric `F` to zero. This is the gauge-side **contracted**
  identity, the double copy of which is the gravity **second (contracted) Bianchi** — the stress-energy
  conservation `∇^μ T_{μν} = 0` validated by the §7 Bianchi theorem (`eq12_discharges_bcj`).

So both Bianchi identities double-copy from gauge to gravity, with the same conservation law on each side:

* first Bianchi: `dF = 0` (gauge) ↔ Riemann cyclic (gravity);
* second Bianchi: `∂_ν J^ν = 0` (gauge current conservation) ↔ `∇^μ T_{μν} = 0` (gravity stress-energy
  conservation).

* **§A — the EM second Bianchi: current conservation** (`em_second_bianchi`).
* **§B — the first and second Bianchi double copy, validated**
  (`em_first_and_second_bianchi_doublecopy`).

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson (arXiv:0805.3993); R. Heras (covariant Maxwell continuity);
  T. Levi-Civita (arXiv:physics/9906004, §7). structures: `Electromagnetic.MaxwellContinuityCovariant` (`fourCurrent`,
  `fourCurrent_conserved`), `Electromagnetic.EMBianchiDoubleCopyValidation` / `LeviCivita.BianchiDoubleCopy`
  (`firstBianchi_double_copy`, `eq12_discharges_bcj`), `PTSymmetricQFT.MaxwellFaraday` (`faraday`,
  `faraday_bianchi`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSecondBianchiDoubleCopy

open scoped BigOperators

open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant

/-! ## §A — the EM second Bianchi: current conservation `∂_ν J^ν = 0` -/

/-- **The EM second Bianchi identity** `∂_ν J^ν = 0` — the contracted Maxwell identity. With the four-current
`J^ν = ∂_μ F^{μν}` (`fourCurrent`), its four-divergence vanishes because the symmetric derivative pair
contracts the antisymmetric field strength `F` to zero (`fourCurrent_conserved`). This current conservation
is the gauge-side contracted (second) Bianchi, the analog of the gravity contracted second Bianchi
`∇^μ G_{μν} = 0`. -/
theorem em_second_bianchi (k A : Fin 4 → ℝ) : ∑ i, k i * fourCurrent k A i = 0 :=
  fourCurrent_conserved k A

/-! ## §B — the first and second Bianchi double copy, validated -/

/-- **[The EM first and second Bianchi identities double-copy to gravity, validated].** For the
electromagnetic field and a Riemann tensor with the first Bianchi identity, both Bianchi identities map
across the double copy with the same conservation law on each side:

* **first Bianchi** — the EM homogeneous Maxwell `dF = 0` (`k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0`)
  double-copies to the gravity Riemann cyclic identity `R_{ijkl} + R_{iklj} + R_{iljk} = 0`;
* **second Bianchi** — the EM current conservation `∂_ν J^ν = 0` double-copies to the gravity stress-energy
  conservation `∇^μ T_{μν} = 0`, validated by the §7 Bianchi theorem (`eq12_discharges_bcj`).

The electromagnetic and gravitational Bianchi structures are the two sides of the double copy: `dF = 0` ↔
Riemann cyclic (first), `∂J = 0` ↔ `∇T = 0` (second). -/
theorem em_first_and_second_bianchi_doublecopy {R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hFB : FirstBianchi R) (a b cc d : Fin 4) (k A : Fin 4 → ℝ) (lam μ ν : Fin 4)
    (divRicci gradScalar divT : Fin 4 → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hField : einsteinDivergence divRicci gradScalar = (-κ) • divT)
    (hBianchi : contractedSecondBianchi divRicci gradScalar) :
    (k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0)
      ∧ (R a b cc d + R a cc d b + R a d b cc = 0)
      ∧ (∑ i, k i * fourCurrent k A i = 0)
      ∧ divT = 0 :=
  ⟨faraday_bianchi k A lam μ ν, hFB a b cc d, em_second_bianchi k A,
    eq12_discharges_bcj divRicci gradScalar divT κ hκ hField hBianchi⟩

end Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMSecondBianchiDoubleCopy

end
