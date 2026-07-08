/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation

/-!
# The Levi-Civita Bianchi validation and the double copy: gravity ↔ gauge Bianchi identities

Links Levi-Civita's **§7 formal validation from the Bianchi identities** (`LeviCivita.BianchiValidation`,
the curvature/gravity side) to the **gauge-side Bianchi identities** of the BCJ double copy
(`BCJDoubleCopy.SecondBianchiConservation`). Both Bianchi identities appear on each side of the double copy, and the
two validations are the same statement read on the two sides:

* the **first Bianchi identity** is cyclic on both sides — the gravity-side **Riemann cyclic identity**
  `R_{ijkl} + R_{iklj} + R_{iljk} = 0` (`FirstBianchi`, `LeviCivita.BianchiValidation`) and the gauge-side
  **Maxwell cyclic identity** `k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0` (`faraday_bianchi`, the BCJ
  kinematic Jacobi `n_s + n_t + n_u = 0`) — the two first Bianchi identities of the double copy
  (`firstBianchi_double_copy`);

* the **second (contracted) Bianchi identity** validates the field equations on both sides — Levi-Civita's
  Eq. 12 `∑ g^{(kl)}G_{ikl} − ½ G_i = 0` (`contractedSecondBianchi`, the vanishing Einstein divergence) is
  the gravity-side instance of the BCJ contracted second Bianchi `∇^μ G_{μν} = 0`; with the field equation
  it yields stress-energy conservation `∇^μ T_{μν} = 0` through the *same* implication
  (`eq12_discharges_bcj`, routing Levi-Civita's Eq. 12 through `contracted_bianchi_conservation`).

So Levi-Civita's §7 validation is the gravity face of the double copy's Bianchi structure: the first
Bianchi (cyclic) is the kinematic-Jacobi face on both sides, and the contracted second Bianchi is the
on-shell transversality / conservation face on both sides.

* **§A — the two first Bianchi identities of the double copy** (`firstBianchi_double_copy`).
* **§B — the contracted second Bianchi: Levi-Civita's Eq. 12 yields BCJ conservation**
  (`eq12_discharges_bcj`).
* **§C — the assembly** (`leviCivita_bianchi_double_copy_validation`).

## References

* T. Levi-Civita (arXiv:physics/9906004, §7); Z. Bern, J. J. M. Carrasco, H. Johansson (arXiv:0805.3993).
  structures: `LeviCivita.BianchiValidation` (`FirstBianchi`, `contractedSecondBianchi`,
  `einsteinDivergence_eq_zero_iff`), `BCJDoubleCopy.SecondBianchiConservation` (`contracted_bianchi_conservation`),
  `PTSymmetricQFT.MaxwellFaraday` (`faraday`, `faraday_bianchi`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiDoubleCopy

open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.SecondBianchiConservation
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday

/-! ## §A — the two first Bianchi identities of the double copy -/

/-- **[The first Bianchi identity on both sides of the double copy].** The gravity-side **Riemann cyclic
identity** `R_{ijkl} + R_{iklj} + R_{iljk} = 0` (from `FirstBianchi`, Levi-Civita's "well known properties
of the Riemann symbols") and the gauge-side **Maxwell cyclic identity**
`k_λ F_{μν} + k_μ F_{νλ} + k_ν F_{λμ} = 0` (`faraday_bianchi`, the BCJ kinematic Jacobi) are the two first
Bianchi identities of the double copy — the homogeneous (cyclic) identity on the curvature and on the field
strength. -/
theorem firstBianchi_double_copy {R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hFB : FirstBianchi R) (a b c d : Fin 4) (k A : Fin 4 → ℝ) (lam μ ν : Fin 4) :
    (R a b c d + R a c d b + R a d b c = 0)
      ∧ (k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0) :=
  ⟨hFB a b c d, faraday_bianchi k A lam μ ν⟩

/-! ## §B — the contracted second Bianchi: Levi-Civita's Eq. 12 yields BCJ conservation -/

/-- **[Levi-Civita's Eq. 12 yields the BCJ contracted-Bianchi conservation] `∇^μ T_{μν} = 0`.**
Levi-Civita's twice-contracted second Bianchi identity (Eq. 12, the vanishing Einstein divergence
`einsteinDivergence = 0`) is exactly the BCJ contracted second Bianchi `∇^μ G_{μν} = 0`; routed through the
field equation `G = −κT` (`κ ≠ 0`) it yields stress-energy conservation `∇^μ T_{μν} = 0` via the
double copy's `contracted_bianchi_conservation`. The gravity-side §7 validation is the same implication as
the BCJ gravity-side conservation. -/
theorem eq12_discharges_bcj (divRicci gradScalar divT : Fin 4 → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hField : einsteinDivergence divRicci gradScalar = (-κ) • divT)
    (hBianchi : contractedSecondBianchi divRicci gradScalar) : divT = 0 :=
  contracted_bianchi_conservation (-κ) (neg_ne_zero.mpr hκ)
    (einsteinDivergence divRicci gradScalar) divT hField
    ((einsteinDivergence_eq_zero_iff divRicci gradScalar).mpr hBianchi)

/-! ## §C — the assembly -/

/-- **[Levi-Civita's §7 validation as the gravity face of the double copy's Bianchi structure].** For a
Riemann tensor `R` with the first Bianchi identity, a Faraday field, and the contracted second Bianchi (Eq.
12) with the field equation `G = −κT` (`κ ≠ 0`):

* the gravity-side first Bianchi (Riemann cyclic) and the gauge-side first Bianchi (Maxwell cyclic / BCJ
  kinematic Jacobi) both hold — the two first Bianchi identities of the double copy;
* Levi-Civita's Eq. 12 (the contracted second Bianchi) yields stress-energy conservation
  `∇^μ T_{μν} = 0`, the same conservation as the BCJ gravity side.

Levi-Civita's §7 formal validation is the gravity face of the double copy's Bianchi structure: cyclic first
Bianchi (kinematic Jacobi) on both sides, contracted second Bianchi (conservation) on both sides. -/
theorem leviCivita_bianchi_double_copy_validation {R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hFB : FirstBianchi R) (a b c d : Fin 4) (k A : Fin 4 → ℝ) (lam μ ν : Fin 4)
    (divRicci gradScalar divT : Fin 4 → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hField : einsteinDivergence divRicci gradScalar = (-κ) • divT)
    (hBianchi : contractedSecondBianchi divRicci gradScalar) :
    (R a b c d + R a c d b + R a d b c = 0)
      ∧ (k lam * faraday k A μ ν + k μ * faraday k A ν lam + k ν * faraday k A lam μ = 0)
      ∧ divT = 0 :=
  ⟨hFB a b c d, faraday_bianchi k A lam μ ν,
    eq12_discharges_bcj divRicci gradScalar divT κ hκ hField hBianchi⟩

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiDoubleCopy

end
