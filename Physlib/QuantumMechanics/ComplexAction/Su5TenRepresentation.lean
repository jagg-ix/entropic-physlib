/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Su5ElectroweakParticleLinks

/-!
# The `SU(5)` `10` representation — completing the fermion generation

A Standard-Model fermion generation fills the `SU(5)` reducible representation `5̄ ⊕ 10`. The `5̄`
`= (d^c, d^c, d^c, e⁻, ν)` was formalized in `Su5ChargeQuantizationCartanTensor` /
`Su5ElectroweakParticleLinks`. The **`10` = Λ²(5)** holds the rest of the generation: the quark
doublet `Q = (u, d)` in three colours, the up antiquark `u^c` in three colours, and the positron
`e⁺` — `3 + 3 + 3 + 1 = 10` states.

* **§A — the `10` electric charges** (`su5TenCharge`), tied to the winding charges: `u = +2/3`
  (`su5Ten_up_charge`), `d = −1/3` (`su5Ten_down_charge`), `u^c = −2/3` (`su5Ten_upAntiquark_charge`),
  `e⁺ = +1` (`su5Ten_positron_charge`, `= windingCharge 3 = Q(W⁺)`).
* **§B — charge quantization on the `10`**: electric charge is a traceless `SU(5)` generator on the
  `10` too, so `∑ Q = 0` (`su5TenCharge_isAffineWeight`, reusing `IsAffineWeight`).
* **§C — the full generation `5̄ ⊕ 10`**: the electric charge sums to zero over the whole generation
  (`su5_generation_charge_neutral`) — the mixed gravitational–`U(1)` anomaly cancels because `Q` is
  traceless on each irreducible piece; the generation has `5 + 10 = 15` chiral states
  (`su5_generation_state_count`).

**Honest layering.** Proven: the `10` charges match the winding charges, `Tr(Q) = 0` on the `10`, and
the full-generation charge neutrality. Interpretive: the identification with the `SM` multiplets and
the full gauge-anomaly cancellation (cubic Casimir `A(5̄) + A(10) = 0`) are the representation theory
this charge structure sits inside, not re-derived here.

## References

* H. Georgi, S. L. Glashow, "Unity of All Elementary-Particle Forces", Phys. Rev. Lett. **32**, 438
  (1974) — the `5̄ ⊕ 10` generation. Reuses `Su5ChargeQuantizationCartanTensor` (`su5AntifundCharge`,
  `IsAffineWeight`), `Winding.QuarkChargeWinding`, `GaugeBosonClassification` (`Wplus_charge`).


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Su5TenRepresentation

open Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4
open Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor
open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
open Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification


/-- **The electric charges of the `SU(5)` `10 = Λ²(5)`** `= (u, u, u, d, d, d, u^c, u^c, u^c, e⁺)`:
the quark doublet `(u, d)` in three colours, the up antiquark `u^c` in three colours, and the
positron `e⁺`. -/
def su5TenCharge : Fin 10 → ℚ := ![2/3, 2/3, 2/3, -1/3, -1/3, -1/3, -2/3, -2/3, -2/3, 1]

/-- **The up quark `u` charge `+2/3`** = `windingCharge upWinding` (reusing `upQuark_charge`). -/
lemma su5Ten_up_charge : su5TenCharge 0 = windingCharge upWinding := by
  rw [upQuark_charge]; simp [su5TenCharge]

/-- **The down quark `d` charge `−1/3`** = `windingCharge downWinding` (reusing `downQuark_charge`). -/
lemma su5Ten_down_charge : su5TenCharge 3 = windingCharge downWinding := by
  rw [downQuark_charge]; simp [su5TenCharge]

/-- **The up antiquark `u^c` charge `−2/3`** = `windingCharge (-2)` — the charge conjugate of `u`. -/
lemma su5Ten_upAntiquark_charge : su5TenCharge 6 = windingCharge (-2) := by
  simp [su5TenCharge, windingCharge]

/-- **The positron `e⁺` charge `+1`** = `windingCharge 3 = Q(W⁺)` (reusing `Wplus_charge`). -/
lemma su5Ten_positron_charge : su5TenCharge 9 = windingCharge 3 := by
  rw [Wplus_charge]; simp [su5TenCharge]


/-- **Electric charge is a traceless `SU(5)` generator on the `10`**: `∑ Q = 0` — the same
tracelessness (`IsAffineWeight`) that quantized the `5̄` charges holds on the `10`. -/
lemma su5TenCharge_isAffineWeight : IsAffineWeight su5TenCharge := by
  unfold IsAffineWeight su5TenCharge
  simp [Fin.sum_univ_succ]; norm_num


/-- **The electric charge cancels over a full generation** `5̄ ⊕ 10`: `∑_{5̄} Q + ∑_{10} Q = 0` —
because `Q` is traceless on each irreducible piece, the mixed gravitational–`U(1)` anomaly of a
generation vanishes. -/
lemma su5_generation_charge_neutral :
    (∑ i, su5AntifundCharge i) + (∑ i, su5TenCharge i) = 0 := by
  have h5 : ∑ i, su5AntifundCharge i = 0 := su5AntifundCharge_isAffineWeight
  have h10 : ∑ i, su5TenCharge i = 0 := su5TenCharge_isAffineWeight
  rw [h5, h10]; ring

/-- **A `SU(5)` fermion generation has `5 + 10 = 15` chiral states.** -/
lemma su5_generation_state_count :
    Fintype.card (Fin 5) + Fintype.card (Fin 10) = 15 := by decide

end Physlib.QuantumMechanics.ComplexAction.Su5TenRepresentation
