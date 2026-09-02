/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Su5WeinbergGutNormalization
public import Physlib.QuantumMechanics.ComplexAction.Particles.GellMannStructureConstants
public import Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification

/-!
# Links: the `SU(5)` `5̄` charges are the repository's particle charges

The `SU(5)` electroweak development (`Su5ChargeQuantizationCartanTensor`, `WeinbergAngle`,
`Su5WeinbergGutNormalization`) assigns electric charges to the `5̄ = (d^c, d^c, d^c, e⁻, ν)` as a
`ℚ`-vector `su5AntifundCharge`. This module shows those are exactly the charges already carried by the
winding model and the canonical Gell-Mann–Nishijima relation, so the new work is tied into the
existing particle infrastructure rather than a parallel copy.

* **§A — the `5̄` charges are the winding charges** (`Winding.QuarkChargeWinding.windingCharge`): the
  down antiquark is `+1/3` (`su5_downAntiquark_charge`), the electron `−1` (`su5_electron_charge`,
  reusing `electron_charge`), the neutrino `0` (`su5_neutrino_charge`, reusing `neutrino_charge`).
* **§B — the `(T₃, Y)` reproduce the canonical Gell-Mann–Nishijima** `Q = T₃ + Y/2`
  (`Particles.GellMannNishijima.gellMannNishijima`): `su5_charge_eq_canonical_gmn`, reconciling the
  two hypercharge conventions (this module's `Y` is half the conventional one, `2 · hyperchargeY`).
* **§C — the lepton-doublet charge splitting is the `W±` charge**: `Q(ν) − Q(e⁻) = 1 = Q(W⁺)`
  (`su5_leptonDoublet_splitting_eq_Wcharge`, reusing `GaugeBosonClassification.Wplus_charge`) — the
  intra-doublet splitting of `GellMannNishijima.doublet_charge_splitting`.


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Su5ElectroweakParticleLinks

open Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor
open Physlib.QuantumMechanics.ComplexAction.WeinbergAngle
open Physlib.QuantumMechanics.ComplexAction.Su5WeinbergGutNormalization
open Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
open Physlib.QuantumMechanics.ComplexAction.Particles.GellMannNishijima
open Physlib.QuantumMechanics.ComplexAction.Particles.GaugeBosonClassification


/-- **The down antiquark `d^c` charge `+1/3`** = `windingCharge 1` (the anti-down, `−`winding of the
down quark `windingCharge (-1) = −1/3`). -/
lemma su5_downAntiquark_charge : su5AntifundCharge 0 = windingCharge 1 := by
  simp [su5AntifundCharge, windingCharge]

/-- **The electron charge `−1`** = `windingCharge (-3)` — reusing `Winding.electron_charge`. -/
lemma su5_electron_charge : su5AntifundCharge 3 = windingCharge (-3) := by
  rw [electron_charge]; simp [su5AntifundCharge]

/-- **The neutrino charge `0`** = `windingCharge 0` — reusing `Winding.neutrino_charge`. -/
lemma su5_neutrino_charge : su5AntifundCharge 4 = windingCharge 0 := by
  rw [neutrino_charge]; simp [su5AntifundCharge]


/-- **The `5̄` charges are the canonical Gell-Mann–Nishijima charges** `Q = T₃ + Y_conv/2`, with the
conventional weak hypercharge `Y_conv = 2 · hyperchargeY` (this module normalizes `Y` to add directly
to `T₃`). Reuses the repository's `Particles.GellMannNishijima.gellMannNishijima`. -/
lemma su5_charge_eq_canonical_gmn (i : Fin 5) :
    su5AntifundCharge i = gellMannNishijima (weakIsospin3 i) (2 * hyperchargeY i) := by
  rw [su5Charge_isospin_add_hypercharge i]
  unfold gellMannNishijima
  ring


/-- **The `5̄` lepton-doublet charge splitting is the `W⁺` charge**: `Q(ν) − Q(e⁻) = 1 = Q(W⁺)`
(`windingCharge 3`, reusing `GaugeBosonClassification.Wplus_charge`) — the intra-doublet charge
difference of `GellMannNishijima.doublet_charge_splitting`, carried by the `W`. -/
lemma su5_leptonDoublet_splitting_eq_Wcharge :
    su5AntifundCharge 4 - su5AntifundCharge 3 = windingCharge 3 := by
  rw [Wplus_charge]; simp [su5AntifundCharge]

end Physlib.QuantumMechanics.ComplexAction.Su5ElectroweakParticleLinks
