/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon

/-!
# Hawking radiation is thermal: the Bose–Einstein spectrum and KMS detailed balance at `T = κ/2π` (Kay–Wald)

Completes the Kay–Wald thermal picture: the KMS state at the Hawking temperature `T = κ/2π` on the bifurcate
Killing horizon (`KayWaldHawkingKMSHorizon`) radiates with a **thermal Bose–Einstein spectrum**, and the KMS
condition is the **detailed balance** between emission and absorption — the Boltzmann factor `e^{−βω}` — which is
the arc's entropic weight.

* the **Hawking occupation number** is Bose–Einstein `n(ω) = 1/(e^{βω} − 1)` at the Hawking inverse temperature
 `β = 2π/κ` (`hawkingOccupation`) — the thermal spectrum of black-hole / Killing-horizon radiation, the same
 `boseEinstein` occupation as the repository's thermofield oscillator;
* the **KMS detailed balance** `n/(n+1) = e^{−βω}` (`hawking_detailed_balance`) — the ratio of stimulated to total
 emission is the Boltzmann factor, the defining thermal (KMS) relation of the Hawking state;
* the **detailed-balance factor is the entropic weight** `e^{−βω} = kuikenWeight (1/β) ω = kuikenWeight T_H ω`
 (`detailed_balance_is_kuiken`) — the Hawking radiation's Boltzmann factor at `T_H = κ/2π` sits on the same
 `kuikenWeight = e^{−·/·}` hub as the quasi-free state, confinement, and the entropic-dynamics transition
 probability.

So the Kay–Wald KMS state on a bifurcate Killing horizon emits a thermal Bose–Einstein spectrum at the Hawking
temperature, its detailed-balance Boltzmann factor is the arc's entropic weight — the Hawking effect, from the
horizon geometry (`U = e^{κv}`) through the KMS periodicity (`2π/κ`) to the thermal radiation spectrum, all on the
`kuikenWeight` hub.

* **§A — the Bose–Einstein occupation** (`hawkingOccupation`).
* **§B — KMS detailed balance = the Boltzmann factor** (`hawking_detailed_balance`).
* **§C — the Boltzmann factor is the entropic weight** (`detailed_balance_is_kuiken`).

The Bose–Einstein occupation, the detailed-balance identity, and the `kuikenWeight`
identification are exact `Real.exp` algebra. The greybody factors, the mode-by-mode Bogoliubov derivation of the
spectrum, and the full KMS analyticity are the referenced content. No new axioms.

## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49; S.W. Hawking (thermal radiation). Repo dependencies:
 `EntropicTime.KayWaldHawkingKMSHorizon`, `ThermoFieldDynamics.MatsubaraThermalOscillator` (`boseEinstein`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein

/-! ## §A — the Bose–Einstein occupation -/

/-- **The Hawking occupation number** `n(ω) = 1/(e^{βω} − 1)` at the Hawking inverse temperature `β = 2π/κ` — the
thermal Bose–Einstein spectrum of radiation from a bifurcate Killing horizon (the same `boseEinstein` occupation
as the thermofield oscillator). -/
noncomputable def hawkingOccupation (β ω : ℝ) : ℝ := 1 / (Real.exp (β * ω) - 1)

/-! ## §B — KMS detailed balance = the Boltzmann factor -/

/-- **[KMS detailed balance: `n/(n+1) = e^{−βω}`].** The ratio of stimulated emission to total emission of the
Hawking thermal state is the Boltzmann factor `e^{−βω}`: `n = 1/(e^{βω}−1)`, `n+1 = e^{βω}/(e^{βω}−1)`, so
`n/(n+1) = e^{−βω}` — the detailed-balance / KMS condition defining thermal equilibrium at the Hawking
temperature. -/
theorem hawking_detailed_balance (β ω : ℝ) (h : Real.exp (β * ω) - 1 ≠ 0) :
    hawkingOccupation β ω / (hawkingOccupation β ω + 1) = Real.exp (-(β * ω)) := by
  unfold hawkingOccupation
  have hE : Real.exp (β * ω) ≠ 0 := Real.exp_ne_zero _
  rw [Real.exp_neg]
  field_simp
  ring

/-! ## §C — the Boltzmann factor is the entropic weight -/

/-- **[The Hawking Boltzmann factor is the entropic weight] `e^{−βω} = kuikenWeight (1/β) ω`.** The
detailed-balance Boltzmann factor of the Hawking thermal state is the complex-action entropic weight
`kuikenWeight c Π = e^{−Π/c}` at `c = 1/β = T_H = κ/2π`: the Hawking radiation spectrum lives on the arc's
`kuikenWeight` hub. -/
theorem detailed_balance_is_kuiken (β ω : ℝ) :
    Real.exp (-(β * ω)) = kuikenWeight (1 / β) ω := by
  unfold kuikenWeight
  rw [one_div, div_inv_eq_mul]
  ring_nf

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein

end
