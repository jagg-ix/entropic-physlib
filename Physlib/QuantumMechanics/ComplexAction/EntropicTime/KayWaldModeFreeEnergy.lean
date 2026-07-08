/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBosonicThermalEntropy

/-!
# The free energy of a Hawking mode and the Gibbs relation `F = ⟨E⟩ − TS` (Kay–Wald)

Closes the thermodynamics of a single bosonic Killing-horizon mode in the Hawking–KMS state: the **partition
function** `Z = 1/(1 − e^{−βω}) = n + 1`, the **mean energy** `⟨E⟩ = ωn`, the **Helmholtz free energy**
`F = −T ln Z = −(1/β) ln(n+1)`, and the **Gibbs (thermodynamic) relation**

`F = ⟨E⟩ − T S`, equivalently `T S = ⟨E⟩ − F`,

tying together the free energy, the mean energy, and the bosonic thermal entropy `S = βω·n + ln(n+1)` of
`KayWaldBosonicThermalEntropy`. Everything rides on the single identity `Z = n + 1`: the single-mode partition
function is the total-emission occupation, so `ln Z = ln(n+1)` is exactly the free-energy term appearing in the
entropy's first-law split.

* the **single-mode partition function is the total-emission occupation** `Z = 1/(1 − e^{−βω}) = n + 1`
 (`modePartition_eq_occupation_add_one`);
* the **Gibbs relation** `F = ⟨E⟩ − T S` (`gibbs_relation`) — the Helmholtz free energy equals the mean energy
 minus the temperature times the entropy, the defining thermodynamic identity of the equilibrium (KMS) state;
* the **Clausius / heat form** `T S = ⟨E⟩ − F` (`heat_eq_energy_minus_free`) — the heat content of the thermal
 mode;
* the **Hawking specialization** `β = 2π/κ` (`hawking_gibbs_relation`) — the Gibbs relation for a
 bifurcate-Killing-horizon mode at the Hawking temperature.

So the Kay–Wald thermal mode obeys the full Gibbs thermodynamics `F = ⟨E⟩ − TS` with `Z = n+1`, `⟨E⟩ = ωn`, and
the bosonic entropy `S`; the free energy, energy, and entropy of the Hawking radiation are one consistent
equilibrium, on the same thermal spine as the KMS periodicity and the entropy.

* **§A — the partition function `Z = n + 1`** (`modeMeanEnergy`, `modePartitionFunction`, `modeFreeEnergy`,
 `modePartition_eq_occupation_add_one`).
* **§B — the Gibbs relation and its heat form** (`gibbs_relation`, `heat_eq_energy_minus_free`).
* **§C — the Hawking specialization `β = 2π/κ`** (`hawking_gibbs_relation`).

The partition-function identity, the free-energy definition, and the Gibbs relation are exact
`Real.log`/`Real.exp` algebra for a single mode with mean energy `⟨E⟩ = ωn` (zero-point energy omitted, as is
conventional for the radiation content). The full grand-canonical ensemble, the integrated Stefan–Boltzmann free
energy (`StatisticalMechanics.MasslessStefanBoltzmann`, a distinct integrated object), and the operator-algebraic
KMS derivation are the referenced content. No new axioms.

## References

* B.S. Kay, R.M. Wald, Phys. Rep. 207 (1991) 49; standard equilibrium thermodynamics. Repo structure:
 `EntropicTime.KayWaldBosonicThermalEntropy` (`bosonicEntropy`, `bosonicEntropy_thermal`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingRadiationBoseEinstein
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldHawkingKMSHorizon
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldBosonicThermalEntropy

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy

/-! ## §A — the partition function `Z = n + 1` -/

/-- **The mean energy of the thermal mode** `⟨E⟩ = ωn` — the mode frequency times the Bose occupation (the
radiation energy above the ground state). -/
noncomputable def modeMeanEnergy (β ω : ℝ) : ℝ := ω * hawkingOccupation β ω

/-- **The single-mode bosonic partition function** `Z = 1/(1 − e^{−βω})` — the geometric sum over the oscillator
tower `Σ_k e^{−βωk}`. -/
noncomputable def modePartitionFunction (β ω : ℝ) : ℝ := 1 / (1 - Real.exp (-(β * ω)))

/-- **The Helmholtz free energy of the mode** `F = −T ln Z = −(1/β) ln Z` — the free energy of the thermal
Killing-horizon mode. -/
noncomputable def modeFreeEnergy (β ω : ℝ) : ℝ := -(1 / β) * Real.log (modePartitionFunction β ω)

/-- **[The single-mode partition function is the total-emission occupation] `Z = 1/(1 − e^{−βω}) = n + 1`.** The
geometric partition function of the bosonic tower equals `n + 1` with `n = 1/(e^{βω}−1)` the Bose occupation, so
`ln Z = ln(n+1)` is exactly the free-energy term in the entropy's first-law split. -/
theorem modePartition_eq_occupation_add_one (β ω : ℝ) (hβω : 0 < β * ω) :
    modePartitionFunction β ω = hawkingOccupation β ω + 1 := by
  have hE1 : 1 < Real.exp (β * ω) := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hβω
  have hEne : Real.exp (β * ω) ≠ 0 := (Real.exp_pos _).ne'
  have hd : Real.exp (β * ω) - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; exact absurd h.symm (by linarith)
  unfold modePartitionFunction hawkingOccupation
  rw [Real.exp_neg]
  field_simp
  ring

/-! ## §B — the Gibbs relation and its heat form -/

/-- **[The Gibbs relation] `F = ⟨E⟩ − T S`.** The Helmholtz free energy of the thermal mode equals the mean energy
minus temperature times entropy (`T = 1/β`): using `Z = n+1` and the first-law entropy `S = βω·n + ln(n+1)`, the
`ω n` terms cancel and leave `F = −(1/β) ln(n+1)`. This is the defining thermodynamic identity of the equilibrium
(KMS) state. -/
theorem gibbs_relation (β ω : ℝ) (hβ : β ≠ 0) (hβω : 0 < β * ω) :
    modeFreeEnergy β ω
      = modeMeanEnergy β ω - (1 / β) * bosonicEntropy (hawkingOccupation β ω) := by
  unfold modeFreeEnergy modeMeanEnergy
  rw [modePartition_eq_occupation_add_one β ω hβω, bosonicEntropy_thermal β ω hβω]
  field_simp
  ring

/-- **[The Clausius / heat form] `T S = ⟨E⟩ − F`.** Rearranging the Gibbs relation: the heat content `T S` of the
thermal mode is the mean energy minus the free energy. -/
theorem heat_eq_energy_minus_free (β ω : ℝ) (hβ : β ≠ 0) (hβω : 0 < β * ω) :
    (1 / β) * bosonicEntropy (hawkingOccupation β ω) = modeMeanEnergy β ω - modeFreeEnergy β ω := by
  rw [gibbs_relation β ω hβ hβω]; ring

/-! ## §C — the Hawking specialization `β = 2π/κ` -/

/-- **[The Gibbs relation for a Hawking mode at `T_H = κ/2π`].** Specializing to the Hawking inverse temperature
`β = hawkingBeta 1 κ 1 1 = 2π/κ`: the free energy, mean energy, and bosonic entropy of a bifurcate-Killing-horizon
mode form a consistent equilibrium `F = ⟨E⟩ − T_H S`. -/
theorem hawking_gibbs_relation (κ ω : ℝ) (hβ : hawkingBeta 1 κ 1 1 ≠ 0)
    (hκω : 0 < hawkingBeta 1 κ 1 1 * ω) :
    modeFreeEnergy (hawkingBeta 1 κ 1 1) ω
      = modeMeanEnergy (hawkingBeta 1 κ 1 1) ω
        - (1 / hawkingBeta 1 κ 1 1) * bosonicEntropy (hawkingOccupation (hawkingBeta 1 κ 1 1) ω) :=
  gibbs_relation (hawkingBeta 1 κ 1 1) ω hβ hκω

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.KayWaldModeFreeEnergy

end
