/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionMutex
public import Physlib.QuantumMechanics.ComplexAction.Fermion.ModularThermalOccupation

/-!
# The exclusion cell's boundary is thermal: Fermi–Dirac emission and a one-bit critical point

Closes the electron-exclusion-cell arc's black-hole/horizon analogy on the **thermal** side. The boundary of
the exclusion cell — the mutex/CAR mode `n = f†f` — emits and absorbs photons *thermally*: under the
Tomita–Takesaki modular (KMS) flow of the entanglement Hamiltonian `K = ε·n` (`ε = ℏω` the photon gap), the
occupation is the **Fermi–Dirac distribution** `⟨n⟩ = 1/(e^{βε}+1)`
(`Fermion.ModularThermalOccupation.gibbsOccupation_eq_fermiDirac`), the Hawking/Unruh-style thermal spectrum of
the boundary. Crucially the occupation is **capped at 1** (`gibbsOccupation_mem_unitInterval`) — this is exactly
the mutex exclusion `n² = n` of `ElectronExclusionMutex` in its thermal/KMS form: a boundary mode is thermally
occupied *at most once*.

**The massless bifurcation is a one-bit thermal critical point.** At the photon / lightlike critical point the
gap collapses, `ε = 0` (`ElectronExclusionPhotonBifurcation`'s TISE-gap collapse). There the boundary
occupation is exactly `⟨n⟩ = 1/2` (`exclusionCell_critical_halfOccupation`) — maximal binary uncertainty — and
its binary entropy is `H(1/2) = log 2` (`exclusionCell_critical_one_bit_entropy`): the boundary carries exactly
**one bit** of thermal entropy, the same one bit the cell was shown to hold in `ElectronExclusionMutex`
(`fermion_horizon_one_bit`). The critical point of the TISE bifurcation is the maximum-entropy state of the
boundary.

* **§A — the boundary occupation is thermal and exclusion-capped** (`exclusionCell_boundary_thermal_bounded`).
* **§B — the massless critical point is half-occupied** (`exclusionCell_critical_halfOccupation`).
* **§C — the critical boundary carries one bit of thermal entropy** (`exclusionCell_critical_one_bit_entropy`).
* **§D — assembled** (`electron_exclusion_thermal_boundary`).

**Honest layering.** §A reuses `gibbsOccupation_mem_unitInterval` verbatim (the thermal exclusion). §B/§C are
exact `Real.exp`/`Real.binEntropy` computations (`gibbsOccupation β 0 = 1/2`, `binEntropy (1/2) = log 2` via
`Real.binEntropy_two_inv`). The new content is the *identification* — the exclusion cell's boundary emission is
this thermal (KMS/Fermi–Dirac) occupation, and its massless bifurcation is the one-bit maximum-entropy point.
No claim of a geometric Hawking temperature is made; the temperature is the modular/entanglement (KMS) one.

## References

* Repo carriers: `Fermion.ModularThermalOccupation` (Fermi–Dirac as KMS occupation),
  `HorizonCell.{ElectronExclusionMutex,ElectronExclusionPhotonBifurcation}`, `Mathlib …BinaryEntropy`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Fermion.ModularThermalOccupation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionThermalBoundary


/-- **[The boundary thermal occupation is capped at one] `0 ≤ ⟨n⟩ ≤ 1`.** At inverse temperature `β` and
photon gap `ε = ℏω`, the exclusion cell's boundary emits/absorbs with the Fermi–Dirac (KMS) occupation
`⟨n⟩ = gibbsOccupation β ε` (`gibbsOccupation_eq_fermiDirac`), which lies in `[0, 1]`: the thermal / KMS form of
the mutex exclusion `n² = n` — a boundary mode is thermally occupied at most once. -/
lemma exclusionCell_boundary_thermal_bounded (β ε : ℝ) :
    0 ≤ gibbsOccupation β ε ∧ gibbsOccupation β ε ≤ 1 :=
  gibbsOccupation_mem_unitInterval β ε


/-- **[At the massless bifurcation the boundary is half-occupied] `⟨n⟩ = 1/2` at `ε = 0`.** At the photon /
lightlike critical point the gap collapses (`ε = 0`), and the Fermi–Dirac occupation is exactly
`e^0/(1 + e^0) = 1/2` — maximal binary uncertainty, the middle of the exclusion interval `[0, 1]`. -/
lemma exclusionCell_critical_halfOccupation (β : ℝ) : gibbsOccupation β 0 = 1 / 2 := by
  simp only [gibbsOccupation, mul_zero, neg_zero, Real.exp_zero]
  norm_num


/-- **[The critical boundary carries one bit of thermal entropy] `H(⟨n⟩) = log 2` at `ε = 0`.** With the
massless-critical occupation `⟨n⟩ = 1/2`, the binary entropy of the boundary is `H(1/2) = log 2` — exactly one
bit. The critical point of the TISE bifurcation is the maximum-entropy state of the exclusion cell's boundary,
carrying the same one bit it holds as a mutex (`fermion_horizon_one_bit`). -/
lemma exclusionCell_critical_one_bit_entropy (β : ℝ) :
    Real.binEntropy (gibbsOccupation β 0) = Real.log 2 := by
  rw [exclusionCell_critical_halfOccupation, show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by norm_num,
    Real.binEntropy_two_inv]


/-- **[The exclusion cell's thermal boundary, assembled].** The boundary occupation is thermal and
exclusion-capped `0 ≤ ⟨n⟩ ≤ 1`; at the massless bifurcation `ε = 0` it is half-occupied `⟨n⟩ = 1/2` and carries
exactly one bit of thermal entropy `H(1/2) = log 2`. The exclusion cell's boundary emits photons with the
Fermi–Dirac (KMS/Hawking-analog) spectrum, and its massless critical point is the one-bit maximum-entropy
state. -/
lemma electron_exclusion_thermal_boundary (β ε : ℝ) :
    (0 ≤ gibbsOccupation β ε ∧ gibbsOccupation β ε ≤ 1)
      ∧ gibbsOccupation β 0 = 1 / 2
      ∧ Real.binEntropy (gibbsOccupation β 0) = Real.log 2 :=
  ⟨exclusionCell_boundary_thermal_bounded β ε,
    exclusionCell_critical_halfOccupation β,
    exclusionCell_critical_one_bit_entropy β⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionThermalBoundary

end
