/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonEntanglementEntropy
public import Physlib.QuantumMechanics.ComplexAction.Fermion.ModularThermalOccupation
public import Physlib.Thermodynamics.SecondLaw.SergiOperatorTimeFree

/-!
# The Sorkin–Johnston region entropy, modular occupation, and entropic time

This file wires the Sorkin–Johnston entanglement-entropy arc
(`SorkinJohnstonEntanglementEntropy`) into two existing repo hubs:

* the **modular / KMS thermal occupation** `gibbsOccupation` of the fermion-region AQFT arc
 (`Fermion.ModularThermalOccupation`), showing the SJ thermal entropy is the binary entropy of the
 Gibbs occupation of the modular Hamiltonian; and
* the **entropic time** `entropicTimeOf S_I ℏ = S_I/ℏ` of the second-law arc
 (`Thermodynamics.SecondLaw`), showing the SJ entanglement entropy *is* an entropic time (the
 imaginary action per `ℏ`).

* **§A — modular occupation.** `sjThermalEntropy β ε = binEntropy(gibbsOccupation β ε)`
 (`sjThermalEntropy_eq_gibbsEntropy`): the SJ region thermal entanglement entropy is the entropy of
 the KMS/Gibbs modular occupation.
* **§B — the pure (ground-state) limit.** `sjGibbs_pure_iff`: the SJ region mode is pure (zero
 entanglement) iff the modular occupation saturates Pauli exclusion (empty or full) — the `T → 0`
 vacuum.
* **§C — entropy is entropic time.** `sjEntropy_as_entropicTime`:
 `entropicTimeOf (ℏ · S(λ)) ℏ = S(λ)`, so the SJ entanglement entropy is the entropic time of a mode
 whose imaginary action is `ℏ` times its entropy; `sjEntropicTime_nonneg` (the entropic time is
 non-negative, reusing `entropicTimeOf_nonneg`).

Proven: all three bridges as exact identities on the existing definitions. No new
physical content is asserted beyond identifying the SJ region entropy with the modular occupation
entropy and with an entropic time — the interpretation that the modular Hamiltonian generates the
region's thermal state is encoded in the imported `ModularThermalOccupation` arc.

## References

* R. D. Sorkin (SJ vacuum / spacetime entropy). Reuses `SorkinJohnstonEntanglementEntropy`
 (`sjModeEntropy`, `sjThermalEntropy`), `Fermion.ModularThermalOccupation`
 (`gibbsOccupation`, `gibbsOccupation_eq_fermiDirac`), and `Thermodynamics.SecondLaw`
 (`entropicTimeOf`, `entropicTimeOf_nonneg`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonModular

open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonEntanglementEntropy
open Physlib.QuantumMechanics.ComplexAction.Fermion.ModularThermalOccupation
open Physlib.Thermodynamics.SecondLaw

/-! ## §A — modular / KMS occupation -/

/-- **The SJ thermal entropy is the entropy of the modular occupation** `S_thermal(β,ε) =
binEntropy(gibbsOccupation β ε)`: the Sorkin–Johnston region entanglement entropy at the modular
(Bisognano–Wichmann/Unruh) temperature is the binary entropy of the KMS/Gibbs occupation of the
modular Hamiltonian `K = ε n`. -/
theorem sjThermalEntropy_eq_gibbsEntropy (β ε : ℝ) :
    sjThermalEntropy β ε = sjModeEntropy (gibbsOccupation β ε) := by
  unfold sjThermalEntropy
  rw [gibbsOccupation_eq_fermiDirac]

/-! ## §B — the pure (ground-state) limit -/

/-- **The SJ region mode is pure iff Pauli-saturated** `S = 0 ↔ occupation ∈ {0,1}`: the modular mode
has no entanglement exactly when the Gibbs occupation is empty or full — the `T → 0` ground-state
(pure vacuum) limit of the region state. -/
theorem sjGibbs_pure_iff (β ε : ℝ) :
    sjModeEntropy (gibbsOccupation β ε) = 0 ↔ gibbsOccupation β ε = 0 ∨ gibbsOccupation β ε = 1 :=
  sjModeEntropy_pure (gibbsOccupation β ε)

/-! ## §C — the entanglement entropy is an entropic time -/

/-- **The SJ entanglement entropy is an entropic time** `entropicTimeOf(ℏ · S(λ)) ℏ = S(λ)`: for a mode
whose imaginary action is `ℏ` times its entanglement entropy, the entropic time `S_I/ℏ` of the
second-law arc equals the entanglement entropy — the SJ region entropy is read as an entropic time. -/
theorem sjEntropy_as_entropicTime (lam ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    entropicTimeOf (ℏ * sjModeEntropy lam) ℏ = sjModeEntropy lam := by
  show ℏ * sjModeEntropy lam / ℏ = sjModeEntropy lam
  rw [mul_comm, mul_div_assoc, div_self hℏ, mul_one]

/-- **The SJ entropic time is non-negative** on the physical occupation range `λ ∈ [0,1]` — the region
entanglement entropy, read as an entropic time, respects the arrow of the second law
(`entropicTimeOf_nonneg`). -/
theorem sjEntropicTime_nonneg (lam ℏ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hℏ : 0 < ℏ) :
    0 ≤ entropicTimeOf (ℏ * sjModeEntropy lam) ℏ :=
  entropicTimeOf_nonneg (mul_nonneg hℏ.le (sjModeEntropy_nonneg lam h0 h1)) hℏ

end Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonModular
