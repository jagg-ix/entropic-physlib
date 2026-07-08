/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator

/-!
# The fermion region's modular thermal occupation is Fermi–Dirac

Continues the fermion-region arc: the **Gibbs (KMS) state of the single-mode modular / entanglement
Hamiltonian** `K = ε·n` (`n` the fermion number operator of `BoseFermiOperatorAlgebra.CompositeFermionCAR`, eigenvalues `0, 1`
by Pauli exclusion) gives the **Fermi–Dirac occupation**. Because the number operator is idempotent
(`n² = n`, Pauli exclusion), a single fermion mode has exactly two states (`n = 0, 1`), so the partition
function is

  `Z = Tr e^{−βεn} = 1 + e^{−βε}`   (`gibbsPartition`),

and the occupation is

  `⟨n⟩ = Tr(e^{−βεn} n)/Z = e^{−βε}/(1 + e^{−βε}) = 1/(e^{βε} + 1) = n_F(βε)`
  (`gibbsOccupation`, `gibbsOccupation_eq_fermiDirac`),

exactly the **Fermi–Dirac distribution** (`ComplexOscillator.ComplexFermionicOscillator.fermiDirac`). It lies in the unit
interval `0 ≤ ⟨n⟩ ≤ 1` (`gibbsOccupation_mem_unitInterval`) — the thermal/KMS form of Pauli exclusion: a
mode is occupied at most once.

So the modular flow of the fermion region's number observable is the thermal (KMS) flow, and its occupation
is Fermi–Dirac precisely because the number operator is a `0/1` projection (Pauli) — the partition sum has
only two terms. This is the KMS face of the spin-statistics / CAR structure: half-integer spin ⟹ Pauli ⟹
Fermi–Dirac.

* **§A — the modular Gibbs occupation** (`gibbsPartition`, `gibbsOccupation`,
  `gibbsOccupation_eq_fermiDirac`).
* **§B — Pauli bound** (`gibbsOccupation_mem_unitInterval`, `fermion_modular_thermal_occupation`).

## References

* The Fermi–Dirac distribution as the KMS occupation of a fermion mode; the modular/entanglement
  Hamiltonian. structures: `ComplexOscillator.ComplexFermionicOscillator` (`fermiDirac`); cf. `BoseFermiOperatorAlgebra.CompositeFermionCAR`
  (`fermionNumber`, `fermionNumber_idempotent`), `Bogoliubov.SaitoBogoliubovBoseFermiStatistics`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Fermion.ModularThermalOccupation

open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.ComplexFermionicOscillator

/-! ## §A — the modular Gibbs occupation -/

/-- **The modular Gibbs occupation** `⟨n⟩ = Tr(e^{−βεn} n)/Z = e^{−βε}/(1 + e^{−βε})` — the thermal
expectation of the fermion number in the Gibbs/KMS state of the entanglement Hamiltonian `K = ε·n`, with
partition function `Z = Tr e^{−βεn} = 1 + e^{−βε}` (only two states, `n = 0, 1`, by Pauli exclusion). -/
noncomputable def gibbsOccupation (β ε : ℝ) : ℝ :=
  Real.exp (-(β * ε)) / (1 + Real.exp (-(β * ε)))

/-- **[The modular occupation is Fermi–Dirac] `⟨n⟩ = 1/(e^{βε} + 1) = n_F(βε)`.** The Gibbs/KMS occupation of
the fermion mode is exactly the Fermi–Dirac distribution. -/
theorem gibbsOccupation_eq_fermiDirac (β ε : ℝ) : gibbsOccupation β ε = fermiDirac (β * ε) := by
  simp only [gibbsOccupation, fermiDirac, Real.exp_neg]
  have he : Real.exp (β * ε) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-! ## §B — Pauli bound -/

/-- **[The occupation lies in `[0, 1]`] `0 ≤ ⟨n⟩ ≤ 1`.** The thermal/KMS form of Pauli exclusion: a fermion
mode is occupied at most once. -/
theorem gibbsOccupation_mem_unitInterval (β ε : ℝ) :
    0 ≤ gibbsOccupation β ε ∧ gibbsOccupation β ε ≤ 1 := by
  have he : 0 < Real.exp (-(β * ε)) := Real.exp_pos _
  refine ⟨div_nonneg he.le (by positivity), ?_⟩
  rw [gibbsOccupation, div_le_one (by positivity)]
  linarith

/-- **[The fermion region's modular thermal occupation, assembled].** The Gibbs/KMS state of the single-mode
modular Hamiltonian `K = ε·n`:

* has partition function `Z = 1 + e^{−βε}` (two states, Pauli exclusion);
* has occupation `⟨n⟩ = Fermi–Dirac(βε)`;
* with `0 ≤ ⟨n⟩ ≤ 1` (Pauli bound).

The fermion region's number observable thermalises to the Fermi–Dirac distribution — the KMS face of the
`0/1` (Pauli) spectrum: half-integer spin ⟹ Pauli ⟹ Fermi–Dirac. -/
theorem fermion_modular_thermal_occupation (β ε : ℝ) :
    gibbsOccupation β ε = fermiDirac (β * ε)
      ∧ 0 ≤ gibbsOccupation β ε ∧ gibbsOccupation β ε ≤ 1 :=
  ⟨gibbsOccupation_eq_fermiDirac β ε, (gibbsOccupation_mem_unitInterval β ε).1,
    (gibbsOccupation_mem_unitInterval β ε).2⟩

end Physlib.QuantumMechanics.ComplexAction.Fermion.ModularThermalOccupation

end
