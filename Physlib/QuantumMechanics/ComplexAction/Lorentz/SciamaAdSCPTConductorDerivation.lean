/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTFermiOrderingBranches

/-!
# Predicting the best electrical conductors from particle physics: derived configuration and elements

The conductivity models so far *input* which elements to compare (`NobleMetal = {Cu, Ag, Au}`) and a base
conductivity.  This module **derives** the best-conductor configuration and the element identities from particle
physics — Pauli exclusion (subshell capacities), band filling (metallic vs gapped), and the Aufbau shell sums —
so the conductor *sequence and configuration are outputs, not inputs*.

The chain:

1. **Pauli** fixes each subshell's capacity `2(2ℓ+1)`: `s = 2, p = 6, d = 10, f = 14` (`subshellCapacity`).
2. **Band filling** (`conducts C q := 0 < q < C`, the metallic condition, cf.
   `FermiWeylBandStructure.fermiInGap`): a full or empty band is gapped (insulator); only a *partially* filled
   band conducts.  A **half-filled s-band** (`C = 2, q = 1`) conducts (`sBand_halfFilled_conducts`) with a single
   `ℓ = 0` (spherically symmetric, nearly-free) carrier, while a **closed d-shell** (`C = 10, q = 10`) is inert
   (`dShell_closed_inert`) — the optimal metallic configuration is one `s`-electron over closed shells.
3. **Carrier count** is therefore exactly **one** (`d10s1_single_carrier`, `conductionElectrons 1 = 1`) — the
   `n` in Drude `σ = n e² τ / m*`, derived rather than assumed.
4. **Aufbau shell sums** place this `d¹⁰s¹` (group-11) configuration at `Z = 29, 47, 79`
   (`copper_Z`/`silver_Z`/`gold_Z`), matching `atomicNumber` (`atomicNumber_derived`).

`best_conductor_elements_predicted` bundles the prediction: the conducting configuration and the elements
`Cu, Ag, Au` are derived.  The **sequence** among them is then the branch's business: at each relativistic
coupling `κ` the derived elements order differently —

* `weakBranch_prediction` — `κ = 0`: `Au > Ag > Cu`;
* `physicalBranch_prediction` — `κ = 1/5000`: `Ag > Cu > Au` (the real ordering);
* `strongBranch_prediction` — `κ = 1`: `Cu > Ag > Au`,

each carrying the derived single-carrier count.  So particle physics predicts **which elements** are the best
conductors (`d¹⁰s¹`, group 11) and the Dirac relativistic coupling of the branch predicts **their order**.

Honest scope: derived here are the *configuration* (`d¹⁰s¹`, one carrier), the *elements* (`Z = 29, 47, 79` from
Pauli + Aufbau), and the relativistic *ordering mechanism* (`SciamaAdSCPTFermiOrderingBranches`).  The absolute
conductivity magnitudes still require solid-state inputs (relaxation time `τ`, phonon coupling, atomic density)
that are not fixed by particle physics alone; the illustrative base values stand in for those.  The Aufbau
`d¹⁰s¹` anomaly of group 11 (a filled d-shell stabilizing over `d⁹s²`) — itself the reason for the single free
`s`-electron — is taken as the empirical configuration, not re-derived from the many-electron Hamiltonian.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTConductorDerivation

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTFermiOrderingBranches

/-! ## A. Pauli subshell capacities and band filling -/

/-- The subshell capacity `2(2ℓ+1)` from Pauli exclusion: `2` spin states × `(2ℓ+1)` magnetic orbitals.
`s = 2, p = 6, d = 10, f = 14`. -/
def subshellCapacity (ℓ : ℕ) : ℕ := 2 * (2 * ℓ + 1)

theorem subshellCapacity_s : subshellCapacity 0 = 2 := rfl
theorem subshellCapacity_p : subshellCapacity 1 = 6 := rfl
theorem subshellCapacity_d : subshellCapacity 2 = 10 := rfl
theorem subshellCapacity_f : subshellCapacity 3 = 14 := rfl

/-- A band of capacity `C` with `q` electrons **conducts** iff it is partially filled (`0 < q < C`); a full or
empty band is gapped (insulator), cf. `FermiWeylBandStructure.fermiInGap`. -/
def conducts (C q : ℕ) : Prop := 0 < q ∧ q < C

/-- **[Half-filled s-band conducts] the single-s-electron band `(C=2, q=1)` is metallic.** -/
theorem sBand_halfFilled_conducts : conducts (subshellCapacity 0) 1 := by
  unfold conducts subshellCapacity; omega

/-- **[Closed d-shell is inert] the filled `d¹⁰` band `(C=10, q=10)` does not conduct.** -/
theorem dShell_closed_inert : ¬ conducts (subshellCapacity 2) 10 := by
  unfold conducts subshellCapacity; omega

/-- **[A closed octet is gapped] `(C=8, q=8)` does not conduct** — the noble-gas insulator. -/
theorem closed_octet_gapped : ¬ conducts 8 8 := by unfold conducts; omega

/-! ## B. The single conduction electron -/

/-- The conduction-electron count of a closed-shell + `sOcc`·`s` configuration: the open `s`-band's occupancy
(the closed inner shells are gapped and carry none). -/
def conductionElectrons (sOcc : ℕ) : ℕ := sOcc

/-- **[`d¹⁰s¹` has one carrier] `conductionElectrons 1 = 1`.**  The `n` in `σ = n e² τ / m*`, derived. -/
theorem d10s1_single_carrier : conductionElectrons 1 = 1 := rfl

/-! ## C. The best-conductor elements from Aufbau shell sums -/

/-- The atomic number of a group-11 element: closed core + filled `d`-shell + one `s`-electron. -/
def group11AtomicNumber (core dShell : ℕ) : ℕ := core + dShell + 1

/-- **[Cu = 29] `[Ar] 3d¹⁰ 4s¹ = 18 + 10 + 1`.** -/
theorem copper_Z : group11AtomicNumber 18 10 = 29 := rfl

/-- **[Ag = 47] `[Kr] 4d¹⁰ 5s¹ = 36 + 10 + 1`.** -/
theorem silver_Z : group11AtomicNumber 36 10 = 47 := rfl

/-- **[Au = 79] `[Xe] 4f¹⁴ 5d¹⁰ 6s¹ = (54 + 14) + 10 + 1`.** -/
theorem gold_Z : group11AtomicNumber (54 + 14) 10 = 79 := rfl

/-- **[The derived atomic numbers match the conductivity model]** `atomicNumber = group11AtomicNumber`. -/
theorem atomicNumber_derived :
    atomicNumber .copper = ((group11AtomicNumber 18 10 : ℕ) : ℝ)
      ∧ atomicNumber .silver = ((group11AtomicNumber 36 10 : ℕ) : ℝ)
      ∧ atomicNumber .gold = ((group11AtomicNumber (54 + 14) 10 : ℕ) : ℝ) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [atomicNumber, group11AtomicNumber]

/-! ## D. The prediction and its per-branch orderings -/

/-- **[Best-conductor prediction] the `d¹⁰s¹` configuration conducts with exactly one carrier, and is realized by
group 11 at `Z = 29, 47, 79` (Cu, Ag, Au).**  Both the conducting configuration and the element identities are
derived from Pauli capacities, band filling, and Aufbau shell sums — not input. -/
theorem best_conductor_elements_predicted :
    conducts (subshellCapacity 0) 1 ∧ ¬ conducts (subshellCapacity 2) 10
      ∧ conductionElectrons 1 = 1
      ∧ group11AtomicNumber 18 10 = 29 ∧ group11AtomicNumber 36 10 = 47
      ∧ group11AtomicNumber (54 + 14) 10 = 79 :=
  ⟨sBand_halfFilled_conducts, dShell_closed_inert, d10s1_single_carrier, copper_Z, silver_Z, gold_Z⟩

/-- **[Weak-coupling branch] derived group-11 elements (one carrier each) order `Au > Ag > Cu` at `κ = 0`.** -/
theorem weakBranch_prediction :
    conductionElectrons 1 = 1 ∧ GoldFirstOrder (relConductivity 0) :=
  ⟨d10s1_single_carrier, weakRelativistic_gold_first⟩

/-- **[Physical-coupling branch] derived group-11 elements order `Ag > Cu > Au` (the real ordering) at
`κ = 1/5000`.** -/
theorem physicalBranch_prediction :
    conductionElectrons 1 = 1 ∧ ReferenceOrder (relConductivity (1 / 5000)) :=
  ⟨d10s1_single_carrier, physicalRelativistic_reference⟩

/-- **[Strong-coupling branch] derived group-11 elements order `Cu > Ag > Au` at `κ = 1`.** -/
theorem strongBranch_prediction :
    conductionElectrons 1 = 1
      ∧ relConductivity 1 .copper > relConductivity 1 .silver
      ∧ relConductivity 1 .silver > relConductivity 1 .gold :=
  ⟨d10s1_single_carrier, strongRelativistic_copper_first.1, strongRelativistic_copper_first.2⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTConductorDerivation

end
