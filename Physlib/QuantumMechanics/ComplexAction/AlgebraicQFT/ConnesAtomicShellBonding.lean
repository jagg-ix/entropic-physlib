/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov
public import Physlib.QuantumMechanics.ComplexAction.Particles.AtomicShellInformationCapacityOctet
public import Physlib.CondensedMatter.WaterCovalentBonding
meta import Zil

/-!
# Connes spectral data on atomic shell and covalent-bond carriers

This module connects the repository's noncommutative-geometric carrier to atomic structures that
were already formalized independently.  It introduces no new shell-counting or chemical model:

* the Connes effective dimension is identified with the proved principal-shell bit capacity;
* a constant spectral action counts the actual magnetic/spin modes of a bound subshell, and the
  same modes support the existing Boolean, Pauli-Fock, and Liouville carriers;
* the linear index is evaluated on the actual subshell mode space;
* hydrogen and oxygen closure defects become exact finite index pairings, so the existing `H2O`
  uniqueness theorem has an equivalent index equation.

## Honest scope

These results are finite-dimensional index pairings.  They do not assert that molecular bonding is
classified by analytic `KK`-theory, nor do they derive an interacting molecular Hamiltonian from a
spectral action.  The spectral triple is supplied as data, and the constant cutoff only counts its
eigenbasis multiplicity.  The chemical conclusion re-expresses already-proved Aufbau closure counts
as genuine Mathlib linear-map indices.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtomicShellBonding

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtiyahSingerKasparov
open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers
open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicShellInformationCapacityOctet
open Physlib.QuantumMechanics.ComplexAction.PeriodicTableAufbauStructure
open CondensedMatter.WaterCovalentBonding

/-! ## A. Principal-shell spectral dimension -/

/-- The effective dimension read from the atomic Dirac exponent is exactly the already-proved
principal-shell information capacity `sum_(l<n) 2(2l+1)`. -/
theorem principalShell_effectiveDimension_eq_bitCapacity (n : Nat) :
    effectiveDimensionFromExponent (atomicDiracGrowthExponent n) =
      ((∑ l ∈ Finset.range n, capacityOfAngularMomentum l : Nat) : ℝ) := by
  rw [atomic_effectiveDimension_eq_two_mul_sq, principalShell_bitCapacity]

/-! ## B. Spectral action on the physical subshell carrier -/

/-- For a finite spectral triple whose eigenbasis is indexed by a bound subshell's magnetic/spin
modes, a constant spectral cutoff counts exactly the Pauli bit capacity of that subshell. -/
theorem subshell_spectralAction_const_eq_bitCapacity
    {A H : Type*} [Semiring A] [Algebra ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (q : BoundSubshell) (T : FiniteSpectralTriple A H (SubshellMode q)) (c Λ : ℝ) :
    T.spectralAction (fun _ => c) Λ = (q.capacity : ℝ) * c := by
  rw [FiniteSpectralTriple.spectralAction_const, card_subshellMode]

/-- The same subshell multiplicity counted by the constant spectral action is simultaneously the
Boolean information-register capacity and the number of Pauli-nilpotent Fock creation modes. -/
theorem subshell_spectralAction_register_fock_bridge
    {A H : Type*} [Semiring A] [Algebra ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (q : BoundSubshell) (T : FiniteSpectralTriple A H (SubshellMode q)) (Λ : ℝ) :
    T.spectralAction (fun _ => 1) Λ = q.capacity
      ∧ Fintype.card (subshellStorageStates q) = 2 ^ q.capacity
      ∧ ∀ mode : SubshellMode q,
        subshellFockCreation q mode * subshellFockCreation q mode = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using subshell_spectralAction_const_eq_bitCapacity q T 1 Λ
  · exact (subshellRegister_secondQuantized_capacity_bridge q).1
  · exact (subshellRegister_secondQuantized_capacity_bridge q).2.1

/-! ## C. Atomic mode and covalent-defect index pairings -/

/-- The zero chiral operator from the actual subshell wavefunction carrier to the empty negative
sector.  Its index measures the full Pauli mode multiplicity of the subshell. -/
def subshellModeIndexOperator (q : BoundSubshell) :
    (SubshellMode q → ℂ) →ₗ[ℂ] FiniteModeSpace 0 :=
  0

/-- The index of the actual subshell-mode carrier equals its established Pauli capacity. -/
theorem subshellModeIndexOperator_index (q : BoundSubshell) :
    (subshellModeIndexOperator q).index = q.capacity := by
  rw [LinearMap.index_eq_of_finiteDimensional]
  simp [FiniteModeSpace, BoundSubshell.capacity, capacityOfAngularMomentum]
  ring

/-- Finite index pairing between a closed-shell register and its occupied modes. -/
def closureDefectIndex (capacity occupied : Nat) : Int :=
  (finiteIndexPairingOperator capacity occupied).index

/-- A closure-defect index is the signed difference between available and occupied modes. -/
theorem closureDefectIndex_eq (capacity occupied : Nat) :
    closureDefectIndex capacity occupied = (capacity : Int) - (occupied : Int) := by
  exact finiteIndexPairingOperator_index capacity occupied

/-- Hydrogen's one missing closure mode is exactly a finite analytic index. -/
theorem hydrogen_closureDefectIndex :
    closureDefectIndex (cumulativeCapacity 1) hydrogenZ = 1 := by
  rw [closureDefectIndex_eq, noble_gas_numbers.1]
  norm_num [hydrogenZ]

/-- Oxygen's two missing octet modes are exactly a finite analytic index. -/
theorem oxygen_closureDefectIndex :
    closureDefectIndex (cumulativeCapacity 3) oxygenZ = 2 := by
  rw [closureDefectIndex_eq, noble_gas_numbers.2.1]
  norm_num [oxygenZ]

/-- Water stoichiometry in index form: there is a unique natural number of hydrogen one-index
defects whose sum equals oxygen's two-index defect, and that number is two. -/
theorem water_stoichiometry_index :
    ∃! n : Nat,
      (n : Int) * closureDefectIndex (cumulativeCapacity 1) hydrogenZ =
        closureDefectIndex (cumulativeCapacity 3) oxygenZ := by
  refine ⟨2, ?_, ?_⟩
  · rw [hydrogen_closureDefectIndex, oxygen_closureDefectIndex]
    norm_num
  · intro n hn
    rw [hydrogen_closureDefectIndex, oxygen_closureDefectIndex] at hn
    omega

/-- The original Aufbau stoichiometry and the index equation agree on their unique witness. -/
theorem water_stoichiometry_and_index :
    (∃! n : Nat, n * hydrogenZ = cumulativeCapacity 3 - oxygenZ)
      ∧ (∃! n : Nat,
        (n : Int) * closureDefectIndex (cumulativeCapacity 1) hydrogenZ =
          closureDefectIndex (cumulativeCapacity 3) oxygenZ) :=
  ⟨water_stoichiometry, water_stoichiometry_index⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtomicShellBonding

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtomicShellBonding.principalShell_effectiveDimension_eq_bitCapacity where
  derives @ "claim:connes-effective-dimension = established-principal-shell-information-capacity",
  supported_by @ "theorem:principalShell_bitCapacity",
  caveat @ "claim:model-growth-exponent-identification-not-a-derivation-of-the-interacting-atomic-dirac-spectrum"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtomicShellBonding.subshell_spectralAction_register_fock_bridge where
  derives @ "claim:constant-spectral-action-count = pauli-register-capacity = second-quantized-mode-count",
  supported_by @ "theorem:subshellRegister_secondQuantized_capacity_bridge",
  caveat @ "claim:constant-cutoff-multiplicity-identity-not-an-interacting-molecular-spectral-action"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtomicShellBonding.water_stoichiometry_and_index where
  derives @ "claim:H2O-unique-closure-count = finite-linear-index-defect-equation",
  supported_by @ "theorem:water_stoichiometry",
  caveat @ "claim:index-reexpression-of-aufbau-closure-count-not-an-analytic-KK-classification-of-covalent-bonding"

zil_file_contract physlib.connesAtomicShellBonding where
  promises "The Connes effective dimension agrees with the established principal-shell information capacity; a constant finite spectral action counts the actual subshell Pauli/Fock register; and hydrogen/oxygen closure defects give a unique H2O stoichiometry equation as genuine finite linear-map indices."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.AtomicShellInformationCapacityOctet.principalShell_bitCapacity",
    "lean:Physlib.CondensedMatter.WaterCovalentBonding.water_stoichiometry"]
  forbids_substitutes ["interacting molecular spectrum claimed from a constant cutoff",
    "analytic KK classification inferred from finite index arithmetic",
    "empirical chemistry claimed beyond the imported Aufbau and covalent-bond theorems"]
  witnessed_by [
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtomicShellBonding.principalShell_effectiveDimension_eq_bitCapacity,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtomicShellBonding.subshell_spectralAction_register_fock_bridge,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtomicShellBonding.subshellModeIndexOperator_index,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConnesAtomicShellBonding.water_stoichiometry_and_index]

/- ZIL-END -/
