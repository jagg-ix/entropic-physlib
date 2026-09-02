/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.AtomicShellInformationCapacityOctet
public import Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableShellCapacity
public import Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa
public import Physlib.Thermodynamics.BekensteinJacobsonEntropicBits
public import Physlib.Thermodynamics.KullbackLeiblerInformationGain

/-!
# Horizon information capacity and the atomic octet register

`Particles.AtomicShellInformationCapacityOctet` proves the atomic side: Pauli turns each electron mode into a
Boolean storage slot, so the valence `s+p` register has capacity `2 + 6 = 8` bits.

This file closes the formal bridge to the horizon side.  The repository already has the Bekenstein
bit carrier

`bekensteinBits A ellP = A / (4 * ellP^2 * log 2)`,

so an `B`-bit horizon register is represented by the area

`A_B = 4 * ellP^2 * log 2 * B`.

The bridge proves that this area has Bekenstein capacity `B`, and then specializes to the octet
capacity `B = 8`.  It also connects the same area to the complex-action horizon imaginary action
`horizonImaginaryAction G c A = c^3 A / (4G)`: under the Planck relation
`ellP^2 = hbar * G / c^3`, the imaginary action of the `B`-bit horizon is
`hbar * log 2 * B`.

The result is intentionally exact and modest: it identifies the *same bit-counting normalization* on
the horizon and atomic sides.  It does not claim that horizon physics causes the octet rule.


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.AtomicInformationCapacity

open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers
open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicShellInformationCapacityOctet
open Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableShellCapacity
open Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTablePeriods
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GravitationalMassHorizonEntropyNoYukawa
open Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.FromArchive
open Physlib.QuantumMechanics.ComplexAction.IcosahedralStressEnergyAction
open Physlib.QuantumMechanics.ComplexAction.IcosahedralWeylNetSymmetry
open Physlib.QuantumMechanics.ComplexAction.IcosahedralRotationsHyperbolic
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4
open Physlib.QuantumMechanics.ComplexAction.Su5ChargeQuantizationCartanTensor
open Physlib.Thermodynamics.KullbackLeiblerInformationGain


/-- A finite `B`-bit register: each slot is occupied/true or empty/false. -/
abbrev finiteBitRegister (B : Nat) : Type := Fin B → Bool

/-- A `B`-bit register has `2^B` occupation configurations. -/
lemma finiteBitRegister_card (B : Nat) :
    Fintype.card (finiteBitRegister B) = 2 ^ B := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- The valence `s+p` octet register. -/
abbrev octetRegister : Type :=
  finiteBitRegister (capacityOfAngularMomentum 0 + capacityOfAngularMomentum 1)

/-- The octet register has `256` occupation configurations. -/
lemma octetRegister_card : Fintype.card octetRegister = 256 := by
  rw [finiteBitRegister_card, octet_storageCount]

/-- The octet capacity as a real number, for comparison with Bekenstein bit counts. -/
def octetBitCapacityReal : ℝ :=
  (capacityOfAngularMomentum 0 + capacityOfAngularMomentum 1 : Nat)

/-- The octet capacity is exactly `8` bits. -/
lemma octetBitCapacityReal_eq_eight : octetBitCapacityReal = 8 := by
  norm_num [octetBitCapacityReal, capacityOfAngularMomentum]


/-- The horizon area whose Bekenstein bit count is `B`.

Since `bekensteinBits A ellP = A/(4 ellP^2 log 2)`, this is the inverse area map. -/
def horizonAreaForBitCapacity (B ellP : ℝ) : ℝ :=
  4 * ellP ^ 2 * Real.log 2 * B

/-- The area `4 ellP^2 log 2 * B` stores exactly `B` Bekenstein-Landauer bits. -/
lemma bekensteinBits_horizonAreaForBitCapacity (B ellP : ℝ) (hellP : ellP ≠ 0) :
    bekensteinBits (horizonAreaForBitCapacity B ellP) ellP = B := by
  unfold bekensteinBits horizonAreaForBitCapacity
  have hlog2 : Real.log 2 ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num))
  field_simp [pow_ne_zero 2 hellP, hlog2]

/-- The octet-sized horizon area has the same bit capacity as the atomic valence `s+p` register. -/
lemma bekensteinBits_octetArea (ellP : ℝ) (hellP : ellP ≠ 0) :
    bekensteinBits (horizonAreaForBitCapacity octetBitCapacityReal ellP) ellP
      = octetBitCapacityReal :=
  bekensteinBits_horizonAreaForBitCapacity octetBitCapacityReal ellP hellP

/-- The octet-sized horizon area stores exactly eight Bekenstein-Landauer bits. -/
lemma bekensteinBits_octetArea_eq_eight (ellP : ℝ) (hellP : ellP ≠ 0) :
    bekensteinBits (horizonAreaForBitCapacity octetBitCapacityReal ellP) ellP = 8 := by
  rw [bekensteinBits_octetArea ellP hellP, octetBitCapacityReal_eq_eight]

/-- In nats, the same octet-sized horizon capacity is `log 2 * 8`. -/
lemma bekensteinTauEnt_octetArea
    (ellP : ℝ) (hellP : ellP ≠ 0) :
    bekensteinTauEnt (horizonAreaForBitCapacity octetBitCapacityReal ellP) ellP
      = Real.log 2 * octetBitCapacityReal := by
  rw [bekensteinTauEnt_eq_ln2_mul_bits (A := horizonAreaForBitCapacity octetBitCapacityReal ellP)
    (ℓP := ellP) hellP, bekensteinBits_octetArea ellP hellP]


/-- Under the Planck relation `ellP^2 = hbar * G / c^3`, the horizon imaginary action is
`hbar * log 2` times the Bekenstein bit count. -/
lemma horizonImaginaryAction_eq_hbar_ln2_mul_bekensteinBits
    (G c hbar A ellP : ℝ) (hG : G ≠ 0) (hc : c ≠ 0) (hhbar : hbar ≠ 0)
    (hPlanck : ellP ^ 2 = hbar * G / c ^ 3) :
    horizonImaginaryAction G c A = hbar * Real.log 2 * bekensteinBits A ellP := by
  unfold horizonImaginaryAction bekensteinBits
  rw [hPlanck]
  have hlog2 : Real.log 2 ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hG, hc, hhbar, hlog2, pow_ne_zero 3 hc]

/-- The octet-sized horizon area has imaginary action `hbar * log 2 * 8`, matching the atomic octet
capacity after the standard nats-to-bits conversion. -/
lemma horizonImaginaryAction_octetArea
    (G c hbar ellP : ℝ) (hG : G ≠ 0) (hc : c ≠ 0) (hhbar : hbar ≠ 0)
    (hellP : ellP ≠ 0) (hPlanck : ellP ^ 2 = hbar * G / c ^ 3) :
    horizonImaginaryAction G c (horizonAreaForBitCapacity octetBitCapacityReal ellP)
      = hbar * Real.log 2 * octetBitCapacityReal := by
  rw [horizonImaginaryAction_eq_hbar_ln2_mul_bekensteinBits G c hbar
      (horizonAreaForBitCapacity octetBitCapacityReal ellP) ellP hG hc hhbar hPlanck,
    bekensteinBits_octetArea ellP hellP]

/-- The atomic octet register and an octet-sized Bekenstein horizon register carry the same checked
information capacity: eight bits, `256` Boolean configurations on the atomic side, and imaginary action
`hbar * log 2 * 8` on the horizon side. -/
lemma octet_horizon_information_capacity_assembly
    (G c hbar ellP : ℝ) (hG : G ≠ 0) (hc : c ≠ 0) (hhbar : hbar ≠ 0)
    (hellP : ellP ≠ 0) (hPlanck : ellP ^ 2 = hbar * G / c ^ 3) :
    Fintype.card octetRegister = 256
      ∧ bekensteinBits (horizonAreaForBitCapacity octetBitCapacityReal ellP) ellP = 8
      ∧ bekensteinTauEnt (horizonAreaForBitCapacity octetBitCapacityReal ellP) ellP
          = Real.log 2 * 8
      ∧ horizonImaginaryAction G c (horizonAreaForBitCapacity octetBitCapacityReal ellP)
          = hbar * Real.log 2 * 8 := by
  refine ⟨octetRegister_card, bekensteinBits_octetArea_eq_eight ellP hellP, ?_, ?_⟩
  · rw [bekensteinTauEnt_octetArea ellP hellP, octetBitCapacityReal_eq_eight]
  · rw [horizonImaginaryAction_octetArea G c hbar ellP hG hc hhbar hellP hPlanck,
      octetBitCapacityReal_eq_eight]

/-- Any finite subshell Feynman/Tasaki occupation number can be used as a Bekenstein bit count:
the inverse-area map stores exactly `Σ n_α` bits, and Pauli bounds that number by the subshell
capacity `2(2l+1)`. -/
lemma subshellFeynmanNumber_horizonCapacity_bridge
    (q : BoundSubshell) (occ : SubshellMode q → Bool) (ellP : ℝ) (hellP : ellP ≠ 0) :
    bekensteinBits (horizonAreaForBitCapacity (feynmanNumberEigenvalue occ : ℝ) ellP) ellP =
        (feynmanNumberEigenvalue occ : ℝ)
      ∧ feynmanNumberEigenvalue occ ≤ q.capacity := by
  exact ⟨bekensteinBits_horizonAreaForBitCapacity (feynmanNumberEigenvalue occ : ℝ) ellP hellP,
    by
      calc
        feynmanNumberEigenvalue occ ≤ Fintype.card (SubshellMode q) :=
          feynmanNumberEigenvalue_le_card occ
        _ = q.capacity := card_subshellMode q⟩


/-- The non-vacuous synthesis requested by the document inspection.

The periodic-table content is phrased as a derivation chain, not as a list of
numerical facts:

* a subshell mode is a finite magnetic carrier times a two-state spin carrier;
* Pauli/CAR turns each such mode into a Boolean occupation register and a
  self-adjoint idempotent number projection;
* shell capacity is the sum of these finite mode-cardinalities and therefore
  `2n²`;
* each period capacity is a shell capacity from the Aufbau grouping.

The `A₅/S₅/SU(5)` side remains separate: it proves that the Cartan/weight-space
tensor and traceless charge constraints are symmetry-preserving. -/
def HasDerivedPauliCARRegistersAndSu5IcosahedralTensors : Prop :=
  (∀ q : BoundSubshell,
      Fintype.card (SubshellMode q) = 2 * (2 * q.l + 1))
    ∧ (∀ q : BoundSubshell,
        Fintype.card (subshellStorageStates q) = 2 ^ (2 * (2 * q.l + 1)))
    ∧ (∀ {A : Type*} [Ring A] [StarRing A] (q : BoundSubshell)
        (R : SubshellKalnayRealization A q) (mode : SubshellMode q),
        star (modeNumber R mode) = modeNumber R mode
          ∧ modeNumber R mode * modeNumber R mode = modeNumber R mode)
    ∧ (∀ n : Nat,
        shellCapacity n =
          ∑ l ∈ Finset.range n, Fintype.card (Fin (2 * l + 1) × Fin 2))
    ∧ (∀ n : Nat, shellCapacity n = 2 * n ^ 2)
    ∧ octetCapacity = shellCapacity 2
    ∧ shellCapacity 2 = 2 * 2 ^ 2
    ∧ periods.flatten = aufbauCapacities
    ∧ (∀ K : Nat, K ∈ periodLengths →
        ∃ n : Nat, K = shellCapacity n ∧ shellCapacity n = 2 * n ^ 2)
    ∧ Fintype.card Su5WeylGroup = 2 * Fintype.card IcosahedralGroup
    ∧ (∀ i : Fin 5,
        (fun j => su5CartanMetric i j) = affineBasis i
          ∧ ∑ j, su5CartanMetric i j = 0)
    ∧ (∀ σ : Su5WeylGroup, ∀ i j : Fin 5,
        su5CartanMetric (σ i) (σ j) = su5CartanMetric i j)
    ∧ (∀ g : IcosahedralGroup, ∀ i j : Fin 5,
        su5CartanMetric ((g : Equiv.Perm (Fin 5)) i) ((g : Equiv.Perm (Fin 5)) j)
          = su5CartanMetric i j)
    ∧ (∀ q : Fin 5 → ℚ, IsAffineWeight q →
        q 0 = q 1 ∧ q 1 = q 2 → q 4 = 0 → 3 * q 0 = -q 3)
    ∧ (∀ g : IcosahedralGroup,
        IsAffineWeight (fun i => su5AntifundCharge ((g : Equiv.Perm (Fin 5)) i)))

/-- **[Derived Pauli/CAR registers + period capacities + symmetry tensors]**
Lean checks the derivation chain:

`SubshellMode q`
  gives `2(2l+1)` finite electron modes;
Pauli/CAR gives Boolean occupancy and idempotent number projections;
the shell sum gives `shellCapacity n = 2n²`;
the Aufbau period grouping makes each period capacity one of these shell
capacities; and, independently, the `A₅/S₅/SU(5)` tensor infrastructure
preserves the Cartan metric and traceless charge constraints. -/
lemma derived_pauliCAR_registers_periodCapacities_su5IcosahedralTensors_checked :
    HasDerivedPauliCARRegistersAndSu5IcosahedralTensors := by
  refine ⟨?_, ?_, ?_, ?_, shellCapacity_eq_two_nSq, ?_, ?_, periods_flatten_eq_aufbau,
    ?_, icosahedralGroup_index_two_in_su5Weyl, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    simpa [BoundSubshell.capacity, capacityOfAngularMomentum] using card_subshellMode q
  · intro q
    simpa [subshellBitCapacity, BoundSubshell.capacity, capacityOfAngularMomentum]
      using subshellStorageCount q
  · intro A _ _ q R mode
    exact ⟨modeNumber_selfAdjoint R mode, modeNumber_idempotent R mode⟩
  · intro n
    unfold shellCapacity
    apply Finset.sum_congr rfl
    intro l _
    simp [capacityOfAngularMomentum, Nat.mul_comm]
  · rw [octetCapacity_eq_eight, shellCapacity_eq_two_nSq]
    norm_num
  · rw [shellCapacity_eq_two_nSq]
  · intro K hK
    rw [periodLengths_eq_shellCapacities] at hK
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
    rcases hK with h | h | h | h | h | h | h
    · exact ⟨1, h, shellCapacity_eq_two_nSq 1⟩
    · exact ⟨2, h, shellCapacity_eq_two_nSq 2⟩
    · exact ⟨2, h, shellCapacity_eq_two_nSq 2⟩
    · exact ⟨3, h, shellCapacity_eq_two_nSq 3⟩
    · exact ⟨3, h, shellCapacity_eq_two_nSq 3⟩
    · exact ⟨4, h, shellCapacity_eq_two_nSq 4⟩
    · exact ⟨4, h, shellCapacity_eq_two_nSq 4⟩
  · intro i
    exact ⟨su5CartanMetric_row_eq_affineBasis i, su5CartanMetric_row_sum_zero i⟩
  · intro σ i j
    exact su5CartanMetric_permInvariant σ i j
  · intro g i j
    exact su5CartanMetric_icosahedral_invariant g i j
  · intro q htrace hcolor hnu
    exact su5_charge_quantization q htrace hcolor hnu
  · intro g
    unfold IsAffineWeight
    rw [Equiv.sum_comp (g : Equiv.Perm (Fin 5)) su5AntifundCharge]
    exact su5AntifundCharge_isAffineWeight


/-- The finite KL stress of an occupation row, using the repository's finite KL divergence directly.
The maps `p` and `q` are the model's observed and reference five-channel distributions associated
to the occupation row. -/
def occupationKLDivergenceStress
    (p q : List Nat → Fin 5 → ℝ) (occupations : List Nat) : ℝ :=
  finiteKLDivergence (p occupations) (q occupations)

/-- If the observed five-channel law is the reference law and no channel has zero reference weight,
the KL contribution vanishes. -/
lemma occupationKLDivergenceStress_zero_of_reference_eq
    (p : List Nat → Fin 5 → ℝ) (occupations : List Nat)
    (hpos : ∀ i, p occupations i ≠ 0) :
    occupationKLDivergenceStress p p occupations = 0 := by
  unfold occupationKLDivergenceStress finiteKLDivergence
  apply Finset.sum_eq_zero
  intro i _hi
  rw [div_self (hpos i)]
  simp

/-- The `SU(5)` Cartan-metric stress of an occupation row.  The map `w` is the traceless or centered
five-channel occupation weight supplied by the atomic model; the tensor itself is the existing
`su5CartanMetric`, not a redefinition. -/
noncomputable def su5OccupationCartanStress
    (w : List Nat → Fin 5 → ℝ) (occupations : List Nat) : ℝ :=
  ∑ i, ∑ j, w occupations i * su5CartanMetric i j * w occupations j

/-- A zero occupation weight has zero Cartan stress. -/
lemma su5OccupationCartanStress_zero_of_weight_zero
    (w : List Nat → Fin 5 → ℝ) (occupations : List Nat)
    (hzero : ∀ i, w occupations i = 0) :
    su5OccupationCartanStress w occupations = 0 := by
  unfold su5OccupationCartanStress
  simp [hzero]

/-- A concrete score constructor for recomputing atomic occupation rows without an exception table:
Hund level/pairing/exchange energy plus KL information stress, `SU(5)` Cartan stress, and the
icosahedral stress term supplied by the Newton--Ostrovskyi bridge. -/
noncomputable def atomicInformationGeometryFunctional
    (hundEnergyAt : Nat → HundSubshellEnergy)
    (lambdaInfo lambdaCartan lambdaIcosahedral : ℝ)
    (p q : List Nat → Fin 5 → ℝ)
    (w : List Nat → Fin 5 → ℝ)
    (icosahedralStress : List Nat → ℝ) : AtomicEnergyFunctional where
  hundEnergyAt := hundEnergyAt
  informationWeight := lambdaInfo
  informationStress := occupationKLDivergenceStress p q
  cartanWeight := lambdaCartan
  cartanStress := su5OccupationCartanStress w
  icosahedralWeight := lambdaIcosahedral
  icosahedralStress := icosahedralStress

/-- The same KL/Cartan/icosahedral score constructor, but with Hund coefficients derived from a
common-unit orbital-integral model rather than supplied as a raw function. -/
noncomputable def atomicInformationGeometryFunctionalFromOrbitalIntegrals
    (M : AtomicOrbitalIntegralModel)
    (lambdaInfo lambdaCartan lambdaIcosahedral : ℝ)
    (p q : List Nat → Fin 5 → ℝ)
    (w : List Nat → Fin 5 → ℝ)
    (icosahedralStress : List Nat → ℝ) : AtomicEnergyFunctional :=
  atomicEnergyFunctionalFromOrbitalIntegrals M
    lambdaInfo (occupationKLDivergenceStress p q)
    lambdaCartan (su5OccupationCartanStress w)
    lambdaIcosahedral icosahedralStress

/-- The concrete score is exactly the sum of the existing Hund algebra, finite KL divergence,
`SU(5)` Cartan-metric stress, and the supplied icosahedral stress term. -/
lemma atomicInformationGeometryFunctional_totalScore_eq
    (hundEnergyAt : Nat → HundSubshellEnergy)
    (lambdaInfo lambdaCartan lambdaIcosahedral : ℝ)
    (p q : List Nat → Fin 5 → ℝ)
    (w : List Nat → Fin 5 → ℝ)
    (icosahedralStress : List Nat → ℝ) (occupations : List Nat) :
    (atomicInformationGeometryFunctional hundEnergyAt
        lambdaInfo lambdaCartan lambdaIcosahedral p q w icosahedralStress).totalScore occupations
      =
        (hundOccupationEnergyWith hundEnergyAt 0 aufbauSubshells occupations : ℝ)
          + lambdaInfo * finiteKLDivergence (p occupations) (q occupations)
          + lambdaCartan * su5OccupationCartanStress w occupations
          + lambdaIcosahedral * icosahedralStress occupations := by
  rfl

/-- Expanding the derived information-geometry score: the Hund part is computed from
`AtomicOrbitalIntegralModel`, while the information-theory part is the existing finite KL
divergence and the geometric parts are the existing `SU(5)` Cartan and icosahedral stresses. -/
lemma atomicInformationGeometryFunctionalFromOrbitalIntegrals_totalScore_eq
    (M : AtomicOrbitalIntegralModel)
    (lambdaInfo lambdaCartan lambdaIcosahedral : ℝ)
    (p q : List Nat → Fin 5 → ℝ)
    (w : List Nat → Fin 5 → ℝ)
    (icosahedralStress : List Nat → ℝ) (occupations : List Nat) :
    (atomicInformationGeometryFunctionalFromOrbitalIntegrals M
        lambdaInfo lambdaCartan lambdaIcosahedral p q w icosahedralStress).totalScore occupations
      =
        (hundOccupationEnergyWith M.hundEnergyAt 0 aufbauSubshells occupations : ℝ)
          + lambdaInfo * finiteKLDivergence (p occupations) (q occupations)
          + lambdaCartan * su5OccupationCartanStress w occupations
          + lambdaIcosahedral * icosahedralStress occupations := by
  rfl

section HamiltonianInformationGeometry

variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
variable {ι : Type*} [Fintype ι] {H : SecondQuantizedElectronicHamiltonian A ι}

/-- The KL/Cartan/icosahedral information-geometry score backed directly by one
second-quantized electronic Hamiltonian model.  Its Hund coefficients are not a separate table:
they are read from `SubshellHamiltonianEnergyDerivation H` rows. -/
noncomputable def atomicInformationGeometryFunctionalFromHamiltonianIntegrals
    (M : AtomicHamiltonianIntegralModel H)
    (lambdaInfo lambdaCartan lambdaIcosahedral : ℝ)
    (p q : List Nat → Fin 5 → ℝ)
    (w : List Nat → Fin 5 → ℝ)
    (icosahedralStress : List Nat → ℝ) : AtomicEnergyFunctional :=
  atomicEnergyFunctionalFromHamiltonianIntegrals M
    lambdaInfo (occupationKLDivergenceStress p q)
    lambdaCartan (su5OccupationCartanStress w)
    lambdaIcosahedral icosahedralStress

/-- Expanding the Hamiltonian-backed information-geometry score: the Hund term is computed from
subshell derivations of the same second-quantized Hamiltonian, while the information/geometric
terms are the existing finite KL, `SU(5)` Cartan, and icosahedral stresses. -/
lemma atomicInformationGeometryFunctionalFromHamiltonianIntegrals_totalScore_eq
    (M : AtomicHamiltonianIntegralModel H)
    (lambdaInfo lambdaCartan lambdaIcosahedral : ℝ)
    (p q : List Nat → Fin 5 → ℝ)
    (w : List Nat → Fin 5 → ℝ)
    (icosahedralStress : List Nat → ℝ) (occupations : List Nat) :
    (atomicInformationGeometryFunctionalFromHamiltonianIntegrals M
        lambdaInfo lambdaCartan lambdaIcosahedral p q w icosahedralStress).totalScore occupations
      =
        (hundOccupationEnergyWith
            (fun i => (M.subshellDerivationAt i).toHundSubshellEnergy)
            0 aufbauSubshells occupations : ℝ)
          + lambdaInfo * finiteKLDivergence (p occupations) (q occupations)
          + lambdaCartan * su5OccupationCartanStress w occupations
          + lambdaIcosahedral * icosahedralStress occupations := by
  rfl

end HamiltonianInformationGeometry

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.AtomicInformationCapacity

end

end
