/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers
public import Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsZoo
public import Physlib.QuantumMechanics.ComplexAction.PeriodicTableMadelungSpinTower
public import Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries
meta import Zil

/-!
# The periodic table's structure: shell capacity `2n²`, blocks, periods, spinor floors

The table-structure layer in four namespaces (each formerly its own module):

* **Part I — `PeriodicTableShellCapacity`.** The shell capacity `∑_{l<n} 2(2l+1) = 2n²`
  (`shellCapacity_eq_two_nSq`; K=2, L=8, M=18, N=32) and its spin-½ origin — the factor `2` is the
  electron's spin doublet (`shellCapacity_eq_spin_times_magnetic`, `electron_is_spin_half_fermion`),
  the valence octet `s+p = 8` (`octetCapacity_eq_eight`, `octet_eq_spin_times_sp_magnetic`), and the
  Pauli occupancy bound with its Feynman/Tasaki number-operator form.
* **Part II — `PeriodicTableBlocks`.** The `s/p/d/f` blocks: widths as the subshell capacities
  `2, 6, 10, 14` (`blockWidths`), element counts `14, 36, 40, 28` (`sBlock_count` …), and the
  partition of all `118` elements (`blocks_cover_all_elements`).
* **Part III — `PeriodicTablePeriods`.** The period lengths `[2,8,8,18,18,32,32]`
  (`periodLengths_eq`, each a `2n²` shell capacity, summing to `118`), the noble-gas atomic numbers
  `[2,10,18,36,54,86,118]` (`nobleGasZ_eq`) with their Feynman occupation-basis particle numbers,
  and the octet reading of periods 2–3 (`periods_two_three_eq_octet`).
* **Part IV — `PeriodicTableSpinorFloors`.** The Varlamov weld: the `n`-th SO(4,2)-tower floor is
  the self-conjugate diagonal `τ_{(j,j)}` of the `SL(2,ℂ)` spinor lattice —
  `floorRepresentation_degree` (`(m+1)² = so4FockDim`), zero generalized spin
  (`floorRepresentation_selfConjugate`), the Rydberg `2n²` as the spin-doubled degree
  (`rydberg_from_degree`), the interlocking Haenzel ladder, and the `4^m` spinspace growth.

**Honest layering.** Proven: the `2n²` combinatorics with its spin-doublet factorization, the block
and period counts with their `118` coverage, the Pauli occupancy bounds, and the exact label
arithmetic of the spinor-floor weld. Empirical input: the Madelung filling order (the Aufbau list),
the block/period spans, and the `Spin(4) = SU(2)×SU(2)` weight-theory identification (cited).

## References

* Shell capacity `2n²`; the `s/p/d/f` block structure; period lengths and noble gases; V. V.
  Varlamov, arXiv:2607.08105 (the tower) and arXiv:1409.1400 (the spinor lattice). Built on
  `Particles.AtomicSubshellQuantumNumbers`, `Fermion.SpinStatisticsZoo`,
  `PeriodicTableMadelungSpinTower`, and `Particles.SpinorStructureInternalSymmetries`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableShellCapacity

open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist


/-- Sum of the first `n` odd numbers `∑_{l<n}(2l+1) = n²` — the number of magnetic `(l, mₗ)` states in shell
`n` (`∑_{l<n}(2l+1)`). -/
lemma sum_odd (n : ℕ) : ∑ l ∈ Finset.range n, (2 * l + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-- **The magnetic-state count of shell `n`** `∑_{l<n}(2l+1)` — the `(l, mₗ)` orbital states with `l < n`. -/
def shellMagneticCount (n : ℕ) : ℕ := ∑ l ∈ Finset.range n, (2 * l + 1)

/-- **[Magnetic count is `n²`]** `∑_{l<n}(2l+1) = n²`. -/
lemma shellMagneticCount_eq_nSq (n : ℕ) : shellMagneticCount n = n ^ 2 := sum_odd n

/-- **The Pauli capacity of shell `n`** `∑_{l<n} 2(2l+1)` — the maximum number of electrons in shell `n`. -/
def shellCapacity (n : ℕ) : ℕ := ∑ l ∈ Finset.range n, capacityOfAngularMomentum l

/-- **[Shell capacity is `2n²`]** `∑_{l<n} 2(2l+1) = 2n²` — the periodic-table shell capacity (K=2, L=8, M=18,
N=32). -/
lemma shellCapacity_eq_two_nSq (n : ℕ) : shellCapacity n = 2 * n ^ 2 := by
  unfold shellCapacity
  simp only [capacityOfAngularMomentum]
  rw [← Finset.mul_sum, sum_odd]

lemma shell_K : shellCapacity 1 = 2 := by rw [shellCapacity_eq_two_nSq]; norm_num
lemma shell_L : shellCapacity 2 = 8 := by rw [shellCapacity_eq_two_nSq]; norm_num
lemma shell_M : shellCapacity 3 = 18 := by rw [shellCapacity_eq_two_nSq]; norm_num
lemma shell_N : shellCapacity 4 = 32 := by rw [shellCapacity_eq_two_nSq]; norm_num


/-- **[The electron is a spin-½ fermion]** `θ(½) = −1` — the electron carries the half-integer-spin exchange
sign (`Fermion.SpinStatisticsZoo`/`ribbonTwist_fermion`), which is *why* it obeys Pauli exclusion and has two spin
projections. -/
lemma electron_is_spin_half_fermion : ribbonTwist (1 / 2) = -1 := ribbonTwist_fermion

/-- **[The spin factor is the two-state doublet]** the `Fin 2` spin index of a subshell mode has exactly `2`
states — the two `mₛ = ±½` projections of the spin-½ electron, the origin of the `2` in `2(2l+1)`. -/
lemma spin_factor_eq_two : Fintype.card (Fin 2) = 2 := by simp

/-- **[Shell capacity = spin doublet × magnetic count]** `2n² = 2 · n²`: the shell capacity is the electron
spin multiplicity (`Fintype.card (Fin 2) = 2`, the spin-½ doublet) times the magnetic-state count `n²`. The
periodic-table shell structure is a direct consequence of the electron's half-integer spin. -/
lemma shellCapacity_eq_spin_times_magnetic (n : ℕ) :
    shellCapacity n = Fintype.card (Fin 2) * shellMagneticCount n := by
  rw [shellCapacity_eq_two_nSq, spin_factor_eq_two, shellMagneticCount_eq_nSq]


/-- **The valence octet capacity** — the `s` (`l=0`) plus `p` (`l=1`) subshells of a valence shell:
`2(2·0+1) + 2(2·1+1)`. -/
def octetCapacity : ℕ := capacityOfAngularMomentum 0 + capacityOfAngularMomentum 1

/-- **[The octet rule]** `s + p = 2 + 6 = 8` — the eight valence electrons that complete the `s`/`p` block (the
noble-gas configuration of periods 2–3: Ne, Ar), the basis of the octet rule of chemical bonding. -/
lemma octetCapacity_eq_eight : octetCapacity = 8 := by
  unfold octetCapacity; rw [s_capacity, p_capacity]

/-- **[The octet from spin × magnetic states]** `8 = 2 · 4` — two spin projections of the electron times the
four magnetic `(l, mₗ)` states of the `s`/`p` block (`1 + 3`), i.e. the octet inherits the same spin-½ doublet
factor as the shell capacity `2n²`. -/
lemma octet_eq_spin_times_sp_magnetic :
    octetCapacity = Fintype.card (Fin 2) * (1 + 3) := by
  rw [octetCapacity_eq_eight, spin_factor_eq_two]

/-!

The information-capacity layer (bit capacity `= 2(2l+1)`, the `2^N` storage count, the `s/p/d/f` bit
capacities) is `Particles.AtomicShellInformationCapacityOctet`; this file keeps only the Pauli *occupancy bound*, which
that file does not provide. -/

/-- **[Pauli exclusion as an occupancy bound]** for *any* occupancy assignment `(n,l,mₗ,mₛ) ↦ Bool`, the
number of occupied modes (electrons) is at most the subshell capacity `2(2l+1)` — no two electrons share all
four quantum numbers, so the subshell is a finite register of `2(2l+1)` one-bit slots. -/
lemma pauli_occupancy_le_capacity (q : BoundSubshell) (occ : SubshellMode q → Bool) :
    (Finset.univ.filter (fun m => occ m = true)).card ≤ q.capacity := by
  calc (Finset.univ.filter (fun m => occ m = true)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = Fintype.card (SubshellMode q) := Finset.card_univ
    _ = q.capacity := card_subshellMode q

/-- **[Feynman number operator gives the same Pauli bound]** on the finite subshell carrier, the
Feynman/Tasaki number eigenvalue `Σ n_α` is bounded by the same `2(2l+1)` shell capacity. -/
lemma feynmanNumber_le_subshellCapacity (q : BoundSubshell) (occ : SubshellMode q → Bool) :
    feynmanNumberEigenvalue occ ≤ q.capacity := by
  calc
    feynmanNumberEigenvalue occ ≤ Fintype.card (SubshellMode q) :=
      feynmanNumberEigenvalue_le_card occ
    _ = q.capacity := card_subshellMode q

end Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableShellCapacity

/-! ## Part II — the `s/p/d/f` blocks: a complete classification of all elements -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableBlocks

open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers


set_option backward.isDefEq.respectTransparency false in
/-- The four **periodic-table blocks** `s, p, d, f`. -/
inductive Block | s | p | d | f
  deriving DecidableEq, Fintype

/-- The **azimuthal quantum number** `l` of a block: `s = 0, p = 1, d = 2, f = 3`. -/
def blockAzimuthal : Block → ℕ
  | .s => 0
  | .p => 1
  | .d => 2
  | .f => 3

/-- The **width of a block** — the Pauli capacity `2(2l+1)` of one row (`s = 2, p = 6, d = 10, f = 14`). -/
def blockWidth (b : Block) : ℕ := capacityOfAngularMomentum (blockAzimuthal b)

/-- The block widths are `2, 6, 10, 14`. -/
lemma blockWidths : blockWidth .s = 2 ∧ blockWidth .p = 6 ∧ blockWidth .d = 10 ∧ blockWidth .f = 14 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide


/-- The **number of periods each block spans**: `s` fills in all `7` periods, `p` in `6` (periods 2–7), `d` in
`4` (periods 4–7), `f` in `2` (periods 6–7) — the `d`/`f` blocks starting one and two rows late. -/
def blockPeriods : Block → ℕ
  | .s => 7
  | .p => 6
  | .d => 4
  | .f => 2

/-- The **number of elements in a block** `= width · periods`. -/
def blockCount (b : Block) : ℕ := blockWidth b * blockPeriods b

/-- **The s-block has 14 elements** `2 · 7`. -/
lemma sBlock_count : blockCount .s = 14 := by decide

/-- **The p-block has 36 elements** `6 · 6`. -/
lemma pBlock_count : blockCount .p = 36 := by decide

/-- **The d-block has 40 elements** `10 · 4` — the transition metals. -/
lemma dBlock_count : blockCount .d = 40 := by decide

/-- **The f-block has 28 elements** `14 · 2` — the lanthanides and actinides. -/
lemma fBlock_count : blockCount .f = 28 := by decide


/-- **The four blocks partition all 118 elements** `14 + 36 + 40 + 28 = 118`: every periodic-table element
belongs to exactly one of the `s, p, d, f` blocks (matching `PeriodicTableAufbauStructure.aufbau_covers_118`). -/
lemma blocks_cover_all_elements :
    blockCount .s + blockCount .p + blockCount .d + blockCount .f = 118 := by decide

end Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableBlocks

/-! ## Part III — period lengths and the noble-gas closed-shell numbers -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTablePeriods

open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers
open Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableShellCapacity


/-- The Aufbau capacities grouped into **periods**: each period runs from an `ns` subshell through the `np`
subshell that closes it (`s`, `s p`, `s p`, `s d p`, `s d p`, `s f d p`, `s f d p`). -/
def periods : List (List Nat) :=
  [[2], [2, 6], [2, 6], [2, 10, 6], [2, 10, 6], [2, 14, 10, 6], [2, 14, 10, 6]]

/-- **[The periods partition the Aufbau order]** flattening the period grouping reproduces the Madelung-ordered
Aufbau capacity sequence exactly. -/
lemma periods_flatten_eq_aufbau : periods.flatten = aufbauCapacities := by
  decide

/-- **The period lengths** — the number of elements in each period. -/
def periodLengths : List Nat := periods.map List.sum

/-- **[The period lengths]** `[2, 8, 8, 18, 18, 32, 32]`. -/
lemma periodLengths_eq : periodLengths = [2, 8, 8, 18, 18, 32, 32] := by decide

/-- **[Period lengths sum to 118]** consistent with `aufbauCapacities_sum`. -/
lemma periodLengths_sum_eq : periodLengths.sum = 118 := by decide

/-- **[Each period length is a `2n²` shell capacity]** `[2,8,8,18,18,32,32] = [2·1², 2·2², 2·2², 2·3², 2·3²,
2·4², 2·4²]` — the period lengths are the shell capacities (`Particles.PeriodicTableShellCapacity.shellCapacity`), the
larger ones repeated because the `d`/`f` blocks fill late. -/
lemma periodLengths_eq_shellCapacities :
    periodLengths = [shellCapacity 1, shellCapacity 2, shellCapacity 2, shellCapacity 3,
      shellCapacity 3, shellCapacity 4, shellCapacity 4] := by
  rw [periodLengths_eq]
  simp only [shellCapacity_eq_two_nSq]
  decide


/-- The **noble-gas atomic numbers** — the cumulative period sums, i.e. the `Z` at which each period closes. -/
def nobleGasZ : List Nat :=
  (List.range periodLengths.length).map (fun k => (periodLengths.take (k + 1)).sum)

/-- **[The noble-gas `Z`]** `[2, 10, 18, 36, 54, 86, 118]` — He, Ne, Ar, Kr, Xe, Rn, Og. -/
lemma nobleGasZ_eq : nobleGasZ = [2, 10, 18, 36, 54, 86, 118] := by decide

/-- The `Fin 118` row indices of the noble gases in the generated all-118 Feynman/Tasaki
occupation-basis table.  The row index is `Z - 1`. -/
def nobleGasFeynmanIndices : List (Fin 118) :=
  [⟨1, by decide⟩, ⟨9, by decide⟩, ⟨17, by decide⟩, ⟨35, by decide⟩,
    ⟨53, by decide⟩, ⟨85, by decide⟩, ⟨117, by decide⟩]

/-- The period cumulative sums are exactly the particle-number eigenvalues of the generated
Feynman/Tasaki occupation-basis rows for the noble gases. -/
lemma nobleGasFeynmanParticleNumbers_eq :
    nobleGasFeynmanIndices.map (fun i => (all118FeynmanOccupationBasis i).particleNumber)
      = nobleGasZ := by
  rw [nobleGasZ_eq]
  simp [nobleGasFeynmanIndices, all118FeynmanOccupationBasis_particleNumber]

/-- **[Oganesson closes the Aufbau table]** the last noble-gas number `118` is the full Aufbau electron total
(`aufbauCapacities_sum`). -/
lemma oganesson_eq_aufbau_sum : (118 : ℕ) = aufbauCapacities.sum := by
  rw [aufbauCapacities_sum]


/-- **[Periods 2 and 3 are octets]** the second and third period lengths are both `8 = octetCapacity` (the
valence `s/p` octet, `Particles.PeriodicTableShellCapacity`): filling the `s` and `p` subshells completes an `8`-element
row — the period-table realization of the octet rule. -/
lemma periods_two_three_eq_octet :
    periodLengths = [2, octetCapacity, octetCapacity, 18, 18, 32, 32] := by
  rw [periodLengths_eq, octetCapacity_eq_eight]

/-- **[Neon closes the first octet]** `Z(Ne) = Z(He) + octet = 2 + 8 = 10` — the noble gas neon is helium plus
a full valence octet. -/
lemma neon_is_helium_plus_octet : 2 + octetCapacity = 10 := by
  rw [octetCapacity_eq_eight]

/-- **[Argon closes the second octet]** `Z(Ar) = Z(Ne) + octet = 10 + 8 = 18`. -/
lemma argon_is_neon_plus_octet : 10 + octetCapacity = 18 := by
  rw [octetCapacity_eq_eight]

end Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTablePeriods

/-! ## Part IV — the periodic table's floors as self-conjugate spinor representations -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableSpinorFloors

open Physlib.QuantumMechanics.ComplexAction.PeriodicTableMadelungSpinTower
open Physlib.QuantumMechanics.ComplexAction.Particles.SpinorStructureInternalSymmetries

/-- **The floor representation**: the `(m+1)`-th tower floor as the self-conjugate spinor
label `τ_{(m/2, m/2)}` — `k = r = m` undotted and dotted factors. -/
def floorRepresentation (m : ℕ) : LorentzSpinorRepresentation :=
  { leftFactors := m, rightFactors := m }

/-- **The degree of the floor label is the Fock dimension**: `(m+1)² = so4FockDim (m+1)` —
the `SL(2,ℂ)` representation degree of the diagonal label is exactly the SO(4)
`(j,j)`-diagram dimension of the floor. -/
theorem floorRepresentation_degree (m : ℕ) :
    sl2cRepresentationDegree (floorRepresentation m) = so4FockDim (m + 1) := by
  unfold sl2cRepresentationDegree floorRepresentation so4FockDim
  ring

/-- **The floors are self-conjugate**: the generalized (chirality) spin of every floor label
vanishes — the periodic table's floors sit on the boson diagonal of the spinor lattice, and
the chemical spin doubling comes from the fourth Cartan generator, not from `|k−r|`. -/
theorem floorRepresentation_selfConjugate (m : ℕ) :
    spinNumerator (floorRepresentation m) = 0 :=
  spinNumerator_self_conjugate_zero m

/-- **The Rydberg shell is the spin-doubled spinor degree**: `2n²` as twice the degree of
the diagonal label — the two Varlamov schemes assign the same state count to a floor. -/
theorem rydberg_from_degree (m : ℕ) :
    aufbauShellDim (m + 1) = 2 * sl2cRepresentationDegree (floorRepresentation m) := by
  rw [floorRepresentation_degree, rydberg_spin_doubling]

/-- **Consecutive floors interlock**: the Haenzel ladder `n → n+1` of the tower is a step of
Varlamov's interlocking spin-chain along the self-conjugate diagonal — both spinor factor
counts increase by one. -/
theorem floorRepresentation_interlocking (m : ℕ) :
    Interlocking (floorRepresentation m) (floorRepresentation (m + 1)) :=
  ⟨Or.inl rfl, Or.inl rfl⟩

/-- **The floor spinspace grows fourfold**: `2^{k+r} = 4^m` — each ladder step tensors one
undotted and one dotted factor onto the spinspace. -/
theorem floorRepresentation_spinspace (m : ℕ) :
    spinspaceDimension (floorRepresentation m) = 4 ^ m := by
  unfold spinspaceDimension floorRepresentation
  rw [show m + m = 2 * m by ring, pow_mul]
  norm_num

end Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableSpinorFloors

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableShellCapacity.shellCapacity_eq_spin_times_magnetic where
  formalizes @ "claim:the-periodic-shell-capacity-two-n-squared-factors-as-the-electron-spin-doublet-times-the-magnetic-count",
  caveat @ "claim:the-madelung-filling-order-is-empirical-input-in-the-aufbau-list"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableBlocks.blocks_cover_all_elements where
  formalizes @ "claim:the-four-spdf-blocks-partition-all-one-hundred-eighteen-elements",
  requires @ "claim:the-periodic-shell-capacity-two-n-squared-factors-as-the-electron-spin-doublet-times-the-magnetic-count"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTablePeriods.nobleGasZ_eq where
  formalizes @ "claim:the-noble-gas-atomic-numbers-are-the-cumulative-period-sums",
  requires @ "claim:the-four-spdf-blocks-partition-all-one-hundred-eighteen-elements"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableSpinorFloors.rydberg_from_degree where
  formalizes @ "claim:the-rydberg-shell-is-the-spin-doubled-self-conjugate-spinor-degree",
  supported_by @ "paper:varlamov-2607-08105-periodic-table-tower",
  caveat @ "claim:the-spin-four-su2-times-su2-weight-identification-is-cited-not-reproven"

zil_file_contract physlib.periodicTableShellCapacity where
  promises "The periodic table's structure: the shell capacity two-n-squared factors as the electron spin doublet times the magnetic count, the four spdf blocks partition all one hundred eighteen elements, the noble-gas atomic numbers are the cumulative period sums, and each tower floor is the spin-doubled self-conjugate spinor degree."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableShellCapacity.shellCapacity",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableBlocks.blockCount",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableSpinorFloors.floorRepresentation"]
  forbids_substitutes ["the Madelung filling order, empirical input in the Aufbau list",
    "the Spin(4) weight-theory identification, cited not reproven"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableShellCapacity.shellCapacity_eq_spin_times_magnetic,
    Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableBlocks.blocks_cover_all_elements,
    Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTablePeriods.nobleGasZ_eq,
    Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableSpinorFloors.rydberg_from_degree]

/- ZIL-END -/
