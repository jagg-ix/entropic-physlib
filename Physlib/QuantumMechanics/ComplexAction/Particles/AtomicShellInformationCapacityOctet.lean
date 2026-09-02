/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers
public import Physlib.QuantumMechanics.ComplexAction.Particles.CriticalStabilityPrinciple
public import Mathlib.Data.Nat.Choose.Basic
meta import Zil

/-!
# Atomic shells: information registers, Hund magnetism, and the relativistic collapse bound

The atomic-shell layer in three namespaces (each formerly its own module):

* **Part I — `AtomicShellInformationCapacityOctet`.** Each electron mode `(m_l, m_s)` is a one-bit
  Pauli storage slot, so a subshell is a finite information register: `2^capacity` configurations
  (`subshellStorageCount`), the octet rule as an 8-bit capacity (`octet_bitCapacity`,
  `octet_storageCount` `2^8 = 256`), the `s,p,d,f` capacities `2, 6, 10, 14`
  (`subshell_bitCapacities`), the principal-shell `2n²` (`principalShell_bitCapacity`), the
  register/Fock/Liouville compatibility of the same carrier
  (`subshellRegister_secondQuantized_capacity_bridge`), the Feynman/Tasaki occupation-number
  compatibility, the sp³ tetrahedral factorization of the octet (`octet_eq_spatial_times_spin`),
  and the d-shell's unique pair-capacity coincidence with the `SU(5)` `10`
  (`dShell_unique_pairs_eq_capacity`).
* **Part II — `AtomicHundMagnetism`.** Hund's first rule as spin-doublet combinatorics: the unpaired
  count `min(q, C−q)` vanishing at the diamagnetic closures, peaking at the half-filled shell
  (`hund_max_at_halffill` — the stability of `p³`, `d⁵`, `f⁷`), with the concrete magnetic subshells
  (N, Mn²⁺/Fe³⁺, Eu²⁺/Gd³⁺, Zn).
* **Part III — `AtomicRelativisticStabilityBound`.** The atomic continuous-cost cliff: the
  Dirac–Coulomb `1s` radicand `1 − (Zα)²` is nonnegative iff `Z ≤ 1/α` (`bound_state_iff_Z`,
  `heaviestBoundZ_137`), and the collapse is a `CriticalStabilitySystem` instance whose bounded
  stable region is exactly `{Z < 1/α}` (`atomic_collapse_cliff`, `atomic_stable_region_eq`) — the
  atomic column of the critical-stability map, parallel to the nuclear fission cliff.

**Honest layering.** The register counts, the octet factorization, the pair-capacity uniqueness, the
unpaired-count combinatorics, and the collapse criterion with its bounded region are all derived.
Stated as input: the Dirac–Coulomb `1s` energy formula (the exact spectral result), and the standard
readings "more unpaired = larger moment" and the holographic information-capacity analogy.

## References

* W. Pauli (1925), exclusion; G. N. Lewis (1916), the octet rule; Hund's rules; the Sommerfeld /
  Dirac–Coulomb `Z ≈ 137` collapse. Built on `Particles.AtomicSubshellQuantumNumbers` and
  `Particles.CriticalStabilityPrinciple`; the electronic analogue of `Particles.NuclearPairingParity`
  (in `NuclearIsotopeStability`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.AtomicShellInformationCapacityOctet

open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers
open Physlib.QuantumMechanics.Liouville.SecondQuantization

/-- **The occupation configurations of a subshell**: each mode `(m_l, m_s)` is filled (`true`) or empty
(`false`) — the storable states of the subshell information register (Pauli: ≤ 1 electron per mode). -/
abbrev subshellStorageStates (q : BoundSubshell) : Type := SubshellMode q → Bool

/-- **The information capacity of a subshell, in bits** `= 2(2l+1)` — the number of one-bit modes. -/
def subshellBitCapacity (q : BoundSubshell) : Nat := q.capacity

/-- **[A `B`-bit subshell has `2^B` configurations]** `#{occupations} = 2^capacity`: the subshell stores
exactly its `capacity = 2(2l+1)` bits of information. -/
lemma subshellStorageCount (q : BoundSubshell) :
    Fintype.card (subshellStorageStates q) = 2 ^ subshellBitCapacity q := by
  show Fintype.card (SubshellMode q → Bool) = 2 ^ q.capacity
  rw [Fintype.card_fun, Fintype.card_bool, card_subshellMode]

/-! ## Register/Fock/Liouville compatibility -/

/-- **[Subshell register = Pauli Fock modes = Liouville fixed-number sector]** the same finite
subshell mode set supports all three representations used in the repo:

* the Boolean occupation register has `2^capacity` configurations,
* the exterior-algebra Fock creation generator squares to zero for each mode,
* the Liouville fixed-particle sector has the chosen number-operator eigenvalue.

This is the formal bridge from the information-capacity count to the second-quantized electron
carrier; it does not introduce empirical exceptions or fitted shell energies. -/
lemma subshellRegister_secondQuantized_capacity_bridge (q : BoundSubshell) :
    Fintype.card (subshellStorageStates q) = 2 ^ q.capacity
      ∧ (∀ mode : SubshellMode q,
          subshellFockCreation q mode * subshellFockCreation q mode = 0)
      ∧ (∀ (e : ℕ) (n : FixedSubshellLiouvilleOccupation q e),
          liouvilleNumberOperatorPairSum n.1 = e) := by
  exact ⟨by simpa [subshellBitCapacity] using subshellStorageCount q,
    (fun mode => subshellFockCreation_sq q mode),
    (fun e n => fixedSubshellLiouville_numberOperator q e n)⟩

/-! ## Feynman/Tasaki occupation-number compatibility -/

/-- The Boolean information register is the same finite carrier consumed by the Feynman/Tasaki
number operator: the number eigenvalue of any subshell occupation is bounded by the Pauli capacity. -/
lemma subshellStorage_feynmanNumber_le_capacity
    (q : BoundSubshell) (occ : subshellStorageStates q) :
    feynmanNumberEigenvalue occ ≤ q.capacity := by
  calc
    feynmanNumberEigenvalue occ ≤ Fintype.card (SubshellMode q) :=
      feynmanNumberEigenvalue_le_card occ
    _ = q.capacity := card_subshellMode q

/-- The information-register view and the diagonal noninteracting Hamiltonian view agree on the
same occupation carrier: moving an occupied higher-energy mode into an empty lower-energy mode is a
fixed-particle Feynman/Tasaki exchange step and cannot increase `H₀`. -/
lemma subshellStorageDiagonal_exchange_nonincreasing
    (q : BoundSubshell) (ε : SubshellMode q → ℝ) (occ : subshellStorageStates q)
    {low high : SubshellMode q} (hlow : occ low = false) (hhigh : occ high = true)
    (hle : ε low ≤ ε high) :
    feynmanDiagonalHamiltonianEigenvalue ε (feynmanMoveOccupation occ high low) ≤
      feynmanDiagonalHamiltonianEigenvalue ε occ :=
  feynmanDiagonalHamiltonian_exchange_nonincreasing ε occ hlow hhigh hle

/-! ## The octet rule as an 8-bit capacity -/

/-- **[The octet rule is 8 bits]** the valence `s+p` shells store `capacity(s) + capacity(p) = 2 + 6 = 8`
bits of occupation information — the chemical "rule of 8". -/
lemma octet_bitCapacity : capacityOfAngularMomentum 0 + capacityOfAngularMomentum 1 = 8 := by decide

/-- **[The octet register holds `2^8 = 256` configurations]** the eight `s+p` valence modes give `256`
distinguishable occupation states. -/
lemma octet_storageCount : 2 ^ (capacityOfAngularMomentum 0 + capacityOfAngularMomentum 1) = 256 := by
  decide

/-! ## Subshell and principal-shell bit capacities -/

/-- **[`s, p, d, f` bit capacities `= 2, 6, 10, 14`]** the information capacities of the angular-momentum
subshells. -/
lemma subshell_bitCapacities :
    capacityOfAngularMomentum 0 = 2 ∧ capacityOfAngularMomentum 1 = 6
      ∧ capacityOfAngularMomentum 2 = 10 ∧ capacityOfAngularMomentum 3 = 14 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **[A principal shell `n` stores `2n²` bits]** `Σ_{l<n} 2(2l+1) = 2n²` — the period lengths
`2, 8, 18, 32, …` are the information capacities of the principal shells. -/
lemma principalShell_bitCapacity (n : Nat) :
    (∑ l ∈ Finset.range n, capacityOfAngularMomentum l) = 2 * n ^ 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, capacityOfAngularMomentum]
      ring

/-! ## The valence octet and d-shell as orbital-symmetry frames

The valence and `d` registers carry the two lowest finite-rotation-group frames of
`ComplexAction.TetrahedralLorentzFrame`: the four sp³ directions (tetrahedral, `4`) and the five `d`
orbitals (icosahedral, `5`). -/

/-- **The four sp³ valence spatial slots** `1 s ⊕ 3 p ≃ Fin 4`: the one `s` and three `p` valence orbitals
hybridize into the four sp³ directions — the vertices of a regular tetrahedron
(`ComplexAction.TetrahedralLorentzFrame`). -/
def sp3Equiv : (Fin 1 ⊕ Fin 3) ≃ Fin 4 := finSumFinEquiv

/-- **There are four spatial valence orbitals** (`1 s + 3 p`) — the tetrahedral leg count. -/
lemma spatialValenceDegeneracy : (2 * 0 + 1) + (2 * 1 + 1) = 4 := by decide

/-- **The octet is four spatial directions × two spin states** `capacity(s) + capacity(p) = 4 · 2`: the 8-bit
valence register (`octet_bitCapacity`) factorizes as the four sp³ orbital directions times the spin double
cover (`Fin 2`). -/
lemma octet_eq_spatial_times_spin :
    capacityOfAngularMomentum 0 + capacityOfAngularMomentum 1 = 4 * 2 := by decide

/-- **The antisymmetric-pair count of `2l+1` orbitals** `C(2l+1, 2) = (2l+1)·l`. -/
lemma choose_orbital_pairs (l : Nat) : Nat.choose (2 * l + 1) 2 = (2 * l + 1) * l := by
  rw [Nat.choose_two_right]
  have h : 2 * l + 1 - 1 = 2 * l := by omega
  rw [h, show (2 * l + 1) * (2 * l) = 2 * ((2 * l + 1) * l) by ring,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

/-- **The d-shell antisymmetric-pair count equals its capacity** `C(5, 2) = capacity(l=2) = 10`: the
`C(2·2+1, 2) = 10` ordered pairs of the five `l = 2` orbitals (`dSpatialDegeneracy = 5`) match the d-shell
Pauli capacity — the dimension of the `SU(5)` `10 = Λ²(5)` (`ComplexAction.Su5TenRepresentation`). -/
lemma dShell_pairs_eq_capacity :
    Nat.choose dSpatialDegeneracy 2 = capacityOfAngularMomentum 2 := by decide

/-- **The d-shell is the unique subshell** whose antisymmetric-pair count equals its Pauli capacity:
`C(2l+1, 2) = capacity(l) ⟺ l = 2`. (`p`: `C(3,2) = 3 ≠ 6`; `f`: `C(7,2) = 21 ≠ 14`.) The identity
`C(n,2) = 2n` holds only at `n = 5`, so the `SU(5)` `10 = Λ²(5)` and the d-shell register share the value `10`
for a reason special to the five-fold. -/
lemma dShell_unique_pairs_eq_capacity (l : Nat) :
    Nat.choose (2 * l + 1) 2 = capacityOfAngularMomentum l ↔ l = 2 := by
  rw [capacityOfAngularMomentum, choose_orbital_pairs]
  constructor
  · intro hh
    have hmul : (2 * l + 1) * l = (2 * l + 1) * 2 := by rw [hh]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
  · rintro rfl; rfl

/-- **The d-shell capacity equals the `SU(5)` `10`-representation dimension** `= 10`
(`ComplexAction.Su5TenRepresentation.su5TenCharge : Fin 10 → ℚ`): equidimensional — the antisymmetric `Λ²(5)`
versus the orbital ⊗ spin register — coinciding by `dShell_unique_pairs_eq_capacity`. -/
lemma dCapacity_eq_su5TenDim : capacityOfAngularMomentum 2 = Fintype.card (Fin 10) := by decide

end Physlib.QuantumMechanics.ComplexAction.Particles.AtomicShellInformationCapacityOctet

/-! ## Part II — Hund's rule and subshell magnetism, from the spin-doublet count -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.AtomicHundMagnetism

open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers


/-- The **spatial orbitals** of subshell `l`: the `2l+1` magnetic states, each holding a spin pair. -/
def spatialOrbitals (l : ℕ) : ℕ := 2 * l + 1

/-- The **unpaired electrons** of `q` electrons in subshell `l` — by Hund's first rule (singly fill before
pairing), `min(q, C − q)` with `C = 2(2l+1)`; the distance to the nearer closed configuration. -/
def unpairedElectrons (l q : ℕ) : ℕ := min q (capacityOfAngularMomentum l - q)

/-- **An empty subshell is diamagnetic** `unpairedElectrons l 0 = 0`. -/
lemma unpaired_empty (l : ℕ) : unpairedElectrons l 0 = 0 := by unfold unpairedElectrons; omega

/-- **A full subshell is diamagnetic** `unpairedElectrons l C = 0` — all electrons paired (a closed shell). -/
lemma unpaired_full (l : ℕ) : unpairedElectrons l (capacityOfAngularMomentum l) = 0 := by
  unfold unpairedElectrons; omega

/-- **A half-filled subshell has every orbital singly occupied** `unpairedElectrons l (2l+1) = 2l+1` — maximal
spin. -/
lemma unpaired_halffill (l : ℕ) : unpairedElectrons l (spatialOrbitals l) = spatialOrbitals l := by
  unfold unpairedElectrons spatialOrbitals capacityOfAngularMomentum; omega


/-- **No filling exceeds the half-filled shell in unpaired electrons** — the half-filled subshell attains the
maximal spin (Hund's first rule), the source of the enhanced stability of `d⁵`, `f⁷`, `p³` configurations. -/
lemma hund_max_at_halffill (l q : ℕ) (h : q ≤ capacityOfAngularMomentum l) :
    unpairedElectrons l q ≤ unpairedElectrons l (spatialOrbitals l) := by
  rw [unpaired_halffill]
  unfold unpairedElectrons spatialOrbitals capacityOfAngularMomentum at *
  omega


/-- **Nitrogen `p³` is half-filled** — `3` unpaired electrons. -/
lemma p3_half_filled : unpairedElectrons 1 3 = 3 := by decide

/-- **High-spin `d⁵` (Mn²⁺, Fe³⁺) has five unpaired electrons** — the maximal-spin transition-metal shell. -/
lemma d5_half_filled : unpairedElectrons 2 5 = 5 := by decide

/-- **Half-filled `f⁷` (Eu²⁺, Gd³⁺) has seven unpaired electrons** — the maximal-spin lanthanide shell. -/
lemma f7_half_filled : unpairedElectrons 3 7 = 7 := by decide

/-- **Filled `d¹⁰` (Zn) is diamagnetic** — `0` unpaired electrons. -/
lemma d10_filled : unpairedElectrons 2 10 = 0 := by decide

end Physlib.QuantumMechanics.ComplexAction.Particles.AtomicHundMagnetism

/-! ## Part III — the relativistic `Z`-collapse bound: the atomic continuous-cost cliff -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.AtomicRelativisticStabilityBound

open Physlib.QuantumMechanics.ComplexAction.Particles.CriticalStabilityPrinciple


/-- The **Sommerfeld radicand** `1 − (Zα)²` under the Dirac–Coulomb `1s` energy `E = mc²√(1 − (Zα)²)`. The
ground state is real and bound iff this is nonnegative. -/
def sommerfeldRadicand (Z α : ℝ) : ℝ := 1 - (Z * α) ^ 2

/-- The **heaviest bound atomic number** `Z = 1/α` — derived from the collapse criterion (§A), not tabulated. -/
noncomputable def heaviestBoundZ (α : ℝ) : ℝ := 1 / α

/-- **The bound-state criterion, derived** `0 ≤ 1 − (Zα)² ↔ Zα ≤ 1`: the Dirac `1s` energy is real exactly when
the coupling stays below the critical value `Zα = 1`. -/
lemma bound_state_iff (Z α : ℝ) (hZ : 0 < Z) (hα : 0 < α) :
    0 ≤ sommerfeldRadicand Z α ↔ Z * α ≤ 1 := by
  unfold sommerfeldRadicand
  constructor
  · intro h; nlinarith [mul_pos hZ hα]
  · intro h; nlinarith [mul_pos hZ hα]

/-- **The collapse bound on the periodic table, derived** `0 ≤ 1 − (Zα)² ↔ Z ≤ 1/α`: a real bound ground state
exists exactly up to `Z = 1/α`, the heaviest bound atomic number. -/
lemma bound_state_iff_Z (Z α : ℝ) (hZ : 0 < Z) (hα : 0 < α) :
    0 ≤ sommerfeldRadicand Z α ↔ Z ≤ heaviestBoundZ α := by
  rw [bound_state_iff Z α hZ hα, heaviestBoundZ, le_div_iff₀ hα]

/-- **The collapse threshold is `Z = 137`** at the empirical fine-structure constant `α = 1/137`. -/
lemma heaviestBoundZ_137 : heaviestBoundZ (1 / 137) = 137 := by
  unfold heaviestBoundZ; norm_num


/-- The **relativistic collapse system**: the effective Coulomb coupling cost `α · Z` with critical threshold
`1` (the coupling `Zα` at which the `1s` level meets the negative continuum). A `CriticalStabilitySystem` via
`linearConfinement` — the same shape as the nuclear fission cliff. -/
noncomputable def relativisticCollapseSystem (α : ℝ) (hα : 0 < α) : CriticalStabilitySystem :=
  linearConfinement α 1 hα

/-- **The atomic collapse cliff** — the stable (bound) `Z` region is **bounded above**: the periodic table
terminates at the relativistic collapse. Inherited from `CriticalStabilityPrinciple.stable_bounded`. -/
lemma atomic_collapse_cliff (α : ℝ) (hα : 0 < α) :
    BddAbove {Z | (relativisticCollapseSystem α hα).cost Z < 1} :=
  (relativisticCollapseSystem α hα).stable_bounded

/-- **The abstract cliff is exactly the collapse bound** `{Z | cost Z < 1} = {Z | Z < 1/α}`: the
`CriticalStabilityPrinciple` stable region coincides with the derived `heaviestBoundZ` of §A. -/
lemma atomic_stable_region_eq (α : ℝ) (hα : 0 < α) :
    {Z | (relativisticCollapseSystem α hα).cost Z < 1} = {Z | Z < heaviestBoundZ α} := by
  ext Z
  show α * Z < 1 ↔ Z < heaviestBoundZ α
  rw [heaviestBoundZ, lt_div_iff₀ hα, mul_comm α Z]

end Physlib.QuantumMechanics.ComplexAction.Particles.AtomicRelativisticStabilityBound

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.AtomicShellInformationCapacityOctet.subshellStorageCount where
  formalizes @ "claim:a-subshell-is-a-finite-information-register-with-two-to-the-capacity-configurations",
  caveat @ "claim:the-holographic-information-capacity-analogy-is-the-physical-reading"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.AtomicShellInformationCapacityOctet.dShell_unique_pairs_eq_capacity where
  formalizes @ "claim:the-d-shell-is-the-unique-subshell-whose-antisymmetric-pair-count-equals-its-capacity-ten",
  requires @ "claim:a-subshell-is-a-finite-information-register-with-two-to-the-capacity-configurations"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.AtomicHundMagnetism.hund_max_at_halffill where
  formalizes @ "claim:hunds-rule-the-half-filled-subshell-attains-the-maximal-unpaired-spin",
  requires @ "claim:a-subshell-is-a-finite-information-register-with-two-to-the-capacity-configurations"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.AtomicRelativisticStabilityBound.bound_state_iff_Z where
  formalizes @ "claim:the-relativistic-collapse-bounds-the-periodic-table-at-Z-equals-one-over-alpha",
  supported_by @ "paper:sommerfeld-dirac-coulomb-fine-structure",
  caveat @ "claim:the-dirac-coulomb-one-s-energy-formula-is-taken-as-the-exact-spectral-input"

zil_file_contract physlib.atomicShellInformationCapacityOctet where
  promises "Atomic shells as information registers: a subshell has two-to-the-capacity configurations, the d-shell is the unique subshell whose antisymmetric pair count equals its capacity ten, Hund's rule gives the half-filled subshell maximal spin, and the relativistic collapse bounds the periodic table at Z equals one over alpha."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.AtomicShellInformationCapacityOctet.subshellBitCapacity",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.AtomicRelativisticStabilityBound.sommerfeldRadicand"]
  forbids_substitutes ["the Dirac-Coulomb one-s energy formula, taken as exact spectral input",
    "the holographic information-capacity analogy, the physical reading"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.AtomicShellInformationCapacityOctet.subshellStorageCount,
    Physlib.QuantumMechanics.ComplexAction.Particles.AtomicShellInformationCapacityOctet.dShell_unique_pairs_eq_capacity,
    Physlib.QuantumMechanics.ComplexAction.Particles.AtomicHundMagnetism.hund_max_at_halffill,
    Physlib.QuantumMechanics.ComplexAction.Particles.AtomicRelativisticStabilityBound.bound_state_iff_Z]

/- ZIL-END -/
