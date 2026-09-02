/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NewtonOstrovskyiIcosahedralVortexStability
public import Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit
public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
public import Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.FromArchive
public import Physlib.QuantumMechanics.ComplexAction.Fermion.SecondQuantizationFunctor
public import Physlib.QuantumMechanics.Liouville.SecondQuantization

/-!
# Atomic subshell quantum numbers and the Ostrovskyi boundary carrier

This file adds the standard finite quantum-number layer needed before any periodic-table data can be
used in the icosahedral boundary formalization.

The formal content is intentionally conservative:

* a bound subshell carries the usual principal and angular quantum numbers `(n,l)` with `l < n`;
* a one-electron mode in that subshell is a magnetic index and a spin index, hence has capacity
  `2 * (2*l + 1)`;
* the Feynman/Tasaki occupation-number representation is exposed as a finite fermion basis:
  creation/annihilation edit finite Pauli-valid occupation vectors, the number operator is
  `Σ nα`, the diagonal noninteracting Hamiltonian is `Σ εα nα`, and an occupied higher mode
  can be moved to an empty lower-energy mode without increasing `H₀`;
* the aufbau subshell list through `7p` has total capacity `118`;
* filling that finite list with any atomic number `1 <= Z <= 118` gives exactly `Z` electrons and
  never violates the Pauli capacity bound;
* an atom-to-icosahedral-coefficient map lands in the already-proved Newton--Ostrovskyi grouped
  relative-equilibrium family.

This does not assert that the Ostrovskyi vortex Hamiltonian derives the chemical periodic table.  It
provides a checked interface: standard fermionic shell data can be carried into the existing
icosahedral boundary/stress-channel layer once a physical coefficient map is supplied.

The finite occupation-number layer follows Hal Tasaki's Feynman-inspired account of creation and
annihilation operators for nonrelativistic many-body quantum mechanics (`arXiv:1812.10732v5`):
Slater/occupation states, `N = Σ nα`, and diagonal `H₀ = Σ εα nα`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers

open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NewtonOstrovskyiIcosahedralVortexStability
open Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit
open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
open Physlib.QuantumMechanics.ComplexAction.QuantumChemistry.FromArchive
open Physlib.QuantumMechanics.ComplexAction.Fermion.SecondQuantizationFunctor
open Physlib.QuantumMechanics.Liouville.SecondQuantization

/-! ## Subshell quantum numbers and Pauli capacity -/

/-- A bound atomic subshell, with principal quantum number `n` and angular quantum number `l`. -/
structure BoundSubshell where
  n : Nat
  l : Nat
  l_lt_n : l < n
deriving Repr

/-- The standard magnetic/spin carrier of a subshell.  The `Fin (2*l+1)` component indexes
`m_l = -l, ..., l`; the `Fin 2` component indexes the two spin states. -/
abbrev SubshellMode (q : BoundSubshell) : Type := Fin (2 * q.l + 1) × Fin 2

/-- The signed magnetic quantum number represented by a magnetic index. -/
def magneticQuantumNumber (q : BoundSubshell) (m : Fin (2 * q.l + 1)) : Int :=
  (m.val : Int) - (q.l : Int)

/-- Twice the spin quantum number, avoiding rational bookkeeping: `-1` means `-1/2`, `1` means `1/2`. -/
def twiceSpinQuantumNumber (s : Fin 2) : Int :=
  if s = 0 then -1 else 1

@[simp] lemma twiceSpinQuantumNumber_zero : twiceSpinQuantumNumber 0 = -1 := by
  simp [twiceSpinQuantumNumber]

@[simp] lemma twiceSpinQuantumNumber_one : twiceSpinQuantumNumber 1 = 1 := by
  simp [twiceSpinQuantumNumber]

/-- The `Fin 2` spin index carries exactly the two spin-`1/2` projections, encoded as twice-spin. -/
lemma twiceSpinQuantumNumber_spectrum (s : Fin 2) :
    twiceSpinQuantumNumber s = -1 ∨ twiceSpinQuantumNumber s = 1 := by
  fin_cases s <;> simp

/-- The Pauli capacity of angular-momentum shell `l`: two spin states for each of `2*l+1`
magnetic states. -/
def capacityOfAngularMomentum (l : Nat) : Nat := 2 * (2 * l + 1)

/-- The Pauli capacity of a bound subshell. -/
def BoundSubshell.capacity (q : BoundSubshell) : Nat := capacityOfAngularMomentum q.l

/-- The finite mode carrier has exactly the standard Pauli capacity. -/
lemma card_subshellMode (q : BoundSubshell) :
    Fintype.card (SubshellMode q) = q.capacity := by
  simp [SubshellMode, BoundSubshell.capacity, capacityOfAngularMomentum, Nat.mul_comm]

lemma s_capacity : capacityOfAngularMomentum 0 = 2 := by
  norm_num [capacityOfAngularMomentum]

lemma p_capacity : capacityOfAngularMomentum 1 = 6 := by
  norm_num [capacityOfAngularMomentum]

lemma d_capacity : capacityOfAngularMomentum 2 = 10 := by
  norm_num [capacityOfAngularMomentum]

lemma f_capacity : capacityOfAngularMomentum 3 = 14 := by
  norm_num [capacityOfAngularMomentum]

/-! ## Spin and Kálnay-CAR carriers for a subshell mode -/

/-- The Pauli `z` axis used to read the two spin projections in a subshell mode. -/
def spinZAxis (i : Fin 3) : ℝ := if i = 2 then 1 else 0

lemma spinZAxis_dot_self : dotR spinZAxis spinZAxis = 1 := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  simp [spinZAxis, dotR, h02, h12]

/-- The subshell spin carrier is the usual Pauli spin-`1/2` carrier along `z`: `(σ_z)^2 = 1`. -/
lemma sigmaDot_spinZAxis_sq :
    sigmaDot spinZAxis * sigmaDot spinZAxis = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simpa [spinZAxis_dot_self] using sigmaDot_sq spinZAxis

/-- A spin already aligned with the chosen quantization axis has zero self-precession. -/
lemma spinZAxis_self_precession_zero (ℏ : ℂ) :
    heisenbergGen ℏ (sigmaDot spinZAxis) (sigmaDot spinZAxis) = 0 := by
  rw [heisenberg_spin_precession, crossR_self]
  simp [sigmaDot]

/-- A Kálnay/CAR realization of all one-electron modes in a fixed subshell.  Each finite
magnetic/spin mode is represented by a composite fermion operator satisfying the CAR. -/
structure SubshellKalnayRealization (A : Type*) [Ring A] [StarRing A] (q : BoundSubshell) where
  modeOp : SubshellMode q → A
  isFermion : ∀ mode, IsFermionMode (modeOp mode)

/-- The number projection associated to one realized subshell mode. -/
def modeNumber {A : Type*} [Ring A] [StarRing A] {q : BoundSubshell}
    (R : SubshellKalnayRealization A q) (mode : SubshellMode q) : A :=
  fermionNumber (R.modeOp mode)

lemma modeNumber_selfAdjoint {A : Type*} [Ring A] [StarRing A] {q : BoundSubshell}
    (R : SubshellKalnayRealization A q) (mode : SubshellMode q) :
    star (modeNumber R mode) = modeNumber R mode := by
  exact fermionNumber_selfAdjoint (R.modeOp mode)

/-- Pauli exclusion at one subshell mode: the Kálnay/CAR number operator is a projection. -/
lemma modeNumber_idempotent {A : Type*} [Ring A] [StarRing A] {q : BoundSubshell}
    (R : SubshellKalnayRealization A q) (mode : SubshellMode q) :
    modeNumber R mode * modeNumber R mode = modeNumber R mode := by
  exact fermionNumber_idempotent (R.modeOp mode) (R.isFermion mode)

/-- A realized subshell mode combines the Pauli spin carrier with Kálnay's CAR Pauli-exclusion
projection. -/
lemma subshellMode_pauli_spin_and_kalnay_projection {A : Type*} [Ring A] [StarRing A]
    {q : BoundSubshell} (R : SubshellKalnayRealization A q) (mode : SubshellMode q) :
    sigmaDot spinZAxis * sigmaDot spinZAxis = (1 : Matrix (Fin 2) (Fin 2) ℂ)
      ∧ star (modeNumber R mode) = modeNumber R mode
      ∧ modeNumber R mode * modeNumber R mode = modeNumber R mode := by
  exact ⟨sigmaDot_spinZAxis_sq, modeNumber_selfAdjoint R mode, modeNumber_idempotent R mode⟩

/-! ## Second-quantized Fock and Liouville carriers for subshell modes -/

/-- The finite one-particle space spanned by the magnetic/spin modes of a subshell. -/
abbrev SubshellOneParticleSpace (q : BoundSubshell) : Type := SubshellMode q → ℂ

/-- The fermionic Fock space over the finite subshell one-particle space, supplied by the repository's
exterior-algebra second-quantization functor. -/
abbrev SubshellFock (q : BoundSubshell) : Type :=
  FermionFock (SubshellOneParticleSpace q)

/-- The basis vector of the one-particle subshell space corresponding to one magnetic/spin mode. -/
def subshellModeKet (q : BoundSubshell) (mode : SubshellMode q) :
    SubshellOneParticleSpace q :=
  fun mode' => if mode' = mode then 1 else 0

/-- The Fock creation generator for one atomic subshell mode. -/
noncomputable def subshellFockCreation (q : BoundSubshell) (mode : SubshellMode q) :
    SubshellFock q :=
  creation (subshellModeKet q mode)

/-- The exterior-algebra Fock functor gives Pauli exclusion for each subshell creation generator:
`a†_mode a†_mode = 0`. -/
lemma subshellFockCreation_sq (q : BoundSubshell) (mode : SubshellMode q) :
    subshellFockCreation q mode * subshellFockCreation q mode = 0 :=
  creation_sq (subshellModeKet q mode)

/-- Creation generators for any two finite subshell modes anticommute in the exterior-algebra Fock
space. -/
lemma subshellFockCreation_anticomm
    (q : BoundSubshell) (mode mode' : SubshellMode q) :
    subshellFockCreation q mode * subshellFockCreation q mode'
      + subshellFockCreation q mode' * subshellFockCreation q mode = 0 :=
  creation_anticomm (subshellModeKet q mode) (subshellModeKet q mode')

/-- The Liouville occupation register over the finite subshell mode carrier.  For a subshell with
`M = capacity` one-electron modes, Liouville modes are matrix-unit labels `(i,j)` over that carrier. -/
abbrev SubshellLiouvilleOccupation (q : BoundSubshell) : Type :=
  LiouvilleOccupation q.capacity

/-- Fixed-electron-count Liouville occupation register over a finite subshell carrier. -/
abbrev FixedSubshellLiouvilleOccupation (q : BoundSubshell) (e : ℕ) : Type :=
  FixedParticleLiouvilleOccupation q.capacity e

/-- The Liouville number operator on a fixed subshell register has eigenvalue equal to the chosen
electron count. -/
lemma fixedSubshellLiouville_numberOperator
    (q : BoundSubshell) (e : ℕ) (n : FixedSubshellLiouvilleOccupation q e) :
    liouvilleNumberOperatorPairSum n.1 = e :=
  fixedParticle_numberOperator_pair_sum n

/-- A Liouville bilinear transfer `b†_creator b_annihilator` preserves the fixed electron count on
the finite subshell density-register carrier whenever the annihilated mode is occupied. -/
lemma subshellLiouville_transfer_preserves_total
    (q : BoundSubshell) (e : ℕ)
    (creator annihilator : LiouvilleMode q.capacity)
    (n : FixedSubshellLiouvilleOccupation q e) (hpos : 0 < n.1 annihilator) :
    totalOccupation (transferOccupation creator annihilator n.1) = e := by
  rw [totalOccupation_transfer creator annihilator n.1 hpos]
  exact n.2

/-- The assembled single-mode bridge: the same finite subshell mode has an exterior-algebra Fock
creation operator satisfying Pauli, and any Kálnay/CAR realization gives a self-adjoint idempotent
number projection for that mode. -/
lemma subshellMode_secondQuantized_and_kalnay_projection
    {A : Type*} [Ring A] [StarRing A] {q : BoundSubshell}
    (R : SubshellKalnayRealization A q) (mode : SubshellMode q) :
    subshellFockCreation q mode * subshellFockCreation q mode = 0
      ∧ star (modeNumber R mode) = modeNumber R mode
      ∧ modeNumber R mode * modeNumber R mode = modeNumber R mode :=
  ⟨subshellFockCreation_sq q mode, modeNumber_selfAdjoint R mode, modeNumber_idempotent R mode⟩

/-! ## Aufbau filling through the known periodic table -/

/-- The aufbau subshell order through `7p`, enough capacity for neutral atoms `Z = 1,...,118`. -/
def aufbauSubshells : List BoundSubshell :=
  [ ⟨1, 0, by decide⟩,
    ⟨2, 0, by decide⟩,
    ⟨2, 1, by decide⟩,
    ⟨3, 0, by decide⟩,
    ⟨3, 1, by decide⟩,
    ⟨4, 0, by decide⟩,
    ⟨3, 2, by decide⟩,
    ⟨4, 1, by decide⟩,
    ⟨5, 0, by decide⟩,
    ⟨4, 2, by decide⟩,
    ⟨5, 1, by decide⟩,
    ⟨6, 0, by decide⟩,
    ⟨4, 3, by decide⟩,
    ⟨5, 2, by decide⟩,
    ⟨6, 1, by decide⟩,
    ⟨7, 0, by decide⟩,
    ⟨5, 3, by decide⟩,
    ⟨6, 2, by decide⟩,
    ⟨7, 1, by decide⟩ ]

/-- The Pauli capacities of the aufbau subshell order. -/
def aufbauCapacities : List Nat := aufbauSubshells.map BoundSubshell.capacity

lemma aufbauCapacities_sum : aufbauCapacities.sum = 118 := by
  native_decide

/-- Fill a finite capacity list with `Z` fermions, saturating each slot before moving to the next. -/
def fillCounts : Nat -> List Nat -> List Nat
  | _, [] => []
  | Z, c :: cs =>
      let e := min Z c
      e :: fillCounts (Z - e) cs

/-- Slotwise Pauli validity for occupation counts against capacities. -/
def PauliValidCounts (counts capacities : List Nat) : Prop :=
  List.Forall₂ (fun e c => e <= c) counts capacities

lemma fillCounts_pauli (Z : Nat) (capacities : List Nat) :
    PauliValidCounts (fillCounts Z capacities) capacities := by
  induction capacities generalizing Z with
  | nil =>
      simp [PauliValidCounts, fillCounts]
  | cons c cs ih =>
      unfold PauliValidCounts at ih ⊢
      change List.Forall₂ (fun e c => e <= c)
        (min Z c :: fillCounts (Z - min Z c) cs) (c :: cs)
      exact List.Forall₂.cons (Nat.min_le_right Z c) (ih (Z - min Z c))

lemma sum_fillCounts_eq_min (Z : Nat) (capacities : List Nat) :
    (fillCounts Z capacities).sum = min Z capacities.sum := by
  induction capacities generalizing Z with
  | nil =>
      simp [fillCounts]
  | cons c cs ih =>
      by_cases hZc : Z <= c
      · have hmin : min Z c = Z := Nat.min_eq_left hZc
        have htotal : min Z (c + cs.sum) = Z := Nat.min_eq_left (by omega)
        simp [fillCounts, hmin, ih, htotal]
      · have hcZ : c <= Z := Nat.le_of_lt (Nat.lt_of_not_ge hZc)
        have hmin : min Z c = c := Nat.min_eq_right hcZ
        by_cases hrem : Z - c <= cs.sum
        · have hleft : min (Z - c) cs.sum = Z - c := Nat.min_eq_left hrem
          have hright : min Z (c + cs.sum) = Z := Nat.min_eq_left (by omega)
          simp [fillCounts, hmin, ih, hleft, hright]
          omega
        · have hsrem : cs.sum <= Z - c := Nat.le_of_lt (Nat.lt_of_not_ge hrem)
          have hleft : min (Z - c) cs.sum = cs.sum := Nat.min_eq_right hsrem
          have hright : min Z (c + cs.sum) = c + cs.sum := Nat.min_eq_right (by omega)
          simp [fillCounts, hmin, ih, hleft, hright]

/-- Atomic numbers of the currently known neutral chemical elements, `1 <= Z <= 118`. -/
abbrev KnownElement := { Z : Nat // 1 <= Z ∧ Z <= 118 }

/-- A verified finite subshell occupation model for a neutral atom. -/
structure AtomicConfiguration where
  atomicNumber : Nat
  subshells : List BoundSubshell
  occupations : List Nat
  pauli : PauliValidCounts occupations (subshells.map BoundSubshell.capacity)
  electron_count : occupations.sum = atomicNumber

/-- The canonical aufbau configuration for a known atomic number.  This is the standard shell-filling
carrier; empirical exception data can refine the order later without changing the interface. -/
def knownElementConfiguration (E : KnownElement) : AtomicConfiguration where
  atomicNumber := E.val
  subshells := aufbauSubshells
  occupations := fillCounts E.val aufbauCapacities
  pauli := fillCounts_pauli E.val aufbauCapacities
  electron_count := by
    rw [sum_fillCounts_eq_min, aufbauCapacities_sum]
    exact Nat.min_eq_left E.property.2

lemma knownElementConfiguration_count (E : KnownElement) :
    (knownElementConfiguration E).occupations.sum = E.val :=
  (knownElementConfiguration E).electron_count

lemma knownElementConfiguration_pauli (E : KnownElement) :
    PauliValidCounts (knownElementConfiguration E).occupations aufbauCapacities :=
  (knownElementConfiguration E).pauli

/-! ## The first four elements: explicit atomic quantum numbers -/

/-- A concrete one-electron atomic quantum-number tuple `(n,l,m_l,2s)`.  The spin is stored as
twice the usual spin projection, so the allowed values are `-1` and `1`. -/
structure ElectronQuantumNumbers where
  n : Nat
  l : Nat
  m : Int
  twiceSpin : Int
deriving Repr, DecidableEq

/-- Validity of the standard bound-state atomic quantum numbers:
`1 <= n`, `0 <= l < n`, `-l <= m_l <= l`, and `2s = ±1`. -/
def IsValidElectronQuantumNumbers (q : ElectronQuantumNumbers) : Prop :=
  1 <= q.n ∧ q.l < q.n ∧ -(q.l : Int) <= q.m ∧ q.m <= (q.l : Int)
    ∧ (q.twiceSpin = -1 ∨ q.twiceSpin = 1)

/-- A Boolean subshell test used to count explicit quantum-number lists. -/
def inSubshell (n l : Nat) (q : ElectronQuantumNumbers) : Bool :=
  q.n == n && q.l == l

/-- Count how many explicit electron quantum-number tuples occupy a given `(n,l)` subshell. -/
def countInSubshell (n l : Nat) (qs : List ElectronQuantumNumbers) : Nat :=
  (qs.filter (inSubshell n l)).length

/-- A deterministic ordering of the one-electron quantum-number tuples inside one subshell.
The magnetic index runs from `m_l = -l` to `m_l = l`; for each magnetic state the two spin projections
are listed as `2s = -1, 1`. -/
def subshellQuantumNumbersInOrder (q : BoundSubshell) : List ElectronQuantumNumbers :=
  List.flatMap (fun magIndex =>
    [ { n := q.n, l := q.l, m := (magIndex : Int) - (q.l : Int), twiceSpin := -1 },
      { n := q.n, l := q.l, m := (magIndex : Int) - (q.l : Int), twiceSpin := 1 } ])
    (List.range (2 * q.l + 1))

/-- Fill the first `e` ordered one-electron states of a subshell.  The caller supplies `e` from
`fillCounts`, so the Pauli bound is inherited from `fillCounts_pauli`. -/
def filledSubshellQuantumNumbers (q : BoundSubshell) (e : Nat) : List ElectronQuantumNumbers :=
  (subshellQuantumNumbersInOrder q).take e

/-- Compute electron quantum-number tuples from an Aufbau subshell list and its computed occupation
counts. -/
def quantumNumbersFromFilling : List BoundSubshell → List Nat → List ElectronQuantumNumbers
  | [], _ => []
  | _, [] => []
  | q :: qs, e :: es => filledSubshellQuantumNumbers q e ++ quantumNumbersFromFilling qs es

/-- The computed electron quantum-number tuples of a known neutral element, obtained from
`knownElementConfiguration` rather than from an external table. -/
def computedKnownElementQuantumNumbers (E : KnownElement) : List ElectronQuantumNumbers :=
  quantumNumbersFromFilling aufbauSubshells (knownElementConfiguration E).occupations

/-- Count the occupied quantum-number tuples in every subshell of the repository's Aufbau list. -/
def aufbauSubshellCounts (qs : List ElectronQuantumNumbers) : List Nat :=
  aufbauSubshells.map fun q => countInSubshell q.n q.l qs

/-- The deterministic mode listing has exactly the Pauli capacity of the subshell. -/
lemma subshellQuantumNumbersInOrder_length (q : BoundSubshell) :
    (subshellQuantumNumbersInOrder q).length = q.capacity := by
  simp [subshellQuantumNumbersInOrder, BoundSubshell.capacity, capacityOfAngularMomentum]
  ring

/-- Taking a Pauli-allowed number of occupied modes from a subshell produces exactly that many
one-electron quantum-number tuples. -/
lemma filledSubshellQuantumNumbers_length_of_le (q : BoundSubshell) (e : Nat)
    (he : e <= q.capacity) :
    (filledSubshellQuantumNumbers q e).length = e := by
  simp [filledSubshellQuantumNumbers, List.length_take, subshellQuantumNumbersInOrder_length,
    Nat.min_eq_left he]

/-- If the occupation counts are Pauli-valid, the generated explicit quantum-number list has length
equal to the total occupation count. -/
lemma quantumNumbersFromFilling_length_eq_sum :
    ∀ (subshells : List BoundSubshell) (occupations : List Nat),
      PauliValidCounts occupations (subshells.map BoundSubshell.capacity) →
        (quantumNumbersFromFilling subshells occupations).length = occupations.sum
  | [], [], _ => by simp [quantumNumbersFromFilling]
  | [], _ :: _, h => by cases h
  | _ :: _, [], _ => by simp [quantumNumbersFromFilling]
  | q :: qs, e :: es, h => by
      cases h with
      | cons he htail =>
          simp [quantumNumbersFromFilling, filledSubshellQuantumNumbers_length_of_le q e he,
            quantumNumbersFromFilling_length_eq_sum qs es htail]

/-- The first three aufbau subshell counts, in the order `[1s, 2s, 2p]`. -/
def firstThreeSubshellCounts (qs : List ElectronQuantumNumbers) : List Nat :=
  [countInSubshell 1 0 qs, countInSubshell 2 0 qs, countInSubshell 2 1 qs]

/-- The first three computed aufbau occupation counts, in the order `[1s, 2s, 2p]`. -/
def firstThreeOccupationPrefix (E : KnownElement) : List Nat :=
  (knownElementConfiguration E).occupations.take 3

/-- Hydrogen, `Z = 1`. -/
def hydrogen : KnownElement := ⟨1, by decide⟩

/-- Helium, `Z = 2`. -/
def helium : KnownElement := ⟨2, by decide⟩

/-- Lithium, `Z = 3`. -/
def lithium : KnownElement := ⟨3, by decide⟩

/-- Beryllium, `Z = 4`. -/
def beryllium : KnownElement := ⟨4, by decide⟩

/-- The `1s` spin-down one-electron state: `(n,l,m_l,2s) = (1,0,0,-1)`. -/
def oneSDown : ElectronQuantumNumbers where
  n := 1
  l := 0
  m := 0
  twiceSpin := -1

/-- The `1s` spin-up one-electron state: `(n,l,m_l,2s) = (1,0,0,1)`. -/
def oneSUp : ElectronQuantumNumbers where
  n := 1
  l := 0
  m := 0
  twiceSpin := 1

/-- The `2s` spin-up one-electron state: `(n,l,m_l,2s) = (2,0,0,1)`. -/
def twoSUp : ElectronQuantumNumbers where
  n := 2
  l := 0
  m := 0
  twiceSpin := 1

/-- The `2s` spin-down one-electron state: `(n,l,m_l,2s) = (2,0,0,-1)`. -/
def twoSDown : ElectronQuantumNumbers where
  n := 2
  l := 0
  m := 0
  twiceSpin := -1

lemma oneSDown_valid : IsValidElectronQuantumNumbers oneSDown := by
  norm_num [IsValidElectronQuantumNumbers, oneSDown]

lemma oneSUp_valid : IsValidElectronQuantumNumbers oneSUp := by
  norm_num [IsValidElectronQuantumNumbers, oneSUp]

lemma twoSUp_valid : IsValidElectronQuantumNumbers twoSUp := by
  norm_num [IsValidElectronQuantumNumbers, twoSUp]

lemma twoSDown_valid : IsValidElectronQuantumNumbers twoSDown := by
  norm_num [IsValidElectronQuantumNumbers, twoSDown]

/-- A spin-up representative of neutral hydrogen: `1s¹`. -/
def hydrogenQuantumNumbers : List ElectronQuantumNumbers := [oneSUp]

/-- Neutral helium: `1s²`, with the two allowed spin states. -/
def heliumQuantumNumbers : List ElectronQuantumNumbers := [oneSDown, oneSUp]

/-- Neutral lithium: `1s² 2s¹`, with a spin-up representative for the outer `2s` electron. -/
def lithiumQuantumNumbers : List ElectronQuantumNumbers := [oneSDown, oneSUp, twoSUp]

/-- Neutral beryllium: `1s² 2s²`, filling both `2s` spin states. -/
def berylliumQuantumNumbers : List ElectronQuantumNumbers :=
  [oneSDown, oneSUp, twoSDown, twoSUp]

lemma hydrogenQuantumNumbers_valid :
    hydrogenQuantumNumbers.Forall IsValidElectronQuantumNumbers := by
  simp [hydrogenQuantumNumbers, oneSUp_valid]

lemma heliumQuantumNumbers_valid :
    heliumQuantumNumbers.Forall IsValidElectronQuantumNumbers := by
  simp [heliumQuantumNumbers, oneSDown_valid, oneSUp_valid]

lemma lithiumQuantumNumbers_valid :
    lithiumQuantumNumbers.Forall IsValidElectronQuantumNumbers := by
  simp [lithiumQuantumNumbers, oneSDown_valid, oneSUp_valid, twoSUp_valid]

lemma berylliumQuantumNumbers_valid :
    berylliumQuantumNumbers.Forall IsValidElectronQuantumNumbers := by
  simp [berylliumQuantumNumbers, oneSDown_valid, oneSUp_valid, twoSDown_valid, twoSUp_valid]

lemma hydrogenQuantumNumbers_pauliDistinct : hydrogenQuantumNumbers.Nodup := by
  native_decide

lemma heliumQuantumNumbers_pauliDistinct : heliumQuantumNumbers.Nodup := by
  native_decide

lemma lithiumQuantumNumbers_pauliDistinct : lithiumQuantumNumbers.Nodup := by
  native_decide

lemma berylliumQuantumNumbers_pauliDistinct : berylliumQuantumNumbers.Nodup := by
  native_decide

lemma hydrogenQuantumNumbers_count : hydrogenQuantumNumbers.length = hydrogen.val := by
  native_decide

lemma heliumQuantumNumbers_count : heliumQuantumNumbers.length = helium.val := by
  native_decide

lemma lithiumQuantumNumbers_count : lithiumQuantumNumbers.length = lithium.val := by
  native_decide

lemma berylliumQuantumNumbers_count : berylliumQuantumNumbers.length = beryllium.val := by
  native_decide

lemma hydrogenOccupationPrefix : firstThreeOccupationPrefix hydrogen = [1, 0, 0] := by
  native_decide

lemma heliumOccupationPrefix : firstThreeOccupationPrefix helium = [2, 0, 0] := by
  native_decide

lemma lithiumOccupationPrefix : firstThreeOccupationPrefix lithium = [2, 1, 0] := by
  native_decide

lemma berylliumOccupationPrefix : firstThreeOccupationPrefix beryllium = [2, 2, 0] := by
  native_decide

lemma hydrogenQuantumNumbers_match_aufbauPrefix :
    firstThreeSubshellCounts hydrogenQuantumNumbers = firstThreeOccupationPrefix hydrogen := by
  native_decide

lemma heliumQuantumNumbers_match_aufbauPrefix :
    firstThreeSubshellCounts heliumQuantumNumbers = firstThreeOccupationPrefix helium := by
  native_decide

lemma lithiumQuantumNumbers_match_aufbauPrefix :
    firstThreeSubshellCounts lithiumQuantumNumbers = firstThreeOccupationPrefix lithium := by
  native_decide

lemma berylliumQuantumNumbers_match_aufbauPrefix :
    firstThreeSubshellCounts berylliumQuantumNumbers = firstThreeOccupationPrefix beryllium := by
  native_decide

/-- The first-three-elements summary: the explicit quantum-number lists for H, He, and Li are valid,
Pauli-distinct, have electron count `Z`, and match the computed aufbau occupation prefix `[1s,2s,2p]`. -/
lemma first_three_elements_atomic_quantum_numbers_checked :
    hydrogenQuantumNumbers.Forall IsValidElectronQuantumNumbers
      ∧ heliumQuantumNumbers.Forall IsValidElectronQuantumNumbers
      ∧ lithiumQuantumNumbers.Forall IsValidElectronQuantumNumbers
      ∧ hydrogenQuantumNumbers.Nodup
      ∧ heliumQuantumNumbers.Nodup
      ∧ lithiumQuantumNumbers.Nodup
      ∧ hydrogenQuantumNumbers.length = hydrogen.val
      ∧ heliumQuantumNumbers.length = helium.val
      ∧ lithiumQuantumNumbers.length = lithium.val
      ∧ firstThreeSubshellCounts hydrogenQuantumNumbers = firstThreeOccupationPrefix hydrogen
      ∧ firstThreeSubshellCounts heliumQuantumNumbers = firstThreeOccupationPrefix helium
      ∧ firstThreeSubshellCounts lithiumQuantumNumbers = firstThreeOccupationPrefix lithium := by
  exact ⟨hydrogenQuantumNumbers_valid, heliumQuantumNumbers_valid, lithiumQuantumNumbers_valid,
    hydrogenQuantumNumbers_pauliDistinct, heliumQuantumNumbers_pauliDistinct,
    lithiumQuantumNumbers_pauliDistinct, hydrogenQuantumNumbers_count, heliumQuantumNumbers_count,
    lithiumQuantumNumbers_count, hydrogenQuantumNumbers_match_aufbauPrefix,
    heliumQuantumNumbers_match_aufbauPrefix, lithiumQuantumNumbers_match_aufbauPrefix⟩

/-- The first-four-elements summary: the explicit quantum-number lists for H, He, Li, and Be are valid,
Pauli-distinct, have electron count `Z`, and match the computed aufbau occupation prefix `[1s,2s,2p]`.
For Be the computed prefix is `[2,2,0]`, i.e. `1s² 2s²` with no `2p` occupation. -/
lemma first_four_elements_atomic_quantum_numbers_checked :
    hydrogenQuantumNumbers.Forall IsValidElectronQuantumNumbers
      ∧ heliumQuantumNumbers.Forall IsValidElectronQuantumNumbers
      ∧ lithiumQuantumNumbers.Forall IsValidElectronQuantumNumbers
      ∧ berylliumQuantumNumbers.Forall IsValidElectronQuantumNumbers
      ∧ hydrogenQuantumNumbers.Nodup
      ∧ heliumQuantumNumbers.Nodup
      ∧ lithiumQuantumNumbers.Nodup
      ∧ berylliumQuantumNumbers.Nodup
      ∧ hydrogenQuantumNumbers.length = hydrogen.val
      ∧ heliumQuantumNumbers.length = helium.val
      ∧ lithiumQuantumNumbers.length = lithium.val
      ∧ berylliumQuantumNumbers.length = beryllium.val
      ∧ firstThreeSubshellCounts hydrogenQuantumNumbers = firstThreeOccupationPrefix hydrogen
      ∧ firstThreeSubshellCounts heliumQuantumNumbers = firstThreeOccupationPrefix helium
      ∧ firstThreeSubshellCounts lithiumQuantumNumbers = firstThreeOccupationPrefix lithium
      ∧ firstThreeSubshellCounts berylliumQuantumNumbers = firstThreeOccupationPrefix beryllium := by
  exact ⟨hydrogenQuantumNumbers_valid, heliumQuantumNumbers_valid, lithiumQuantumNumbers_valid,
    berylliumQuantumNumbers_valid, hydrogenQuantumNumbers_pauliDistinct,
    heliumQuantumNumbers_pauliDistinct, lithiumQuantumNumbers_pauliDistinct,
    berylliumQuantumNumbers_pauliDistinct, hydrogenQuantumNumbers_count, heliumQuantumNumbers_count,
    lithiumQuantumNumbers_count, berylliumQuantumNumbers_count,
    hydrogenQuantumNumbers_match_aufbauPrefix, heliumQuantumNumbers_match_aufbauPrefix,
    lithiumQuantumNumbers_match_aufbauPrefix, berylliumQuantumNumbers_match_aufbauPrefix⟩

/-! ## Computed first-four-element quantum numbers from Aufbau filling -/

lemma computedHydrogenQuantumNumbers_eq :
    computedKnownElementQuantumNumbers hydrogen = [oneSDown] := by
  native_decide

lemma computedHeliumQuantumNumbers_eq :
    computedKnownElementQuantumNumbers helium = [oneSDown, oneSUp] := by
  native_decide

lemma computedLithiumQuantumNumbers_eq :
    computedKnownElementQuantumNumbers lithium = [oneSDown, oneSUp, twoSDown] := by
  native_decide

lemma computedBerylliumQuantumNumbers_eq :
    computedKnownElementQuantumNumbers beryllium = [oneSDown, oneSUp, twoSDown, twoSUp] := by
  native_decide

lemma computedHydrogenQuantumNumbers_valid :
    (computedKnownElementQuantumNumbers hydrogen).Forall IsValidElectronQuantumNumbers := by
  rw [computedHydrogenQuantumNumbers_eq]
  simp [oneSDown_valid]

lemma computedHeliumQuantumNumbers_valid :
    (computedKnownElementQuantumNumbers helium).Forall IsValidElectronQuantumNumbers := by
  rw [computedHeliumQuantumNumbers_eq]
  simp [oneSDown_valid, oneSUp_valid]

lemma computedLithiumQuantumNumbers_valid :
    (computedKnownElementQuantumNumbers lithium).Forall IsValidElectronQuantumNumbers := by
  rw [computedLithiumQuantumNumbers_eq]
  simp [oneSDown_valid, oneSUp_valid, twoSDown_valid]

lemma computedBerylliumQuantumNumbers_valid :
    (computedKnownElementQuantumNumbers beryllium).Forall IsValidElectronQuantumNumbers := by
  rw [computedBerylliumQuantumNumbers_eq]
  simp [oneSDown_valid, oneSUp_valid, twoSDown_valid, twoSUp_valid]

lemma computedHydrogenQuantumNumbers_pauliDistinct :
    (computedKnownElementQuantumNumbers hydrogen).Nodup := by
  rw [computedHydrogenQuantumNumbers_eq]
  native_decide

lemma computedHeliumQuantumNumbers_pauliDistinct :
    (computedKnownElementQuantumNumbers helium).Nodup := by
  rw [computedHeliumQuantumNumbers_eq]
  native_decide

lemma computedLithiumQuantumNumbers_pauliDistinct :
    (computedKnownElementQuantumNumbers lithium).Nodup := by
  rw [computedLithiumQuantumNumbers_eq]
  native_decide

lemma computedBerylliumQuantumNumbers_pauliDistinct :
    (computedKnownElementQuantumNumbers beryllium).Nodup := by
  rw [computedBerylliumQuantumNumbers_eq]
  native_decide

lemma computedHydrogenQuantumNumbers_count :
    (computedKnownElementQuantumNumbers hydrogen).length = hydrogen.val := by
  rw [computedHydrogenQuantumNumbers_eq]
  native_decide

lemma computedHeliumQuantumNumbers_count :
    (computedKnownElementQuantumNumbers helium).length = helium.val := by
  rw [computedHeliumQuantumNumbers_eq]
  native_decide

lemma computedLithiumQuantumNumbers_count :
    (computedKnownElementQuantumNumbers lithium).length = lithium.val := by
  rw [computedLithiumQuantumNumbers_eq]
  native_decide

lemma computedBerylliumQuantumNumbers_count :
    (computedKnownElementQuantumNumbers beryllium).length = beryllium.val := by
  rw [computedBerylliumQuantumNumbers_eq]
  native_decide

lemma computedHydrogenQuantumNumbers_match_aufbauPrefix :
    firstThreeSubshellCounts (computedKnownElementQuantumNumbers hydrogen)
      = firstThreeOccupationPrefix hydrogen := by
  native_decide

lemma computedHeliumQuantumNumbers_match_aufbauPrefix :
    firstThreeSubshellCounts (computedKnownElementQuantumNumbers helium)
      = firstThreeOccupationPrefix helium := by
  native_decide

lemma computedLithiumQuantumNumbers_match_aufbauPrefix :
    firstThreeSubshellCounts (computedKnownElementQuantumNumbers lithium)
      = firstThreeOccupationPrefix lithium := by
  native_decide

lemma computedBerylliumQuantumNumbers_match_aufbauPrefix :
    firstThreeSubshellCounts (computedKnownElementQuantumNumbers beryllium)
      = firstThreeOccupationPrefix beryllium := by
  native_decide

/-- The first four neutral atoms are computed from `fillCounts`/Aufbau capacities, not imported as
external data.  Lean checks that the computed occupied tuples are valid bound-state quantum numbers,
Pauli-distinct, have exactly `Z` electrons, and reproduce the computed subshell occupations:
`H = 1s¹`, `He = 1s²`, `Li = 1s²2s¹`, `Be = 1s²2s²`. -/
lemma computed_first_four_elements_atomic_quantum_numbers_checked :
    (computedKnownElementQuantumNumbers hydrogen).Forall IsValidElectronQuantumNumbers
      ∧ (computedKnownElementQuantumNumbers helium).Forall IsValidElectronQuantumNumbers
      ∧ (computedKnownElementQuantumNumbers lithium).Forall IsValidElectronQuantumNumbers
      ∧ (computedKnownElementQuantumNumbers beryllium).Forall IsValidElectronQuantumNumbers
      ∧ (computedKnownElementQuantumNumbers hydrogen).Nodup
      ∧ (computedKnownElementQuantumNumbers helium).Nodup
      ∧ (computedKnownElementQuantumNumbers lithium).Nodup
      ∧ (computedKnownElementQuantumNumbers beryllium).Nodup
      ∧ (computedKnownElementQuantumNumbers hydrogen).length = hydrogen.val
      ∧ (computedKnownElementQuantumNumbers helium).length = helium.val
      ∧ (computedKnownElementQuantumNumbers lithium).length = lithium.val
      ∧ (computedKnownElementQuantumNumbers beryllium).length = beryllium.val
      ∧ firstThreeSubshellCounts (computedKnownElementQuantumNumbers hydrogen)
          = firstThreeOccupationPrefix hydrogen
      ∧ firstThreeSubshellCounts (computedKnownElementQuantumNumbers helium)
          = firstThreeOccupationPrefix helium
      ∧ firstThreeSubshellCounts (computedKnownElementQuantumNumbers lithium)
          = firstThreeOccupationPrefix lithium
      ∧ firstThreeSubshellCounts (computedKnownElementQuantumNumbers beryllium)
          = firstThreeOccupationPrefix beryllium := by
  exact ⟨computedHydrogenQuantumNumbers_valid, computedHeliumQuantumNumbers_valid,
    computedLithiumQuantumNumbers_valid, computedBerylliumQuantumNumbers_valid,
    computedHydrogenQuantumNumbers_pauliDistinct, computedHeliumQuantumNumbers_pauliDistinct,
    computedLithiumQuantumNumbers_pauliDistinct, computedBerylliumQuantumNumbers_pauliDistinct,
    computedHydrogenQuantumNumbers_count, computedHeliumQuantumNumbers_count,
    computedLithiumQuantumNumbers_count, computedBerylliumQuantumNumbers_count,
    computedHydrogenQuantumNumbers_match_aufbauPrefix, computedHeliumQuantumNumbers_match_aufbauPrefix,
    computedLithiumQuantumNumbers_match_aufbauPrefix, computedBerylliumQuantumNumbers_match_aufbauPrefix⟩

/-! ## Computed quantum numbers for the first 77 neutral elements -/

/-- The first 77 neutral elements, indexed by `Fin 77`; index `0` is hydrogen (`Z = 1`) and
index `76` is iridium (`Z = 77`). -/
def first77KnownElement (i : Fin 77) : KnownElement :=
  ⟨i.val + 1, by omega⟩

/-- The computed occupied one-electron quantum-number tuples for one of the first 77 neutral elements. -/
def first77QuantumNumbers (i : Fin 77) : List ElectronQuantumNumbers :=
  computedKnownElementQuantumNumbers (first77KnownElement i)

/-- The computed first-77 quantum-number table.  It is a finite function rather than an imported table:
each row is generated from `fillCounts`, `aufbauSubshells`, and the deterministic subshell mode order. -/
def first77QuantumNumberTable : Fin 77 → List ElectronQuantumNumbers :=
  first77QuantumNumbers

lemma first77_atomicNumber (i : Fin 77) :
    (first77KnownElement i).val = i.val + 1 := rfl

/-- Lean checks the occupation source used to generate the first-77 quantum-number table.  For every
`Z = 1,...,77`, the computed Aufbau occupation list has exactly `Z` electrons and satisfies the Pauli
capacity bound in every subshell. -/
lemma first77ComputedOccupations_checked :
    ∀ i : Fin 77,
      (knownElementConfiguration (first77KnownElement i)).occupations.sum = i.val + 1
        ∧ PauliValidCounts
            (knownElementConfiguration (first77KnownElement i)).occupations aufbauCapacities := by
  intro i
  exact ⟨by simpa [first77KnownElement] using
      knownElementConfiguration_count (first77KnownElement i),
    knownElementConfiguration_pauli (first77KnownElement i)⟩

/-- The generated first-77 quantum-number table has exactly `Z` explicit occupied one-electron
states in row `Z`.  The rows are computed from the Aufbau capacity list and the deterministic
magnetic/spin ordering, not imported from an external table. -/
lemma first77QuantumNumberTable_length_checked (i : Fin 77) :
    (first77QuantumNumberTable i).length = i.val + 1 := by
  unfold first77QuantumNumberTable first77QuantumNumbers computedKnownElementQuantumNumbers
  rw [quantumNumbersFromFilling_length_eq_sum]
  · exact by
      simpa [first77KnownElement] using knownElementConfiguration_count (first77KnownElement i)
  · exact knownElementConfiguration_pauli (first77KnownElement i)

/-! ## Computed quantum numbers for the remaining known neutral elements -/

/-- The remaining known neutral elements after iridium, indexed by `Fin 41`; index `0` is platinum
(`Z = 78`) and index `40` is oganesson (`Z = 118`).  This is a range carrier, not an imported
configuration table. -/
def late41KnownElement (i : Fin 41) : KnownElement :=
  ⟨i.val + 78, by omega⟩

/-- The computed occupied one-electron quantum-number tuples for one of the remaining
`Z = 78,...,118` neutral elements. -/
def late41QuantumNumbers (i : Fin 41) : List ElectronQuantumNumbers :=
  computedKnownElementQuantumNumbers (late41KnownElement i)

/-- The computed `Z = 78,...,118` quantum-number table.  Rows are generated from the finite Pauli
carrier and Aufbau capacity list; no external configuration row is copied into Lean. -/
def late41QuantumNumberTable : Fin 41 → List ElectronQuantumNumbers :=
  late41QuantumNumbers

lemma late41_atomicNumber (i : Fin 41) :
    (late41KnownElement i).val = i.val + 78 := rfl

/-- Lean checks the occupation source used to generate the `Z = 78,...,118` quantum-number table. -/
lemma late41ComputedOccupations_checked :
    ∀ i : Fin 41,
      (knownElementConfiguration (late41KnownElement i)).occupations.sum = i.val + 78
        ∧ PauliValidCounts
            (knownElementConfiguration (late41KnownElement i)).occupations aufbauCapacities := by
  intro i
  exact ⟨by simpa [late41KnownElement] using
      knownElementConfiguration_count (late41KnownElement i),
    knownElementConfiguration_pauli (late41KnownElement i)⟩

/-- The generated `Z = 78,...,118` quantum-number table has exactly `Z` occupied one-electron states
in row `Z`. -/
lemma late41QuantumNumberTable_length_checked (i : Fin 41) :
    (late41QuantumNumberTable i).length = i.val + 78 := by
  unfold late41QuantumNumberTable late41QuantumNumbers computedKnownElementQuantumNumbers
  rw [quantumNumbersFromFilling_length_eq_sum]
  · exact by
      simpa [late41KnownElement] using knownElementConfiguration_count (late41KnownElement i)
  · exact knownElementConfiguration_pauli (late41KnownElement i)

/-! ## Computed quantum numbers for all 118 currently named elements -/

/-- All known neutral elements, indexed by atomic number minus one; index `0` is hydrogen and
index `117` is oganesson. -/
def all118KnownElement (i : Fin 118) : KnownElement :=
  ⟨i.val + 1, by omega⟩

/-- The computed occupied one-electron quantum-number tuples for any `Z = 1,...,118` neutral
element. -/
def all118QuantumNumbers (i : Fin 118) : List ElectronQuantumNumbers :=
  computedKnownElementQuantumNumbers (all118KnownElement i)

/-- The full generated neutral-element quantum-number table through oganesson. -/
def all118QuantumNumberTable : Fin 118 → List ElectronQuantumNumbers :=
  all118QuantumNumbers

lemma all118_atomicNumber (i : Fin 118) :
    (all118KnownElement i).val = i.val + 1 := rfl

/-- Lean checks the generated source for all neutral elements `Z = 1,...,118`: every row has exactly
`Z` electrons and satisfies all Pauli capacity bounds. -/
lemma all118ComputedOccupations_checked :
    ∀ i : Fin 118,
      (knownElementConfiguration (all118KnownElement i)).occupations.sum = i.val + 1
        ∧ PauliValidCounts
            (knownElementConfiguration (all118KnownElement i)).occupations aufbauCapacities := by
  intro i
  exact ⟨by simpa [all118KnownElement] using
      knownElementConfiguration_count (all118KnownElement i),
    knownElementConfiguration_pauli (all118KnownElement i)⟩

/-- The full generated quantum-number table has exactly `Z` occupied one-electron states in row `Z`. -/
lemma all118QuantumNumberTable_length_checked (i : Fin 118) :
    (all118QuantumNumberTable i).length = i.val + 1 := by
  unfold all118QuantumNumberTable all118QuantumNumbers computedKnownElementQuantumNumbers
  rw [quantumNumbersFromFilling_length_eq_sum]
  · exact by
      simpa [all118KnownElement] using knownElementConfiguration_count (all118KnownElement i)
  · exact knownElementConfiguration_pauli (all118KnownElement i)

/-! ## Feynman/Tasaki second-quantized occupation representation -/

/-- Finite diagonal form of Feynman's number operator:
`N = Σ_α n_α`, where a fermionic mode has occupation `n_α ∈ {0,1}`. -/
noncomputable def feynmanNumberEigenvalue {α : Type*} [Fintype α]
    (n : α → Bool) : ℕ :=
  ∑ a : α, if n a then 1 else 0

/-- Finite diagonal form of the noninteracting Hamiltonian in the occupation-number basis:
`H₀ = Σ_α ε_α n_α`. -/
noncomputable def feynmanDiagonalHamiltonianEigenvalue {α : Type*} [Fintype α]
    (ε : α → ℝ) (n : α → Bool) : ℝ :=
  ∑ a : α, ε a * if n a then 1 else 0

/-- If every one-particle energy is `1`, the diagonal Hamiltonian eigenvalue is the number-operator
eigenvalue.  This is the finite form of the relation between `H₀ = Σ ε_α n_α` and `N = Σ n_α`. -/
lemma feynmanDiagonalHamiltonian_one_eq_number {α : Type*} [Fintype α]
    (n : α → Bool) :
    feynmanDiagonalHamiltonianEigenvalue (fun _ : α => (1 : ℝ)) n =
      (feynmanNumberEigenvalue n : ℝ) := by
  unfold feynmanDiagonalHamiltonianEigenvalue feynmanNumberEigenvalue
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : n a <;> simp [h]

/-- The finite fermionic number eigenvalue is bounded by the number of one-particle modes. -/
lemma feynmanNumberEigenvalue_le_card {α : Type*} [Fintype α]
    (n : α → Bool) : feynmanNumberEigenvalue n ≤ Fintype.card α := by
  unfold feynmanNumberEigenvalue
  calc
    ∑ a : α, (if n a then 1 else 0 : ℕ) ≤ ∑ _a : α, 1 := by
      exact Finset.sum_le_sum fun a _ => by
        by_cases h : n a <;> simp [h]
    _ = Fintype.card α := by simp

/-- Move one fermionic occupation from `source` to `target`.  This is the finite occupation-basis
version of replacing an occupied one-particle eigenstate by another one-particle eigenstate. -/
def feynmanMoveOccupation {α : Type*} [DecidableEq α]
    (n : α → Bool) (source target : α) : α → Bool :=
  fun a => if a = target then true else if a = source then false else n a

/-- Two one-particle labels with different Boolean occupations are distinct. -/
private lemma fermionOccupation_false_true_ne {α : Type*} {n : α → Bool} {low high : α}
    (hlow : n low = false) (hhigh : n high = true) : low ≠ high := by
  intro h
  subst high
  simp [hlow] at hhigh

/-- A finite occupation move is unchanged away from its source and target labels. -/
private lemma feynmanMoveOccupation_eq_of_ne {α : Type*} [DecidableEq α]
    (n : α → Bool) {source target a : α} (htarget : a ≠ target) (hsource : a ≠ source) :
    feynmanMoveOccupation n source target a = n a := by
  simp [feynmanMoveOccupation, htarget, hsource]

/-- Decompose a finite sum into two selected entries and the remaining modes. -/
private lemma sum_eq_two_point_decomposition
    {α β : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid β]
    {low high : α} (hne : low ≠ high) (v : α → β) :
    (∑ a : α, v a) =
      v high + v low + ∑ a ∈ (Finset.univ.erase high).erase low, v a := by
  have hlow_mem : low ∈ (Finset.univ.erase high : Finset α) := by
    simp [hne]
  rw [← Finset.sum_erase_add (Finset.univ) v (by simp : high ∈ (Finset.univ : Finset α))]
  rw [← Finset.sum_erase_add (Finset.univ.erase high) v hlow_mem]
  abel

/-- Decompose a finite sum after an update that changes only two selected modes. -/
private lemma sum_eq_two_point_decomposition_of_eq_off
    {α β : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid β]
    {low high : α} (hne : low ≠ high) (old new : α → β)
    (hrest : ∀ a, a ≠ low → a ≠ high → new a = old a) :
    (∑ a : α, new a) =
      new high + new low + ∑ a ∈ (Finset.univ.erase high).erase low, old a := by
  rw [sum_eq_two_point_decomposition hne new]
  have hsum :
      ∑ a ∈ (Finset.univ.erase high).erase low, new a =
        ∑ a ∈ (Finset.univ.erase high).erase low, old a := by
    apply Finset.sum_congr rfl
    intro a ha
    have ahigh : a ≠ high := by
      simpa using (Finset.mem_erase.mp (Finset.mem_of_mem_erase ha)).1
    have alow : a ≠ low := by
      exact (Finset.mem_erase.mp ha).1
    exact hrest a alow ahigh
  rw [hsum]

/-- Moving an occupied fermion from a higher mode to an empty lower mode preserves particle number. -/
lemma feynmanMoveOccupation_number_preserved {α : Type*} [Fintype α] [DecidableEq α]
    (n : α → Bool) {low high : α}
    (hlow : n low = false) (hhigh : n high = true) :
    feynmanNumberEigenvalue (feynmanMoveOccupation n high low) = feynmanNumberEigenvalue n := by
  classical
  have hne : low ≠ high := fermionOccupation_false_true_ne hlow hhigh
  let old : α → ℕ := fun a => if n a then 1 else 0
  let new : α → ℕ := fun a => if feynmanMoveOccupation n high low a then 1 else 0
  have hrest : ∀ a, a ≠ low → a ≠ high → new a = old a := by
    intro a alow ahigh
    simp [new, old, feynmanMoveOccupation_eq_of_ne n alow ahigh]
  unfold feynmanNumberEigenvalue
  change (∑ a : α, new a) = (∑ a : α, old a)
  rw [sum_eq_two_point_decomposition_of_eq_off hne old new hrest]
  rw [sum_eq_two_point_decomposition hne old]
  simp [new, old, feynmanMoveOccupation, hlow, hhigh, hne, hne.symm]

/-- Exact two-mode exchange identity for the noninteracting Hamiltonian
`H₀ = Σ_α ε_α n_α`.  If `high` is occupied and `low` is empty, the finite occupation move changes
the diagonal energy by `ε_low - ε_high`. -/
lemma feynmanDiagonalHamiltonian_move_eq_add_sub {α : Type*} [Fintype α] [DecidableEq α]
    (ε : α → ℝ) (n : α → Bool) {low high : α}
    (hlow : n low = false) (hhigh : n high = true) :
    feynmanDiagonalHamiltonianEigenvalue ε (feynmanMoveOccupation n high low) =
      feynmanDiagonalHamiltonianEigenvalue ε n + ε low - ε high := by
  classical
  have hne : low ≠ high := fermionOccupation_false_true_ne hlow hhigh
  let old : α → ℝ := fun a => ε a * if n a then 1 else 0
  let new : α → ℝ := fun a => ε a * if feynmanMoveOccupation n high low a then 1 else 0
  have hrest : ∀ a, a ≠ low → a ≠ high → new a = old a := by
    intro a alow ahigh
    simp [new, old, feynmanMoveOccupation_eq_of_ne n alow ahigh]
  unfold feynmanDiagonalHamiltonianEigenvalue
  change (∑ a : α, new a) = (∑ a : α, old a) + ε low - ε high
  rw [sum_eq_two_point_decomposition_of_eq_off hne old new hrest]
  rw [sum_eq_two_point_decomposition hne old]
  simp [new, old, feynmanMoveOccupation, hlow, hhigh, hne, hne.symm]
  ring

/-- The finite exchange step behind Feynman's noninteracting fermion ground state: replacing an
occupied higher-energy mode by an empty lower-energy mode cannot increase the diagonal
Hamiltonian. -/
lemma feynmanDiagonalHamiltonian_exchange_nonincreasing
    {α : Type*} [Fintype α] [DecidableEq α]
    (ε : α → ℝ) (n : α → Bool) {low high : α}
    (hlow : n low = false) (hhigh : n high = true) (hle : ε low ≤ ε high) :
    feynmanDiagonalHamiltonianEigenvalue ε (feynmanMoveOccupation n high low) ≤
      feynmanDiagonalHamiltonianEigenvalue ε n := by
  rw [feynmanDiagonalHamiltonian_move_eq_add_sub ε n hlow hhigh]
  linarith

/-- A finite Feynman/Tasaki fermion occupation-basis vector: a Pauli-distinct list of occupied
one-particle labels.  For the atomic application, the labels are the computed
`(n,l,m_l,2s)` one-electron quantum-number tuples. -/
structure FeynmanFermionOccupationBasis (α : Type*) [DecidableEq α] where
  /-- Occupied one-particle modes. -/
  occupied : List α
  /-- Pauli exclusion: no occupied mode appears twice. -/
  pauliDistinct : occupied.Nodup

namespace FeynmanFermionOccupationBasis

/-- Whether a one-particle label is occupied in the finite occupation-basis vector. -/
def occupies {α : Type*} [DecidableEq α] (B : FeynmanFermionOccupationBasis α) (a : α) : Bool :=
  a ∈ B.occupied

/-- The mode occupation number `n_α`, valued in `{0,1}` for fermions. -/
def occupationNumber {α : Type*} [DecidableEq α] (B : FeynmanFermionOccupationBasis α)
    (a : α) : Nat :=
  if B.occupies a then 1 else 0

/-- Total particle number of a finite occupation-basis vector. -/
def particleNumber {α : Type*} [DecidableEq α] (B : FeynmanFermionOccupationBasis α) : Nat :=
  B.occupied.length

/-- Fermion mode occupations are exactly zero or one. -/
lemma occupationNumber_zero_or_one {α : Type*} [DecidableEq α]
    (B : FeynmanFermionOccupationBasis α) (a : α) :
    B.occupationNumber a = 0 ∨ B.occupationNumber a = 1 := by
  unfold occupationNumber occupies
  by_cases h : a ∈ B.occupied <;> simp [h]

/-- Create one fermion in a previously empty mode. -/
def create {α : Type*} [DecidableEq α]
    (B : FeynmanFermionOccupationBasis α) (a : α) (h : a ∉ B.occupied) :
    FeynmanFermionOccupationBasis α where
  occupied := a :: B.occupied
  pauliDistinct := by
    simpa [h] using B.pauliDistinct

/-- Creating a fermion in an empty mode raises the particle number by one. -/
lemma create_particleNumber {α : Type*} [DecidableEq α]
    (B : FeynmanFermionOccupationBasis α) (a : α) (h : a ∉ B.occupied) :
    (B.create a h).particleNumber = B.particleNumber + 1 := by
  simp [create, particleNumber]

/-- The created mode has occupation number one. -/
lemma create_occupationNumber_self {α : Type*} [DecidableEq α]
    (B : FeynmanFermionOccupationBasis α) (a : α) (h : a ∉ B.occupied) :
    (B.create a h).occupationNumber a = 1 := by
  simp [create, occupationNumber, occupies]

/-- A second creation in the same finite fermion mode is forbidden by the Pauli side condition. -/
lemma create_same_mode_not_empty {α : Type*} [DecidableEq α]
    (B : FeynmanFermionOccupationBasis α) (a : α) (h : a ∉ B.occupied) :
    ¬ a ∉ (B.create a h).occupied := by
  simp [create]

/-- Annihilate one fermion from a finite occupation-basis vector. -/
def annihilate {α : Type*} [DecidableEq α]
    (B : FeynmanFermionOccupationBasis α) (a : α) : FeynmanFermionOccupationBasis α where
  occupied := B.occupied.erase a
  pauliDistinct := B.pauliDistinct.erase a

/-- Annihilating an occupied mode lowers the particle number by one. -/
lemma annihilate_particleNumber_add_one {α : Type*} [DecidableEq α]
    (B : FeynmanFermionOccupationBasis α) (a : α) (h : a ∈ B.occupied) :
    (B.annihilate a).particleNumber + 1 = B.particleNumber := by
  unfold annihilate particleNumber
  exact List.length_erase_add_one h

/-- After annihilating a Pauli-distinct mode, that mode has occupation number zero. -/
lemma annihilate_occupationNumber_self {α : Type*} [DecidableEq α]
    (B : FeynmanFermionOccupationBasis α) (a : α) :
    (B.annihilate a).occupationNumber a = 0 := by
  unfold annihilate occupationNumber occupies
  have hnot : a ∉ B.occupied.erase a := by
    intro hmem
    have hpair := (B.pauliDistinct.mem_erase_iff).mp hmem
    exact hpair.1 rfl
  simp [hnot]

/-- Diagonal one-body observable `Σ_{occupied α} ε_α` on a finite occupation-basis vector. -/
def diagonalOneBodyEigenvalue {α : Type*} [DecidableEq α]
    (ε : α → ℝ) (B : FeynmanFermionOccupationBasis α) : ℝ :=
  (B.occupied.map ε).sum

/-- The list form of a diagonal one-body observable equals the finite Feynman/Tasaki Hamiltonian
sum `Σ_α ε_α n_α` for the same occupation basis. -/
lemma diagonalOneBodyEigenvalue_eq_feynmanDiagonalHamiltonian
    {α : Type*} [Fintype α] [DecidableEq α]
    (ε : α → ℝ) (B : FeynmanFermionOccupationBasis α) :
    B.diagonalOneBodyEigenvalue ε =
      feynmanDiagonalHamiltonianEigenvalue ε B.occupies := by
  classical
  unfold diagonalOneBodyEigenvalue feynmanDiagonalHamiltonianEigenvalue occupies
  rw [← List.sum_toFinset ε B.pauliDistinct]
  calc
    B.occupied.toFinset.sum ε = ∑ a : α, if a ∈ B.occupied then ε a else 0 := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext a
        simp
      · intro _ _
        rfl
    _ = ∑ a : α, ε a * if decide (a ∈ B.occupied) = true then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : a ∈ B.occupied <;> simp [h]

/-- A finite integer-valued quantum-number observable is the sum of the one-particle labels over
occupied modes. -/
def quantumNumberObservable {α : Type*} [DecidableEq α]
    (q : α → ℤ) (B : FeynmanFermionOccupationBasis α) : ℤ :=
  (B.occupied.map q).sum

/-- The constant one-body quantum-number observable is the particle number. -/
lemma particleNumber_eq_quantumNumberObservable_one {α : Type*} [DecidableEq α]
    (B : FeynmanFermionOccupationBasis α) :
    B.quantumNumberObservable (fun _ => (1 : ℤ)) = (B.particleNumber : ℤ) := by
  unfold quantumNumberObservable particleNumber
  induction B.occupied with
  | nil => simp
  | cons _ _ ih =>
      simp
      omega

end FeynmanFermionOccupationBasis

/-- Explicit decidability of the bound-state quantum-number validity predicate, used for generated
finite tables. -/
instance instDecidablePredIsValidElectronQuantumNumbers :
    DecidablePred IsValidElectronQuantumNumbers := fun q => by
  unfold IsValidElectronQuantumNumbers
  infer_instance

/-- Every generated all-118 row consists of valid bound-state one-electron quantum-number tuples. -/
lemma all118QuantumNumberTable_valid_checked :
    ∀ i : Fin 118, (all118QuantumNumberTable i).Forall IsValidElectronQuantumNumbers := by
  native_decide

/-- Every generated all-118 row is Pauli-distinct at the explicit `(n,l,m_l,2s)` mode level. -/
lemma all118QuantumNumberTable_pauliDistinct_checked :
    ∀ i : Fin 118, (all118QuantumNumberTable i).Nodup := by
  native_decide

/-- The generated all-118 periodic-table rows as Feynman/Tasaki occupation-basis vectors. -/
def all118FeynmanOccupationBasis (i : Fin 118) :
    FeynmanFermionOccupationBasis ElectronQuantumNumbers where
  occupied := all118QuantumNumberTable i
  pauliDistinct := all118QuantumNumberTable_pauliDistinct_checked i

/-- The Feynman/Tasaki occupation-basis vector for row `Z` has particle number `Z`. -/
lemma all118FeynmanOccupationBasis_particleNumber (i : Fin 118) :
    (all118FeynmanOccupationBasis i).particleNumber = i.val + 1 :=
  all118QuantumNumberTable_length_checked i

/-- The occupied one-particle labels of each generated Feynman/Tasaki row are valid atomic
quantum-number tuples. -/
lemma all118FeynmanOccupationBasis_valid (i : Fin 118) :
    (all118FeynmanOccupationBasis i).occupied.Forall IsValidElectronQuantumNumbers :=
  all118QuantumNumberTable_valid_checked i

/-- On every generated element row, the constant quantum-number observable `Σ 1` equals the atomic
number `Z`.  This is the occupation-basis number-operator statement specialized to the computed
periodic-table carrier. -/
lemma all118FeynmanOccupationBasis_numberObservable_one (i : Fin 118) :
    (all118FeynmanOccupationBasis i).quantumNumberObservable (fun _ => (1 : ℤ)) =
      (i.val + 1 : ℤ) := by
  rw [FeynmanFermionOccupationBasis.particleNumber_eq_quantumNumberObservable_one]
  exact congrArg Int.ofNat (all118FeynmanOccupationBasis_particleNumber i)

/-! ## Reference scope for professional periodic-table data -/

/-- Scope marker for external professional reference tables.  CODATA/NIST supplies physical
constants; NIST atomic spectroscopy and IUPAC/CIAAW supply periodic-table reference data.  In this
file, those references determine only the neutral-element range `1 <= Z <= 118`; the occupations and
quantum-number rows above are computed internally from Pauli capacity and the repository's subshell
carrier. -/
structure ProfessionalPeriodicTableReferenceScope where
  supportsNeutralAtomicNumbersThroughOganesson : Prop
  rowsComputedInLeanNotImported : Prop

/-- The repository's current reference scope: all named neutral elements through oganesson are in
range, and the electron rows are generated in Lean rather than imported from a reference table. -/
def nistCiaawCodataPeriodicReferenceScope : ProfessionalPeriodicTableReferenceScope where
  supportsNeutralAtomicNumbersThroughOganesson :=
    ∀ i : Fin 118, (all118KnownElement i).val = i.val + 1
  rowsComputedInLeanNotImported :=
    ∀ i : Fin 118, (all118QuantumNumberTable i).length = i.val + 1

lemma nistCiaawCodataPeriodicReferenceScope_checked :
    nistCiaawCodataPeriodicReferenceScope.supportsNeutralAtomicNumbersThroughOganesson
      ∧ nistCiaawCodataPeriodicReferenceScope.rowsComputedInLeanNotImported := by
  exact ⟨all118_atomicNumber, all118QuantumNumberTable_length_checked⟩

/-! ## Hund exchange energetics and configuration-exception obligations -/

/-- The number of unordered pairs among `n` electrons. -/
def chooseTwo (n : Nat) : Nat := n * (n - 1) / 2

/-- In a subshell with `g = 2l+1` spatial orbitals, the number of paired electrons after Hund filling:
zero until each spatial orbital is singly occupied, then one added pair for each additional electron. -/
def hundPairingCount (g e : Nat) : Nat := e - min e g

/-- In a Hund-filled subshell, the number of same-spin exchange pairs.  Majority-spin electrons occupy
distinct orbitals first; minority-spin electrons then form their own exchange pairs. -/
def hundExchangePairCount (g e : Nat) : Nat :=
  chooseTwo (min e g) + chooseTwo (e - g)

/-- A coarse-grained Hund energy for one subshell:

`levelCost * e + pairingPenalty * pairCount - exchangeReward * exchangePairCount`.

This record is not meant to be fitted directly.  Below, `IntegerScaledSubshellHamiltonianIntegrals`
and `SubshellHamiltonianEnergyDerivation` derive these three coefficients from the one-electron
and two-electron matrix elements of the second-quantized electronic Hamiltonian, after choosing a
common energy unit. -/
structure HundSubshellEnergy where
  levelCost : ℤ
  pairingPenalty : ℤ
  exchangeReward : ℤ

/-- Integer-scaled subshell matrix elements of the electronic Hamiltonian.  The entries are the
finite, fixed-energy-unit representatives of:

* the diagonal one-electron/core integral `h_pp`;
* the direct Coulomb cost for double occupation;
* the exchange Coulomb integral that lowers same-spin distinct-orbital occupations.

The conversion to `HundSubshellEnergy` is therefore a derivation of the Hund coefficients from
Hamiltonian matrix elements, not an independent parameter choice. -/
structure IntegerScaledSubshellHamiltonianIntegrals where
  oneElectronLevel : ℤ
  sameOrbitalDirectCoulomb : ℤ
  sameSpinExchangeCoulomb : ℤ

/-- Read integer-scaled Hamiltonian matrix elements as the Hund coefficients used by the finite
occupation-energy model. -/
def IntegerScaledSubshellHamiltonianIntegrals.toHundSubshellEnergy
    (I : IntegerScaledSubshellHamiltonianIntegrals) : HundSubshellEnergy where
  levelCost := I.oneElectronLevel
  pairingPenalty := I.sameOrbitalDirectCoulomb
  exchangeReward := I.sameSpinExchangeCoulomb

@[simp] lemma IntegerScaledSubshellHamiltonianIntegrals.toHundSubshellEnergy_levelCost
    (I : IntegerScaledSubshellHamiltonianIntegrals) :
    I.toHundSubshellEnergy.levelCost = I.oneElectronLevel := rfl

@[simp] lemma IntegerScaledSubshellHamiltonianIntegrals.toHundSubshellEnergy_pairingPenalty
    (I : IntegerScaledSubshellHamiltonianIntegrals) :
    I.toHundSubshellEnergy.pairingPenalty = I.sameOrbitalDirectCoulomb := rfl

@[simp] lemma IntegerScaledSubshellHamiltonianIntegrals.toHundSubshellEnergy_exchangeReward
    (I : IntegerScaledSubshellHamiltonianIntegrals) :
    I.toHundSubshellEnergy.exchangeReward = I.sameSpinExchangeCoulomb := rfl

section HamiltonianMatrixElementDerivation

variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
variable {ι : Type*} [Fintype ι]

/-- A Lean-checked extraction of the integer-scaled Hund coefficients from a concrete
second-quantized electronic Hamiltonian.  The equalities say exactly which matrix elements are being
used and how the chosen positive energy unit scales them. -/
structure SubshellHamiltonianEnergyDerivation
    (H : SecondQuantizedElectronicHamiltonian A ι) where
  levelOrbital : ι
  pairedOrbital : ι
  exchangeOrbital : ι
  energyUnit : ℝ
  energyUnit_pos : 0 < energyUnit
  oneElectronLevel : ℤ
  sameOrbitalDirectCoulomb : ℤ
  sameSpinExchangeCoulomb : ℤ
  oneElectronLevel_scales :
    (oneElectronLevel : ℝ) * energyUnit = (H.oneBodyInt levelOrbital levelOrbital).re
  directCoulomb_scales :
    (sameOrbitalDirectCoulomb : ℝ) * energyUnit =
      (H.twoBodyInt levelOrbital pairedOrbital levelOrbital pairedOrbital).re
  exchangeCoulomb_scales :
    (sameSpinExchangeCoulomb : ℝ) * energyUnit =
      (H.twoBodyInt levelOrbital exchangeOrbital exchangeOrbital levelOrbital).re

/-- Forget only the explicit source Hamiltonian after the matrix-element equalities have produced
integer-scaled subshell integrals. -/
def SubshellHamiltonianEnergyDerivation.toIntegerScaledIntegrals
    {H : SecondQuantizedElectronicHamiltonian A ι}
    (D : SubshellHamiltonianEnergyDerivation H) :
    IntegerScaledSubshellHamiltonianIntegrals where
  oneElectronLevel := D.oneElectronLevel
  sameOrbitalDirectCoulomb := D.sameOrbitalDirectCoulomb
  sameSpinExchangeCoulomb := D.sameSpinExchangeCoulomb

/-- The Hund coefficients induced by a Hamiltonian matrix-element extraction. -/
def SubshellHamiltonianEnergyDerivation.toHundSubshellEnergy
    {H : SecondQuantizedElectronicHamiltonian A ι}
    (D : SubshellHamiltonianEnergyDerivation H) : HundSubshellEnergy :=
  D.toIntegerScaledIntegrals.toHundSubshellEnergy

@[simp] lemma SubshellHamiltonianEnergyDerivation.toHundSubshellEnergy_levelCost
    {H : SecondQuantizedElectronicHamiltonian A ι}
    (D : SubshellHamiltonianEnergyDerivation H) :
    D.toHundSubshellEnergy.levelCost = D.oneElectronLevel := rfl

@[simp] lemma SubshellHamiltonianEnergyDerivation.toHundSubshellEnergy_pairingPenalty
    {H : SecondQuantizedElectronicHamiltonian A ι}
    (D : SubshellHamiltonianEnergyDerivation H) :
    D.toHundSubshellEnergy.pairingPenalty = D.sameOrbitalDirectCoulomb := rfl

@[simp] lemma SubshellHamiltonianEnergyDerivation.toHundSubshellEnergy_exchangeReward
    {H : SecondQuantizedElectronicHamiltonian A ι}
    (D : SubshellHamiltonianEnergyDerivation H) :
    D.toHundSubshellEnergy.exchangeReward = D.sameSpinExchangeCoulomb := rfl

/-- The diagonal level coefficient is the fixed-unit representative of the one-electron Hamiltonian
matrix element `h_pp`. -/
lemma SubshellHamiltonianEnergyDerivation.levelCost_scales_oneBody
    {H : SecondQuantizedElectronicHamiltonian A ι}
    (D : SubshellHamiltonianEnergyDerivation H) :
    (D.toHundSubshellEnergy.levelCost : ℝ) * D.energyUnit =
      (H.oneBodyInt D.levelOrbital D.levelOrbital).re := by
  simpa using D.oneElectronLevel_scales

/-- The pairing penalty is the fixed-unit representative of the direct Coulomb matrix element. -/
lemma SubshellHamiltonianEnergyDerivation.pairingPenalty_scales_directCoulomb
    {H : SecondQuantizedElectronicHamiltonian A ι}
    (D : SubshellHamiltonianEnergyDerivation H) :
    (D.toHundSubshellEnergy.pairingPenalty : ℝ) * D.energyUnit =
      (H.twoBodyInt D.levelOrbital D.pairedOrbital D.levelOrbital D.pairedOrbital).re := by
  simpa using D.directCoulomb_scales

/-- The exchange reward is the fixed-unit representative of the exchange Coulomb matrix element. -/
lemma SubshellHamiltonianEnergyDerivation.exchangeReward_scales_exchangeCoulomb
    {H : SecondQuantizedElectronicHamiltonian A ι}
    (D : SubshellHamiltonianEnergyDerivation H) :
    (D.toHundSubshellEnergy.exchangeReward : ℝ) * D.energyUnit =
      (H.twoBodyInt D.levelOrbital D.exchangeOrbital D.exchangeOrbital D.levelOrbital).re := by
  simpa using D.exchangeCoulomb_scales

end HamiltonianMatrixElementDerivation

/-- A common-unit orbital-integral model for all subshells in the finite atomic carrier.  Each row
gets its Hund coefficients by reading Hamiltonian matrix elements in the same integer energy unit. -/
structure AtomicOrbitalIntegralModel where
  energyUnit : ℝ
  energyUnit_pos : 0 < energyUnit
  subshellIntegralsAt : Nat → IntegerScaledSubshellHamiltonianIntegrals

/-- The Hund coefficients at a subshell index, derived from the corresponding Hamiltonian integral
data in the common energy unit. -/
def AtomicOrbitalIntegralModel.hundEnergyAt
    (M : AtomicOrbitalIntegralModel) (i : Nat) : HundSubshellEnergy :=
  (M.subshellIntegralsAt i).toHundSubshellEnergy

@[simp] lemma AtomicOrbitalIntegralModel.hundEnergyAt_levelCost
    (M : AtomicOrbitalIntegralModel) (i : Nat) :
    (M.hundEnergyAt i).levelCost = (M.subshellIntegralsAt i).oneElectronLevel := rfl

@[simp] lemma AtomicOrbitalIntegralModel.hundEnergyAt_pairingPenalty
    (M : AtomicOrbitalIntegralModel) (i : Nat) :
    (M.hundEnergyAt i).pairingPenalty =
      (M.subshellIntegralsAt i).sameOrbitalDirectCoulomb := rfl

@[simp] lemma AtomicOrbitalIntegralModel.hundEnergyAt_exchangeReward
    (M : AtomicOrbitalIntegralModel) (i : Nat) :
    (M.hundEnergyAt i).exchangeReward =
      (M.subshellIntegralsAt i).sameSpinExchangeCoulomb := rfl

section AtomicHamiltonianIntegralModel

variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
variable {ι : Type*} [Fintype ι]

/-- A full atomic integral model whose subshell coefficients are extracted from one
second-quantized electronic Hamiltonian. -/
structure AtomicHamiltonianIntegralModel
    (H : SecondQuantizedElectronicHamiltonian A ι) where
  energyUnit : ℝ
  energyUnit_pos : 0 < energyUnit
  subshellDerivationAt : Nat → SubshellHamiltonianEnergyDerivation H
  common_energyUnit :
    ∀ i, (subshellDerivationAt i).energyUnit = energyUnit

/-- Forget the source Hamiltonian after all subshell-level scaling proofs have supplied the
common-unit integer integral model consumed by the atomic minimizer. -/
def AtomicHamiltonianIntegralModel.toAtomicOrbitalIntegralModel
    {H : SecondQuantizedElectronicHamiltonian A ι}
    (M : AtomicHamiltonianIntegralModel H) : AtomicOrbitalIntegralModel where
  energyUnit := M.energyUnit
  energyUnit_pos := M.energyUnit_pos
  subshellIntegralsAt := fun i =>
    (M.subshellDerivationAt i).toIntegerScaledIntegrals

@[simp] lemma AtomicHamiltonianIntegralModel.toAtomicOrbitalIntegralModel_hundEnergyAt
    {H : SecondQuantizedElectronicHamiltonian A ι}
    (M : AtomicHamiltonianIntegralModel H) (i : Nat) :
    M.toAtomicOrbitalIntegralModel.hundEnergyAt i =
      (M.subshellDerivationAt i).toHundSubshellEnergy := rfl

end AtomicHamiltonianIntegralModel

/-- Combined subshell bridge: the Hund coefficients are fixed-unit representatives of matrix
elements of a second-quantized electronic Hamiltonian, while the same finite subshell mode is carried
by the repository's exterior-algebra Fock functor and Kálnay/CAR number-projection layer. -/
lemma subshellHamiltonianEnergyDerivation_secondQuantized_mode_bridge
    {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
    {ι : Type*} [Fintype ι] {H : SecondQuantizedElectronicHamiltonian A ι}
    (D : SubshellHamiltonianEnergyDerivation H)
    {B : Type*} [Ring B] [StarRing B] {q : BoundSubshell}
    (R : SubshellKalnayRealization B q) (mode : SubshellMode q) :
    (D.toHundSubshellEnergy.levelCost : ℝ) * D.energyUnit =
        (H.oneBodyInt D.levelOrbital D.levelOrbital).re
      ∧ (D.toHundSubshellEnergy.pairingPenalty : ℝ) * D.energyUnit =
        (H.twoBodyInt D.levelOrbital D.pairedOrbital D.levelOrbital D.pairedOrbital).re
      ∧ (D.toHundSubshellEnergy.exchangeReward : ℝ) * D.energyUnit =
        (H.twoBodyInt D.levelOrbital D.exchangeOrbital D.exchangeOrbital D.levelOrbital).re
      ∧ subshellFockCreation q mode * subshellFockCreation q mode = 0
      ∧ star (modeNumber R mode) = modeNumber R mode
      ∧ modeNumber R mode * modeNumber R mode = modeNumber R mode := by
  exact ⟨SubshellHamiltonianEnergyDerivation.levelCost_scales_oneBody D,
    SubshellHamiltonianEnergyDerivation.pairingPenalty_scales_directCoulomb D,
    SubshellHamiltonianEnergyDerivation.exchangeReward_scales_exchangeCoulomb D,
    subshellFockCreation_sq q mode, modeNumber_selfAdjoint R mode, modeNumber_idempotent R mode⟩

/-- The Hund energy contribution of one subshell with `g` spatial orbitals and `e` electrons. -/
def hundSubshellEnergy (P : HundSubshellEnergy) (g e : Nat) : ℤ :=
  P.levelCost * (e : ℤ)
    + P.pairingPenalty * (hundPairingCount g e : ℤ)
    - P.exchangeReward * (hundExchangePairCount g e : ℤ)

/-- The Hund subshell score written directly in terms of the Hamiltonian-derived matrix elements. -/
lemma hundSubshellEnergy_eq_integerScaledSubshellHamiltonianIntegrals
    (I : IntegerScaledSubshellHamiltonianIntegrals) (g e : Nat) :
    hundSubshellEnergy I.toHundSubshellEnergy g e
      =
        I.oneElectronLevel * (e : ℤ)
          + I.sameOrbitalDirectCoulomb * (hundPairingCount g e : ℤ)
          - I.sameSpinExchangeCoulomb * (hundExchangePairCount g e : ℤ) := by
  rfl

/-- Two-subshell valence energy, used for `ns ↔ (n-1)d` and analogous promotion comparisons. -/
def hundTwoSubshellEnergy
    (inner outer : HundSubshellEnergy) (gInner : Nat) (innerOcc outerOcc : Nat) : ℤ :=
  hundSubshellEnergy inner gInner innerOcc + hundSubshellEnergy outer 1 outerOcc

/-- The energy gap for promoting one outer `s` electron into an inner open shell:
`inner^d outer^2 → inner^(d+1) outer^1`.  A negative gap is exactly a Hund configuration exception. -/
def hundOneElectronPromotionGap
    (inner outer : HundSubshellEnergy) (gInner d : Nat) : ℤ :=
  hundTwoSubshellEnergy inner outer gInner (d + 1) 1
    - hundTwoSubshellEnergy inner outer gInner d 2

/-- The promoted configuration is lower in energy than the regular Aufbau occupation. -/
def HundOneElectronPromotionLowers
    (inner outer : HundSubshellEnergy) (gInner d : Nat) : Prop :=
  hundTwoSubshellEnergy inner outer gInner (d + 1) 1
    < hundTwoSubshellEnergy inner outer gInner d 2

/-- A one-electron Hund exception is a Pauli-allowed promotion whose promoted occupation is lower in
the Hund energy functional. -/
def HundOneElectronException
    (inner outer : HundSubshellEnergy) (gInner d : Nat) : Prop :=
  d + 1 <= 2 * gInner ∧ HundOneElectronPromotionLowers inner outer gInner d

/-- **Hund exception criterion.**  The promotion
`inner^d outer² → inner^(d+1) outer¹` is energetically favored iff the computed promotion gap is negative.
This is the exact finite inequality that must be discharged for any claimed configuration exception. -/
lemma hundOneElectronPromotion_lowers_iff_gap_negative
    (inner outer : HundSubshellEnergy) (gInner d : Nat) :
    HundOneElectronPromotionLowers inner outer gInner d
      ↔ hundOneElectronPromotionGap inner outer gInner d < 0 := by
  unfold HundOneElectronPromotionLowers hundOneElectronPromotionGap
  omega

/-- If the Hund promotion gap is nonnegative, Lean rejects the corresponding one-electron exception. -/
lemma no_hundOneElectronException_of_nonnegative_gap
    (inner outer : HundSubshellEnergy) (gInner d : Nat)
    (hgap : 0 <= hundOneElectronPromotionGap inner outer gInner d) :
    ¬ HundOneElectronException inner outer gInner d := by
  intro h
  rcases h with ⟨_, hlower⟩
  rw [hundOneElectronPromotion_lowers_iff_gap_negative] at hlower
  omega

/-- Conversely, a Pauli-allowed negative promotion gap is exactly the one-electron Hund exception. -/
lemma hundOneElectronException_of_negative_gap
    (inner outer : HundSubshellEnergy) (gInner d : Nat)
    (hcap : d + 1 <= 2 * gInner)
    (hgap : hundOneElectronPromotionGap inner outer gInner d < 0) :
    HundOneElectronException inner outer gInner d := by
  exact ⟨hcap, (hundOneElectronPromotion_lowers_iff_gap_negative inner outer gInner d).2 hgap⟩

/-- The `d`-subshell spatial degeneracy `g = 2l+1 = 5`. -/
def dSpatialDegeneracy : Nat := 2 * 2 + 1

/-- The `f`-subshell spatial degeneracy `g = 2l+1 = 7`. -/
def fSpatialDegeneracy : Nat := 2 * 3 + 1

lemma dSpatialDegeneracy_eq_five : dSpatialDegeneracy = 5 := by decide

lemma fSpatialDegeneracy_eq_seven : fSpatialDegeneracy = 7 := by decide

/-! ### Explicit half-filled and filled-shell Hund promotion gaps -/

/-- For a `d` shell, the promotion `d³s² → d⁴s¹` has gap
`Δε - P_s - 3J_d`.  This is the single-promotion inequality shape needed for the
niobium-type row before any corrected configuration can be installed. -/
lemma d3_s2_to_d4_s1_gap_eq (inner outer : HundSubshellEnergy) :
    hundOneElectronPromotionGap inner outer dSpatialDegeneracy 3
      = inner.levelCost - outer.levelCost - outer.pairingPenalty
        - 3 * inner.exchangeReward := by
  simp [hundOneElectronPromotionGap, hundTwoSubshellEnergy, hundSubshellEnergy,
    dSpatialDegeneracy, hundPairingCount, hundExchangePairCount, chooseTwo]
  ring

/-- A Pauli-allowed `d³s² → d⁴s¹` exception follows exactly from the negative
Hund gap computed in `d3_s2_to_d4_s1_gap_eq`. -/
lemma d3_s2_to_d4_s1_exception_of_gap_negative
    (inner outer : HundSubshellEnergy)
    (hgap : inner.levelCost - outer.levelCost - outer.pairingPenalty
        - 3 * inner.exchangeReward < 0) :
    HundOneElectronException inner outer dSpatialDegeneracy 3 := by
  apply hundOneElectronException_of_negative_gap
  · decide
  · rwa [d3_s2_to_d4_s1_gap_eq]

/-- For a `d` shell, the half-filled promotion `d⁴s² → d⁵s¹` has gap
`Δε - P_s - 4J_d`.  Thus the exception is derived from a finite energy inequality: the
single-particle level cost must be outweighed by the removed `s` pairing plus four new exchange
pairs in the `d` shell. -/
lemma d4_s2_to_d5_s1_gap_eq (inner outer : HundSubshellEnergy) :
    hundOneElectronPromotionGap inner outer dSpatialDegeneracy 4
      = inner.levelCost - outer.levelCost - outer.pairingPenalty
        - 4 * inner.exchangeReward := by
  simp [hundOneElectronPromotionGap, hundTwoSubshellEnergy, hundSubshellEnergy,
    dSpatialDegeneracy, hundPairingCount, hundExchangePairCount, chooseTwo]
  ring

/-- A Pauli-allowed `d⁴s² → d⁵s¹` half-filled-shell exception follows exactly from the negative
Hund gap computed in `d4_s2_to_d5_s1_gap_eq`. -/
lemma d4_s2_to_d5_s1_exception_of_gap_negative
    (inner outer : HundSubshellEnergy)
    (hgap : inner.levelCost - outer.levelCost - outer.pairingPenalty
        - 4 * inner.exchangeReward < 0) :
    HundOneElectronException inner outer dSpatialDegeneracy 4 := by
  apply hundOneElectronException_of_negative_gap
  · decide
  · rwa [d4_s2_to_d5_s1_gap_eq]

/-- For a `d` shell, the promotion `d⁶s² → d⁷s¹` has gap
`Δε + P_d - P_s - J_d`. -/
lemma d6_s2_to_d7_s1_gap_eq (inner outer : HundSubshellEnergy) :
    hundOneElectronPromotionGap inner outer dSpatialDegeneracy 6
      = inner.levelCost - outer.levelCost + inner.pairingPenalty - outer.pairingPenalty
        - inner.exchangeReward := by
  simp [hundOneElectronPromotionGap, hundTwoSubshellEnergy, hundSubshellEnergy,
    dSpatialDegeneracy, hundPairingCount, hundExchangePairCount, chooseTwo]
  ring

/-- A Pauli-allowed `d⁶s² → d⁷s¹` exception follows exactly from the negative
Hund gap computed in `d6_s2_to_d7_s1_gap_eq`. -/
lemma d6_s2_to_d7_s1_exception_of_gap_negative
    (inner outer : HundSubshellEnergy)
    (hgap : inner.levelCost - outer.levelCost + inner.pairingPenalty - outer.pairingPenalty
        - inner.exchangeReward < 0) :
    HundOneElectronException inner outer dSpatialDegeneracy 6 := by
  apply hundOneElectronException_of_negative_gap
  · decide
  · rwa [d6_s2_to_d7_s1_gap_eq]

/-- For a `d` shell, the promotion `d⁷s² → d⁸s¹` has gap
`Δε + P_d - P_s - 2J_d`. -/
lemma d7_s2_to_d8_s1_gap_eq (inner outer : HundSubshellEnergy) :
    hundOneElectronPromotionGap inner outer dSpatialDegeneracy 7
      = inner.levelCost - outer.levelCost + inner.pairingPenalty - outer.pairingPenalty
        - 2 * inner.exchangeReward := by
  simp [hundOneElectronPromotionGap, hundTwoSubshellEnergy, hundSubshellEnergy,
    dSpatialDegeneracy, hundPairingCount, hundExchangePairCount, chooseTwo]
  ring

/-- A Pauli-allowed `d⁷s² → d⁸s¹` exception follows exactly from the negative
Hund gap computed in `d7_s2_to_d8_s1_gap_eq`. -/
lemma d7_s2_to_d8_s1_exception_of_gap_negative
    (inner outer : HundSubshellEnergy)
    (hgap : inner.levelCost - outer.levelCost + inner.pairingPenalty - outer.pairingPenalty
        - 2 * inner.exchangeReward < 0) :
    HundOneElectronException inner outer dSpatialDegeneracy 7 := by
  apply hundOneElectronException_of_negative_gap
  · decide
  · rwa [d7_s2_to_d8_s1_gap_eq]

/-- For a `d` shell, the promotion `d⁸s² → d⁹s¹` has gap
`Δε + P_d - P_s - 3J_d`.  This is the first one-electron step toward the
palladium-type full-`d` row, but by itself it is not the observed `d¹⁰s⁰` substitution. -/
lemma d8_s2_to_d9_s1_gap_eq (inner outer : HundSubshellEnergy) :
    hundOneElectronPromotionGap inner outer dSpatialDegeneracy 8
      = inner.levelCost - outer.levelCost + inner.pairingPenalty - outer.pairingPenalty
        - 3 * inner.exchangeReward := by
  simp [hundOneElectronPromotionGap, hundTwoSubshellEnergy, hundSubshellEnergy,
    dSpatialDegeneracy, hundPairingCount, hundExchangePairCount, chooseTwo]
  ring

/-- A Pauli-allowed `d⁸s² → d⁹s¹` exception follows exactly from the negative
Hund gap computed in `d8_s2_to_d9_s1_gap_eq`. -/
lemma d8_s2_to_d9_s1_exception_of_gap_negative
    (inner outer : HundSubshellEnergy)
    (hgap : inner.levelCost - outer.levelCost + inner.pairingPenalty - outer.pairingPenalty
        - 3 * inner.exchangeReward < 0) :
    HundOneElectronException inner outer dSpatialDegeneracy 8 := by
  apply hundOneElectronException_of_negative_gap
  · decide
  · rwa [d8_s2_to_d9_s1_gap_eq]

/-- For a `d` shell, the filled-shell promotion `d⁹s² → d¹⁰s¹` has gap
`Δε + P_d - P_s - 4J_d`.  The extra `d` pairing penalty must still be overcome by the lost
outer-shell pairing and the four additional exchange pairs. -/
lemma d9_s2_to_d10_s1_gap_eq (inner outer : HundSubshellEnergy) :
    hundOneElectronPromotionGap inner outer dSpatialDegeneracy 9
      = inner.levelCost - outer.levelCost + inner.pairingPenalty - outer.pairingPenalty
        - 4 * inner.exchangeReward := by
  simp [hundOneElectronPromotionGap, hundTwoSubshellEnergy, hundSubshellEnergy,
    dSpatialDegeneracy, hundPairingCount, hundExchangePairCount, chooseTwo]
  ring

/-- A Pauli-allowed `d⁹s² → d¹⁰s¹` filled-shell exception follows exactly from the negative
Hund gap computed in `d9_s2_to_d10_s1_gap_eq`. -/
lemma d9_s2_to_d10_s1_exception_of_gap_negative
    (inner outer : HundSubshellEnergy)
    (hgap : inner.levelCost - outer.levelCost + inner.pairingPenalty - outer.pairingPenalty
        - 4 * inner.exchangeReward < 0) :
    HundOneElectronException inner outer dSpatialDegeneracy 9 := by
  apply hundOneElectronException_of_negative_gap
  · decide
  · rwa [d9_s2_to_d10_s1_gap_eq]

/-- The energy gap for promoting both outer `s` electrons into an inner open shell:
`inner^d outer² → inner^(d+2) outer⁰`.  This is needed for palladium-type rows, where the
observed correction is not a one-electron `s² → s¹` promotion. -/
def hundTwoElectronPromotionGap
    (inner outer : HundSubshellEnergy) (gInner d : Nat) : ℤ :=
  hundTwoSubshellEnergy inner outer gInner (d + 2) 0
    - hundTwoSubshellEnergy inner outer gInner d 2

/-- The two-electron promoted configuration is lower than the regular Aufbau occupation. -/
def HundTwoElectronPromotionLowers
    (inner outer : HundSubshellEnergy) (gInner d : Nat) : Prop :=
  hundTwoSubshellEnergy inner outer gInner (d + 2) 0
    < hundTwoSubshellEnergy inner outer gInner d 2

/-- A two-electron Hund exception is a Pauli-allowed double promotion whose promoted occupation is
lower in the same Hund energy functional. -/
def HundTwoElectronException
    (inner outer : HundSubshellEnergy) (gInner d : Nat) : Prop :=
  d + 2 <= 2 * gInner ∧ HundTwoElectronPromotionLowers inner outer gInner d

/-- The two-electron promotion criterion is again exactly a negative energy gap. -/
lemma hundTwoElectronPromotion_lowers_iff_gap_negative
    (inner outer : HundSubshellEnergy) (gInner d : Nat) :
    HundTwoElectronPromotionLowers inner outer gInner d
      ↔ hundTwoElectronPromotionGap inner outer gInner d < 0 := by
  unfold HundTwoElectronPromotionLowers hundTwoElectronPromotionGap
  omega

/-- A Pauli-allowed negative two-electron promotion gap is exactly a two-electron Hund exception. -/
lemma hundTwoElectronException_of_negative_gap
    (inner outer : HundSubshellEnergy) (gInner d : Nat)
    (hcap : d + 2 <= 2 * gInner)
    (hgap : hundTwoElectronPromotionGap inner outer gInner d < 0) :
    HundTwoElectronException inner outer gInner d := by
  exact ⟨hcap, (hundTwoElectronPromotion_lowers_iff_gap_negative inner outer gInner d).2 hgap⟩

/-- For a `d` shell, the palladium-type double promotion `d⁸s² → d¹⁰s⁰` has gap
`2Δε + 2P_d - P_s - 7J_d`. -/
lemma d8_s2_to_d10_s0_gap_eq (inner outer : HundSubshellEnergy) :
    hundTwoElectronPromotionGap inner outer dSpatialDegeneracy 8
      = 2 * (inner.levelCost - outer.levelCost)
        + 2 * inner.pairingPenalty - outer.pairingPenalty
        - 7 * inner.exchangeReward := by
  simp [hundTwoElectronPromotionGap, hundTwoSubshellEnergy, hundSubshellEnergy,
    dSpatialDegeneracy, hundPairingCount, hundExchangePairCount, chooseTwo]
  ring

/-- A Pauli-allowed palladium-type `d⁸s² → d¹⁰s⁰` exception follows exactly from the negative
two-electron Hund gap computed in `d8_s2_to_d10_s0_gap_eq`. -/
lemma d8_s2_to_d10_s0_exception_of_gap_negative
    (inner outer : HundSubshellEnergy)
    (hgap : 2 * (inner.levelCost - outer.levelCost)
        + 2 * inner.pairingPenalty - outer.pairingPenalty
        - 7 * inner.exchangeReward < 0) :
    HundTwoElectronException inner outer dSpatialDegeneracy 8 := by
  apply hundTwoElectronException_of_negative_gap
  · decide
  · rwa [d8_s2_to_d10_s0_gap_eq]

/-- For an `f` shell, the half-filled promotion `f⁶s² → f⁷s¹` has gap
`Δε - P_s - 6J_f`. -/
lemma f6_s2_to_f7_s1_gap_eq (inner outer : HundSubshellEnergy) :
    hundOneElectronPromotionGap inner outer fSpatialDegeneracy 6
      = inner.levelCost - outer.levelCost - outer.pairingPenalty
        - 6 * inner.exchangeReward := by
  simp [hundOneElectronPromotionGap, hundTwoSubshellEnergy, hundSubshellEnergy,
    fSpatialDegeneracy, hundPairingCount, hundExchangePairCount, chooseTwo]
  ring

/-- A Pauli-allowed `f⁶s² → f⁷s¹` half-filled-shell exception follows exactly from the negative
Hund gap computed in `f6_s2_to_f7_s1_gap_eq`. -/
lemma f6_s2_to_f7_s1_exception_of_gap_negative
    (inner outer : HundSubshellEnergy)
    (hgap : inner.levelCost - outer.levelCost - outer.pairingPenalty
        - 6 * inner.exchangeReward < 0) :
    HundOneElectronException inner outer fSpatialDegeneracy 6 := by
  apply hundOneElectronException_of_negative_gap
  · decide
  · rwa [f6_s2_to_f7_s1_gap_eq]

/-- For an `f` shell, the filled-shell promotion `f¹³s² → f¹⁴s¹` has gap
`Δε + P_f - P_s - 6J_f`. -/
lemma f13_s2_to_f14_s1_gap_eq (inner outer : HundSubshellEnergy) :
    hundOneElectronPromotionGap inner outer fSpatialDegeneracy 13
      = inner.levelCost - outer.levelCost + inner.pairingPenalty - outer.pairingPenalty
        - 6 * inner.exchangeReward := by
  simp [hundOneElectronPromotionGap, hundTwoSubshellEnergy, hundSubshellEnergy,
    fSpatialDegeneracy, hundPairingCount, hundExchangePairCount, chooseTwo]
  ring

/-- A Pauli-allowed `f¹³s² → f¹⁴s¹` filled-shell exception follows exactly from the negative
Hund gap computed in `f13_s2_to_f14_s1_gap_eq`. -/
lemma f13_s2_to_f14_s1_exception_of_gap_negative
    (inner outer : HundSubshellEnergy)
    (hgap : inner.levelCost - outer.levelCost + inner.pairingPenalty - outer.pairingPenalty
        - 6 * inner.exchangeReward < 0) :
    HundOneElectronException inner outer fSpatialDegeneracy 13 := by
  apply hundOneElectronException_of_negative_gap
  · decide
  · rwa [f13_s2_to_f14_s1_gap_eq]

/-! ### Global variational occupation model

The preceding gap formulas are local energy comparisons.  The non-exceptional periodic-table model
is instead global: for a fixed atomic number `Z`, search over all Pauli-valid occupation rows with
total electron count `Z`, score each row by one functional, and call the minimizer the computed
configuration.  Aufbau filling is then only an initial/generated row; Cr/Cu/Pd-type rows are not
special substitutions, but ordinary minimizers when the same score makes a promoted row lower.

The score has explicit hooks for the already-existing repository infrastructure:

* `hundEnergyAt` supplies the level, pairing, and exchange coefficients used by
  `hundSubshellEnergy`;
* `informationStress` is the slot where the finite KL / mutual-information channel terms from
  `Physlib.Thermodynamics.KullbackLeiblerInformationGain` are consumed;
* `cartanStress` is the slot for the `SU(5)` Cartan metric / `A₅`-invariant tensor score from
  `Su5ChargeQuantizationCartanTensor`;
* `icosahedralStress` is the slot for the Newton--Ostrovskyi boundary/vortex stress channel already
  imported above.

This file does not duplicate those definitions.  It exposes the finite minimization interface that
lets bridge files plug them in without treating any element as an external exception table.
-/

/-- A Pauli-valid atomic occupation row with exactly `Z` electrons. -/
def ValidAtomicOccupation (Z : Nat) (occupations : List Nat) : Prop :=
  PauliValidCounts occupations aufbauCapacities ∧ occupations.sum = Z

lemma knownElementConfiguration_validAtomicOccupation (E : KnownElement) :
    ValidAtomicOccupation E.val (knownElementConfiguration E).occupations := by
  exact ⟨knownElementConfiguration_pauli E, knownElementConfiguration_count E⟩

/-- Recursive Hund contribution of a whole occupation row.  The natural-number index lets the caller
assign different level/pairing/exchange coefficients to different subshells without redefining the
subshell list. -/
def hundOccupationEnergyWith
    (hundEnergyAt : Nat → HundSubshellEnergy) :
    Nat → List BoundSubshell → List Nat → ℤ
  | _, [], _ => 0
  | _, _ :: _, [] => 0
  | i, q :: qs, e :: es =>
      hundSubshellEnergy (hundEnergyAt i) (2 * q.l + 1) e
        + hundOccupationEnergyWith hundEnergyAt (i + 1) qs es

/-- The global atomic score.  The non-Hund stress terms are supplied by bridge files, so the atomic
layer can consume KL/channel, `SU(5)` Cartan, and icosahedral stress scores without importing or
redefining them here. -/
structure AtomicEnergyFunctional where
  hundEnergyAt : Nat → HundSubshellEnergy
  informationWeight : ℝ
  informationStress : List Nat → ℝ
  cartanWeight : ℝ
  cartanStress : List Nat → ℝ
  icosahedralWeight : ℝ
  icosahedralStress : List Nat → ℝ

/-- The Hund component of the atomic score for the repository's finite Aufbau subshell carrier. -/
def AtomicEnergyFunctional.hundOccupationEnergy
    (Φ : AtomicEnergyFunctional) (occupations : List Nat) : ℤ :=
  hundOccupationEnergyWith Φ.hundEnergyAt 0 aufbauSubshells occupations

/-- The total real-valued score minimized by the non-exceptional atomic model.  The finite Hund
energy is integer-valued; KL, mutual-information, Cartan, and icosahedral stress terms are naturally
real-valued, so the Hund term is cast only at this boundary. -/
def AtomicEnergyFunctional.totalScore
    (Φ : AtomicEnergyFunctional) (occupations : List Nat) : ℝ :=
  (Φ.hundOccupationEnergy occupations : ℝ)
    + Φ.informationWeight * Φ.informationStress occupations
    + Φ.cartanWeight * Φ.cartanStress occupations
    + Φ.icosahedralWeight * Φ.icosahedralStress occupations

/-- Build the atomic score from a common-unit orbital-integral model.  This is the non-table route:
the level, pairing, and exchange terms are read from Hamiltonian matrix elements through
`AtomicOrbitalIntegralModel.hundEnergyAt`; the remaining real-valued stress terms are supplied by
the KL/channel, Cartan, and icosahedral bridge layers. -/
def atomicEnergyFunctionalFromOrbitalIntegrals
    (M : AtomicOrbitalIntegralModel)
    (informationWeight : ℝ) (informationStress : List Nat → ℝ)
    (cartanWeight : ℝ) (cartanStress : List Nat → ℝ)
    (icosahedralWeight : ℝ) (icosahedralStress : List Nat → ℝ) :
    AtomicEnergyFunctional where
  hundEnergyAt := M.hundEnergyAt
  informationWeight := informationWeight
  informationStress := informationStress
  cartanWeight := cartanWeight
  cartanStress := cartanStress
  icosahedralWeight := icosahedralWeight
  icosahedralStress := icosahedralStress

@[simp] lemma atomicEnergyFunctionalFromOrbitalIntegrals_hundEnergyAt
    (M : AtomicOrbitalIntegralModel)
    (informationWeight : ℝ) (informationStress : List Nat → ℝ)
    (cartanWeight : ℝ) (cartanStress : List Nat → ℝ)
    (icosahedralWeight : ℝ) (icosahedralStress : List Nat → ℝ) :
    (atomicEnergyFunctionalFromOrbitalIntegrals M
      informationWeight informationStress cartanWeight cartanStress
      icosahedralWeight icosahedralStress).hundEnergyAt = M.hundEnergyAt := rfl

/-- Expanding the derived score shows that the Hund term is the one computed from the
orbital-integral model, not an independently supplied energy table. -/
lemma atomicEnergyFunctionalFromOrbitalIntegrals_totalScore_eq
    (M : AtomicOrbitalIntegralModel)
    (informationWeight : ℝ) (informationStress : List Nat → ℝ)
    (cartanWeight : ℝ) (cartanStress : List Nat → ℝ)
    (icosahedralWeight : ℝ) (icosahedralStress : List Nat → ℝ)
    (occupations : List Nat) :
    (atomicEnergyFunctionalFromOrbitalIntegrals M
      informationWeight informationStress cartanWeight cartanStress
      icosahedralWeight icosahedralStress).totalScore occupations
      =
        (hundOccupationEnergyWith M.hundEnergyAt 0 aufbauSubshells occupations : ℝ)
          + informationWeight * informationStress occupations
          + cartanWeight * cartanStress occupations
          + icosahedralWeight * icosahedralStress occupations := by
  rfl

section AtomicHamiltonianEnergyFunctional

variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
variable {ι : Type*} [Fintype ι] {H : SecondQuantizedElectronicHamiltonian A ι}

/-- Build the global atomic score directly from a second-quantized Hamiltonian integral model.
This is the fully linked route: each subshell's Hund row is obtained from a
`SubshellHamiltonianEnergyDerivation H`, and the non-Hund terms remain the existing KL/channel,
Cartan, and icosahedral stress hooks. -/
def atomicEnergyFunctionalFromHamiltonianIntegrals
    (M : AtomicHamiltonianIntegralModel H)
    (informationWeight : ℝ) (informationStress : List Nat → ℝ)
    (cartanWeight : ℝ) (cartanStress : List Nat → ℝ)
    (icosahedralWeight : ℝ) (icosahedralStress : List Nat → ℝ) :
    AtomicEnergyFunctional :=
  atomicEnergyFunctionalFromOrbitalIntegrals M.toAtomicOrbitalIntegralModel
    informationWeight informationStress cartanWeight cartanStress
    icosahedralWeight icosahedralStress

@[simp] lemma atomicEnergyFunctionalFromHamiltonianIntegrals_hundEnergyAt
    (M : AtomicHamiltonianIntegralModel H)
    (informationWeight : ℝ) (informationStress : List Nat → ℝ)
    (cartanWeight : ℝ) (cartanStress : List Nat → ℝ)
    (icosahedralWeight : ℝ) (icosahedralStress : List Nat → ℝ) :
    (atomicEnergyFunctionalFromHamiltonianIntegrals M
      informationWeight informationStress cartanWeight cartanStress
      icosahedralWeight icosahedralStress).hundEnergyAt =
        fun i => (M.subshellDerivationAt i).toHundSubshellEnergy := by
  funext i
  rfl

/-- Expanding the Hamiltonian-derived score shows that the Hund term is computed from the
subshell derivations of the same second-quantized electronic Hamiltonian, not from a separate
energy table. -/
lemma atomicEnergyFunctionalFromHamiltonianIntegrals_totalScore_eq
    (M : AtomicHamiltonianIntegralModel H)
    (informationWeight : ℝ) (informationStress : List Nat → ℝ)
    (cartanWeight : ℝ) (cartanStress : List Nat → ℝ)
    (icosahedralWeight : ℝ) (icosahedralStress : List Nat → ℝ)
    (occupations : List Nat) :
    (atomicEnergyFunctionalFromHamiltonianIntegrals M
      informationWeight informationStress cartanWeight cartanStress
      icosahedralWeight icosahedralStress).totalScore occupations
      =
        (hundOccupationEnergyWith
            (fun i => (M.subshellDerivationAt i).toHundSubshellEnergy)
            0 aufbauSubshells occupations : ℝ)
          + informationWeight * informationStress occupations
          + cartanWeight * cartanStress occupations
          + icosahedralWeight * icosahedralStress occupations := by
  rfl

end AtomicHamiltonianEnergyFunctional

/-- A ground-state atomic occupation is a Pauli-valid row that minimizes one global score among all
Pauli-valid rows with the same electron count. -/
structure AtomicVariationalGroundState (E : KnownElement) (Φ : AtomicEnergyFunctional) where
  occupations : List Nat
  valid : ValidAtomicOccupation E.val occupations
  minimal :
    ∀ occupations',
      ValidAtomicOccupation E.val occupations' →
        Φ.totalScore occupations <= Φ.totalScore occupations'

/-- View a variational ground-state row as an atomic configuration. -/
def AtomicVariationalGroundState.toAtomicConfiguration
    {E : KnownElement} {Φ : AtomicEnergyFunctional}
    (G : AtomicVariationalGroundState E Φ) : AtomicConfiguration where
  atomicNumber := E.val
  subshells := aufbauSubshells
  occupations := G.occupations
  pauli := G.valid.1
  electron_count := G.valid.2

lemma AtomicVariationalGroundState.score_le
    {E : KnownElement} {Φ : AtomicEnergyFunctional}
    (G : AtomicVariationalGroundState E Φ) (occupations' : List Nat)
    (hvalid : ValidAtomicOccupation E.val occupations') :
    Φ.totalScore G.occupations <= Φ.totalScore occupations' :=
  G.minimal occupations' hvalid

/-- If some valid row scores strictly below the Aufbau row, then the Aufbau row is not the
variational ground state.  This is the formal replacement for treating such a row as an external
"exception": the single score decides it. -/
lemma aufbau_not_groundState_of_lower_valid_occupation
    (E : KnownElement) (Φ : AtomicEnergyFunctional) (occupations : List Nat)
    (hvalid : ValidAtomicOccupation E.val occupations)
    (hlower :
      Φ.totalScore occupations < Φ.totalScore (knownElementConfiguration E).occupations) :
    ¬ ∃ G : AtomicVariationalGroundState E Φ,
        G.occupations = (knownElementConfiguration E).occupations := by
  intro h
  rcases h with ⟨G, hG⟩
  have hle := G.score_le occupations hvalid
  rw [hG] at hle
  linarith

/-- A first-77 variational model is a ground-state proof for every row `Z = 1,...,77`. -/
def First77VariationalModel (Φ : AtomicEnergyFunctional) : Type :=
  ∀ i : Fin 77, AtomicVariationalGroundState (first77KnownElement i) Φ

/-- Evaluate a first-77 variational model into its computed atomic configuration table. -/
def first77VariationalConfigurationTable
    {Φ : AtomicEnergyFunctional} (M : First77VariationalModel Φ) (i : Fin 77) :
    AtomicConfiguration :=
  (M i).toAtomicConfiguration

/-- Every row computed by a first-77 variational model has the correct electron count and satisfies
the Pauli capacity bounds. -/
lemma first77VariationalConfigurationTable_checked
    {Φ : AtomicEnergyFunctional} (M : First77VariationalModel Φ) (i : Fin 77) :
    ((first77VariationalConfigurationTable M i).occupations.sum = i.val + 1)
      ∧ PauliValidCounts
          (first77VariationalConfigurationTable M i).occupations aufbauCapacities := by
  have h := (M i).valid
  exact ⟨by exact h.2, by exact h.1⟩

/-- A `Z = 78,...,118` variational model is a ground-state proof for every remaining named
neutral element after iridium. -/
def Late41VariationalModel (Φ : AtomicEnergyFunctional) : Type :=
  ∀ i : Fin 41, AtomicVariationalGroundState (late41KnownElement i) Φ

/-- Evaluate a `Z = 78,...,118` variational model into its computed atomic configuration table. -/
def late41VariationalConfigurationTable
    {Φ : AtomicEnergyFunctional} (M : Late41VariationalModel Φ) (i : Fin 41) :
    AtomicConfiguration :=
  (M i).toAtomicConfiguration

/-- Every row computed by a `Z = 78,...,118` variational model has the correct electron count and
satisfies the Pauli capacity bounds. -/
lemma late41VariationalConfigurationTable_checked
    {Φ : AtomicEnergyFunctional} (M : Late41VariationalModel Φ) (i : Fin 41) :
    ((late41VariationalConfigurationTable M i).occupations.sum = i.val + 78)
      ∧ PauliValidCounts
          (late41VariationalConfigurationTable M i).occupations aufbauCapacities := by
  have h := (M i).valid
  exact ⟨by exact h.2, by exact h.1⟩

/-- A complete `Z = 1,...,118` variational periodic-table model: every named neutral element is a
ground-state row for the same atomic energy functional. -/
def All118VariationalModel (Φ : AtomicEnergyFunctional) : Type :=
  ∀ i : Fin 118, AtomicVariationalGroundState (all118KnownElement i) Φ

/-- Evaluate a complete `Z = 1,...,118` variational model into its computed atomic configuration
table. -/
def all118VariationalConfigurationTable
    {Φ : AtomicEnergyFunctional} (M : All118VariationalModel Φ) (i : Fin 118) :
    AtomicConfiguration :=
  (M i).toAtomicConfiguration

/-- Every row computed by a complete `Z = 1,...,118` variational model has the correct electron count
and satisfies the Pauli capacity bounds. -/
lemma all118VariationalConfigurationTable_checked
    {Φ : AtomicEnergyFunctional} (M : All118VariationalModel Φ) (i : Fin 118) :
    ((all118VariationalConfigurationTable M i).occupations.sum = i.val + 1)
      ∧ PauliValidCounts
          (all118VariationalConfigurationTable M i).occupations aufbauCapacities := by
  have h := (M i).valid
  exact ⟨by exact h.2, by exact h.1⟩

/-! ### Local transition-metal minimizers without exception tables -/

/-- A Pauli-valid allocation of `total` valence electrons between one open inner subshell with
spatial degeneracy `gInner` and one outer `s` subshell. -/
def TwoSubshellValid (gInner total innerOcc outerOcc : Nat) : Prop :=
  innerOcc <= 2 * gInner ∧ outerOcc <= 2 ∧ innerOcc + outerOcc = total

/-- Pauli-valid `d/s` allocations with six valence electrons are exactly the three neighboring
rows around the chromium half-filled configuration. -/
private lemma TwoSubshellValid.d_six_cases {innerOcc outerOcc : Nat}
    (hvalid : TwoSubshellValid dSpatialDegeneracy 6 innerOcc outerOcc) :
    (innerOcc = 6 ∧ outerOcc = 0)
      ∨ (innerOcc = 5 ∧ outerOcc = 1)
      ∨ (innerOcc = 4 ∧ outerOcc = 2) := by
  unfold TwoSubshellValid dSpatialDegeneracy at hvalid
  omega

/-- Pauli-valid `d/s` allocations with eleven valence electrons are the two rows adjacent to the
copper filled-shell configuration; the formal `d11 s0` row violates Pauli capacity. -/
private lemma TwoSubshellValid.d_eleven_cases {innerOcc outerOcc : Nat}
    (hvalid : TwoSubshellValid dSpatialDegeneracy 11 innerOcc outerOcc) :
    (innerOcc = 10 ∧ outerOcc = 1) ∨ (innerOcc = 9 ∧ outerOcc = 2) := by
  unfold TwoSubshellValid dSpatialDegeneracy at hvalid
  omega

/-- Pauli-valid `d/s` allocations with ten valence electrons are exactly the three rows around the
palladium filled-shell configuration. -/
private lemma TwoSubshellValid.d_ten_cases {innerOcc outerOcc : Nat}
    (hvalid : TwoSubshellValid dSpatialDegeneracy 10 innerOcc outerOcc) :
    (innerOcc = 10 ∧ outerOcc = 0)
      ∨ (innerOcc = 9 ∧ outerOcc = 1)
      ∨ (innerOcc = 8 ∧ outerOcc = 2) := by
  unfold TwoSubshellValid dSpatialDegeneracy at hvalid
  omega

/-- The local two-subshell score already used by the Hund gap formulas. -/
def twoSubshellScore
    (inner outer : HundSubshellEnergy) (gInner innerOcc outerOcc : Nat) : ℤ :=
  hundTwoSubshellEnergy inner outer gInner innerOcc outerOcc

/-- A local two-subshell ground state: a Pauli-valid allocation minimizing the same Hund score over
all allocations with the same electron count. -/
structure TwoSubshellGroundState
    (inner outer : HundSubshellEnergy) (gInner total innerOcc outerOcc : Nat) where
  valid : TwoSubshellValid gInner total innerOcc outerOcc
  minimal :
    ∀ innerOcc' outerOcc',
      TwoSubshellValid gInner total innerOcc' outerOcc' →
        twoSubshellScore inner outer gInner innerOcc outerOcc
          <= twoSubshellScore inner outer gInner innerOcc' outerOcc'

/-- The next allocation after the half-filled `d5 s1` row, namely `d6 s0`, is higher exactly when
`level(d)-level(s)+pairing(d)` is nonnegative. -/
lemma d5_s1_to_d6_s0_gap_eq (inner outer : HundSubshellEnergy) :
    hundTwoSubshellEnergy inner outer dSpatialDegeneracy 6 0
        - hundTwoSubshellEnergy inner outer dSpatialDegeneracy 5 1
      = inner.levelCost - outer.levelCost + inner.pairingPenalty := by
  simp [hundTwoSubshellEnergy, hundSubshellEnergy, dSpatialDegeneracy,
    hundPairingCount, hundExchangePairCount, chooseTwo]
  ring

/-- The last allocation before the filled `d10 s0` row, namely `d9 s1`, differs by
`level(d)-level(s)+pairing(d)-4 exchange(d)`. -/
lemma d9_s1_to_d10_s0_gap_eq (inner outer : HundSubshellEnergy) :
    hundTwoSubshellEnergy inner outer dSpatialDegeneracy 10 0
        - hundTwoSubshellEnergy inner outer dSpatialDegeneracy 9 1
      = inner.levelCost - outer.levelCost + inner.pairingPenalty
        - 4 * inner.exchangeReward := by
  simp [hundTwoSubshellEnergy, hundSubshellEnergy, dSpatialDegeneracy,
    hundPairingCount, hundExchangePairCount, chooseTwo]
  ring

/-- If `d5 s1` beats `d4 s2` and also beats `d6 s0`, then it is the local ground state among all
Pauli-valid allocations of six electrons across the `d/s` block. -/
lemma d5_s1_twoSubshellGroundState_of_inequalities
    (inner outer : HundSubshellEnergy)
    (h42 :
      twoSubshellScore inner outer dSpatialDegeneracy 5 1
        <= twoSubshellScore inner outer dSpatialDegeneracy 4 2)
    (h60 :
      twoSubshellScore inner outer dSpatialDegeneracy 5 1
        <= twoSubshellScore inner outer dSpatialDegeneracy 6 0) :
    TwoSubshellGroundState inner outer dSpatialDegeneracy 6 5 1 := by
  refine ⟨?_, ?_⟩
  · unfold TwoSubshellValid dSpatialDegeneracy
    omega
  · intro innerOcc' outerOcc' hvalid
    rcases TwoSubshellValid.d_six_cases hvalid with hcase | hcase | hcase
    · rcases hcase with ⟨rfl, rfl⟩
      simpa using h60
    · rcases hcase with ⟨rfl, rfl⟩
      rfl
    · rcases hcase with ⟨rfl, rfl⟩
      simpa using h42

/-- Half-filled `d5 s1` is selected by one global local minimization, not by an exception table:
the first inequality makes `d5 s1` beat `d4 s2`, while the second prevents the extra promotion to
`d6 s0`. -/
lemma d5_s1_twoSubshellGroundState_of_gap_conditions
    (inner outer : HundSubshellEnergy)
    (hpromote : hundOneElectronPromotionGap inner outer dSpatialDegeneracy 4 <= 0)
    (hstop : 0 <= inner.levelCost - outer.levelCost + inner.pairingPenalty) :
    TwoSubshellGroundState inner outer dSpatialDegeneracy 6 5 1 := by
  apply d5_s1_twoSubshellGroundState_of_inequalities
  · have hpromote' :
        hundTwoSubshellEnergy inner outer dSpatialDegeneracy 5 1
            - hundTwoSubshellEnergy inner outer dSpatialDegeneracy 4 2 <= 0 := by
      simpa [hundOneElectronPromotionGap] using hpromote
    unfold twoSubshellScore
    omega
  · unfold twoSubshellScore
    rw [← d5_s1_to_d6_s0_gap_eq inner outer] at hstop
    omega

/-- If `d10 s1` beats `d9 s2`, then it is the local ground state among all Pauli-valid allocations
of eleven electrons across the `d/s` block.  The invalid `d11 s0` row is rejected by the Pauli bound,
not by an exception list. -/
lemma d10_s1_twoSubshellGroundState_of_gap_nonpositive
    (inner outer : HundSubshellEnergy)
    (hgap : hundOneElectronPromotionGap inner outer dSpatialDegeneracy 9 <= 0) :
    TwoSubshellGroundState inner outer dSpatialDegeneracy 11 10 1 := by
  have h92 :
      twoSubshellScore inner outer dSpatialDegeneracy 10 1
        <= twoSubshellScore inner outer dSpatialDegeneracy 9 2 := by
    have hgap' :
        hundTwoSubshellEnergy inner outer dSpatialDegeneracy 10 1
            - hundTwoSubshellEnergy inner outer dSpatialDegeneracy 9 2 <= 0 := by
      simpa [hundOneElectronPromotionGap] using hgap
    unfold twoSubshellScore
    omega
  refine ⟨?_, ?_⟩
  · unfold TwoSubshellValid dSpatialDegeneracy
    omega
  · intro innerOcc' outerOcc' hvalid
    rcases TwoSubshellValid.d_eleven_cases hvalid with hcase | hcase
    · rcases hcase with ⟨rfl, rfl⟩
      rfl
    · rcases hcase with ⟨rfl, rfl⟩
      simpa using h92

/-- If filled `d10 s0` beats both neighboring allocations `d8 s2` and `d9 s1`, then it is the local
ground state for ten valence electrons. -/
lemma d10_s0_twoSubshellGroundState_of_inequalities
    (inner outer : HundSubshellEnergy)
    (h82 :
      twoSubshellScore inner outer dSpatialDegeneracy 10 0
        <= twoSubshellScore inner outer dSpatialDegeneracy 8 2)
    (h91 :
      twoSubshellScore inner outer dSpatialDegeneracy 10 0
        <= twoSubshellScore inner outer dSpatialDegeneracy 9 1) :
    TwoSubshellGroundState inner outer dSpatialDegeneracy 10 10 0 := by
  refine ⟨?_, ?_⟩
  · unfold TwoSubshellValid dSpatialDegeneracy
    omega
  · intro innerOcc' outerOcc' hvalid
    rcases TwoSubshellValid.d_ten_cases hvalid with hcase | hcase | hcase
    · rcases hcase with ⟨rfl, rfl⟩
      rfl
    · rcases hcase with ⟨rfl, rfl⟩
      simpa using h91
    · rcases hcase with ⟨rfl, rfl⟩
      simpa using h82

/-- Filled `d10 s0` is selected by the same local minimization when the double-promotion row beats
`d8 s2` and the last one-electron step also lowers the score. -/
lemma d10_s0_twoSubshellGroundState_of_gap_conditions
    (inner outer : HundSubshellEnergy)
    (hdouble : hundTwoElectronPromotionGap inner outer dSpatialDegeneracy 8 <= 0)
    (hlast :
      inner.levelCost - outer.levelCost + inner.pairingPenalty
        - 4 * inner.exchangeReward <= 0) :
    TwoSubshellGroundState inner outer dSpatialDegeneracy 10 10 0 := by
  apply d10_s0_twoSubshellGroundState_of_inequalities
  · have hdouble' :
        hundTwoSubshellEnergy inner outer dSpatialDegeneracy 10 0
            - hundTwoSubshellEnergy inner outer dSpatialDegeneracy 8 2 <= 0 := by
      simpa [hundTwoElectronPromotionGap] using hdouble
    unfold twoSubshellScore
    omega
  · unfold twoSubshellScore
    rw [← d9_s1_to_d10_s0_gap_eq inner outer] at hlast
    omega

/-! ### Hamiltonian-integral forms of the transition-metal inequalities -/

/-- Integral-level Cr-type half-filled gap.  The same inequality is now stated directly in terms of
the integer-scaled one-body/direct-Coulomb/exchange matrix elements extracted from the
second-quantized electronic Hamiltonian. -/
lemma d4_s2_to_d5_s1_gap_eq_integrals
    (inner outer : IntegerScaledSubshellHamiltonianIntegrals) :
    hundOneElectronPromotionGap inner.toHundSubshellEnergy outer.toHundSubshellEnergy
        dSpatialDegeneracy 4
      = inner.oneElectronLevel - outer.oneElectronLevel - outer.sameOrbitalDirectCoulomb
        - 4 * inner.sameSpinExchangeCoulomb := by
  simpa using d4_s2_to_d5_s1_gap_eq inner.toHundSubshellEnergy outer.toHundSubshellEnergy

/-- Integral-level Cu-type filled-shell gap. -/
lemma d9_s2_to_d10_s1_gap_eq_integrals
    (inner outer : IntegerScaledSubshellHamiltonianIntegrals) :
    hundOneElectronPromotionGap inner.toHundSubshellEnergy outer.toHundSubshellEnergy
        dSpatialDegeneracy 9
      = inner.oneElectronLevel - outer.oneElectronLevel + inner.sameOrbitalDirectCoulomb
        - outer.sameOrbitalDirectCoulomb - 4 * inner.sameSpinExchangeCoulomb := by
  simpa using d9_s2_to_d10_s1_gap_eq inner.toHundSubshellEnergy outer.toHundSubshellEnergy

/-- Integral-level Pd-type double-promotion gap. -/
lemma d8_s2_to_d10_s0_gap_eq_integrals
    (inner outer : IntegerScaledSubshellHamiltonianIntegrals) :
    hundTwoElectronPromotionGap inner.toHundSubshellEnergy outer.toHundSubshellEnergy
        dSpatialDegeneracy 8
      = 2 * (inner.oneElectronLevel - outer.oneElectronLevel)
        + 2 * inner.sameOrbitalDirectCoulomb - outer.sameOrbitalDirectCoulomb
        - 7 * inner.sameSpinExchangeCoulomb := by
  simpa using d8_s2_to_d10_s0_gap_eq inner.toHundSubshellEnergy outer.toHundSubshellEnergy

/-- Integral-level `f` half-filled gap. -/
lemma f6_s2_to_f7_s1_gap_eq_integrals
    (inner outer : IntegerScaledSubshellHamiltonianIntegrals) :
    hundOneElectronPromotionGap inner.toHundSubshellEnergy outer.toHundSubshellEnergy
        fSpatialDegeneracy 6
      = inner.oneElectronLevel - outer.oneElectronLevel - outer.sameOrbitalDirectCoulomb
        - 6 * inner.sameSpinExchangeCoulomb := by
  simpa using f6_s2_to_f7_s1_gap_eq inner.toHundSubshellEnergy outer.toHundSubshellEnergy

/-- Integral-level `f` filled-shell gap. -/
lemma f13_s2_to_f14_s1_gap_eq_integrals
    (inner outer : IntegerScaledSubshellHamiltonianIntegrals) :
    hundOneElectronPromotionGap inner.toHundSubshellEnergy outer.toHundSubshellEnergy
        fSpatialDegeneracy 13
      = inner.oneElectronLevel - outer.oneElectronLevel + inner.sameOrbitalDirectCoulomb
        - outer.sameOrbitalDirectCoulomb - 6 * inner.sameSpinExchangeCoulomb := by
  simpa using f13_s2_to_f14_s1_gap_eq inner.toHundSubshellEnergy outer.toHundSubshellEnergy

/-- Integral-level local minimizer for a Cr-type `d5 s1` row.  No exception table is involved:
the row is selected when the Hamiltonian-derived integral inequality promotes `d4 s2` to `d5 s1`,
and the next `d6 s0` step is not lower. -/
lemma d5_s1_twoSubshellGroundState_of_integral_conditions
    (inner outer : IntegerScaledSubshellHamiltonianIntegrals)
    (hpromote :
      inner.oneElectronLevel - outer.oneElectronLevel - outer.sameOrbitalDirectCoulomb
        - 4 * inner.sameSpinExchangeCoulomb <= 0)
    (hstop :
      0 <= inner.oneElectronLevel - outer.oneElectronLevel
        + inner.sameOrbitalDirectCoulomb) :
    TwoSubshellGroundState inner.toHundSubshellEnergy outer.toHundSubshellEnergy
      dSpatialDegeneracy 6 5 1 := by
  apply d5_s1_twoSubshellGroundState_of_gap_conditions
  · rw [d4_s2_to_d5_s1_gap_eq_integrals]
    simpa using hpromote
  · simpa using hstop

/-- Integral-level local minimizer for a Cu-type `d10 s1` row. -/
lemma d10_s1_twoSubshellGroundState_of_integral_gap_nonpositive
    (inner outer : IntegerScaledSubshellHamiltonianIntegrals)
    (hgap :
      inner.oneElectronLevel - outer.oneElectronLevel + inner.sameOrbitalDirectCoulomb
        - outer.sameOrbitalDirectCoulomb - 4 * inner.sameSpinExchangeCoulomb <= 0) :
    TwoSubshellGroundState inner.toHundSubshellEnergy outer.toHundSubshellEnergy
      dSpatialDegeneracy 11 10 1 := by
  apply d10_s1_twoSubshellGroundState_of_gap_nonpositive
  rw [d9_s2_to_d10_s1_gap_eq_integrals]
  simpa using hgap

/-- Integral-level local minimizer for a Pd-type `d10 s0` row. -/
lemma d10_s0_twoSubshellGroundState_of_integral_conditions
    (inner outer : IntegerScaledSubshellHamiltonianIntegrals)
    (hdouble :
      2 * (inner.oneElectronLevel - outer.oneElectronLevel)
        + 2 * inner.sameOrbitalDirectCoulomb - outer.sameOrbitalDirectCoulomb
        - 7 * inner.sameSpinExchangeCoulomb <= 0)
    (hlast :
      inner.oneElectronLevel - outer.oneElectronLevel + inner.sameOrbitalDirectCoulomb
        - 4 * inner.sameSpinExchangeCoulomb <= 0) :
    TwoSubshellGroundState inner.toHundSubshellEnergy outer.toHundSubshellEnergy
      dSpatialDegeneracy 10 10 0 := by
  apply d10_s0_twoSubshellGroundState_of_gap_conditions
  · rw [d8_s2_to_d10_s0_gap_eq_integrals]
    simpa using hdouble
  · simpa using hlast

section HamiltonianDerivedTransitionMetalRows

variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
variable {ι : Type*} [Fintype ι] {H : SecondQuantizedElectronicHamiltonian A ι}

/-- Convert an outer one-electron level scale to the inner subshell's common energy unit. -/
private lemma SubshellHamiltonianEnergyDerivation.outerLevel_scales_common
    (inner outer : SubshellHamiltonianEnergyDerivation H)
    (hunit : outer.energyUnit = inner.energyUnit) :
    (outer.oneElectronLevel : ℝ) * inner.energyUnit =
      (H.oneBodyInt outer.levelOrbital outer.levelOrbital).re := by
  rw [← hunit]
  exact outer.oneElectronLevel_scales

/-- Convert an outer direct-Coulomb scale to the inner subshell's common energy unit. -/
private lemma SubshellHamiltonianEnergyDerivation.outerDirectCoulomb_scales_common
    (inner outer : SubshellHamiltonianEnergyDerivation H)
    (hunit : outer.energyUnit = inner.energyUnit) :
    (outer.sameOrbitalDirectCoulomb : ℝ) * inner.energyUnit =
      (H.twoBodyInt outer.levelOrbital outer.pairedOrbital
        outer.levelOrbital outer.pairedOrbital).re := by
  rw [← hunit]
  exact outer.directCoulomb_scales

/-- Common-unit scaling facts for the outer subshell entries used in transition-metal gaps. -/
private lemma SubshellHamiltonianEnergyDerivation.outerScales_common
    (inner outer : SubshellHamiltonianEnergyDerivation H)
    (hunit : outer.energyUnit = inner.energyUnit) :
    (outer.oneElectronLevel : ℝ) * inner.energyUnit =
        (H.oneBodyInt outer.levelOrbital outer.levelOrbital).re
      ∧ (outer.sameOrbitalDirectCoulomb : ℝ) * inner.energyUnit =
        (H.twoBodyInt outer.levelOrbital outer.pairedOrbital
          outer.levelOrbital outer.pairedOrbital).re := by
  exact ⟨
    SubshellHamiltonianEnergyDerivation.outerLevel_scales_common (H := H) inner outer hunit,
    SubshellHamiltonianEnergyDerivation.outerDirectCoulomb_scales_common (H := H)
      inner outer hunit⟩

/-- Hamiltonian-derived local minimizer for a Cr-type `d5 s1` row.  The coefficients in the
inequalities are the integer representatives whose scaling equalities are stored in the two
`SubshellHamiltonianEnergyDerivation` records. -/
lemma d5_s1_twoSubshellGroundState_of_hamiltonian_derivation_conditions
    (inner outer : SubshellHamiltonianEnergyDerivation H)
    (hpromote :
      inner.oneElectronLevel - outer.oneElectronLevel - outer.sameOrbitalDirectCoulomb
        - 4 * inner.sameSpinExchangeCoulomb <= 0)
    (hstop :
      0 <= inner.oneElectronLevel - outer.oneElectronLevel
        + inner.sameOrbitalDirectCoulomb) :
    TwoSubshellGroundState inner.toHundSubshellEnergy outer.toHundSubshellEnergy
      dSpatialDegeneracy 6 5 1 := by
  exact
    d5_s1_twoSubshellGroundState_of_integral_conditions
      inner.toIntegerScaledIntegrals outer.toIntegerScaledIntegrals hpromote hstop

/-- Hamiltonian-derived local minimizer for a Cu-type `d10 s1` row. -/
lemma d10_s1_twoSubshellGroundState_of_hamiltonian_derivation_gap_nonpositive
    (inner outer : SubshellHamiltonianEnergyDerivation H)
    (hgap :
      inner.oneElectronLevel - outer.oneElectronLevel + inner.sameOrbitalDirectCoulomb
        - outer.sameOrbitalDirectCoulomb - 4 * inner.sameSpinExchangeCoulomb <= 0) :
    TwoSubshellGroundState inner.toHundSubshellEnergy outer.toHundSubshellEnergy
      dSpatialDegeneracy 11 10 1 := by
  exact
    d10_s1_twoSubshellGroundState_of_integral_gap_nonpositive
      inner.toIntegerScaledIntegrals outer.toIntegerScaledIntegrals hgap

/-- Hamiltonian-derived local minimizer for a Pd-type `d10 s0` row. -/
lemma d10_s0_twoSubshellGroundState_of_hamiltonian_derivation_conditions
    (inner outer : SubshellHamiltonianEnergyDerivation H)
    (hdouble :
      2 * (inner.oneElectronLevel - outer.oneElectronLevel)
        + 2 * inner.sameOrbitalDirectCoulomb - outer.sameOrbitalDirectCoulomb
        - 7 * inner.sameSpinExchangeCoulomb <= 0)
    (hlast :
      inner.oneElectronLevel - outer.oneElectronLevel + inner.sameOrbitalDirectCoulomb
        - 4 * inner.sameSpinExchangeCoulomb <= 0) :
    TwoSubshellGroundState inner.toHundSubshellEnergy outer.toHundSubshellEnergy
      dSpatialDegeneracy 10 10 0 := by
  exact
    d10_s0_twoSubshellGroundState_of_integral_conditions
      inner.toIntegerScaledIntegrals outer.toIntegerScaledIntegrals hdouble hlast

/-- The Cr-type half-filled promotion gap, multiplied by the common energy unit, is exactly the
corresponding real linear combination of Hamiltonian matrix elements. -/
lemma d4_s2_to_d5_s1_gap_scales_hamiltonian_matrix_elements
    (inner outer : SubshellHamiltonianEnergyDerivation H)
    (hunit : outer.energyUnit = inner.energyUnit) :
    (hundOneElectronPromotionGap inner.toHundSubshellEnergy outer.toHundSubshellEnergy
        dSpatialDegeneracy 4 : ℝ) * inner.energyUnit
      =
        (H.oneBodyInt inner.levelOrbital inner.levelOrbital).re
          - (H.oneBodyInt outer.levelOrbital outer.levelOrbital).re
          - (H.twoBodyInt outer.levelOrbital outer.pairedOrbital
              outer.levelOrbital outer.pairedOrbital).re
          - 4 * (H.twoBodyInt inner.levelOrbital inner.exchangeOrbital
              inner.exchangeOrbital inner.levelOrbital).re := by
  obtain ⟨houterLevel, houterDirect⟩ :=
    SubshellHamiltonianEnergyDerivation.outerScales_common (H := H) inner outer hunit
  rw [d4_s2_to_d5_s1_gap_eq]
  simp only [SubshellHamiltonianEnergyDerivation.toHundSubshellEnergy_levelCost,
    SubshellHamiltonianEnergyDerivation.toHundSubshellEnergy_pairingPenalty,
    SubshellHamiltonianEnergyDerivation.toHundSubshellEnergy_exchangeReward]
  rw [← inner.oneElectronLevel_scales, ← houterLevel, ← houterDirect,
    ← inner.exchangeCoulomb_scales]
  push_cast
  ring

/-- The Cu-type filled-shell one-electron promotion gap, scaled by the common energy unit, is the
matching real matrix-element combination of the second-quantized Hamiltonian. -/
lemma d9_s2_to_d10_s1_gap_scales_hamiltonian_matrix_elements
    (inner outer : SubshellHamiltonianEnergyDerivation H)
    (hunit : outer.energyUnit = inner.energyUnit) :
    (hundOneElectronPromotionGap inner.toHundSubshellEnergy outer.toHundSubshellEnergy
        dSpatialDegeneracy 9 : ℝ) * inner.energyUnit
      =
        (H.oneBodyInt inner.levelOrbital inner.levelOrbital).re
          - (H.oneBodyInt outer.levelOrbital outer.levelOrbital).re
          + (H.twoBodyInt inner.levelOrbital inner.pairedOrbital
              inner.levelOrbital inner.pairedOrbital).re
          - (H.twoBodyInt outer.levelOrbital outer.pairedOrbital
              outer.levelOrbital outer.pairedOrbital).re
          - 4 * (H.twoBodyInt inner.levelOrbital inner.exchangeOrbital
              inner.exchangeOrbital inner.levelOrbital).re := by
  obtain ⟨houterLevel, houterDirect⟩ :=
    SubshellHamiltonianEnergyDerivation.outerScales_common (H := H) inner outer hunit
  rw [d9_s2_to_d10_s1_gap_eq]
  simp only [SubshellHamiltonianEnergyDerivation.toHundSubshellEnergy_levelCost,
    SubshellHamiltonianEnergyDerivation.toHundSubshellEnergy_pairingPenalty,
    SubshellHamiltonianEnergyDerivation.toHundSubshellEnergy_exchangeReward]
  rw [← inner.oneElectronLevel_scales, ← houterLevel, ← inner.directCoulomb_scales,
    ← houterDirect, ← inner.exchangeCoulomb_scales]
  push_cast
  ring

/-- The Pd-type two-electron promotion gap, scaled by the common energy unit, is the corresponding
two-electron real matrix-element combination of the source Hamiltonian. -/
lemma d8_s2_to_d10_s0_gap_scales_hamiltonian_matrix_elements
    (inner outer : SubshellHamiltonianEnergyDerivation H)
    (hunit : outer.energyUnit = inner.energyUnit) :
    (hundTwoElectronPromotionGap inner.toHundSubshellEnergy outer.toHundSubshellEnergy
        dSpatialDegeneracy 8 : ℝ) * inner.energyUnit
      =
        2 * ((H.oneBodyInt inner.levelOrbital inner.levelOrbital).re
          - (H.oneBodyInt outer.levelOrbital outer.levelOrbital).re)
          + 2 * (H.twoBodyInt inner.levelOrbital inner.pairedOrbital
              inner.levelOrbital inner.pairedOrbital).re
          - (H.twoBodyInt outer.levelOrbital outer.pairedOrbital
              outer.levelOrbital outer.pairedOrbital).re
          - 7 * (H.twoBodyInt inner.levelOrbital inner.exchangeOrbital
              inner.exchangeOrbital inner.levelOrbital).re := by
  obtain ⟨houterLevel, houterDirect⟩ :=
    SubshellHamiltonianEnergyDerivation.outerScales_common (H := H) inner outer hunit
  rw [d8_s2_to_d10_s0_gap_eq]
  simp only [SubshellHamiltonianEnergyDerivation.toHundSubshellEnergy_levelCost,
    SubshellHamiltonianEnergyDerivation.toHundSubshellEnergy_pairingPenalty,
    SubshellHamiltonianEnergyDerivation.toHundSubshellEnergy_exchangeReward]
  rw [← inner.oneElectronLevel_scales, ← houterLevel, ← inner.directCoulomb_scales,
    ← houterDirect, ← inner.exchangeCoulomb_scales]
  push_cast
  ring

end HamiltonianDerivedTransitionMetalRows

/-! ### Certified element-level substitution interface -/

/-- Read a natural-number list with default `0` outside its finite support.  This is used to state
local occupation changes without importing an external periodic-table row. -/
def natAt : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, Nat.succ i => natAt xs i

/-- A one-electron promotion changes exactly two subshell occupation numbers:
the inner/open shell goes from `d` to `d+1`, the outer `s` shell goes from `2` to `1`, and every
other indexed subshell is unchanged. -/
def OneElectronPromotionCounts
    (regular corrected : List Nat) (innerIndex outerIndex d : Nat) : Prop :=
  natAt regular innerIndex = d
    ∧ natAt regular outerIndex = 2
    ∧ natAt corrected innerIndex = d + 1
    ∧ natAt corrected outerIndex = 1
    ∧ ∀ k, k ≠ innerIndex → k ≠ outerIndex → natAt corrected k = natAt regular k

/-- A certified one-electron Hund promotion for an element.  The corrected occupation list is not
accepted merely by being written down: it must be the exact `inner^d outer² → inner^(d+1) outer¹`
count transform from the computed Aufbau row, and it must carry the Pauli-allowed negative Hund-gap
exception proof. -/
structure HundCertifiedPromotion (E : KnownElement) (corrected : List Nat) where
  innerIndex : Nat
  outerIndex : Nat
  gInner : Nat
  d : Nat
  innerEnergy : HundSubshellEnergy
  outerEnergy : HundSubshellEnergy
  countTransform :
    OneElectronPromotionCounts (knownElementConfiguration E).occupations corrected
      innerIndex outerIndex d
  exception : HundOneElectronException innerEnergy outerEnergy gInner d

/-- Any certified Hund promotion contains a negative promotion-gap inequality. -/
lemma HundCertifiedPromotion.negative_gap {E : KnownElement} {corrected : List Nat}
    (P : HundCertifiedPromotion E corrected) :
    hundOneElectronPromotionGap P.innerEnergy P.outerEnergy P.gInner P.d < 0 := by
  rcases P.exception with ⟨_, hlower⟩
  exact (hundOneElectronPromotion_lowers_iff_gap_negative
    P.innerEnergy P.outerEnergy P.gInner P.d).1 hlower

/-- A corrected atomic configuration is a Pauli-valid occupation list with the same electron count as
the neutral atom, plus a certified Hund promotion explaining why the substitution is energetically
allowed. -/
structure HundCorrectedConfiguration (E : KnownElement) where
  occupations : List Nat
  pauli : PauliValidCounts occupations aufbauCapacities
  electron_count : occupations.sum = E.val
  promotion : HundCertifiedPromotion E occupations

/-- Forget the Hund proof and view a certified correction as an ordinary atomic configuration. -/
def HundCorrectedConfiguration.toAtomicConfiguration {E : KnownElement}
    (C : HundCorrectedConfiguration E) : AtomicConfiguration where
  atomicNumber := E.val
  subshells := aufbauSubshells
  occupations := C.occupations
  pauli := by simpa [aufbauCapacities] using C.pauli
  electron_count := C.electron_count

/-- A corrected configuration cannot be used without the negative Hund-gap inequality that justifies
the promotion. -/
lemma HundCorrectedConfiguration.requires_negative_gap {E : KnownElement}
    (C : HundCorrectedConfiguration E) :
    hundOneElectronPromotionGap C.promotion.innerEnergy C.promotion.outerEnergy
      C.promotion.gInner C.promotion.d < 0 :=
  C.promotion.negative_gap

/-- Element-level shell model: use the computed Aufbau configuration unless a certified Hund
correction is supplied. -/
structure HundElementModel (E : KnownElement) where
  corrected : Option (HundCorrectedConfiguration E)

/-- The active configuration of an element model.  Substitution is possible only through the
`some` branch, whose payload contains the level/pairing/exchange inequality proof. -/
def HundElementModel.activeConfiguration {E : KnownElement}
    (M : HundElementModel E) : AtomicConfiguration :=
  match M.corrected with
  | none => knownElementConfiguration E
  | some C => C.toAtomicConfiguration

/-- The active configuration always has the right electron count and satisfies Pauli capacity bounds:
either it is the computed Aufbau row, or it is a certified Hund-corrected row. -/
lemma HundElementModel.activeConfiguration_checked {E : KnownElement}
    (M : HundElementModel E) :
    (M.activeConfiguration).occupations.sum = E.val
      ∧ PauliValidCounts (M.activeConfiguration).occupations aufbauCapacities := by
  cases M with
  | mk corrected =>
      cases corrected with
      | none =>
          exact ⟨knownElementConfiguration_count E, knownElementConfiguration_pauli E⟩
      | some C =>
          exact ⟨C.electron_count, C.pauli⟩

/-- If an element model substitutes a corrected row, that row includes a negative Hund-gap proof. -/
lemma HundElementModel.correction_requires_negative_gap {E : KnownElement}
    (M : HundElementModel E) (C : HundCorrectedConfiguration E)
    (hC : M.corrected = some C) :
    hundOneElectronPromotionGap C.promotion.innerEnergy C.promotion.outerEnergy
      C.promotion.gInner C.promotion.d < 0 := by
  have _ : M.corrected = some C := hC
  exact C.requires_negative_gap

/-- A first-77 element model is a certified element model for each row `Z = 1,...,77`. -/
def First77HundModel : Type :=
  ∀ i : Fin 77, HundElementModel (first77KnownElement i)

/-- The conservative first-77 model with no empirical Hund substitutions. -/
def first77AufbauOnlyHundModel : First77HundModel :=
  fun _ => ⟨none⟩

/-- Evaluate a first-77 Hund model into the active atomic configuration table. -/
def first77HundConfigurationTable (M : First77HundModel) (i : Fin 77) : AtomicConfiguration :=
  (M i).activeConfiguration

/-- Every row of a first-77 Hund model has the correct electron count and Pauli-valid occupations. -/
lemma first77HundConfigurationTable_checked (M : First77HundModel) (i : Fin 77) :
    ((first77HundConfigurationTable M i).occupations.sum = i.val + 1)
      ∧ PauliValidCounts (first77HundConfigurationTable M i).occupations aufbauCapacities := by
  have h := HundElementModel.activeConfiguration_checked (M i)
  exact ⟨by simpa [first77HundConfigurationTable, first77KnownElement] using h.1,
    by simpa [first77HundConfigurationTable] using h.2⟩

/-- A correction in any first-77 row requires the stored level/pairing/exchange inequality. -/
lemma first77Correction_requires_negative_gap
    (M : First77HundModel) (i : Fin 77)
    (C : HundCorrectedConfiguration (first77KnownElement i))
    (hC : (M i).corrected = some C) :
    hundOneElectronPromotionGap C.promotion.innerEnergy C.promotion.outerEnergy
      C.promotion.gInner C.promotion.d < 0 :=
  HundElementModel.correction_requires_negative_gap (M i) C hC

/-! ## Bridge to the Newton--Ostrovskyi icosahedral boundary carrier -/

/-- A conservative bridge from known-element shell data into the existing Ostrovskyi grouped
icosahedral boundary family.  The coefficient functions are the physical input: they say how an
atomic configuration is coarse-grained into the uniform, von-Karman, and polar vortex channels. -/
structure AtomicIcosahedralCoefficientBridge (Row BoundaryState : Type*) [Fintype Row] where
  vortexBridge : IcosahedralVortexBoundaryBridge Row BoundaryState
  uniformCoeff : KnownElement -> Real
  vonKarmanCoeff : KnownElement -> Real
  polarCoeff : KnownElement -> Real

/-- The icosahedral strength assigned to an atom by a coefficient bridge. -/
def atomicBoundaryStrength {Row BoundaryState : Type*} [Fintype Row]
    (B : AtomicIcosahedralCoefficientBridge Row BoundaryState) (E : KnownElement) : VortexStrength :=
  groupedIcosahedralStrength (B.uniformCoeff E) (B.vonKarmanCoeff E) (B.polarCoeff E)

/-- The boundary state assigned to an atom by the existing Ostrovskyi boundary interface. -/
def atomicBoundaryState {Row BoundaryState : Type*} [Fintype Row]
    (B : AtomicIcosahedralCoefficientBridge Row BoundaryState) (E : KnownElement) : BoundaryState :=
  B.vortexBridge.boundaryStateOfStrength (atomicBoundaryStrength B E)

/-- Any known-element coefficient assignment into the grouped Ostrovskyi family is a relative
equilibrium, because that grouped family was already proved to lie in `A Gamma = 0`. -/
lemma atomicBoundaryStrength_relativeEquilibrium
    {Row BoundaryState : Type*} [Fintype Row]
    (B : AtomicIcosahedralCoefficientBridge Row BoundaryState) (E : KnownElement) :
    RelativeEquilibrium B.vortexBridge.matrixData.A (atomicBoundaryStrength B E) := by
  unfold atomicBoundaryStrength
  exact groupedStrength_bridge_relativeEquilibrium B.vortexBridge
    (B.uniformCoeff E) (B.vonKarmanCoeff E) (B.polarCoeff E)

/-- Any known-element coefficient assignment into the grouped Ostrovskyi family lands in the
boundary stress channel supplied by the existing bridge. -/
lemma atomicBoundaryState_stressChannel
    {Row BoundaryState : Type*} [Fintype Row]
    (B : AtomicIcosahedralCoefficientBridge Row BoundaryState) (E : KnownElement) :
    B.vortexBridge.stressChannel (atomicBoundaryState B E) := by
  unfold atomicBoundaryState atomicBoundaryStrength
  exact groupedStrength_is_boundary_stress_channel B.vortexBridge
    (B.uniformCoeff E) (B.vonKarmanCoeff E) (B.polarCoeff E)

/-- The combined checked statement: for every known atomic number, the canonical finite
subshell configuration has exactly the right electron count, satisfies the Pauli capacity
bound, and its supplied icosahedral coarse-graining is a Newton--Ostrovskyi relative equilibrium
in the existing boundary stress channel. -/
lemma knownElement_pauli_and_ostrovskyi_bridge
    {Row BoundaryState : Type*} [Fintype Row]
    (B : AtomicIcosahedralCoefficientBridge Row BoundaryState) (E : KnownElement) :
    (knownElementConfiguration E).occupations.sum = E.val
      ∧ PauliValidCounts (knownElementConfiguration E).occupations aufbauCapacities
      ∧ RelativeEquilibrium B.vortexBridge.matrixData.A (atomicBoundaryStrength B E)
      ∧ B.vortexBridge.stressChannel (atomicBoundaryState B E) := by
  exact ⟨knownElementConfiguration_count E, knownElementConfiguration_pauli E,
    atomicBoundaryStrength_relativeEquilibrium B E, atomicBoundaryState_stressChannel B E⟩

/-- The stronger assembled interface: known-element shell filling is Pauli-valid, every Kálnay/CAR
realized subshell mode has a self-adjoint idempotent number projection, and the same atom-level
coarse-graining lands in the Newton--Ostrovskyi relative-equilibrium stress channel. -/
lemma knownElement_kalnay_pauli_and_ostrovskyi_bridge
    {A Row BoundaryState : Type*} [Ring A] [StarRing A] [Fintype Row]
    (B : AtomicIcosahedralCoefficientBridge Row BoundaryState)
    (R : (q : BoundSubshell) → SubshellKalnayRealization A q) (E : KnownElement) :
    (knownElementConfiguration E).occupations.sum = E.val
      ∧ PauliValidCounts (knownElementConfiguration E).occupations aufbauCapacities
      ∧ (∀ (q : BoundSubshell) (mode : SubshellMode q),
          star (modeNumber (R q) mode) = modeNumber (R q) mode
            ∧ modeNumber (R q) mode * modeNumber (R q) mode = modeNumber (R q) mode)
      ∧ RelativeEquilibrium B.vortexBridge.matrixData.A (atomicBoundaryStrength B E)
      ∧ B.vortexBridge.stressChannel (atomicBoundaryState B E) := by
  exact ⟨knownElementConfiguration_count E, knownElementConfiguration_pauli E,
    (fun q mode => ⟨modeNumber_selfAdjoint (R q) mode, modeNumber_idempotent (R q) mode⟩),
    atomicBoundaryStrength_relativeEquilibrium B E, atomicBoundaryState_stressChannel B E⟩

/-- The fully assembled finite atomic carrier currently available in the repo: known-element shell
filling is Pauli-valid; every subshell mode has an exterior-algebra Fock creation generator with
Pauli square zero and a Kálnay/CAR number projection; fixed Liouville occupation registers satisfy
the finite number-operator equation; and the atom-level coarse-graining lands in the existing
Newton--Ostrovskyi stress channel. -/
lemma knownElement_secondQuantized_kalnay_liouville_and_ostrovskyi_bridge
    {A Row BoundaryState : Type*} [Ring A] [StarRing A] [Fintype Row]
    (B : AtomicIcosahedralCoefficientBridge Row BoundaryState)
    (R : (q : BoundSubshell) → SubshellKalnayRealization A q) (E : KnownElement) :
    (knownElementConfiguration E).occupations.sum = E.val
      ∧ PauliValidCounts (knownElementConfiguration E).occupations aufbauCapacities
      ∧ (∀ (q : BoundSubshell) (mode : SubshellMode q),
          subshellFockCreation q mode * subshellFockCreation q mode = 0
            ∧ star (modeNumber (R q) mode) = modeNumber (R q) mode
            ∧ modeNumber (R q) mode * modeNumber (R q) mode = modeNumber (R q) mode)
      ∧ (∀ (q : BoundSubshell) (e : ℕ) (n : FixedSubshellLiouvilleOccupation q e),
          liouvilleNumberOperatorPairSum n.1 = e)
      ∧ RelativeEquilibrium B.vortexBridge.matrixData.A (atomicBoundaryStrength B E)
      ∧ B.vortexBridge.stressChannel (atomicBoundaryState B E) := by
  exact ⟨knownElementConfiguration_count E, knownElementConfiguration_pauli E,
    (fun q mode => subshellMode_secondQuantized_and_kalnay_projection (R q) mode),
    (fun q e n => fixedSubshellLiouville_numberOperator q e n),
    atomicBoundaryStrength_relativeEquilibrium B E, atomicBoundaryState_stressChannel B E⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers

end
