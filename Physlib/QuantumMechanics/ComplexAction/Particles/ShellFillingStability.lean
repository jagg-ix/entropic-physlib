/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableShellCapacity
public import Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability
public import Physlib.QuantumMechanics.ComplexAction.Particles.AtomicShellInformationCapacityOctet
public import Physlib.QuantumMechanics.ComplexAction.PeriodicTableAufbauStructure
meta import Zil

/-!
# Shell filling: the closure ladder, groups, valence, information, particle-hole geometry

The shell-filling layer in seven namespaces (each formerly its own module):

* **Part I — `ShellFillingStability`.** The abstract closure ladder `closureCount g m = ∑_{i<m} g i`
  with its strict monotonicity (`closureCount_strictMono`), instantiated atomically
  (`atomic_closure_eq_two_nSq` — the noble-gas ladder) and nuclearly (`nuclear_closure_eq_hoMagic` —
  the magic numbers): the periodic table and the nuclear chart as one Pauli construction
  (`shell_closure_ladders_strictMono`).
* **Part II — `PeriodicGroupStructure`.** The column structure from the capacities alone: 8 main
  groups, 18 groups, 32 long-form columns (`= closureCount` ladder values, so groups and periods are
  one construction, `groups_and_periods_same_ladder`), and the eight main-group families with their
  valence positions (`halogen_one_short`).
* **Part III — `PeriodicValenceOctet`.** Ionic valence as distance to the nearest closed register
  `min(q, C−q)`: the half-shell bound, the inert closures, and the octet instances (alkali `+1`,
  halogen `−1`, tetrel `±4`, noble `0`; `octet_completion`).
* **Part IV — `ShellInformationLadder`.** The information reading: `microstateCount = 2^closureCount`
  with Hartley information equal to the bit capacity (`information_content_eq_bitCapacity`), the
  strictly increasing information staircase, the atomic `2^(2n²)` and nuclear `2^(hoMagic k)`
  registers, the 256-state octet register, and the 17-state fundamental-particle register.
* **Part V — `ShellFillingParticleHole`.** The shell distance `min(q, C−q)` unifying valence and
  magnetism (`ionicValence_eq_shellDistance`, `unpairedElectrons_eq_shellDistance`) with the
  particle-hole symmetry (`shellDistance_particle_hole`) and its mirrors (alkali↔halogen, `d³`↔`d⁷`).
* **Part VI — `AtomicIonIsoelectronic`.** Ions reaching noble-gas closures: cation/anion electron
  counts, charge = ionic valence, and the isoelectronic series (`Na⁺, Mg²⁺, Al³⁺ → 10 = Ne`;
  `Cl⁻, S²⁻, P³⁻ → 18 = Ar`).
* **Part VII — `AtomicModeBundleGeometry`.** The table as a fiber bundle over the aufbau curve: the
  spin-over-orbital subshell bundle with the Pauli capacity (`subshellBundle_card`), the 118-mode
  total space with the element↔mode bijection (`atomicMode_card`, `elementCoord`), the `2n²` radial
  fiber, and the particle-hole `Z₂` involution with its half-filled fixed point
  (`particleHole_involutive`, `particleHole_halffill_fixed`).

**Honest layering.** The ladder monotonicity, column/valence/information combinatorics, bundle
cardinalities, and the `Z₂` involution are exact, reusing the proven closed forms (`2n²`, `hoMagic`,
`2^capacity`). The chemical names, the "closed shell = stability" reading, and the Bloch-sphere /
spherical-harmonic identification of the fibers are the standard interpretations.

## References

* The aufbau / noble-gas closures and nuclear magic numbers as cumulative degeneracy sums; the
  group/block structure; G. N. Lewis (1916), the octet rule; isoelectronic ions; the Hartley measure.
  Built on `Particles.PeriodicTableShellCapacity` (both its Part I and Part II namespaces),
  `Particles.NuclearValleyOfStability`, `Particles.AtomicShellInformationCapacityOctet` (including
  its `AtomicHundMagnetism` part), `Particles.CriticalStabilityPrinciple`, and
  `ComplexAction.PeriodicTableAufbauStructure`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingStability

open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers
open Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableShellCapacity
open Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability

open Finset


/-- The **closure count** of a shell degeneracy `g` after filling `m` shells: the cumulative occupancy
`∑_{i<m} g i`. At a shell closure this is a discrete stability node (a noble gas, a magic number). -/
def closureCount (g : ℕ → ℕ) (m : ℕ) : ℕ := ∑ i ∈ range m, g i

/-- **The shell-closure ladder is strictly increasing** for any everywhere-positive degeneracy: filling one
more shell (which holds `g m > 0` fermions) strictly raises the cumulative count. The closed shells therefore
form a strictly increasing sequence of stability thresholds — the discrete-node ladder shared by the periodic
table and the nuclear chart. -/
lemma closureCount_strictMono (g : ℕ → ℕ) (hg : ∀ i, 0 < g i) : StrictMono (closureCount g) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hn := hg n
  rw [closureCount, closureCount, sum_range_succ]
  omega


/-- The **atomic shell degeneracy** `2(2l+1)` — the Pauli capacity of subshell `l` (spin doublet × magnetic
multiplet). -/
def atomicDegeneracy (l : ℕ) : ℕ := capacityOfAngularMomentum l

/-- **The atomic closure count is the shell capacity** `∑_{l<n} 2(2l+1) = 2n²` — the noble-gas closure counts
`2, 8, 18, 32` per shell (reusing `PeriodicTableShellCapacity.shellCapacity_eq_two_nSq`). -/
lemma atomic_closure_eq_two_nSq (n : ℕ) : closureCount atomicDegeneracy n = 2 * n ^ 2 := by
  have h : closureCount atomicDegeneracy n = shellCapacity n := rfl
  rw [h, shellCapacity_eq_two_nSq]

/-- Each atomic subshell holds at least one electron: `2(2l+1) > 0`. -/
lemma atomicDegeneracy_pos (l : ℕ) : 0 < atomicDegeneracy l := by
  unfold atomicDegeneracy capacityOfAngularMomentum; omega

/-- **The atomic shell closures are a strictly increasing ladder** — the aufbau / noble-gas structure. -/
lemma atomic_shells_strictMono : StrictMono (closureCount atomicDegeneracy) :=
  closureCount_strictMono atomicDegeneracy atomicDegeneracy_pos


/-- **The nuclear closure count is the oscillator magic number** `closureCount oscillatorDegeneracy (k+1) =
hoMagic k` — the cumulative shell-model occupancy `2, 8, 20, 40, 70` (reusing
`NuclearValleyOfStability.hoMagic`). -/
lemma nuclear_closure_eq_hoMagic (k : ℕ) :
    closureCount oscillatorDegeneracy (k + 1) = hoMagic k := rfl

/-- Each nuclear oscillator shell holds at least one nucleon: `(N+1)(N+2) > 0`. -/
lemma oscillatorDegeneracy_pos (N : ℕ) : 0 < oscillatorDegeneracy N := by
  unfold oscillatorDegeneracy; positivity

/-- **The nuclear shell closures are a strictly increasing ladder** — the magic numbers. -/
lemma nuclear_shells_strictMono : StrictMono (closureCount oscillatorDegeneracy) :=
  closureCount_strictMono oscillatorDegeneracy oscillatorDegeneracy_pos


/-- **The periodic table and the nuclear chart are one shell-filling ladder** — the atomic noble-gas closures
and the nuclear magic numbers are both strictly-increasing closure ladders of the *same* construction
(`closureCount_strictMono`), differing only in the degeneracy `2(2l+1)` vs `(N+1)(N+2)`. The closed shells are
the discrete stable spectrum — the finite-node side of `CriticalStabilityPrinciple` (whose particle-sector
instance is `stable_fundamental_spectrum_card = 17`). -/
lemma shell_closure_ladders_strictMono :
    StrictMono (closureCount atomicDegeneracy) ∧ StrictMono (closureCount oscillatorDegeneracy) :=
  ⟨atomic_shells_strictMono, nuclear_shells_strictMono⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingStability

/-! ## Part II — periodic-table groups and families, from the shell-filling models alone -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicGroupStructure

open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers
open Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableShellCapacity
open Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableBlocks
open Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingStability


/-- The **main-group (representative) columns** `cap(s) + cap(p) = 8` — the octet of `s`/`p` valence elements. -/
def mainGroupColumns : ℕ := capacityOfAngularMomentum 0 + capacityOfAngularMomentum 1

/-- The **modern group columns** `cap(s) + cap(p) + cap(d) = 18` — adding the ten transition-metal columns. -/
def groupColumns : ℕ := mainGroupColumns + capacityOfAngularMomentum 2

/-- The **long-form columns** `cap(s)+cap(p)+cap(d)+cap(f) = 32` — adding the fourteen lanthanide/actinide
columns. -/
def longFormColumns : ℕ := groupColumns + capacityOfAngularMomentum 3

/-- **There are 8 main-group columns** (the octet). -/
lemma mainGroupColumns_eq : mainGroupColumns = 8 := by decide

/-- **There are 18 groups** in the modern periodic table. -/
lemma groupColumns_eq : groupColumns = 18 := by decide

/-- **There are 32 long-form columns.** -/
lemma longFormColumns_eq : longFormColumns = 32 := by decide

/-- **The 18 groups are the `s`, `d`, `p` block widths** (`= blockWidth s + d + p`), tying the group count to
`PeriodicTableBlocks`. -/
lemma groupColumns_eq_block_widths :
    groupColumns = blockWidth .s + blockWidth .d + blockWidth .p := by decide


/-- **The main-group count is a closure-ladder value** `8 = closureCount atomicDegeneracy 2`. -/
lemma mainGroupColumns_eq_closure : mainGroupColumns = closureCount atomicDegeneracy 2 := by
  rw [atomic_closure_eq_two_nSq]; decide

/-- **The group count is a closure-ladder value** `18 = closureCount atomicDegeneracy 3` — the same ladder as
the period lengths and the information capacity. -/
lemma groupColumns_eq_closure : groupColumns = closureCount atomicDegeneracy 3 := by
  rw [atomic_closure_eq_two_nSq]; decide

/-- **The long-form count is a closure-ladder value** `32 = closureCount atomicDegeneracy 4`. -/
lemma longFormColumns_eq_closure : longFormColumns = closureCount atomicDegeneracy 4 := by
  rw [atomic_closure_eq_two_nSq]; decide

/-- **Groups and periods are one ladder** — the group count equals the period-3 shell capacity
`groupColumns = shellCapacity 3` (both `= closureCount atomicDegeneracy 3 = 2·3²`): the table's columns and rows
are the same cumulative-capacity construction. -/
lemma groups_and_periods_same_ladder : groupColumns = shellCapacity 3 := by
  rw [groupColumns_eq, shellCapacity_eq_two_nSq]; decide

/-- **The long-form width is a full `n=4` shell** `32 = shellCapacity 4 = 2·4²`. -/
lemma longForm_eq_shellCapacity4 : longFormColumns = shellCapacity 4 := by
  rw [longFormColumns_eq, shellCapacity_eq_two_nSq]; decide


set_option backward.isDefEq.respectTransparency false in
/-- The eight **main-group families** — the representative-element valence positions. -/
inductive MainGroupFamily
  | alkali | alkalineEarth | triel | tetrel | pnictogen | chalcogen | halogen | noble
  deriving DecidableEq, Fintype

/-- **There are eight main-group families** `= mainGroupColumns` (the octet). -/
lemma mainGroupFamily_count : Fintype.card MainGroupFamily = mainGroupColumns := by decide

/-- The **valence-electron count** of a main-group family (`s + p` occupancy, `1 … 8`). -/
def familyValence : MainGroupFamily → ℕ
  | .alkali => 1 | .alkalineEarth => 2 | .triel => 3 | .tetrel => 4
  | .pnictogen => 5 | .chalcogen => 6 | .halogen => 7 | .noble => 8

/-- **A noble gas has a full octet valence** `= mainGroupColumns = 8` — the closed representative shell. -/
lemma noble_valence_full_octet : familyValence .noble = mainGroupColumns := by decide

/-- **A halogen is one electron short of the closed shell** `7 + 1 = 8`: adding one electron completes the
octet (the noble-gas closure). -/
lemma halogen_one_short : familyValence .halogen + 1 = familyValence .noble := by decide

/-- **An alkali metal opens a new shell** with one valence electron. -/
lemma alkali_opens_shell : familyValence .alkali = 1 := rfl

end Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicGroupStructure

/-! ## Part III — ionic valence and the octet rule, as distance to the nearest closed shell -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicValenceOctet

open Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicGroupStructure


/-- **Electrons lost** to reach the lower closure — emptying the valence shell (`= q`). -/
def electronsToLose (q : ℕ) : ℕ := q

/-- **Electrons gained** to reach the upper closure — filling the shell of capacity `C` (`= C − q`). -/
def electronsToGain (C q : ℕ) : ℕ := C - q

/-- The **ionic valence** — the shorter path to a closed register, `min(q, C − q)`. -/
def ionicValence (C q : ℕ) : ℕ := min q (C - q)

/-- **You never move more than half a shell** `2 · ionicValence ≤ C`: whichever of losing or gaining is
shorter is at most half the capacity. -/
lemma ionicValence_le_half (C q : ℕ) (h : q ≤ C) : 2 * ionicValence C q ≤ C := by
  unfold ionicValence; omega

/-- **An empty shell is inert** `ionicValence C 0 = 0` — already a closed (lower) register. -/
lemma empty_shell_inert (C : ℕ) : ionicValence C 0 = 0 := by unfold ionicValence; omega

/-- **A full shell is inert** `ionicValence C C = 0` — a closed (upper) register (the noble gas). -/
lemma full_shell_inert (C : ℕ) : ionicValence C C = 0 := by unfold ionicValence; omega


/-- **An alkali metal is monovalent `+1`** — `ionicValence 8 1 = 1`, reached by losing its single `s` electron
(`Na → Na⁺`). -/
lemma alkali_valence_one : ionicValence mainGroupColumns (familyValence .alkali) = 1 := by decide

/-- **A halogen is monovalent `−1`** — `ionicValence 8 7 = 1`, reached by gaining one electron to close the
octet (`Cl → Cl⁻`). -/
lemma halogen_valence_one : ionicValence mainGroupColumns (familyValence .halogen) = 1 := by decide

/-- **A tetrel (carbon group) is tetravalent** — `ionicValence 8 4 = 4`: equidistant from both closures. -/
lemma tetrel_valence_four : ionicValence mainGroupColumns (familyValence .tetrel) = 4 := by decide

/-- **A noble gas is inert** `ionicValence 8 8 = 0` — the closed octet. -/
lemma noble_valence_zero : ionicValence mainGroupColumns (familyValence .noble) = 0 := by decide

/-- **The octet closes** — a family's valence electrons plus the electrons it gains fill the shell
`familyValence + electronsToGain = mainGroupColumns`. -/
lemma octet_completion (f : MainGroupFamily) (h : familyValence f ≤ mainGroupColumns) :
    familyValence f + electronsToGain mainGroupColumns (familyValence f) = mainGroupColumns := by
  unfold electronsToGain; omega

end Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicValenceOctet

/-! ## Part IV — the stability ladder as an information-capacity ladder -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.ShellInformationLadder

open Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingStability
open Physlib.QuantumMechanics.ComplexAction.Particles.NuclearValleyOfStability
open Physlib.QuantumMechanics.ComplexAction.Particles.CriticalStabilityPrinciple


/-- The **occupation microstate count** of `m` filled shells: `2^(closureCount g m)` — each of the
`closureCount g m` single-particle modes is an occupation bit (generalizing
`AtomicShellInformationCapacityOctet.subshellStorageCount = 2^capacity`). -/
def microstateCount (g : ℕ → ℕ) (m : ℕ) : ℕ := 2 ^ closureCount g m

/-- **The Hartley information is the bit capacity** `log₂(microstateCount) = closureCount`: the information
content of the filled-shell register equals its cumulative Pauli-mode count. -/
lemma information_content_eq_bitCapacity (g : ℕ → ℕ) (m : ℕ) :
    Nat.log 2 (microstateCount g m) = closureCount g m := by
  rw [microstateCount, Nat.log_pow (by norm_num)]

/-- **The information ladder is strictly increasing** for any everywhere-positive degeneracy: each filled shell
strictly raises the microstate count (hence the stored information). The information staircase of the periodic
table and the nuclear chart. -/
lemma microstate_ladder_strictMono (g : ℕ → ℕ) (hg : ∀ i, 0 < g i) :
    StrictMono (microstateCount g) := by
  intro a b hab
  have h := closureCount_strictMono g hg hab
  exact Nat.pow_lt_pow_right (by norm_num) h


/-- **The atomic shell information** `microstateCount = 2^(2n²)`: the occupation register of the first `n`
subshells (reusing `atomic_closure_eq_two_nSq`). -/
lemma atomic_microstates_eq (n : ℕ) : microstateCount atomicDegeneracy n = 2 ^ (2 * n ^ 2) := by
  rw [microstateCount, atomic_closure_eq_two_nSq]

/-- **The valence octet is an 8-bit register** `microstateCount atomicDegeneracy 2 = 256 = 2⁸`, matching
`AtomicShellInformationCapacityOctet.octet_storageCount` — the `s+p` valence stores `256` configurations. -/
lemma octet_register : microstateCount atomicDegeneracy 2 = 256 := by
  rw [atomic_microstates_eq]; norm_num


/-- **The nuclear shell information** `microstateCount oscillatorDegeneracy (k+1) = 2^(hoMagic k)`: the
occupation register at the `k`-th magic closure (reusing `nuclear_closure_eq_hoMagic`). -/
lemma nuclear_microstates_eq (k : ℕ) :
    microstateCount oscillatorDegeneracy (k + 1) = 2 ^ hoMagic k := by
  rw [microstateCount, nuclear_closure_eq_hoMagic]


/-- **The fundamental-particle register has 17 states** — the Standard-Model fundamental particles form a finite
information register; specifying one costs `log₂ 17` bits (the particle-sector node of the discrete stable
spectrum, `CriticalStabilityPrinciple.stable_fundamental_spectrum_card`). -/
lemma fundamental_spectrum_register :
    Fintype.card StandardModelParticleContent.SMParticle = 17 :=
  stable_fundamental_spectrum_card

end Physlib.QuantumMechanics.ComplexAction.Particles.ShellInformationLadder

/-! ## Part V — particle-hole symmetry: valence and magnetism as one shell-distance function -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingParticleHole

open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers
open Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicGroupStructure
open Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicValenceOctet
open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicHundMagnetism


/-- The **shell distance** `min(q, C − q)` — the distance from occupancy `q` to the nearer closed configuration
of a register of capacity `C`. -/
def shellDistance (C q : ℕ) : ℕ := min q (C - q)

/-- **The shell distance is at most half the capacity** `2 · shellDistance ≤ C`. -/
lemma shellDistance_le_half (C q : ℕ) (h : q ≤ C) : 2 * shellDistance C q ≤ C := by
  unfold shellDistance; omega

/-- **The shell distance vanishes at the closures** `q = 0` or `q = C`. -/
lemma shellDistance_closed_zero (C q : ℕ) (h : q = 0 ∨ q = C) : shellDistance C q = 0 := by
  unfold shellDistance; omega

/-- **Particle-hole symmetry** `shellDistance C q = shellDistance C (C − q)`: an occupancy and its
complement (electrons ↔ holes) are equidistant from closure. -/
lemma shellDistance_particle_hole (C q : ℕ) (h : q ≤ C) :
    shellDistance C q = shellDistance C (C - q) := by
  unfold shellDistance; omega


/-- **Ionic valence is the shell distance** on the shell capacity. -/
lemma ionicValence_eq_shellDistance (C q : ℕ) : ionicValence C q = shellDistance C q := rfl

/-- **The unpaired-electron count is the shell distance** on the subshell capacity `2(2l+1)`. -/
lemma unpairedElectrons_eq_shellDistance (l q : ℕ) :
    unpairedElectrons l q = shellDistance (capacityOfAngularMomentum l) q := rfl


/-- **Valence is particle-hole symmetric** — an occupancy and its complement share the ionic valence magnitude
(alkali `s¹` ↔ halogen, both `|charge| = 1`). -/
lemma valence_particle_hole (C q : ℕ) (h : q ≤ C) :
    ionicValence C q = ionicValence C (C - q) := by
  rw [ionicValence_eq_shellDistance, ionicValence_eq_shellDistance, shellDistance_particle_hole C q h]

/-- **Magnetism is particle-hole symmetric** — `q` electrons and `C − q` (holes) have the same unpaired count. -/
lemma magnetism_particle_hole (l q : ℕ) (h : q ≤ capacityOfAngularMomentum l) :
    unpairedElectrons l q = unpairedElectrons l (capacityOfAngularMomentum l - q) := by
  rw [unpairedElectrons_eq_shellDistance, unpairedElectrons_eq_shellDistance,
    shellDistance_particle_hole _ q h]

/-- **Alkali and halogen mirror** — `ionicValence 8 1 = ionicValence 8 7`: the `s¹` electron and the `p⁵`
(one-hole) shell are both one step from a closed octet. -/
lemma alkali_halogen_mirror : ionicValence mainGroupColumns 1 = ionicValence mainGroupColumns 7 := by decide

/-- **`d³` and `d⁷` share a magnetic moment** — `unpairedElectrons 2 3 = unpairedElectrons 2 7 = 3`
(`V²⁺`/`Cr³⁺` and `Co²⁺`), the electron-hole mirror across the half-filled `d⁵`. -/
lemma d3_d7_same_moment : unpairedElectrons 2 3 = unpairedElectrons 2 7 := by decide

end Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingParticleHole

/-! ## Part VI — ions and isoelectronic series: reaching a noble-gas closure -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.AtomicIonIsoelectronic

open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers
open Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicGroupStructure
open Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicValenceOctet


/-- The **cation electron count** — losing the `q` valence electrons (`Z − q`). -/
def cationElectrons (Z q : ℕ) : ℕ := Z - q

/-- The **anion electron count** — gaining `C − q` electrons to fill the valence shell (`Z + (C − q)`). -/
def anionElectrons (Z C q : ℕ) : ℕ := Z + (C - q)


/-- **An electropositive element's cation charge is its ionic valence** `q ≤ 4 ⟹ ionicValence 8 q = q`: it
loses exactly `q` electrons to reach the lower closure. -/
lemma cation_charge_eq_valence (q : ℕ) (h : q ≤ 4) :
    ionicValence mainGroupColumns q = q := by
  unfold ionicValence mainGroupColumns capacityOfAngularMomentum; omega

/-- **An electronegative element's anion charge is its ionic valence** `4 ≤ q ≤ 8 ⟹ ionicValence 8 q = 8 − q`:
it gains `8 − q` electrons to reach the upper closure. -/
lemma anion_charge_eq_valence (q : ℕ) (h : 4 ≤ q) (h2 : q ≤ 8) :
    ionicValence mainGroupColumns q = 8 - q := by
  unfold ionicValence mainGroupColumns capacityOfAngularMomentum; omega


/-- **`Na⁺` is isoelectronic with neon** — `cationElectrons 11 1 = 10`. -/
lemma sodium_cation_neon : cationElectrons 11 1 = 10 := by decide

/-- **`Mg²⁺` is isoelectronic with neon** — `cationElectrons 12 2 = 10`. -/
lemma magnesium_cation_neon : cationElectrons 12 2 = 10 := by decide

/-- **`Al³⁺` is isoelectronic with neon** — `cationElectrons 13 3 = 10`. -/
lemma aluminium_cation_neon : cationElectrons 13 3 = 10 := by decide

/-- **`Cl⁻` is isoelectronic with argon** — `anionElectrons 17 8 7 = 18`. -/
lemma chlorine_anion_argon : anionElectrons 17 8 7 = 18 := by decide

/-- **`S²⁻` is isoelectronic with argon** — `anionElectrons 16 8 6 = 18`. -/
lemma sulfur_anion_argon : anionElectrons 16 8 6 = 18 := by decide

/-- **`P³⁻` is isoelectronic with argon** — `anionElectrons 15 8 5 = 18`. -/
lemma phosphorus_anion_argon : anionElectrons 15 8 5 = 18 := by decide

/-- **`Na⁺`, `Mg²⁺`, `Al³⁺` are mutually isoelectronic** — all `10` electrons (the neon closed shell). -/
lemma na_mg_al_isoelectronic :
    cationElectrons 11 1 = cationElectrons 12 2 ∧ cationElectrons 12 2 = cationElectrons 13 3 := by decide

end Physlib.QuantumMechanics.ComplexAction.Particles.AtomicIonIsoelectronic

/-! ## Part VII — the periodic table as a fiber bundle: the geometric skeleton -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.AtomicModeBundleGeometry

open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers
open Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicTableShellCapacity
open Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingParticleHole
open Physlib.QuantumMechanics.ComplexAction.PeriodicTableAufbauStructure


/-- The **orbital multiplet** of subshell `l` — the `2l+1` magnetic states `m_l` (the spherical-harmonic base). -/
abbrev orbitalMultiplet (l : ℕ) : Type := Fin (2 * l + 1)

/-- The **spin doublet** — the two `m_s = ±½` states (the Bloch two-level `CP¹`). -/
abbrev spinDoublet : Type := Fin 2

/-- The **subshell bundle** — a spin doublet fibered over the orbital multiplet, `SubshellMode` in geometric
form. -/
abbrev subshellBundle (l : ℕ) : Type := orbitalMultiplet l × spinDoublet

/-- **The spin fiber is the two-level Bloch sphere** `card = 2`. -/
lemma spinDoublet_card : Fintype.card spinDoublet = 2 := by simp [spinDoublet]

/-- **The subshell bundle has the Pauli capacity** `card (orbital × spin) = 2(2l+1)`. -/
lemma subshellBundle_card (l : ℕ) :
    Fintype.card (subshellBundle l) = capacityOfAngularMomentum l := by
  simp only [subshellBundle, orbitalMultiplet, spinDoublet, Fintype.card_prod, Fintype.card_fin,
    capacityOfAngularMomentum]
  ring


/-- The **total mode space** — the fibers `Fin (capacity)` of each subshell, summed over the 19-subshell aufbau
base. A point is `(subshell index, mode within it) = (n, l, m_l, m_s)`. -/
abbrev AtomicMode : Type := Σ i : Fin aufbauList.length, Fin (subshellCapacity (aufbauList.get i))

/-- **There are exactly 118 modes** `card AtomicMode = 118` — the total space has one point per element (the
sum of the subshell capacities, `PeriodicTableAufbauStructure.aufbau_covers_118`). -/
lemma atomicMode_card : Fintype.card AtomicMode = 118 := by
  simp only [AtomicMode, Fintype.card_sigma, Fintype.card_fin]
  rw [← aufbau_covers_118, ← List.sum_ofFn]
  congr 1

/-- **The element-to-mode coordinate map** `Fin 118 ≃ AtomicMode` — each element is assigned a distinct
quantum-number mode `(n, l, m_l, m_s)`. Its existence is the geometric content of Pauli exclusion. -/
noncomputable def elementCoord : Fin 118 ≃ AtomicMode :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, atomicMode_card])

/-- **No two elements share a mode** — the coordinate map is injective (Pauli exclusion). -/
lemma elementCoord_injective : Function.Injective elementCoord := elementCoord.injective


/-- **The shell `n` holds `2n²` modes** — the modes with principal quantum number `n` (the concentric shell of
radius `n`), the `closureCount = 2n²` ladder read radially. -/
lemma shell_mode_count (n : ℕ) : shellCapacity n = 2 * n ^ 2 := shellCapacity_eq_two_nSq n


/-- The **particle-hole map** on a block of capacity `C`: occupancy `q ↦ C − q` (electrons ↔ holes), as an
endomorphism of `Fin (C+1)`. -/
def particleHole (C : ℕ) (q : Fin (C + 1)) : Fin (C + 1) := ⟨C - q, by omega⟩

/-- **Particle-hole is an involution** `q ↦ C − q ↦ q` — the block's `Z₂` symmetry. -/
lemma particleHole_involutive (C : ℕ) : Function.Involutive (particleHole C) := by
  intro q
  apply Fin.ext
  simp only [particleHole]
  omega

/-- The **half-filled occupancy** `q = 2l+1` of subshell `l` as an index. -/
def halfFillIndex (l : ℕ) : Fin (capacityOfAngularMomentum l + 1) :=
  ⟨2 * l + 1, by unfold capacityOfAngularMomentum; omega⟩

/-- **The half-filled shell is the fixed point** — `particleHole` fixes `q = 2l+1` (the half-filled `l`
subshell), the axis of the electron-hole mirror. -/
lemma particleHole_halffill_fixed (l : ℕ) :
    particleHole (capacityOfAngularMomentum l) (halfFillIndex l) = halfFillIndex l := by
  apply Fin.ext
  simp only [particleHole, halfFillIndex, capacityOfAngularMomentum]
  omega

/-- **Particle-hole preserves the shell distance** `shellDistance C (C − q) = shellDistance C q` — mirror
partners share valence and magnetic moment. -/
lemma particleHole_preserves_shellDistance (C q : ℕ) (h : q ≤ C) :
    shellDistance C (C - q) = shellDistance C q :=
  (shellDistance_particle_hole C q h).symm

end Physlib.QuantumMechanics.ComplexAction.Particles.AtomicModeBundleGeometry

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingStability.shell_closure_ladders_strictMono where
  formalizes @ "claim:the-periodic-table-and-nuclear-chart-are-one-strictly-increasing-shell-closure-ladder",
  caveat @ "claim:the-closed-shell-equals-stability-reading-is-the-standard-shell-model-interpretation"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicValenceOctet.octet_completion where
  formalizes @ "claim:ionic-valence-is-the-shell-distance-to-the-nearest-closed-register",
  requires @ "claim:the-periodic-table-and-nuclear-chart-are-one-strictly-increasing-shell-closure-ladder"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.ShellInformationLadder.information_content_eq_bitCapacity where
  formalizes @ "claim:the-hartley-information-of-a-filled-shell-register-is-its-cumulative-pauli-mode-count",
  requires @ "claim:the-periodic-table-and-nuclear-chart-are-one-strictly-increasing-shell-closure-ladder"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.AtomicModeBundleGeometry.atomicMode_card where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PeriodicTableAufbauStructure.aufbau_covers_118",
  formalizes @ "claim:the-periodic-table-is-a-one-hundred-eighteen-mode-fiber-bundle-over-the-aufbau-curve",
  requires @ "claim:the-periodic-table-and-nuclear-chart-are-one-strictly-increasing-shell-closure-ladder"

zil_file_contract physlib.shellFillingStability where
  promises "Shell filling as one construction: the periodic table and nuclear chart are one strictly increasing closure ladder, ionic valence is the shell distance to the nearest closed register, the Hartley information of a filled register is its cumulative Pauli-mode count, and the table is a one-hundred-eighteen-mode fiber bundle over the aufbau curve."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingStability.closureCount",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicValenceOctet.ionicValence",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.AtomicModeBundleGeometry.AtomicMode"]
  forbids_substitutes ["the closed-shell equals stability reading, the standard shell-model interpretation",
    "the Bloch-sphere identification of the bundle fibers, geometric reading only"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.ShellFillingStability.shell_closure_ladders_strictMono,
    Physlib.QuantumMechanics.ComplexAction.Particles.PeriodicValenceOctet.octet_completion,
    Physlib.QuantumMechanics.ComplexAction.Particles.ShellInformationLadder.information_content_eq_bitCapacity,
    Physlib.QuantumMechanics.ComplexAction.Particles.AtomicModeBundleGeometry.atomicMode_card]

/- ZIL-END -/
