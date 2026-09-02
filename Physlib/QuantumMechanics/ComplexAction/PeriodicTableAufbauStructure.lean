/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers
meta import Mathlib.Order.Interval.Finset.Nat
meta import Mathlib.Data.Finset.Basic
meta import Mathlib.Data.List.Basic

/-!
# A structural method for all periodic-table elements: the aufbau subshell sequence

This file gives a single **structural scheme that covers every element** of the periodic table, built on the
existing subshell register (`Particles.AtomicSubshellQuantumNumbers`, `capacityOfAngularMomentum l = 2(2l+1)`).

**The method.** An element is its atomic number `Z : ℕ`. Its ground-state electron configuration is obtained
by filling subshells `(n, l)` in **Madelung (aufbau) order** — increasing `n + l`, ties broken by increasing
`n` — each subshell holding its Pauli capacity `2(2l+1)`. The sequence of subshells is `aufbauList`; the
partial sums of its capacities (`cumulativeCapacity`) partition the atomic numbers into subshells, periods, and
blocks, so *every* `Z` maps to a definite subshell being filled. The four orbital blocks carry the
finite-rotation-group frames of `TetrahedralLorentzFrame` / `AtomicShellInformationCapacityOctet`:

| block | `l` | spatial `2l+1` | capacity `2(2l+1)` | frame |
|-------|-----|----------------|--------------------|-------|
| s + p | 0,1 | `1 + 3 = 4`    | `2 + 6 = 8`        | tetrahedral (4-fold, sp³ octet) |
| d     | 2   | `5`            | `10`               | icosahedral (5-fold, `SU(5)` `10 = Λ²(5)`) |
| f     | 3   | `7`            | `14`               | 7-fold |

* **§A — the subshell and its aufbau key.** `subshellCapacity`, `spatialDegeneracy`, `madelungKey`.
* **§B — the aufbau sequence.** `aufbauList` (the 19 subshells `1s … 7p`), `aufbau_madelung_sorted` (it is in
  strict Madelung order), `aufbau_length` (`= 19`).
* **§C — coverage of all elements.** `aufbau_covers_118` (the total capacity `1s … 7p` is `118` = all known
  elements), `noble_gas_numbers` (the cumulative capacities at the `s…p` closures are exactly the noble-gas
  atomic numbers `2, 10, 18, 36, 54, 86, 118`), and `cumulative_strictMono` (the cumulative capacities are
  strictly increasing `0 → 118`, so `[1, 118]` is partitioned into `19` subshell blocks — every element is
  covered by a unique aufbau subshell).

**Honest layering.** Every theorem is an exact `ℕ`/`List` identity over the concrete aufbau sequence (Madelung
sortedness, total `118`, noble-gas closures, strict monotonicity). The block/frame column and the reading of
`Z` as an element are the structural interpretation; the arithmetic backbone that covers all `118` elements is
what is proven. No spectroscopic anomalies (Cr, Cu, Pd, … the aufbau exceptions) or ionization dynamics are
modeled — the scheme is the ground-state aufbau ordering.

## References

* Madelung / Klechkowski `n + l` rule; aufbau principle. Built on `Particles.AtomicSubshellQuantumNumbers`
  (`capacityOfAngularMomentum`) and the block frames of `TetrahedralLorentzFrame` /
  `Particles.AtomicShellInformationCapacityOctet`.


-/

set_option autoImplicit false

open scoped BigOperators

open Physlib.QuantumMechanics.ComplexAction.Particles.AtomicSubshellQuantumNumbers

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PeriodicTableAufbauStructure


/-- A **subshell** `(n, l)` — principal and azimuthal quantum numbers. -/
abbrev Subshell : Type := ℕ × ℕ

/-- The **Pauli capacity** of a subshell `2(2l+1)`. -/
def subshellCapacity (s : Subshell) : ℕ := 2 * (2 * s.2 + 1)

/-- The subshell capacity is the angular-momentum capacity of `Particles.AtomicSubshellQuantumNumbers`. -/
lemma subshellCapacity_eq_capacity (s : Subshell) :
    subshellCapacity s = capacityOfAngularMomentum s.2 := rfl

/-- The **spatial degeneracy** `2l+1` — the number of orbitals (`s,p,d,f → 1,3,5,7`). -/
def spatialDegeneracy (s : Subshell) : ℕ := 2 * s.2 + 1

/-- The **Madelung (aufbau) sort key** `(n+l)·8 + n`: subshells fill by increasing `n+l`, ties by increasing
`n` (the `·8` encodes the lexicographic `(n+l, n)` order since `n ≤ 7`). -/
def madelungKey (s : Subshell) : ℕ := (s.1 + s.2) * 8 + s.1


/-- The **aufbau sequence** of the 19 subshells from `1s` to `7p`, in Madelung order — the filling order that
generates the whole periodic table. -/
def aufbauList : List Subshell :=
  [(1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (3, 2), (4, 1), (5, 0), (4, 2),
   (5, 1), (6, 0), (4, 3), (5, 2), (6, 1), (7, 0), (5, 3), (6, 2), (7, 1)]

/-- **The aufbau sequence is in strict Madelung order** — its keys are strictly increasing, so it is exactly
the `n+l` (Klechkowski) filling order. -/
lemma aufbau_madelung_sorted : (aufbauList.map madelungKey).Pairwise (· < ·) := by decide

/-- The aufbau sequence has the `19` subshells `1s … 7p`. -/
lemma aufbau_length : aufbauList.length = 19 := by decide


/-- **The aufbau sequence covers all `118` elements** `∑ capacities(1s … 7p) = 118`: the total electron
capacity of the ground-state filling order through `7p` is `118`, exactly the number of known elements
(period 7). -/
lemma aufbau_covers_118 : (aufbauList.map subshellCapacity).sum = 118 := by decide

/-- The **cumulative capacity** through the first `k` aufbau subshells — the atomic number at which the `k`-th
subshell finishes filling. -/
def cumulativeCapacity (k : ℕ) : ℕ := ((aufbauList.take k).map subshellCapacity).sum

/-- **The noble-gas atomic numbers** are the cumulative capacities at the `s…p` period closures:
`He 2, Ne 10, Ar 18, Kr 36, Xe 54, Rn 86, Og 118`. -/
lemma noble_gas_numbers :
    cumulativeCapacity 1 = 2 ∧ cumulativeCapacity 3 = 10 ∧ cumulativeCapacity 5 = 18
      ∧ cumulativeCapacity 8 = 36 ∧ cumulativeCapacity 11 = 54 ∧ cumulativeCapacity 15 = 86
      ∧ cumulativeCapacity 19 = 118 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The cumulative capacities strictly increase** `0 = c(0) < c(1) < … < c(19) = 118`: the aufbau filling
partitions the atomic numbers `[1, 118]` into `19` subshell blocks, so **every element is covered by a unique
aufbau subshell**. -/
lemma cumulative_strictMono : ∀ k, k < 19 → cumulativeCapacity k < cumulativeCapacity (k + 1) := by
  decide

/-- **Every element `1 ≤ Z ≤ 118` fills a definite aufbau subshell**: for each such `Z` there is a `k ∈ [1,19]`
with `cumulativeCapacity (k-1) < Z ≤ cumulativeCapacity k` — the `k`-th subshell of `aufbauList`. This is the
structural model covering the whole periodic table. -/
lemma element_covered :
    ∀ Z ∈ Finset.Icc 1 118, ∃ k ∈ Finset.Icc 1 19,
      cumulativeCapacity (k - 1) < Z ∧ Z ≤ cumulativeCapacity k := by
  native_decide

end Physlib.QuantumMechanics.ComplexAction.PeriodicTableAufbauStructure
