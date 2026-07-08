/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.Thermodynamics.Landauer
public import Physlib.Thermodynamics.BekensteinJacobsonEntropicBits
public import Physlib.Relativity.SemiClassical.SchwarzschildVerlinde

/-!
# The electron's spacetime region as an exclusion cell: Pauli = Dijkstra mutual exclusion, and the
# black-hole comparison

Both a **fermion mode** and a **black-hole horizon cell** are *one-bit registers governed by an exclusion
principle*. This module makes that shared structure precise and then asks, in what sense the
**spacetime region of an electron** is "like a black hole".

**The shared object — an idempotent occupation.** A fermion mode `f` (`CompositeFermionCAR.IsFermionMode`:
`f² = 0`, `{f, f†} = 1`) has occupation `n = f†f` that is a *projection*, `n² = n`
(`fermionNumber_idempotent`) — spectrum `{0, 1}`, at most one fermion. Read information-theoretically this
is **mutual exclusion**: the mode is a resource held by at most one occupant, exactly **Dijkstra's binary
semaphore** — acquire `P = f†` and release `V = f` are *nilpotent* (`(f†)² = 0`, `f² = 0`: no double-acquire,
no double-release), and the invariant "held at most once" is the idempotent `n² = n`. So **the Pauli
exclusion principle is the mutual-exclusion (mutex) invariant of an occupation register.** The same
one-bit-per-cell exclusion is what the horizon-cell bit-counting of `HorizonCell.AtomicInformationCapacity`
already uses on the atomic and horizon sides.

**The two algebras share their modular flow.** Both a fermion state (Fermi–Dirac occupation from the
Tomita–Takesaki modular automorphism, `Fermion.ModularThermalOccupation.gibbsOccupation_eq_fermiDirac`) and a
horizon (the Hawking/Unruh KMS state) have a modular Hamiltonian `H = −log ρ`, which the entropic-time
bridge (`Landauer.connesRovelli_bridge_modular_eq_complexActionNats`) identifies with `S_I/ℏ`. At one bit,
`S_I = ℏ log 2` and the modular Hamiltonian is `log 2` (`exclusionCell_modular_one_bit`).

**The electron region.** The electron *is* a fermion, so its occupation is an exclusion mutex. Its region has
the Compton radius `λ_C = ℏ/mc`; its worldline "clock" trembles at the Zitterbewegung frequency
`ω_Z = 2mc²/ℏ = 2E/ℏ` (`FrequencyTrinity`), which is exactly the **Margolus–Levitin quantum speed limit**: the
electron's exclusion cell flips at the maximal rate its rest energy allows
(`zitterbewegung_saturates_margolusLevitin`, `ω_Z · t_ML = π`).

**Boundary — the electron is *not* a black hole.** Geometrically the analogy fails: the electron's
Schwarzschild radius sits *inside* its Compton wavelength iff `2Gm² < ℏc`, i.e. `m ≪ m_Planck`
(`electron_not_blackHole`) — true for the electron by ~45 orders of magnitude, so its would-be horizon is far
below its quantum region and it has a single fermionic bit, vastly under the Bekenstein capacity of a
region its size. The correspondence is **information-algebraic** (a one-bit register with an exclusion
invariant and a modular flow, saturating the quantum speed limit), **not** geometric.

* **§A — Pauli exclusion is the Dijkstra mutual-exclusion invariant** (`mutexInvariant`,
 `pauliExclusion_is_mutexInvariant`, `dijkstra_binary_semaphore`).
* **§B — one exclusion cell is one bit; modular flow is entropic time** (`exclusionCell_modular_one_bit`,
 `fermion_horizon_one_bit`).
* **§C — the electron region saturates the Margolus–Levitin speed limit** (`margolusLevitinTime`,
 `zitterbewegung_saturates_margolusLevitin`).
* **§D — the boundary: the electron is not a black hole** (`electron_not_blackHole`).

§A/§B reuse `fermionNumber_idempotent`, `fermionMode_star_sq`,
`complexActionBits_one_bit` and `bekensteinBits` verbatim; the "Pauli = mutex" identification is a naming of
the *existing* idempotent-occupation theorem, not new dynamics. §C is an exact `field_simp` identity built on
`zitterbewegung_rest_eq_two_compton`. §D is an exact `div_lt_div_iff` inequality on the existing
`schwarzschildRadius`/`comptonWavelength`. No claim that the electron is a black hole is made or proved; the
black-hole/fermion parallel is the shared exclusion + modular + speed-limit algebra, recorded as such.

## References

* A. J. Kálnay (CAR / Pauli exclusion, `CompositeFermionCAR`); E. W. Dijkstra, *Cooperating Sequential
 Processes* (the binary semaphore `P`/`V`); N. Margolus, L. B. Levitin, *The maximum speed of dynamical
 evolution*, Physica D 120 (1998) 188 (the `t ≥ πℏ/2E` speed limit). Repo dependencies: `ComptonClock.
 FrequencyTrinity`, `Thermodynamics.{Landauer,BekensteinJacobsonEntropicBits}`,
 `Relativity.SemiClassical.SchwarzschildVerlinde`, `HorizonCell.AtomicInformationCapacity`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.Thermodynamics
open Physlib.Thermodynamics.Landauer
open Physlib.Relativity.SemiClassical

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionMutex

/-! ## §A — Pauli exclusion is the Dijkstra mutual-exclusion invariant -/

variable {A : Type*} [Ring A] [StarRing A]

/-- **The mutual-exclusion (mutex) invariant** of an occupation `n`: `n² = n`. An idempotent occupation is a
projection with spectrum `{0, 1}` — the resource it counts is held by at most one occupant, the defining
invariant of a Dijkstra binary semaphore. -/
def mutexInvariant (n : A) : Prop := n * n = n

/-- **[Pauli exclusion is the mutex invariant].** The fermion number `n = f†f` of a mode `f`
(`IsFermionMode`) satisfies the mutual-exclusion invariant `n² = n`: Pauli exclusion — "a mode is occupied at
most once" — *is* the binary-semaphore invariant "the lock is held at most once". -/
theorem pauliExclusion_is_mutexInvariant (f : A) (h : IsFermionMode f) :
    mutexInvariant (fermionNumber f) :=
  fermionNumber_idempotent f h

/-- **[The fermion mode is a Dijkstra binary semaphore].** With acquire `P = f†` and release `V = f`, both
operations are nilpotent — `(f†)² = 0` (no double-acquire) and `f² = 0` (no double-release) — and the
occupation `n = f†f` obeys the mutual-exclusion invariant `n² = n`. The Pauli mode includes the full
binary-mutex semantics: a resource that at most one occupant can hold. -/
theorem dijkstra_binary_semaphore (f : A) (h : IsFermionMode f) :
    star f * star f = 0 ∧ f * f = 0 ∧ mutexInvariant (fermionNumber f) :=
  ⟨fermionMode_star_sq f h, h.1, fermionNumber_idempotent f h⟩

/-! ## §B — one exclusion cell is one bit; modular flow is entropic time -/

/-- **[The exclusion cell's modular Hamiltonian at one bit is `log 2`].** For the Boltzmann–Wick state
`ρ = exp(−S_I/ℏ)` of an exclusion cell with exactly one bit (`S_I = ℏ log 2`), the modular Hamiltonian
`H = −log ρ` (= the entropic time `S_I/ℏ`, `connesRovelli_bridge_modular_eq_complexActionNats`) equals
`log 2` — one bit in nats. The same modular flow drives a fermion (Fermi–Dirac) and a horizon (Hawking KMS). -/
theorem exclusionCell_modular_one_bit (ħ : ℝ) (hħ : 0 < ħ) :
    -Real.log (Real.exp (-((ħ * Real.log 2) / ħ))) = Real.log 2 := by
  rw [Real.log_exp, neg_neg, mul_comm, mul_div_assoc, div_self hħ.ne', mul_one]

/-- **[One exclusion bit — fermion side and horizon side agree].** A single fermionic exclusion cell records
exactly one bit of imaginary action (`S_I = ℏ log 2` ⟹ `complexActionBits = 1`), and a single horizon
exclusion cell of area `4 ℓ_P² log 2` records exactly one Bekenstein bit. The *same* one-bit
exclusion register on the electron (fermion) side and the black-hole (horizon) side. -/
theorem fermion_horizon_one_bit (ħ ellP : ℝ) (hħ : 0 < ħ) (hℓ : ellP ≠ 0) :
    complexActionBits ħ (ħ * Real.log 2) = 1
      ∧ bekensteinBits (4 * ellP ^ 2 * Real.log 2) ellP = 1 := by
  refine ⟨complexActionBits_one_bit ħ hħ, ?_⟩
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hne : 4 * ellP ^ 2 * Real.log 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hℓ)) h2
  unfold bekensteinBits
  exact div_self hne

/-! ## §C — the electron region saturates the Margolus–Levitin speed limit -/

/-- **The Margolus–Levitin time** `t_ML = πℏ/(2E)` — the minimal time for a state of energy `E` (above its
ground state) to evolve to an orthogonal state: the quantum speed limit on flipping a one-bit register. -/
noncomputable def margolusLevitinTime (E ħ : ℝ) : ℝ := Real.pi * ħ / (2 * E)

/-- **[The electron's exclusion cell saturates the quantum speed limit] `ω_Z · t_ML = π`.** The rest-frame
Zitterbewegung frequency `ω_Z = 2mc²/ℏ = 2E/ℏ` (`zitterbewegung_rest_eq_two_compton`) times the
Margolus–Levitin time `t_ML = πℏ/(2E)` of the rest energy `E = mc²` is exactly `π`: the electron's
one-bit exclusion register flips (orthogonalizes) once per half Zitterbewegung period — the maximal rate its
rest energy permits. The electron is a *maximally fast* mutex. -/
theorem zitterbewegung_saturates_margolusLevitin (m c ħ : ℝ) (hm : 0 < m) (hc : 0 < c) (hħ : 0 < ħ) :
    zitterbewegungFrequency 0 m c ħ * margolusLevitinTime (m * c ^ 2) ħ = Real.pi := by
  rw [zitterbewegung_rest_eq_two_compton m c ħ hm.le]
  unfold comptonFrequency margolusLevitinTime
  have hmc : m * c ^ 2 ≠ 0 := by positivity
  field_simp

/-! ## §D — the boundary: the electron is not a black hole -/

/-- **[The electron is not a black hole].** The Schwarzschild radius `r_S = 2Gm/c²` lies *inside* the reduced
Compton wavelength `λ_C = ℏ/(mc)` iff `2Gm² < ℏc`, i.e. `m < m_Planck/√2`. For the electron this holds by ~45
orders of magnitude: its would-be horizon is buried far below its quantum region, so it has a single
fermionic exclusion bit rather than the vast Bekenstein capacity of a black hole its size. The
electron/black-hole parallel is the shared exclusion + modular + speed-limit *algebra*, not geometry. -/
theorem electron_not_blackHole (G m c ħ : ℝ) (hm : 0 < m) (hc : 0 < c) :
    schwarzschildRadius m G c < comptonWavelength m c ħ ↔ 2 * G * m ^ 2 < ħ * c := by
  unfold schwarzschildRadius comptonWavelength
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  constructor <;> intro h <;> nlinarith [hc, hm, mul_pos hm hc]

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionMutex

end
