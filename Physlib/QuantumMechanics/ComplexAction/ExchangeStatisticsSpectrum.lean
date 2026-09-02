/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState

/-!
# The exchange-statistics spectrum: bosons, fermions, hadrons, anyons

A single **exchange phase** `ω = e^{2πis}` (the `ribbonTwist` at topological spin `s`) organizes the
statistics of quantum fields in a spacetime region:

  * **boson** `ω = +1` (integer spin `s ∈ ℤ`) — e.g. a meson,
  * **fermion** `ω = −1` (half-integer spin `s ∈ ℤ + ½`) — e.g. a quark or electron,
  * **anyon** `ω = e^{iθ}` with `ω ≠ ±1` (fractional spin) — only possible in `2+1` dimensions.

Composite particles inherit `ω^N` from their `N` constituents, so `N` fermions give `(−1)^N`: a
**baryon** (`N = 3`) is a fermion, a **meson** (`N = 2`) a boson — "fermions up to hadrons". The full
**braiding/monodromy** `ω²` (double exchange) is trivial for bosons and fermions but non-trivial for
anyons — the topological signature that distinguishes fractional statistics.

* **§A — the exchange phase** `ω = ribbonTwist s`. `exchangePhase_unit` (`‖ω‖ = 1`, on the circle);
  `IsBosonic/IsFermionic/IsAnyonic`; boson at integer spin, fermion at `½`
  (reusing `ribbonTwist_boson/fermion`), and the spin-statistics shift `ω(s+½) = −ω(s)`.
* **§B — composite (hadron) statistics** `ω^N`. `baryon_is_fermion` (`(−1)³ = −1`),
  `meson_is_boson` (`(−1)² = 1`), and the general `hadron_statistics` (`N` fermions → boson iff `N`
  even). The composite of `N` spin-½ fermions is `ribbonTwist(N/2)` (`composite_eq_ribbonTwist`).
* **§C — braiding / monodromy** `ω²` (double exchange). `monodromy_eq_ribbonTwist` (`ω² = ribbonTwist
  2s`); trivial for bosons and fermions (`boson_trivial_monodromy`, `fermion_trivial_monodromy`), but
  the **semion** anyon `s = ¼` has monodromy `−1` (`semion_nontrivial_monodromy`) — its double exchange
  equals a fermionic single exchange, the hallmark of fractional statistics.
* **§D — the region-vacuum bridge.** The bosonic/fermionic split of the Sorkin–Johnston region vacuum
  (commutator vs anticommutator, `SorkinJohnstonRegionState`) is the `ω = ±1` end of this spectrum
  (`sj_bosonic_is_boson`, `sj_fermionic_is_fermion`).

**Honest layering.** Proven: the unit-circle constraint, the boson/fermion/anyon phase values and the
spin-statistics shift, the composite `ω^N` statistics (baryon/meson), and the monodromy triviality for
`±1` with the semion counterexample. Interpretive: `ω` is the abstract exchange phase; the physical
statement that only `2+1` dimensions admit `ω ≠ ±1`, and the identification of specific hadrons/anyons,
is the modeling layer around these algebraic phase identities.

## References

* J. M. Leinaas, J. Myrheim, "On the theory of identical particles", Nuovo Cim. B 37 (1977) 1
  (anyons); F. Wilczek, "Quantum mechanics of fractional-spin particles", PRL 49 (1982) 957. Reuses
  `Hopf.ChargeConjugationRibbonTwist` (`ribbonTwist`, `ribbonTwist_boson/fermion/spin_statistics/
  half_eq_swap_sign`) and `SorkinJohnstonRegionState`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ExchangeStatisticsSpectrum

open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState


/-- **A bosonic exchange phase** `ω = +1`. -/
def IsBosonic (ω : ℂ) : Prop := ω = 1

/-- **A fermionic exchange phase** `ω = −1`. -/
def IsFermionic (ω : ℂ) : Prop := ω = -1

/-- **An anyonic exchange phase**: on the unit circle but neither `+1` nor `−1` — fractional statistics,
possible only in `2+1` dimensions. -/
def IsAnyonic (ω : ℂ) : Prop := ‖ω‖ = 1 ∧ ω ≠ 1 ∧ ω ≠ -1

/-- **The exchange phase lies on the unit circle** `‖ω‖ = 1` for every spin `s` — statistics is a pure
phase. -/
lemma exchangePhase_unit (s : ℝ) : ‖ribbonTwist s‖ = 1 := by
  rw [ribbonTwist, Complex.norm_exp]
  simp

/-- **Integer spin is bosonic** `ω(n) = +1` (reusing `ribbonTwist_boson`). -/
lemma exchangePhase_boson (n : ℤ) : IsBosonic (ribbonTwist (n : ℝ)) := ribbonTwist_boson n

/-- **Spin ½ is fermionic** `ω(½) = −1` (reusing `ribbonTwist_fermion`). -/
lemma exchangePhase_fermion : IsFermionic (ribbonTwist (1 / 2)) := ribbonTwist_fermion

/-- **The spin-statistics shift** `ω(s + ½) = −ω(s)`: adding a half-unit of spin flips the exchange
phase — bosons ↔ fermions (reusing `ribbonTwist_spin_statistics`). -/
lemma exchangePhase_shift_half (s : ℝ) : ribbonTwist (s + 1 / 2) = -ribbonTwist s :=
  ribbonTwist_spin_statistics s


/-- **The composite exchange phase** `ω^N` of `N` identical constituents (Wilczek's fusion rule for the
abelian case). -/
noncomputable def compositeExchange (ω : ℂ) (N : ℕ) : ℂ := ω ^ N

/-- **A baryon is a fermion** `(−1)³ = −1`: three fermionic quarks compose to a fermion. -/
lemma baryon_is_fermion : IsFermionic (compositeExchange (-1) 3) := by
  unfold compositeExchange IsFermionic; ring

/-- **A meson is a boson** `(−1)² = +1`: a quark–antiquark pair composes to a boson. -/
lemma meson_is_boson : IsBosonic (compositeExchange (-1) 2) := by
  unfold compositeExchange IsBosonic; ring

/-- **Hadron statistics** — `N` fermionic constituents compose to a **boson iff `N` is even**, a fermion
iff `N` is odd: `(−1)^N = +1` (even) or `−1` (odd). "Fermions up to hadrons": mesons (`N = 2`) are
bosons, baryons (`N = 3`) fermions. -/
lemma hadron_statistics (N : ℕ) :
    compositeExchange (-1) N = if Even N then 1 else -1 := by
  unfold compositeExchange
  split_ifs with h
  · exact h.neg_one_pow
  · exact (Nat.not_even_iff_odd.mp h).neg_one_pow

/-- **A composite of `N` spin-½ fermions carries total spin `N/2`** — `(−1)^N = ribbonTwist(N/2)`: the
fermion-fusion phase is the ribbon twist at the summed spin. -/
lemma composite_eq_ribbonTwist (N : ℕ) :
    compositeExchange (ribbonTwist (1 / 2)) N = ribbonTwist (N / 2) := by
  unfold compositeExchange ribbonTwist
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast; ring


/-- **The monodromy** `ω²` — the phase of a full braid (double exchange) of two identical particles. -/
noncomputable def monodromy (ω : ℂ) : ℂ := ω ^ 2

/-- **The monodromy is the ribbon twist at doubled spin** `ω² = ribbonTwist(2s)`. -/
lemma monodromy_eq_ribbonTwist (s : ℝ) : monodromy (ribbonTwist s) = ribbonTwist (2 * s) := by
  unfold monodromy ribbonTwist
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast; ring

/-- **Bosons have trivial monodromy** `ω² = 1`: a full braid of two bosons is the identity. -/
lemma boson_trivial_monodromy (n : ℤ) : monodromy (ribbonTwist (n : ℝ)) = 1 := by
  unfold monodromy; rw [ribbonTwist_boson]; ring

/-- **Fermions have trivial monodromy** `ω² = (−1)² = 1`: a full braid of two fermions is also the
identity — bosons and fermions are the only **abelian**, monodromy-trivial statistics. -/
lemma fermion_trivial_monodromy : monodromy (ribbonTwist (1 / 2)) = 1 := by
  unfold monodromy; rw [ribbonTwist_fermion]; ring

/-- **The semion has non-trivial monodromy** `ω² = −1`: the anyon at spin `¼` has a full-braid phase of
`−1` — its double exchange equals a fermion's single exchange. Non-trivial monodromy (`≠ 1`) is the
topological hallmark of fractional statistics, forbidden for bosons and fermions. -/
lemma semion_nontrivial_monodromy : monodromy (ribbonTwist (1 / 4)) = -1 := by
  rw [monodromy_eq_ribbonTwist,
    show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num, ribbonTwist_fermion]


/-- **The bosonic SJ region vacuum is the `ω = +1` end of the spectrum**: the commutator (antisymmetric)
Sorkin–Johnston vacuum (`SorkinJohnstonRegionState.bosonic_exchange_tag`) carries bosonic statistics. -/
lemma sj_bosonic_is_boson : IsBosonic (ribbonTwist 0) := bosonic_exchange_tag

/-- **The fermionic SJ region vacuum is the `ω = −1` end of the spectrum**: the anticommutator
(symmetric) Sorkin–Johnston vacuum (`SorkinJohnstonRegionState.fermionic_exchange_tag`) carries
fermionic statistics. -/
lemma sj_fermionic_is_fermion : IsFermionic (ribbonTwist (1 / 2)) := fermionic_exchange_tag

end Physlib.QuantumMechanics.ComplexAction.ExchangeStatisticsSpectrum
