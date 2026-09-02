/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ExchangeStatisticsSpectrum

/-!
# Icosahedral Bose–Einstein statistics in cold ¹²C₆₀

Formalizes the nuclear-spin-statistics selection rule confirmed by Chan et al., *Full confirmation of
icosahedral Bose–Einstein statistics in cold ¹²C₆₀*, Phys. Rev. Research **7**, L032029 (2025). The buckyball
¹²C₆₀ has 60 identical **spin-0** ¹²C nuclei — bosons. Bose–Einstein statistics forces the total molecular
wavefunction to be symmetric under any pairwise nuclear exchange, and since the 60 spin-0 nuclei admit only a
**single symmetric** (`I = 0`) nuclear-spin state, the allowed rovibrational states must be totally symmetric
(`A_g`) in the icosahedral group `I_h`. For the vibrational ground state this permits only specific rotational
levels; the rest vanish — the "missing lines" whose observation confirms Bose–Einstein statistics.

* **§A — bosonic exchange (the spin-statistics input).** `carbon12_bosonic` (`ribbonTwist 0 = +1` — spin-0 is
  bosonic, symmetric exchange, reusing `ExchangeStatisticsSpectrum`), contrasted with `carbon13_fermionic`
  (`ribbonTwist ½ = −1`); nuclear-spin-state counts `nuclearSpinStates` with `methane_spin_states` (`2⁴ = 16`,
  `= 5+9+2` the tetrahedral `A/F/E` weights) and `carbon13_60_spin_states` (`2⁶⁰`).
* **§B — the `A_g` rotational levels (`J < 30`).** `allowedJ` (the 15 symmetry-allowed levels
  `0,6,10,12,15,16,18,20,21,22,24,25,26,27,28`), `allowedJ_card` (`= 15`), `forbiddenJ` (the complement) and
  **`missing_lines_count`** (`= 15`) — the 15 missing lines; `levels_partition` (allowed ⊔ forbidden `= {0..29}`).
  `observed_missing` records the experimentally-confirmed absences `R(11,13,14,17,19,23,29)`.
* **§C — the test.** `bosonic_has_forbidden_levels` — the bosonic ¹²C₆₀ has forbidden `J` (missing lines),
  the signature that confirms Bose–Einstein statistics (and bounds violations to `1.4 × 10⁻⁸`).

**Honest layering.** The bosonic exchange phase (`ribbonTwist 0 = 1`) and the spin-state counts are exact; the
partition of `J < 30` into 15 allowed + 15 forbidden is proved from the allowed set. That allowed set — the
`J` whose `SO(3)` rotational multiplet `D^J` contains the `A_g` irrep of `I_h` — is the group-theoretic input
from Harter–Reimer / Bunker–Jensen (recorded as `allowedJ`), not re-derived here.

## References

* Chan, Liu, Scheck, Nesbitt, Ye, Rosenberg, Phys. Rev. Research **7**, L032029 (2025). Harter & Reimer,
  Chem. Phys. Lett. **194**, 230 (1992); Bunker & Jensen, Mol. Phys. **97**, 255 (1999). Built on
  `ComplexAction.ExchangeStatisticsSpectrum` (`ribbonTwist`, `IsBosonic`/`IsFermionic`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.ExchangeStatisticsSpectrum

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.IcosahedralBoseEinsteinC60


/-- **A ¹²C nucleus is a boson** — spin `0` gives the symmetric exchange phase `ribbonTwist 0 = +1`, so the
total ¹²C₆₀ wavefunction is symmetric under any pairwise nuclear exchange (Bose–Einstein). -/
lemma carbon12_bosonic : IsBosonic (ribbonTwist ((0 : ℤ) : ℝ)) := exchangePhase_boson 0

/-- **A ¹³C nucleus is a fermion** — spin `½` gives the antisymmetric exchange phase `ribbonTwist ½ = −1`
(¹³C₆₀ obeys Fermi–Dirac statistics instead). -/
lemma carbon13_fermionic : IsFermionic (ribbonTwist (1 / 2)) := exchangePhase_fermion

/-- The **number of nuclear-spin states** of `n` identical spin-½ nuclei — `2ⁿ`. -/
def nuclearSpinStates (n : ℕ) : ℕ := 2 ^ n

/-- **Methane `¹²CH₄` has 16 nuclear-spin states** `2⁴ = 16`. -/
lemma methane_spin_states : nuclearSpinStates 4 = 16 := by decide

/-- **The methane spin states split as the tetrahedral `A/F/E` weights** `5 + 9 + 2 = 16` (`meta`/`ortho`/`para`,
total nuclear spin `I = 2, 1, 0`). -/
lemma methane_weights_sum : 5 + 9 + 2 = nuclearSpinStates 4 := by decide

/-- **¹³C₆₀ has `2⁶⁰` nuclear-spin states** — 60 indistinguishable spin-½ fermions. -/
lemma carbon13_60_spin_states : nuclearSpinStates 60 = 2 ^ 60 := rfl


/-- The **symmetry-allowed rotational levels** of ground-state ¹²C₆₀ with `J < 30` — the `J` whose `SO(3)`
multiplet `D^J` contains the totally-symmetric `A_g` irrep of `I_h` (each with statistical weight `1`). -/
def allowedJ : Finset ℕ := {0, 6, 10, 12, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 28}

/-- **There are 15 allowed rotational levels** for `J < 30`. -/
lemma allowedJ_card : allowedJ.card = 15 := by decide

/-- The allowed levels all lie in `J < 30`. -/
lemma allowedJ_subset : allowedJ ⊆ Finset.range 30 := by decide

/-- The **forbidden (missing) rotational levels** `J < 30` — the complement of `allowedJ`. -/
def forbiddenJ : Finset ℕ := Finset.range 30 \ allowedJ

/-- **There are 15 missing lines** — exactly half of the `J < 30` levels are forbidden by Bose–Einstein
statistics. -/
lemma missing_lines_count : forbiddenJ.card = 15 := by decide

/-- **Allowed and forbidden levels partition `J < 30`** `allowedJ ∪ forbiddenJ = {0, …, 29}`. -/
lemma levels_partition : allowedJ ∪ forbiddenJ = Finset.range 30 := by decide

/-- **Allowed and forbidden levels are disjoint.** -/
lemma levels_disjoint : Disjoint allowedJ forbiddenJ := by decide

/-- **The experimentally-confirmed absences** `R(J = 11,13,14,17,19,23,29)` are all forbidden levels. -/
lemma observed_missing : ({11, 13, 14, 17, 19, 23, 29} : Finset ℕ) ⊆ forbiddenJ := by decide


/-- **`J = 0` is allowed**; **`J = 1` is forbidden** — the ground rotational level survives while the first
excited one is missing, the hallmark of the ¹²C₆₀ intensity pattern. -/
lemma ground_allowed_first_forbidden : 0 ∈ allowedJ ∧ 1 ∈ forbiddenJ := by decide

/-- **Bosonic ¹²C₆₀ has forbidden rotational levels** — `forbiddenJ` is nonempty: the symmetric-only
constraint of Bose–Einstein statistics deletes rotational states (the missing lines), unlike the fermionic
¹³C₆₀, which has none. -/
lemma bosonic_has_forbidden_levels : forbiddenJ.Nonempty := by decide

end Physlib.QuantumMechanics.ComplexAction.IcosahedralBoseEinsteinC60
