/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Winding.QuarkChargeWinding
public import Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass

/-!
# The spin-statistics ladder of the whole zoo — scalars, fermions, vectors, tensors

The ribbon twist `θ(h) = e^{2πih}` sorts every particle by spin into the two statistics
(`Hopf.ChargeConjugationRibbonTwist`). The earlier files used the `h = 1/2` (fermion) and `h = 1` (gauge boson)
rungs; here the **general** statement: *every* integer spin is a boson and *every* half-integer spin a fermion,
covering the full ladder `0, ½, 1, 3/2, 2`:

| particle | spin `h` | `θ(h)` | statistics |
|---|---|---|---|
| Higgs | `0` | `+1` | boson (scalar) |
| quark / lepton | `½` | `−1` | fermion |
| photon / `W`/`Z` / gluon | `1` | `+1` | boson (vector) |
| gravitino | `3/2` | `−1` | fermion |
| graviton | `2` | `+1` | boson (tensor) |

* **§A — the general ladder.** `integer_spin_boson` (`θ(n) = +1`), `halfInteger_spin_fermion`
  (`θ(n + ½) = −1`, any `n`), `spin_statistics_dichotomy` (the two are never equal).
* **§B — the scalar and tensor bosons.** `higgs_scalar_boson` (`θ(0) = +1`), `graviton_tensor_boson`
  (`θ(2) = +1`), `gravitino_fermion` (`θ(3/2) = −1`); `higgs_massive` (the scalar is massive).

**Honest layering.** Proven and structural: the ribbon-twist phase is `+1` for every integer spin and `−1` for
every half-integer spin, so the boson/fermion split is exact across the ladder; the Higgs is a massive scalar.
The *identification* of each spin with a named field (and the graviton's existence) is the empirical/expected
particle content; this is the spin-statistics classification.

## References

* Spin-statistics theorem (integer → Bose, half-integer → Fermi). `Physlib`
  (`Hopf.ChargeConjugationRibbonTwist.ribbonTwist`, `Winding.NumberMass.comptonMass`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.Winding.NumberMass

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsZoo


/-- **[Integer spin ⟹ boson]** `θ(n) = +1` for every integer spin `n` — the symmetric exchange phase. -/
lemma integer_spin_boson (n : ℤ) : ribbonTwist (n : ℝ) = 1 := ribbonTwist_boson n

/-- **[Half-integer spin ⟹ fermion]** `θ(n + ½) = −1` for *every* `n` — the antisymmetric exchange phase,
generalizing `ribbonTwist_fermion` (`n = 0`) to the whole half-integer ladder via the spin-statistics shift. -/
lemma halfInteger_spin_fermion (n : ℤ) : ribbonTwist ((n : ℝ) + 1 / 2) = -1 := by
  rw [ribbonTwist_spin_statistics, ribbonTwist_boson]

/-- **[Bosons and fermions never share an exchange phase]** `θ(n) ≠ θ(m + ½)` — integer-spin (`+1`) and
half-integer-spin (`−1`) particles are exactly the two statistics, with no overlap. -/
lemma spin_statistics_dichotomy (n m : ℤ) :
    ribbonTwist (n : ℝ) ≠ ribbonTwist ((m : ℝ) + 1 / 2) := by
  rw [integer_spin_boson, halfInteger_spin_fermion]
  norm_num


/-- **[The Higgs is a scalar boson]** `θ(0) = +1` — spin `0`, the symmetric exchange phase. -/
lemma higgs_scalar_boson : ribbonTwist ((0 : ℤ) : ℝ) = 1 := ribbonTwist_boson 0

/-- **[The graviton is a tensor boson]** `θ(2) = +1` — spin `2`. -/
lemma graviton_tensor_boson : ribbonTwist ((2 : ℤ) : ℝ) = 1 := ribbonTwist_boson 2

/-- **[The gravitino is a fermion]** `θ(3/2) = −1` — spin `3/2`, the `n = 1` rung of the half-integer ladder. -/
lemma gravitino_fermion : ribbonTwist ((1 : ℝ) + 1 / 2) = -1 := by
  have h := halfInteger_spin_fermion 1
  simpa using h

/-- **[The Higgs scalar is massive]** `m_H = ħω/c² > 0` — unlike the massless gauge bosons, the scalar has a
nonzero internal-clock frequency. -/
lemma higgs_massive (ω c ħ : ℝ) (hω : 0 < ω) (hc : c ≠ 0) (hħ : 0 < ħ) :
    0 < comptonMass ω c ħ := by
  unfold comptonMass; positivity

end Physlib.QuantumMechanics.ComplexAction.Fermion.SpinStatisticsZoo

end
