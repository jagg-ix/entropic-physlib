/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LorentzViolationVariableLightSpeed
public import Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian

/-!
# The variable-light-speed causal structure: `k`-boosts preserve the Sorkin `(1,1)` cone

Leverages the Sorkin/causal-set infrastructure for the variable-light-speed model. The Lorentzian form
`lorentzianForm q = (Re q)² − (Im q)²` used by the causal structure (`Rapidity.FutureIncludedLorentzian`:
`timelike`, `spacelike`, `timelikeFuture`) — and, through `CausalSetIntervalAbundance.causalSign`, by the
Sorkin–Johnston Pauli–Jordan function — is *exactly* the `k = c` interval of the model. The improvement: the
causal structure is governed by the **invariant speed `k`**, not the light speed `c`, so it is boost-invariant
and robust to the variable light speed (`nc`); the Sorkin causal order survives even where the light-cone timing
reverses.

* **§A — the mass-shell point is timelike-future.** `kMassShell_lorentzianForm`
  (`lorentzianForm(E/c + i·p) = (m₀c)²`) and **`kMassShell_timelikeFuture`**: a real massive particle sits inside
  the forward cone — a `timelikeFuture` point of the causal structure.
* **§B — causal type is boost-invariant.** `kBoost_preserves_lorentzianForm` (the `k = c` boost preserves the
  Lorentzian form, from `kInterval_invariant`) and **`kBoost_preserves_timelike`** /
  `kBoost_preserves_spacelike`: timelike stays timelike and spacelike stays spacelike under the boost — the
  causal order is invariant.

Since a partial order canonically yields the antisymmetric Sorkin–Johnston Pauli–Jordan kernel
(`CausalSetIntervalAbundance.causalSign_isPauliJordan`), the boost-invariant `k`-causal order feeds the Sorkin
construction unchanged — the variable light speed does not disturb it.

**Honest layering.** All are exact specializations (`k = c`) of the model's identities landing on the proven
Lorentzian form; the Sorkin/Pauli–Jordan link is the existing `causalSign` construction, noted here, not
re-derived.

## References

* `ComplexAction.LorentzViolationVariableLightSpeed`, `Rapidity.FutureIncludedLorentzian` (`lorentzianForm`,
  `timelike`), `CausalSetIntervalAbundance` (`causalSign`), `SorkinJohnstonRegionState` (`IsPauliJordan`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.LorentzViolationVariableLightSpeed
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LorentzViolationCausalStructure


/-- **The `k = c` on-shell coordinate has Lorentzian form `(m₀c)²`** — `lorentzianForm(E/c + i·p) = (m₀c)²` with
`E = γm₀c²`, `p = γm₀v`. -/
lemma kMassShell_lorentzianForm (m₀ v c γ : ℝ) (hγ : γ ^ 2 * (c ^ 2 - v ^ 2) = c ^ 2) :
    lorentzianForm ⟨γ * m₀ * c, γ * m₀ * v⟩ = (m₀ * c) ^ 2 := by
  unfold lorentzianForm
  show (γ * m₀ * c) ^ 2 - (γ * m₀ * v) ^ 2 = (m₀ * c) ^ 2
  linear_combination (m₀ ^ 2) * hγ

/-- **A real massive particle is a `timelikeFuture` point** — the on-shell energy–momentum `q = γm₀c + i·γm₀v`
lies inside the forward cone (`0 < lorentzianForm`, `0 < Re q`), the causal-structure statement of the mass
shell. -/
lemma kMassShell_timelikeFuture (m₀ v c γ : ℝ) (hγ : γ ^ 2 * (c ^ 2 - v ^ 2) = c ^ 2)
    (hm : 0 < m₀) (hc : 0 < c) (hγpos : 0 < γ) :
    timelikeFuture ⟨γ * m₀ * c, γ * m₀ * v⟩ := by
  refine ⟨?_, ?_⟩
  · show 0 < lorentzianForm _
    rw [kMassShell_lorentzianForm m₀ v c γ hγ]
    positivity
  · show (0 : ℝ) < γ * m₀ * c
    positivity


/-- **The `k = c` boost preserves the Lorentzian form** — from `kInterval_invariant`, on the coordinate
`q = c·t + i·x` the boost leaves `lorentzianForm q = (ct)² − x²` invariant. -/
lemma kBoost_preserves_lorentzianForm (v c γ t x : ℝ) (hc : c ≠ 0)
    (hγ : γ ^ 2 * (c ^ 2 - v ^ 2) = c ^ 2) :
    lorentzianForm ⟨c * (γ * (t - v * x / c ^ 2)), γ * (x - v * t)⟩ = lorentzianForm ⟨c * t, x⟩ := by
  unfold lorentzianForm
  show (c * (γ * (t - v * x / c ^ 2))) ^ 2 - (γ * (x - v * t)) ^ 2 = (c * t) ^ 2 - x ^ 2
  linear_combination kInterval_invariant v c γ t x hc hγ

/-- **Timelike stays timelike under the boost** — the causal order is invariant: a timelike separation in one
frame is timelike in every boosted frame. -/
lemma kBoost_preserves_timelike (v c γ t x : ℝ) (hc : c ≠ 0) (hγ : γ ^ 2 * (c ^ 2 - v ^ 2) = c ^ 2)
    (h : timelike ⟨c * t, x⟩) : timelike ⟨c * (γ * (t - v * x / c ^ 2)), γ * (x - v * t)⟩ := by
  unfold timelike at h ⊢
  rw [kBoost_preserves_lorentzianForm v c γ t x hc hγ]
  simpa using h

/-- **Spacelike stays spacelike under the boost** — the spacelike (causally-unrelated) relation, which the
Sorkin `causalSign` records as `0`, is boost-invariant. -/
lemma kBoost_preserves_spacelike (v c γ t x : ℝ) (hc : c ≠ 0) (hγ : γ ^ 2 * (c ^ 2 - v ^ 2) = c ^ 2)
    (h : spacelike ⟨c * t, x⟩) : spacelike ⟨c * (γ * (t - v * x / c ^ 2)), γ * (x - v * t)⟩ := by
  unfold spacelike at h ⊢
  rw [kBoost_preserves_lorentzianForm v c γ t x hc hγ]
  simpa using h

end Physlib.QuantumMechanics.ComplexAction.LorentzViolationCausalStructure
