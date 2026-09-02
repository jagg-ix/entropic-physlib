/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ThomasBMTMagicCancellation
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.QuantumGravitySpatialOperators
public import Physlib.QuantumMechanics.ComplexAction.EntangledRegionFrequencyTimeDilation

/-!
# The frequency-pentagon welds

Pairwise welds among five frequency carriers from five sectors — `comptonFrequency`
(the quantum clock), `deBroglieFrequency` (its general-`E` form), `cyclotronRate`
(magnetic precession), `collisionRate` (kinetic theory), `regionFrequency` (cavity modes).
`#zil_groupoid_report` found all ten edges of this pentagon dimensionally homogeneous but
its proven part sparse: only the Compton–de Broglie and Compton–collision edges carried
theorems, leaving the cyclotron and region carriers as isolated vertices of the bridge
groupoid.  The welds below connect every edge; each is the rest-point identification of two
frequency scales, and several name physically distinguished thresholds — the
Compton–cyclotron weld is the **Schwinger critical field**.  Guarded by
`Physlib.Meta.FrequencyPentagonGate`.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.FrequencyPentagonWelds

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ThomasBMTMagicCancellation
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.QuantumGravitySpatialOperators
open Physlib.QuantumMechanics.ComplexAction.EntangledRegionFrequencyTimeDilation

/-- **The cyclotron rate reaches the Compton frequency exactly at the Schwinger critical
field** `qBħ = γm²c²`: at `γ = 1` this is `B = m²c²/(qħ)`, the field at which magnetic
precession runs as fast as the particle's own mass clock — the QED critical-field scale. -/
theorem comptonFrequency_eq_cyclotronRate_iff {m c ħ q γ B : ℝ}
    (hħ : 0 < ħ) (hγ : 0 < γ) (hm : 0 < m) :
    comptonFrequency m c ħ = cyclotronRate q m γ B ↔ γ * m ^ 2 * c ^ 2 = q * B * ħ := by
  unfold comptonFrequency cyclotronRate
  rw [div_eq_div_iff hħ.ne' (by positivity)]
  constructor <;> intro h <;> linear_combination h

/-- **The cyclotron rate reads an energy through `ħ`**: `ω_c = ω_dB(E)` exactly at
`γmE = qBħ` — the general-`E` form of the Schwinger weld (its instance at `E = mc²`). -/
theorem deBroglieFrequency_eq_cyclotronRate_iff {E ħ q γ B m : ℝ}
    (hħ : 0 < ħ) (hγ : 0 < γ) (hm : 0 < m) :
    deBroglieFrequency E ħ = cyclotronRate q m γ B ↔ γ * m * E = q * B * ħ := by
  unfold deBroglieFrequency cyclotronRate
  rw [div_eq_div_iff hħ.ne' (by positivity)]
  constructor <;> intro h <;> linear_combination h

/-- **A cavity resonates at the Compton frequency exactly at `mc²L = κħ`** — the mode whose
size-frequency product matches the particle's mass clock. -/
theorem comptonFrequency_eq_regionFrequency_iff {m c ħ κ L : ℝ}
    (hħ : 0 < ħ) (hL : 0 < L) :
    comptonFrequency m c ħ = regionFrequency κ L ↔ m * c ^ 2 * L = κ * ħ := by
  unfold comptonFrequency regionFrequency
  rw [div_eq_div_iff hħ.ne' hL.ne']

/-- **A cavity resonates at the de Broglie frequency exactly at `EL = κħ`** — the general-`E`
form of the Compton cavity weld. -/
theorem deBroglieFrequency_eq_regionFrequency_iff {E ħ κ L : ℝ}
    (hħ : 0 < ħ) (hL : 0 < L) :
    deBroglieFrequency E ħ = regionFrequency κ L ↔ E * L = κ * ħ := by
  unfold deBroglieFrequency regionFrequency
  rw [div_eq_div_iff hħ.ne' hL.ne']

/-- **The collision rate reads an energy through `ħ`**: `v̄/ℓ = E/ħ` exactly at `Eℓ = v̄ħ`.
Reported by `#zil_groupoid_report` as the pentagon's one underived composite — reachable
through the proven Compton flanks (the boost law `deBroglie_eq_gamma_compton` and the
bound `collisionRate_below_comptonFrequency`) with no direct theorem — and closed here. -/
theorem deBroglieFrequency_eq_collisionRate_iff {E ħ vbar ℓ : ℝ}
    (hħ : 0 < ħ) (hℓ : 0 < ℓ) :
    deBroglieFrequency E ħ = collisionRate vbar ℓ ↔ E * ℓ = vbar * ħ := by
  unfold deBroglieFrequency collisionRate
  rw [div_eq_div_iff hħ.ne' hℓ.ne']

/-- **Magnetic precession keeps pace with kinetic collisions exactly at `qBℓ = γmv̄`** — one
cyclotron turn per mean free path, the magnetization threshold of transport theory (`ω_c τ ≈ 1`). -/
theorem cyclotronRate_eq_collisionRate_iff {q γ B m vbar ℓ : ℝ}
    (hγ : 0 < γ) (hm : 0 < m) (hℓ : 0 < ℓ) :
    cyclotronRate q m γ B = collisionRate vbar ℓ ↔ q * B * ℓ = γ * m * vbar := by
  unfold cyclotronRate collisionRate
  rw [div_eq_div_iff (by positivity) hℓ.ne']
  constructor <;> intro h <;> linear_combination h

/-- **Magnetic precession matches the cavity mode exactly at `qBL = γmκ`.** -/
theorem cyclotronRate_eq_regionFrequency_iff {q γ B m κ L : ℝ}
    (hγ : 0 < γ) (hm : 0 < m) (hL : 0 < L) :
    cyclotronRate q m γ B = regionFrequency κ L ↔ q * B * L = γ * m * κ := by
  unfold cyclotronRate regionFrequency
  rw [div_eq_div_iff (by positivity) hL.ne']
  constructor <;> intro h <;> linear_combination h

/-- **The collision rate matches the cavity mode exactly at `v̄L = κℓ`** — mean free path and
cavity size in the ratio of their speeds. -/
theorem collisionRate_eq_regionFrequency_iff {vbar ℓ κ L : ℝ}
    (hℓ : 0 < ℓ) (hL : 0 < L) :
    collisionRate vbar ℓ = regionFrequency κ L ↔ vbar * L = κ * ℓ := by
  unfold collisionRate regionFrequency
  rw [div_eq_div_iff hℓ.ne' hL.ne']

end Physlib.QuantumMechanics.ComplexAction.FrequencyPentagonWelds
