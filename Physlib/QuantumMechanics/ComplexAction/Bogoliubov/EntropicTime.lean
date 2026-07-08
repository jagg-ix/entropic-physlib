/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Entropic time of the Bogoliubov transformation

This file inspects how the **entropic time** `τ_ent = S_I/ℏ` of the arc enters the Bogoliubov
transformation (`Bogoliubov.Transformation`). The answer: it is the **entanglement entropy of the
quasiparticle occupation** `v²` — the Bogoliubov mode-mixing produces entropy.

For the Bogoliubov-transformed (BCS) state, tracing out one partner of each pair leaves a
single-mode state with occupation `v²`; its (binary / von Neumann) entropy

  `τ_ent = binEntropy(v²)`   (`bogoliubovEntropicTime`)

is the entropy production. It is:

* **`≥ 0`** (`bogoliubov_entropicTime_nonneg`) — the arrow of time;
* **`= 0` exactly when there is no mode mixing** (`v² = 0` or `v² = 1`,
  `bogoliubov_entropicTime_eq_zero_iff`) — the reversible normal state. In particular at
  `Δ = 0` (no pairing) the entropic time vanishes (`bogoliubov_entropicTime_normal_zero`): the
  reversible / alpha-particle / `S_I = 0` point of `KramersKronig.EntropyHamiltonian`;
* **maximal at `ξ = 0`** (`v² = ½`, `bogoliubov_entropicTime_at_zero_xi`), the symmetric pairing
  point where the particle–hole entanglement is greatest.

So the Bogoliubov pairing `Δ ≠ 0` (the irreversible / Kramers–Kronig sector) is exactly what
turns on the entropic time, and the normal state `Δ = 0` is the entropy-free / reversible fiber
the rest of the arc lives on.

## References

* N. N. Bogoljubov (1958); BCS entanglement entropy. `Bogoliubov.Transformation`,
  `KramersKronig.EntropyHamiltonian` (this development); `Real.binEntropy` (Mathlib).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Real
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation

namespace Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime

/-! ## §A — the entropic time of the Bogoliubov state -/

/-- **The entropic time of the Bogoliubov transformation** `τ_ent = binEntropy(v²)` — the
entanglement entropy of the quasiparticle occupation `v²` (the entropy production `S_I/ℏ`). -/
def bogoliubovEntropicTime (ξ Δ : ℝ) : ℝ := Real.binEntropy (bogoliubovV2 ξ Δ)

/-! ## §B — the occupation lies in `[0, 1]` -/

/-- `|ξ| ≤ E` (the kinetic energy is bounded by the quasiparticle energy). -/
theorem abs_le_bogoliubovEnergy (ξ Δ : ℝ) : |ξ| ≤ bogoliubovEnergy ξ Δ := by
  unfold bogoliubovEnergy
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg Δ]

/-- **The occupation is a probability** `0 ≤ v² ≤ 1` (for a genuine gap `Δ ≠ 0`, so `E > 0`). -/
theorem bogoliubovV2_mem_unitInterval (ξ Δ : ℝ) (hΔ : Δ ≠ 0) :
    0 ≤ bogoliubovV2 ξ Δ ∧ bogoliubovV2 ξ Δ ≤ 1 := by
  have hE : 0 < bogoliubovEnergy ξ Δ := by
    unfold bogoliubovEnergy; exact Real.sqrt_pos.mpr (by positivity)
  have habs : |ξ / bogoliubovEnergy ξ Δ| ≤ 1 := by
    rw [abs_div, abs_of_pos hE, div_le_one hE]
    exact abs_le_bogoliubovEnergy ξ Δ
  rw [abs_le] at habs
  unfold bogoliubovV2
  constructor <;> linarith [habs.1, habs.2]

/-! ## §C — entropic time: non-negative, zero iff reversible, maximal at `ξ = 0` -/

/-- **Entropic time is non-negative** (the arrow of time), for a genuine gap `Δ ≠ 0`. -/
theorem bogoliubov_entropicTime_nonneg (ξ Δ : ℝ) (hΔ : Δ ≠ 0) :
    0 ≤ bogoliubovEntropicTime ξ Δ :=
  Real.binEntropy_nonneg (bogoliubovV2_mem_unitInterval ξ Δ hΔ).1
    (bogoliubovV2_mem_unitInterval ξ Δ hΔ).2

/-- **Entropic time vanishes iff there is no mode mixing** (`v² = 0` or `v² = 1`): the reversible
normal state has zero entropy production. -/
theorem bogoliubov_entropicTime_eq_zero_iff (ξ Δ : ℝ) :
    bogoliubovEntropicTime ξ Δ = 0 ↔ bogoliubovV2 ξ Δ = 0 ∨ bogoliubovV2 ξ Δ = 1 :=
  Real.binEntropy_eq_zero

/-- **No pairing ⟹ no entropic time**: at `Δ = 0`, `ξ > 0` the normal state (`v² = 0`) has zero
entropic time — the reversible / alpha-particle / `S_I = 0` fiber. -/
theorem bogoliubov_entropicTime_normal_zero (ξ : ℝ) (hξ : 0 < ξ) :
    bogoliubovEntropicTime ξ 0 = 0 := by
  unfold bogoliubovEntropicTime
  rw [(bogoliubov_normal_state ξ hξ).2, Real.binEntropy_zero]

/-- **At `ξ = 0` the occupation is `½`** (the symmetric pairing point). -/
theorem bogoliubovV2_at_zero_xi (Δ : ℝ) : bogoliubovV2 0 Δ = 1 / 2 := by
  unfold bogoliubovV2; simp

/-- **Entropic time is maximal at `ξ = 0`**: `τ_ent = binEntropy(½)` (the greatest particle–hole
entanglement, the symmetric pairing point). -/
theorem bogoliubov_entropicTime_at_zero_xi (Δ : ℝ) :
    bogoliubovEntropicTime 0 Δ = Real.binEntropy (1 / 2) := by
  unfold bogoliubovEntropicTime
  rw [bogoliubovV2_at_zero_xi]

end Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime

end
