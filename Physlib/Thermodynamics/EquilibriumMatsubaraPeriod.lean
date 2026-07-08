/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Schrodinger.BadialiForwardBackwardDecomposition
public import Physlib.QFT.Matsubara.PathIntegral

/-!
# Bridge: Badiali like-equilibrium condition is the Matsubara thermal period

Companion bridge connecting the algebraic Badiali condition
`τ · k_B · T = ℏ` (paper Eq. 18) to physlib's existing
`ThermalCircle` and Matsubara frequency machinery in
`Physlib/QFT/Matsubara/PathIntegral.lean`.

**The load-bearing identification**:

Badiali 2005 §4 derives the like-equilibrium condition

  `τ* = β* · ℏ = ℏ / (k_B · T*)`     (paper Eq. 18)

as the value of the path-counting interval at which the path
entropy `S_path` becomes the standard thermal entropy.

The Matsubara thermal QFT formalism uses the Euclidean-time period

  `period = β · ℏ`

(`ThermalCircle.period` in physlib) for periodic/antiperiodic
boundary conditions and the discrete Matsubara frequencies
`ω_n = 2πn/(βℏ)`, `(2n+1)π/(βℏ)`.

These are **the same period**.  Badiali's path-counting interval
at like-equilibrium *is* the imaginary-time period that already
exists in physlib's thermal QFT layer.

This file makes that identification a Lean theorem and produces a
constructor `badialiToThermalCircle` that lifts the Badiali
algebraic data `(τ, k_B, T, ℏ)` into a `ThermalCircle` ready for
use with all the existing Matsubara frequency / KMS / Wick-rotation
machinery downstream.

## Why this matters

The previous Badiali file proved `badiali_like_equilibrium_iff`
as a self-contained algebraic identity `τ·k_B·T = ℏ ↔ τ = ℏ/(k_B·T)`.
That identity sat in isolation: no explicit connection to physlib's
Matsubara / thermal-QFT scope.

After this bridge:

* `badialiToThermalCircle` — every Badiali like-equilibrium config
  promotes automatically to a `ThermalCircle`.
* `badialiTau_eq_thermalPeriod` — the path-counting interval **is**
  the Euclidean thermal period.
* The full Matsubara apparatus — bosonic/fermionic Matsubara modes
  (`matsubaraModeBoson`, `matsubaraModeFermion`), KMS periodicity,
  Wick rotation — becomes available to any consumer of Badiali
  path-entropy results, with no further bridge work.

This is the second of the analytic-gap
closure bridges (the first is `BadialiToMadelung.lean`, identifying
the Badiali Born rule with the Madelung polar form).

## Contents

* `badialiToThermalCircle` — constructor from
  `(τ, k_B, T, ℏ)` + positivity + like-equilibrium hypothesis to
  `ThermalCircle`.
* **`badialiTau_eq_thermalPeriod`** — at like-equilibrium, the
  Badiali path interval equals the Matsubara period `β·ℏ`.
* `badialiTau_in_matsubaraBosonZeroMode_zero` —  at the Badiali
  like-equilibrium, the bosonic Matsubara mode `n = 0` at proper
  time `τ` is just `1` (`exp(0)`), the trivial zero-mode evaluation.

## References

* Badiali 2005 *J. Phys. A* 38, 2835 §4, Eq. 18.
* `Physlib.QFT.Matsubara.PathIntegral` — `ThermalCircle`,
  `period`, `matsubaraOmegaBoson`, `matsubaraOmegaFermion`.
* `Physlib.QuantumMechanics.Schrodinger.BadialiForwardBackwardDecomposition`
  — `badialiPathTemperatureProduct`, `badiali_like_equilibrium_iff`.
* Matsubara 1955, *Prog. Theor. Phys.* 14, 351 — thermal QFT.
* Kubo 1957, Martin–Schwinger 1959 — KMS boundary conditions.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics

open Real Physlib.QFT.Matsubara.PathIntegral
open Physlib.QuantumMechanics.Schrodinger

/-! ## §1 — Badiali → ThermalCircle constructor -/

/-- **Badiali → ThermalCircle constructor**.

Given positive `k_B, T, ℏ > 0`, returns the `ThermalCircle` with
`β := 1/(k_B·T)` and the given `ℏ`.

The path-counting interval `τ` that satisfies Badiali's
like-equilibrium condition `τ·k_B·T = ℏ` automatically equals the
Euclidean thermal period `β·ℏ` of this `ThermalCircle` —
`badialiTau_eq_thermalPeriod` certifies this. -/
def badialiToThermalCircle
    (kB T ℏ : ℝ) (hkB_pos : 0 < kB) (hT_pos : 0 < T) (hℏ_pos : 0 < ℏ) :
    ThermalCircle where
  beta     := 1 / (kB * T)
  hbar     := ℏ
  beta_pos := by
    apply div_pos one_pos
    exact mul_pos hkB_pos hT_pos
  hbar_pos := hℏ_pos

/-- **The Badiali → ThermalCircle period is `ℏ / (k_B · T)`**. -/
theorem badialiToThermalCircle_period_eq
    {kB T ℏ : ℝ} (hkB_pos : 0 < kB) (hT_pos : 0 < T) (hℏ_pos : 0 < ℏ) :
    (badialiToThermalCircle kB T ℏ hkB_pos hT_pos hℏ_pos).period
      = ℏ / (kB * T) := by
  unfold badialiToThermalCircle ThermalCircle.period
  simp only
  ring

/-! ## §2 — Badiali like-equilibrium ↔ Matsubara period -/

/-- **At Badiali like-equilibrium, the path-counting interval
equals the Matsubara thermal period**.

Given the Badiali like-equilibrium condition
`τ · k_B · T = ℏ` (paper Eq. 18), the path-counting interval `τ`
equals the Euclidean thermal period `β · ℏ` of the corresponding
thermal circle (with `β = 1/(k_B·T)`).

**Algebraic core**: `badiali_like_equilibrium_iff` gives
`τ = ℏ/(k_B·T)`; `badialiToThermalCircle_period_eq` gives the same
formula for the thermal period. -/
theorem badialiTau_eq_thermalPeriod
    {τ kB T ℏ : ℝ}
    (hkB_pos : 0 < kB) (hT_pos : 0 < T) (hℏ_pos : 0 < ℏ)
    (h_like_eq : badialiPathTemperatureProduct τ kB T = ℏ) :
    τ = (badialiToThermalCircle kB T ℏ hkB_pos hT_pos hℏ_pos).period := by
  rw [badialiToThermalCircle_period_eq hkB_pos hT_pos hℏ_pos]
  exact (badiali_like_equilibrium_iff (ne_of_gt hkB_pos) (ne_of_gt hT_pos)).mp h_like_eq

/-! ## §3 — Matsubara zero-mode evaluation at the Badiali period -/

/-- **Bosonic Matsubara `n = 0` mode at the Badiali path-counting
interval evaluates to `1`**.

The bosonic Matsubara mode `exp(i·ω_0·τ)` with `ω_0 = 0`
trivially evaluates to `exp(0) = 1` at any `τ`.  This is the
**zero-mode preservation** identity at the Badiali like-equilibrium
period: the static thermal zero-mode component is unchanged by
imaginary-time evolution over one period, which is consistent with
the equilibrium interpretation of Badiali's like-equilibrium
condition.

Provides a concrete pinpoint where the Badiali path-counting
interval interacts cleanly with the Matsubara mode structure. -/
theorem badialiTau_in_matsubaraBosonZeroMode_zero
    {τ kB T ℏ : ℝ}
    (hkB_pos : 0 < kB) (hT_pos : 0 < T) (hℏ_pos : 0 < ℏ)
    (h_like_eq : badialiPathTemperatureProduct τ kB T = ℏ) :
    matsubaraModeBoson
        (badialiToThermalCircle kB T ℏ hkB_pos hT_pos hℏ_pos) 0 τ = 1 := by
  unfold matsubaraModeBoson ThermalCircle.matsubaraOmegaBoson
  simp [Complex.exp_zero]

end Physlib.Thermodynamics

end
