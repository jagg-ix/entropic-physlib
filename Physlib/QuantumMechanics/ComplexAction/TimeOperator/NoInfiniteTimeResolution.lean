/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator

/-!
# Infinite time resolution is impossible

Resolving time to arbitrary precision means a time-uncertainty `ΔT → 0`.  The time–energy uncertainty relation
`ΔT·ΔH ≥ ℏ/2` — the genuine Robertson bound from the exact CCR `[T,H] = iℏ`
(`FujiwaraTimeEnergyOperator.time_energy_uncertainty`) — forbids it: with `ℏ > 0` the product is bounded away
from zero, so `ΔT` cannot vanish, and for any *finite* energy spread `ΔH ≤ M` the resolution is bounded below,

  `ΔT ≥ ℏ/(2M) > 0`     (`finite_energy_positive_resolution`).

Infinite time resolution would require infinite energy spread (`ΔH → ∞`).  Since no physical state has unbounded
energy variance, **time has a positive minimal resolution** — there is no infinite resolution for the action
conjugate to energy.

* **§A — the impossibility, abstractly** (`no_infinite_time_resolution`, `time_resolution_lower_bound`,
  `finite_energy_positive_resolution`): direct consequences of `ΔT·ΔH ≥ ℏ/2`.
* **§B — grounded on the Fujiwara time operator** (`fujiwara_time_resolution_positive`): the abstract bound
  applied to the repository's exact `T = iℏ∂_E`, whose Robertson uncertainty is proved from `[T,H] = iℏ`.  Every
  normalized state has strictly positive time-resolution.

This is the microscopic reason the entropic clock has finite resolution — the finite mode cutoff that closes
the Navier–Stokes velocity PDE on the quantized fluid (`NavierStokes.ActionQuantumFiniteResolutionBKM`).  The
continuum's infinite resolution is not merely unproven; it is *forbidden* by the time–energy CCR.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.NoInfiniteTimeResolution

/-! ### §A — The impossibility from the uncertainty relation -/

/-- **No infinite time resolution.**  From the time–energy uncertainty `ℏ/2 ≤ ΔT·ΔH` with `ℏ > 0` and a
non-negative energy spread `ΔH ≥ 0`, the time uncertainty is strictly positive: `ΔT > 0`.  Time cannot be
resolved with zero uncertainty. -/
theorem no_infinite_time_resolution (dT dH ℏ : ℝ) (hℏ : 0 < ℏ) (hdH : 0 ≤ dH)
    (hunc : ℏ / 2 ≤ dT * dH) : 0 < dT := by
  by_contra h
  rw [not_lt] at h
  nlinarith [hunc, hℏ, hdH, h]

/-- **The time resolution is bounded below by the energy spread.**  `ΔT ≥ ℏ/(2ΔH)`: finer time resolution
(smaller `ΔT`) demands larger energy spread `ΔH`. -/
theorem time_resolution_lower_bound (dT dH ℏ : ℝ) (hdH : 0 < dH)
    (hunc : ℏ / 2 ≤ dT * dH) : ℏ / (2 * dH) ≤ dT := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hunc]

/-- **Finite energy forbids infinite resolution.**  If the energy spread is capped, `ΔH ≤ M`, then time cannot
be resolved finer than `ℏ/(2M)`: `ΔT ≥ ℏ/(2M) > 0`.  Infinite time resolution would require `M → ∞` — infinite
energy. -/
theorem finite_energy_positive_resolution (dT dH ℏ M : ℝ) (hℏ : 0 < ℏ) (hdHpos : 0 < dH)
    (hdH : dH ≤ M) (hunc : ℏ / 2 ≤ dT * dH) : ℏ / (2 * M) ≤ dT := by
  have h1 : ℏ / (2 * dH) ≤ dT := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hunc]
  have h2 : ℏ / (2 * M) ≤ ℏ / (2 * dH) := by gcongr
  linarith

/-! ### §B — Grounded on the exact Fujiwara time operator `T = iℏ∂_E` -/

open Physlib.QuantumMechanics.ComplexAction.TimeOperator.FujiwaraTimeEnergyOperator
open LinearPMap
open _root_.QuantumMechanics.SpaceDHilbertSpace
open _root_.QuantumMechanics.SpaceDHilbertSpace.SchwartzSubmodule

/-- **Every normalized state has strictly positive time-resolution.**  Applying the abstract bound to the
repository's exact time operator `T = iℏ∂_E`, whose Robertson uncertainty `ℏ/2 ≤ ΔT·ΔH`
(`time_energy_uncertainty`) is proved from the CCR `[T,H] = iℏ`: the time standard deviation of any unit state
is `> 0`.  There is no state of definite time — infinite time resolution is forbidden by the canonical
commutation relation, not merely unavailable. -/
theorem fujiwara_time_resolution_positive (psi : SchwartzSubmodule 1)
    (hpsi_norm : ‖(psi : EnergyHilbert)‖ = 1) :
    0 < standardDeviation timeOperator psi :=
  no_infinite_time_resolution _ _ Constants.ℏ Constants.ℏ_pos
    (standardDeviation_nonneg energyOperator ⟨psi, psi.property⟩)
    (time_energy_uncertainty psi hpsi_norm)

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.NoInfiniteTimeResolution

end
