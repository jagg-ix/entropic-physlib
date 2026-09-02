/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.NoInfiniteTimeResolution
public import Physlib.ClassicalMechanics.ActionPrinciple

/-!
# Classical continuum time is the `ℏ → 0` limit; the physical time is quantized

Classical mechanics is *subordinate* to quantum mechanics — the `ℏ → 0` limit.  So the classical continuum
time (infinite resolution, `ΔT = 0`) is **not a different time** from the quantum / entropic one; it is the
same time in its unphysical `ℏ → 0` boundary.  This corrects the earlier retraction, which treated the quantum
`ΔT > 0` time as a separate object to be dismissed.

* `infinite_time_resolution_requires_hbar_nonpos` — a perfectly-resolved time `ΔT ≤ 0`, together with the
  uncertainty `ΔT·ΔH ≥ ℏ/2` (`FujiwaraTimeEnergyOperator.time_energy_uncertainty`), forces `ℏ ≤ 0`.  Infinite
  time resolution is available only in the classical (`ℏ = 0`) or unphysical regime.
* `physical_time_is_quantized` — at physical `ℏ > 0` the time is quantized, `ΔT > 0`
  (`NoInfiniteTimeResolution.no_infinite_time_resolution`).  The physical time never has infinite resolution.
* `classical_is_hbar_zero_limit` — the physical (total) action reduces to the classical action exactly when the
  entropic contribution `S_I = ℏ·τ_ent` vanishes (`ClassicalMechanics.ActionPrinciple`): classical mechanics is
  the `ℏτ → 0` limit, subordinate to the quantum.

**Consequence for Navier–Stokes.**  Since classical is the `ℏ → 0` shadow of the physical (quantum) theory, the
physically-correct formulation of the fluid uses the quantized / entropic time `ℏ > 0`, where the resolution is
finite and the velocity PDE closes (`NavierStokes.ActionQuantumFiniteResolutionBKM`), and where the energy is
the simple line `E = E₀ − ℏτ` (`NavierStokes.EntropicTimeEnergyDescentEuclidean`) built on the time-dependence
of velocity and acceleration (`materialAcceleration`).  The classical continuum problem — the Clay statement —
is the *singular `ℏ → 0` limit* of that regular physical problem.

## Honest scope

This is a physical *interpretation*, not a proof of the classical Clay statement.  The regularity mechanism
degenerates exactly as `ℏ → 0` (the finite-resolution bound diverges), so working in the physical `ℏ > 0` time
does not close the `ℏ = 0` mathematical problem — it identifies that problem as the unphysical limit where the
quantum protection is switched off.  The honest content is the *subordination*: the classical continuum time is
the `ℏ → 0` shadow of the physical quantized time, and only at `ℏ > 0` is the description physical.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.ClassicalTimeHbarZeroLimit

open Physlib.QuantumMechanics.ComplexAction.TimeOperator.NoInfiniteTimeResolution
open Physlib.ClassicalMechanics.ActionPrinciple

/-- **Infinite time resolution requires `ℏ ≤ 0` — the classical / unphysical regime.**  If time could be
perfectly resolved, `ΔT ≤ 0`, the uncertainty `ℏ/2 ≤ ΔT·ΔH` (with `ΔH ≥ 0`) forces `ℏ ≤ 0`.  A continuum time
of definite value exists only in the classical `ℏ = 0` limit — not at any physical `ℏ > 0`. -/
theorem infinite_time_resolution_requires_hbar_nonpos (dT dH ℏ : ℝ) (hdT : dT ≤ 0) (hdH : 0 ≤ dH)
    (hunc : ℏ / 2 ≤ dT * dH) : ℏ ≤ 0 := by
  nlinarith [hunc, mul_nonneg (neg_nonneg.2 hdT) hdH]

/-- **At physical `ℏ > 0` the time is quantized.**  Positive `ℏ` and the uncertainty give `ΔT > 0`: the
physical time has strictly positive resolution — the same statement as `no_infinite_time_resolution`, read as
"the physical (`ℏ > 0`) time is the quantized one." -/
theorem physical_time_is_quantized (dT dH ℏ : ℝ) (hℏ : 0 < ℏ) (hdH : 0 ≤ dH)
    (hunc : ℏ / 2 ≤ dT * dH) : 0 < dT :=
  no_infinite_time_resolution dT dH ℏ hℏ hdH hunc

/-- **Classical mechanics is the `ℏτ → 0` limit, subordinate to the quantum.**  The physical (total) action
equals the classical action exactly when the entropic contribution `S_I = ℏ·τ_ent` vanishes: the classical
description is recovered in the `ℏ → 0` (zero entropic) limit of the physical one. -/
theorem classical_is_hbar_zero_limit (A : EntropicAction) :
    A.total = A.classical ↔ A.entropic = 0 :=
  A.total_eq_classical_iff_zero_entropic

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.ClassicalTimeHbarZeroLimit

end
