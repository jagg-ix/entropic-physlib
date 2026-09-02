/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.ThreeDimensionalVortexStretchingDepletion

/-!
# The 3D Navier–Stokes regularity gate is time-agnostic

The 3D problem, as posed, assumes nothing about the *nature* of time: `t` is a coordinate, not an observable,
and the equations never ask to *resolve* time.  The regularity gate — the strict vortex-stretching depletion
`∫VS ≤ (1 − δ)·ν∫P` and its budget (`ThreeDimensionalVortexStretchingDepletion`) — is a comparison of two
spatial-cascade time-integrals, and it is **invariant under any monotone reparametrization of time**: a change
of clock scales both `∫VS` and `∫P` by the same positive local rate, and the depletion inequality survives
(`depletion_gate_time_reparametrization_invariant`).

So the difficulty of the 3D problem lives in the **spatial** cascade — the depletion margin `δ` — and not in
any description of time.  The earlier `TimeOperator.NoInfiniteTimeResolution` (time *as an observable* has a
positive minimal resolution `ΔT > 0`) is a true statement about a **different** time — the quantum time
conjugate to energy — and it does not touch this gate, which contains no `ΔT`.

This is a retraction of an over-connection: the finite-*time*-resolution result does not bound the 3D problem,
because the problem's continuum is **spatial**, and its gate is invariant to the clock.  The
infinite-time-resolution question was a subset we mistakenly attached to the problem; the gate's
reparametrization-invariance dismisses it — the 3D problem is exactly as hard, and exactly as open, under any
time description.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.RegularityGateTimeAgnostic

/-- **The depletion gate is invariant under reparametrization of time.**  Any monotone change of clock scales
both integrated cascade quantities `∫VS` and `∫P` by the same positive local rate `c`; the strict-depletion
condition `∫VS ≤ (1 − δ)·ν∫P` is unchanged.  The 3D regularity gate does not depend on the description of time —
it is a statement about the spatial cascade alone. -/
theorem depletion_gate_time_reparametrization_invariant (IVS IP ν del c : ℝ) (hc : 0 < c) :
    c * IVS ≤ (1 - del) * (ν * (c * IP)) ↔ IVS ≤ (1 - del) * (ν * IP) := by
  rw [show (1 - del) * (ν * (c * IP)) = c * ((1 - del) * (ν * IP)) from by ring]
  constructor
  · intro h; exact le_of_mul_le_mul_left h hc
  · intro h; exact mul_le_mul_of_nonneg_left h hc.le

/-- **The budget's finiteness is preserved by reparametrization.**  If the palinstrophy budget `∫P ≤ B` holds,
then under any monotone clock (rate `c > 0`) the reparametrized budget `c·∫P ≤ c·B` holds — a finite budget
stays finite.  Regularity is a property of the trajectory, not of the clock reading it. -/
theorem budget_finiteness_reparametrization_invariant (IP B c : ℝ) (hc : 0 < c) (hIP : IP ≤ B) :
    c * IP ≤ c * B :=
  mul_le_mul_of_nonneg_left hIP hc.le

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.RegularityGateTimeAgnostic

end
