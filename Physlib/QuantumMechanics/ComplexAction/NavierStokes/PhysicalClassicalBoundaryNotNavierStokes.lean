/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.ThreeDimensionalVortexStretchingDepletion

/-!
# The physical–classical boundary is not a Navier–Stokes problem

The wall separating the physical (`ℏ > 0`) fluid from the classical (`ℏ = 0`) idealization was witnessed by the
*divergence* of the closure prefactor `(1 + k_max²)`.  But that divergence is a **pure arithmetic** fact —
`∀ M, ∃ k, M ≤ 1 + k²` — with **no Navier–Stokes content whatsoever**: it is the unboundedness of `1 + k²`,
true of any parametrized family.  `physicalClassical_boundary_is_arithmetic` proves it directly, using nothing
but the Archimedean property.  So the boundary between the two regimes is *not a Navier–Stokes problem*; it is a
generic singular-limit fact about the resolution parameter, not about the fluid.

The genuine Navier–Stokes problem is on the other side of that observation, and it is **`ℏ`-free**.  The 3D
regularity gate — the strict depletion budget `∫P ≤ Ω₀/(2δν)` (`navierStokes_gate_hbar_free`) — mentions no
`ℏ` at all.  It is the *same* problem at physical (`ℏ > 0`) and classical (`ℏ = 0`) scales; the depletion
margin `δ` is a spatial-cascade quantity, invariant to `ℏ` exactly as it is invariant to the clock.

`gate_navierStokes_boundary_arithmetic` states both at once: the NS problem (the `ℏ`-free gate `δ`) and the
physical–classical boundary (NS-free arithmetic) side by side.

## Honest scope

This *sharpens* the earlier boundary file rather than adding a result: the physical "regularity" was the
finite-*resolution* closure (band-limiting, `ℏ`-dependent), which **sidesteps** the gate `δ` — it does not
solve it.  The genuine NS gate `δ` is untouched, `ℏ`-invariant, and open at every scale; and what separates the
physical from the classical regime is not Navier–Stokes but arithmetic.  Nothing here solves the depletion
problem or the classical Clay statement.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.PhysicalClassicalBoundaryNotNavierStokes

open Physlib.QuantumMechanics.ComplexAction.NavierStokes.ThreeDimensionalVortexStretchingDepletion

/-- **The physical–classical boundary is pure arithmetic — no Navier–Stokes content.**  The divergence that
separates the physical (`ℏ > 0`) from the classical (`ℏ = 0`) regime is the unboundedness of `1 + k²`: for any
`M` there is a resolution with `M ≤ 1 + k²`.  Proved from the Archimedean property alone — no fluid, no
enstrophy, no `ℏ`.  The wall is not a Navier–Stokes problem. -/
theorem physicalClassical_boundary_is_arithmetic (M : ℝ) : ∃ k : ℕ, M ≤ 1 + (k : ℝ) ^ 2 := by
  obtain ⟨k, hk⟩ := exists_nat_ge M
  exact ⟨k, by nlinarith [hk, sq_nonneg (2 * (k : ℝ) - 1)]⟩

/-- **The genuine Navier–Stokes gate is `ℏ`-free.**  The 3D strict-depletion budget `∫P ≤ Ω₀/(2δν)` mentions no
`ℏ`: it is the *same* problem at physical (`ℏ > 0`) and classical (`ℏ = 0`) scales.  The depletion margin `δ` is
a spatial-cascade quantity, invariant to `ℏ`. -/
theorem navierStokes_gate_hbar_free
    (IVS IP Ω_T Ω_0 ν del : ℝ) (hν : 0 < ν) (hdel : 0 < del) (hΩT : 0 ≤ Ω_T)
    (hidentity : Ω_T - Ω_0 = 2 * IVS - 2 * ν * IP)
    (hdepletion : IVS ≤ (1 - del) * (ν * IP)) :
    IP ≤ Ω_0 / (2 * del * ν) :=
  threeDim_palinstrophy_budget_of_strict_depletion IVS IP Ω_T Ω_0 ν del hν hdel hΩT hidentity hdepletion

/-- **The NS problem and the boundary, side by side.**  The genuine Navier–Stokes problem — the `ℏ`-free
depletion gate `δ` — and the physical–classical boundary — NS-free arithmetic — in one statement.  The gate is
the same at all scales; the boundary is not Navier–Stokes.  So the wall between the solved physical fluid and
the open classical statement is not an NS obstruction: the NS content is the `ℏ`-invariant gate `δ`, and the
physical closure sidestepped it by band-limiting rather than solving it. -/
theorem gate_navierStokes_boundary_arithmetic
    (IVS IP Ω_T Ω_0 ν del : ℝ) (hν : 0 < ν) (hdel : 0 < del) (hΩT : 0 ≤ Ω_T)
    (hidentity : Ω_T - Ω_0 = 2 * IVS - 2 * ν * IP)
    (hdepletion : IVS ≤ (1 - del) * (ν * IP)) (M : ℝ) :
    IP ≤ Ω_0 / (2 * del * ν)
      ∧ ∃ k : ℕ, M ≤ 1 + (k : ℝ) ^ 2 :=
  ⟨navierStokes_gate_hbar_free IVS IP Ω_T Ω_0 ν del hν hdel hΩT hidentity hdepletion,
    physicalClassical_boundary_is_arithmetic M⟩

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.PhysicalClassicalBoundaryNotNavierStokes

end
