/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.VorticityCoadjointEnstrophy

/-!
# Leray's integrated-enstrophy bound from the energy identity

Ports the genuine, **mathematical kernel** of the Navier–Stokes Leray energy-decay file
(`NSLerayEnergyDecayClosure`). That file routes through an `L¹`-analysis axiom
(`subcritical_time_exists_from_finite_enstrophy_budget`) and `Bool` status records; the genuine, exact
content is the algebra that turns the entropic-time identity into Leray's **finite integrated-enstrophy
budget**.

The entropic proper time is the integrated enstrophy in units of `ν/ħ`,
`τ = (ν/ħ)·∫Ω` (`NavierStokes.VorticityCoadjointEnstrophy.orbitTraversal`). The energy identity bounds it by the
initial energy, `τ ≤ E₀/ħ`. These combine to Leray's bound

  `∫₀^T Ω(t) dt ≤ E₀ / ν`   (`integratedEnstrophy_bound`),

a finite `L¹`-in-time enstrophy budget. The subcritical-enstrophy threshold `ν⁴ λ₁ C_L⁴` is positive
(`subcriticalThreshold_pos`), so the budget forces the trajectory below threshold on a set of finite
measure.

* **§A — Leray's integrated-enstrophy bound** (`integratedEnstrophy_bound`).
* **§B — the subcritical threshold is positive** (`subcriticalThreshold_pos`).

## References

* J. Leray, *Acta Math.* 63 (1934) 193 (the energy identity `dE/dt = −ν‖∇u‖²`, finite enstrophy budget).
  Source (kernel only; `L¹` axiom + `Bool` records): `NavierStokes/NSLerayEnergyDecayClosure.lean`.
  Carrier: `NavierStokes.VorticityCoadjointEnstrophy` (`orbitTraversal = (ν/ħ)·∫Ω`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSLerayIntegratedEnstrophy

open Physlib.QuantumMechanics.ComplexAction.NavierStokes.VorticityCoadjointEnstrophy


/-- **[Leray's finite enstrophy budget] `∫Ω ≤ E₀/ν`.** From the entropic-time identity
`τ = (ν/ħ)·∫Ω = orbitTraversal ν ħ (∫Ω)` and the energy bound `τ ≤ E₀/ħ`, the integrated enstrophy is
bounded by the initial energy over the viscosity — Leray's `L¹`-in-time enstrophy budget. -/
lemma integratedEnstrophy_bound (ν ħ Ienstrophy E₀ : ℝ) (hν : 0 < ν) (hħ : 0 < ħ)
    (h : orbitTraversal ν ħ Ienstrophy ≤ E₀ / ħ) : Ienstrophy ≤ E₀ / ν := by
  rw [orbitTraversal, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hħ] at h
  rw [le_div_iff₀ hν, mul_comm]
  simpa using h


/-- **[The subcritical threshold is positive] `ν⁴ λ₁ C_L⁴ > 0`.** The enstrophy threshold below which the
Navier–Stokes solution is subcritical is a product of positive constants (viscosity `ν`, first
eigenvalue `λ₁`, Ladyzhenskaya constant `C_L`). -/
lemma subcriticalThreshold_pos (ν lam₁ C_L : ℝ) (hν : 0 < ν) (hlam : 0 < lam₁) (hC : 0 < C_L) :
    0 < ν ^ 4 * lam₁ * C_L ^ 4 := by
  positivity

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSLerayIntegratedEnstrophy

end
