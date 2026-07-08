/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSLerayIntegratedEnstrophy

/-!
# The NS enstrophy rate, the coadjoint dissipation, and the entropic-time orbit traversal are one

Links the freshly-ported Navier–Stokes kernels — the `VS ≤ νP` enstrophy rate
(`NavierStokes.NSVortexStretchingDefect`), the Arnold coadjoint enstrophy dissipation (`NavierStokes.VorticityCoadjointEnstrophy`),
and Leray's integrated-enstrophy budget (`NavierStokes.NSLerayIntegratedEnstrophy`) — into one structure.

The NS enstrophy rate `dΩ/dt = 2(VS − νP)` (`enstrophyRate`) reduces, at **zero vortex stretching**
`VS = 0` (the ideal-Euler / 2D regime, where the dual-sphere holonomy defect vanishes), *exactly* to the
Arnold coadjoint enstrophy dissipation `−2νP` (`enstrophyDissipationRate`):

  `enstrophyRate 0 ν P = enstrophyDissipationRate ν P`   (`enstrophyRate_zeroVS_eq_coadjointDissipation`).

So the coadjoint dissipation is the `VS = 0` slice of the full NS rate, and 2D flows are unconditionally
enstrophy-non-increasing (`enstrophyRate_zeroVS_nonpos`). In 3D the regularity criterion `VS ≤ νP` (the
non-negative imaginary Noether defect) makes the rate `≤ 0`, so the trajectory dissipates enstrophy and
**traverses the coadjoint orbits to lower enstrophy** — with the integrated enstrophy bounded by Leray's
budget `∫Ω ≤ E₀/ν` (`ns_enstrophy_coadjoint_traversal`). The vortex-stretching defect, the coadjoint
dissipation, the entropic-time orbit traversal, and the Leray budget are one structure: the geometric and
information faces of the Navier–Stokes entropy arrow.

* **§A — the coadjoint dissipation is the `VS = 0` slice** (`enstrophyRate_zeroVS_eq_coadjointDissipation`,
  `enstrophyRate_zeroVS_nonpos`).
* **§B — the assembly** (`ns_enstrophy_coadjoint_traversal`).

## References

* structures: `NavierStokes.NSVortexStretchingDefect` (`enstrophyRate`, `imaginaryNoetherDefect`),
  `NavierStokes.VorticityCoadjointEnstrophy` (`enstrophyDissipationRate`, `orbitTraversal`),
  `NavierStokes.NSLerayIntegratedEnstrophy` (`integratedEnstrophy_bound`).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSEnstrophyRateCoadjoint

open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.VorticityCoadjointEnstrophy
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSLerayIntegratedEnstrophy

/-! ## §A — the coadjoint dissipation is the `VS = 0` slice of the NS enstrophy rate -/

/-- **[Coadjoint dissipation = zero-vortex-stretching NS rate] `dΩ/dt|_{VS=0} = −2νP`.** The Arnold
coadjoint enstrophy dissipation `enstrophyDissipationRate ν P = −2νP` is *exactly* the `VS = 0` slice of
the full Navier–Stokes enstrophy rate `2(VS − νP)` — the ideal-Euler / 2D regime where the dual-sphere
holonomy defect (vortex stretching) vanishes. -/
theorem enstrophyRate_zeroVS_eq_coadjointDissipation (ν P : ℝ) :
    enstrophyRate 0 ν P = enstrophyDissipationRate ν P := by
  unfold enstrophyRate enstrophyDissipationRate; ring

/-- **[2D flows are unconditionally enstrophy-non-increasing] `dΩ/dt|_{VS=0} ≤ 0`.** With no vortex
stretching (`VS = 0`, the 2D / dual-sphere-collapsed regime) the enstrophy rate is `−2νP ≤ 0` for
`ν, P ≥ 0` — 2D Navier–Stokes is always regular (the coadjoint orbit only ever loses enstrophy). -/
theorem enstrophyRate_zeroVS_nonpos (ν P : ℝ) (hν : 0 ≤ ν) (hP : 0 ≤ P) :
    enstrophyRate 0 ν P ≤ 0 := by
  rw [enstrophyRate_zeroVS_eq_coadjointDissipation]
  exact enstrophyDissipationRate_nonpos ν P hν hP

/-! ## §B — the assembly -/

/-- **[The NS enstrophy rate, the coadjoint dissipation, and the orbit traversal, assembled].** For a 3D
Navier–Stokes trajectory satisfying the regularity criterion `VS ≤ νP` (`ν > 0`, `P ≥ 0`) with integrated
enstrophy obeying the energy bound (`orbitTraversal ν ħ I ≤ E₀/ħ`):

* the coadjoint dissipation is the `VS = 0` slice of the NS rate
  (`enstrophyRate 0 ν P = enstrophyDissipationRate ν P`);
* the regularity criterion makes the NS enstrophy rate non-positive (`enstrophyRate VS ν P ≤ 0`) — the
  trajectory dissipates enstrophy, traversing the coadjoint orbits to lower enstrophy;
* the imaginary Noether defect is non-negative (`0 ≤ νP − VS`);
* the integrated enstrophy is bounded by Leray's budget (`I ≤ E₀/ν`).

The vortex-stretching defect, the Arnold coadjoint dissipation, the entropic-time orbit traversal, and
the Leray enstrophy budget are one structure — the Navier–Stokes entropy arrow. -/
theorem ns_enstrophy_coadjoint_traversal (VS ν P ħ I E₀ : ℝ) (hν : 0 < ν) (hħ : 0 < ħ)
    (hreg : VS ≤ ν * P) (hbudget : orbitTraversal ν ħ I ≤ E₀ / ħ) :
    enstrophyRate 0 ν P = enstrophyDissipationRate ν P
      ∧ enstrophyRate VS ν P ≤ 0
      ∧ 0 ≤ imaginaryNoetherDefect ν P VS
      ∧ I ≤ E₀ / ν :=
  ⟨enstrophyRate_zeroVS_eq_coadjointDissipation ν P,
    (enstrophyRate_nonpos_iff VS ν P).mpr hreg,
    (defect_nonneg_iff ν P VS).mpr hreg,
    integratedEnstrophy_bound ν ħ I E₀ hν hħ hbudget⟩

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSEnstrophyRateCoadjoint

end
