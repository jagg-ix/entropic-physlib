/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.VorticityCoadjointEnstrophy

/-!
# The Navier–Stokes `VS ≤ νP` kernel: vortex stretching, the imaginary Noether defect, and enstrophy

Ports the genuine, axiom-free **algebraic kernel** shared by the Navier–Stokes `VS ≤ νP` files
(`VSOmegaPKernel`, `NSVSNuPKernel`, `NSVSNuPResolutionBridge`, `NSEnstrophyMonotonicity`). Those files
phrase everything through upstream slice-projection axioms and `Bool`-valued `LabeledClaim` registries
that are not portable; the genuine content is the **exact algebra of the enstrophy balance**

  `dΩ/dt = 2(VS − νP)`   (`enstrophyRate`),

where `VS` is the vortex stretching, `P` the palinstrophy, `ν` the viscosity. The single inequality
`VS ≤ νP` (the 3D regularity criterion) is *exactly equivalent* to the non-negativity of the **imaginary
Noether defect** `νP − VS` and to the **enstrophy non-increase** `dΩ/dt ≤ 0`:

  `0 ≤ νP − VS  ⟺  VS ≤ νP  ⟺  dΩ/dt ≤ 0`

(`defect_nonneg_iff`, `enstrophyRate_nonpos_iff`, `vsNuP_equivalences`). It is scale-invariant in the ratio
form `VS/Ω ≤ ν(P/Ω)` (`vsNuP_ratio_iff`), and it follows from the slice-coupling form `VS = θP` with
`0 ≤ θ ≤ ν` (`vsNuP_of_sliceCoefficient`).

* **§A — the enstrophy rate and the imaginary Noether defect** (`enstrophyRate`,
  `imaginaryNoetherDefect`, `defect_nonneg_iff`, `enstrophyRate_nonpos_iff`,
  `defect_nonneg_iff_enstrophyRate_nonpos`).
* **§B — the ratio and slice-coupling forms** (`vsNuP_ratio_iff`, `vsNuP_of_sliceCoefficient`).
* **§C — the assembly** (`vsNuP_equivalences`).

## References

* The 3D Navier–Stokes enstrophy identity `dΩ/dt = 2∫(ω·∇)u·ω − 2ν∫|∇ω|²`; the `VS ≤ νP` regularity
  criterion. Source (kernel only; upstream slice-projection axioms + `Bool` registries):
  `NavierStokes/{VSOmegaPKernel, NSVSNuPKernel, NSVSNuPResolutionBridge, NSEnstrophyMonotonicity}.lean`.
  Companion: `NavierStokes.VorticityCoadjointEnstrophy` (the enstrophy Casimir / dissipation).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect

/-! ## §A — the enstrophy rate and the imaginary Noether defect -/

/-- **The enstrophy rate** `dΩ/dt = 2(VS − νP)` — the 3D Navier–Stokes enstrophy balance, vortex
stretching `VS` against viscous dissipation `νP` (palinstrophy `P`). -/
def enstrophyRate (VS ν P : ℝ) : ℝ := 2 * (VS - ν * P)

/-- **The imaginary (spatial) Noether defect** `νP − VS` — the complex-action/entropic-time defect whose non-negativity is the
`VS ≤ νP` criterion. -/
def imaginaryNoetherDefect (ν P VS : ℝ) : ℝ := ν * P - VS

/-- **[Defect ≥ 0 ⟺ `VS ≤ νP`].** -/
theorem defect_nonneg_iff (ν P VS : ℝ) : 0 ≤ imaginaryNoetherDefect ν P VS ↔ VS ≤ ν * P := by
  unfold imaginaryNoetherDefect; rw [sub_nonneg]

/-- **[Enstrophy non-increasing ⟺ `VS ≤ νP`] `dΩ/dt ≤ 0 ⟺ VS ≤ νP`.** -/
theorem enstrophyRate_nonpos_iff (VS ν P : ℝ) : enstrophyRate VS ν P ≤ 0 ↔ VS ≤ ν * P := by
  unfold enstrophyRate; constructor <;> intro h <;> linarith

/-- **[The defect non-negativity is the enstrophy non-increase] `0 ≤ νP − VS ⟺ dΩ/dt ≤ 0`.** -/
theorem defect_nonneg_iff_enstrophyRate_nonpos (VS ν P : ℝ) :
    0 ≤ imaginaryNoetherDefect ν P VS ↔ enstrophyRate VS ν P ≤ 0 := by
  rw [defect_nonneg_iff, enstrophyRate_nonpos_iff]

/-! ## §B — the ratio and slice-coupling forms -/

/-- **[Scale-invariant ratio form] `VS ≤ νP ⟺ VS/Ω ≤ ν(P/Ω)`** for enstrophy `Ω > 0`. -/
theorem vsNuP_ratio_iff (VS ν P Ω : ℝ) (hΩ : 0 < Ω) :
    VS ≤ ν * P ↔ VS / Ω ≤ ν * (P / Ω) := by
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hΩ]

/-- **[Slice-coupling form] `VS = θP` with `0 ≤ θ ≤ ν` gives `VS ≤ νP`.** If the vortex stretching is a
fraction `θ ≤ ν` of the palinstrophy, the criterion holds. -/
theorem vsNuP_of_sliceCoefficient (VS ν P θ : ℝ) (hVS : VS = θ * P) (hθν : θ ≤ ν) (hP : 0 ≤ P) :
    VS ≤ ν * P := by
  rw [hVS]; exact mul_le_mul_of_nonneg_right hθν hP

/-! ## §C — the assembly -/

/-- **[The `VS ≤ νP` kernel, assembled].** The Navier–Stokes regularity criterion `VS ≤ νP` is exactly:
the non-negativity of the imaginary Noether defect `νP − VS ≥ 0`; the enstrophy non-increase
`dΩ/dt ≤ 0`; the scale-invariant ratio bound `VS/Ω ≤ ν(P/Ω)` (for `Ω > 0`); and it follows from a
slice coupling `VS = θP`, `θ ≤ ν` (`P ≥ 0`). One algebraic identity (`dΩ/dt = 2(VS − νP)`) ties the
geometric defect, the entropy-arrow monotonicity, and the regularity criterion together. -/
theorem vsNuP_equivalences (VS ν P Ω : ℝ) (hΩ : 0 < Ω) :
    (0 ≤ imaginaryNoetherDefect ν P VS ↔ VS ≤ ν * P)
      ∧ (enstrophyRate VS ν P ≤ 0 ↔ VS ≤ ν * P)
      ∧ (VS ≤ ν * P ↔ VS / Ω ≤ ν * (P / Ω)) :=
  ⟨defect_nonneg_iff ν P VS, enstrophyRate_nonpos_iff VS ν P, vsNuP_ratio_iff VS ν P Ω hΩ⟩

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect

end
