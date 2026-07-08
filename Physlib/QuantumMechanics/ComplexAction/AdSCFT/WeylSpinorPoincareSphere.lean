/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalBoundaryRepoLinks

/-!
# The Weyl spinor of a fermion lives on the boundary Riemann sphere (its Poincaré-sphere point)

Linking the `AdS₃` conformal boundary (`AdSCFT.ConformalBoundaryRepoLinks`,
`Mathematics.Geometry.StereographicRiemannSphere`) to the repo's **fermion/spinor** formalization —
`Hopf.FibrationSpinorMap` (a two-component spinor `χ` and its Bloch/Poincaré-sphere direction) and
`Hopf.SpinHalfDoubleCover` (spin-½ as the `SU(2)`/`SL(2,ℂ)` double cover).

A two-component **Weyl spinor** `χ = (χ₀, χ₁) ∈ ℂ²` (a massless fermion's spinor) determines a point of
the boundary Riemann sphere `CP¹ = OnePoint ℂ` by its projective ratio `χ₀/χ₁` — the *Poincaré-sphere*
(null) direction the spinor points along. `Hopf.FibrationSpinorMap.hopfBase` gives the same direction as
a `Bloch`/Stokes vector on `S²`; this file gives its `CP¹`-coordinate and the fermion's `SL(2,ℂ)`
transformation law on it.

* **§A — the spinor's Poincaré-sphere point.** `weylRatio χ = χ₀/χ₁ ∈ CP¹` (`∞` if `χ₁ = 0`).
* **§B — projective (gauge) invariance.** `weylRatio (u·χ) = weylRatio χ` for any `u ≠ 0`
 (`weylRatio_smul`): the Poincaré-sphere point depends only on the spinor's *direction*, matching the `S¹`
 phase-fiber invariance of `Hopf.FibrationSpinorMap` (`hopfBase_phase_invariant`).
* **§C — the fermion `SL(2,ℂ)` law is the boundary Möbius action.** For `M ∈ SL(2,ℂ)` the transformed
 spinor `(M₀₀χ₀+M₀₁χ₁, M₁₀χ₀+M₁₁χ₁)` has Poincaré-sphere point equal to the boundary Möbius image of the
 original (`sl2c_weylRatio`): the way a Weyl fermion transforms under a Lorentz boost/rotation `= ` the
 Möbius action of `AdSCFT.ConformalBoundaryRepoLinks.boundary_sl2c_mobius` on its boundary point.

Proven: the Poincaré-sphere point, its gauge invariance, and the `SL(2,ℂ)`-equivariance
(spinor transformation `=` boundary Möbius). Interpretive: identifying `χ₀/χ₁` with the fermion's null
direction on the physical Poincaré/boundary sphere, and with `hopfBase`'s Stokes vector, is the
standard spinor-to-flag/Poincaré-sphere dictionary (not re-derived against the Stokes convention here).

No new axioms.
-/

set_option autoImplicit false

open scoped MatrixGroups
open OnePoint

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.WeylSpinorPoincareSphere

/-! ## §A — the Weyl spinor's Poincaré-sphere point on `CP¹` -/

/-- **The Poincaré-sphere `CP¹` point of a Weyl spinor** `χ ↦ χ₀/χ₁ ∈ OnePoint ℂ` (`∞` if `χ₁ = 0`): the null
direction the two-component spinor points along, as a point of the boundary Riemann sphere. -/
noncomputable def weylRatio (χ : Fin 2 → ℂ) : OnePoint ℂ :=
  if χ 1 = 0 then ∞ else ((χ 0 / χ 1 : ℂ) : OnePoint ℂ)

/-! ## §B — projective (gauge) invariance -/

/-- **The Poincaré-sphere point is scale/gauge invariant** `weylRatio (u·χ) = weylRatio χ` for `u ≠ 0`: it
depends only on the spinor's direction — the projective / `S¹`-phase-fiber invariance that
`Hopf.FibrationSpinorMap.hopfBase_phase_invariant` records for the Stokes-vector form. -/
theorem weylRatio_smul (u : ℂ) (hu : u ≠ 0) (χ : Fin 2 → ℂ) :
    weylRatio (u • χ) = weylRatio χ := by
  unfold weylRatio
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases h1 : χ 1 = 0
  · simp [h1]
  · rw [if_neg (mul_ne_zero hu h1), if_neg h1]
    congr 1
    rw [mul_div_mul_left _ _ hu]

/-! ## §C — the fermion `SL(2,ℂ)` transformation is the boundary Möbius action -/

/-- **The Weyl-fermion `SL(2,ℂ)` law is the boundary Möbius action** `M • (χ₀/χ₁) =
(M₀₀χ₀+M₀₁χ₁)/(M₁₀χ₀+M₁₁χ₁)`: the Poincaré-sphere point of the `SL(2,ℂ)`-transformed spinor is the boundary
Möbius image of the original spinor's Poincaré-sphere point (`boundary_sl2c_mobius`). This is the fermion's
Lorentz transformation law realized on the boundary Riemann sphere. -/
theorem sl2c_weylRatio (M : SL(2, ℂ)) (a b : ℂ) (hb : b ≠ 0)
    (hden : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * a + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * b ≠ 0) :
    M.toGL • ((a / b : ℂ) : OnePoint ℂ)
      = ((((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * a + (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * b)
          / ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * a + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * b)
          : ℂ) : OnePoint ℂ) := by
  have hk : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * (a / b) + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
    have he : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * (a / b) + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1
        = ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * a + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * b) / b := by
      field_simp
    rw [he]; exact div_ne_zero hden hb
  rw [ConformalBoundaryRepoLinks.boundary_sl2c_mobius M (a / b) hk]
  congr 1
  rw [div_eq_div_iff hk hden]
  field_simp

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.WeylSpinorPoincareSphere
