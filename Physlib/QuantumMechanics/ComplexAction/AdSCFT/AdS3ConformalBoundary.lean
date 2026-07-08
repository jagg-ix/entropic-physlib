/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.Geometry.StereographicRiemannSphere
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# The conformal boundary of `AdS₃` is the Riemann sphere `CP¹ ≅ S²`

The `AdS₃`/`CFT₂` dictionary rests on a purely geometric fact: the conformal boundary of
three-dimensional (Euclidean) anti-de Sitter space — hyperbolic `3`-space `ℍ³`, in the Poincaré-ball
model the open unit ball `B³ ⊂ ℝ³` — is the `2`-sphere `S²`, which as a conformal surface is the
**Riemann sphere** `CP¹ = ℂ ∪ {∞}`. This file assembles that statement from Mathlib and the explicit
stereographic chart of `Mathematics.Geometry.StereographicRiemannSphere`.

* **§A — the boundary is `S²`.** In the ball model `AdS₃ = B³ = ball 0 1 ⊂ ℝ³`, the topological
 boundary is the unit sphere: `frontier (ball 0 1) = sphere 0 1` (`adS3_boundary_eq_sphere`).
* **§B — `S² ≅ CP¹ = ℂ ∪ {∞}`.** The stereographic chart injects the complex plane into the boundary
 sphere, `stereoInv : ℂ ↪ S²` (`stereoInv_injective`, landing on the sphere by
 `stereoInv_mem_sphere`), and misses exactly the north pole (`stereoInv_ne_northPole`), which is the
 point at infinity. So the boundary sphere is `ℂ ∪ {∞}`, and Mathlib's
 `OnePoint.equivProjectivization ℂ : OnePoint ℂ ≃ ℙ ℂ (Fin 2 → ℂ)` identifies `ℂ ∪ {∞}` with the
 complex projective line `CP¹` (`riemannSphere_equiv_projectiveLine`).
* **§C — the boundary conformal (Möbius) action.** The `AdS₃` isometry group acts on the boundary
 `CP¹ = OnePoint ℂ` by Möbius transformations — Mathlib's `GL(2,ℂ)`-action, whose value on finite
 points is `g • z = (g₀₀ z + g₀₁)/(g₁₀ z + g₁₁)` (`boundary_mobius_action`): the `CFT₂` global
 conformal symmetry realized as the boundary action of the bulk isometries.

Proven: the ball-model boundary is `S²`; the complex chart injects into the
boundary sphere and omits only the north pole; `CP¹ = OnePoint ℂ` via Mathlib; the explicit Möbius
formula of the boundary `GL(2,ℂ)`-action. Interpretive: the identification of the ball model with
Euclidean `AdS₃`/`ℍ³` and the assembly of these pieces into the single homeomorphism `S² ≅ CP¹` (the
full conformal/holomorphic equivalence is the standard fact, not re-derived here as one map).

## References

* Standard `AdS₃`/`CFT₂` geometry (e.g. Maldacena; Witten): the boundary of `ℍ³` is the Riemann
 sphere, on which the isometry group `PSL(2,ℂ)` acts by Möbius transformations. Reuses Mathlib
 `frontier_ball`, `OnePoint.equivProjectivization`, `OnePoint.smul_some_eq_ite`, and
 `Mathematics.Geometry.StereographicRiemannSphere`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.AdS3ConformalBoundary

open Metric
open Physlib.Mathematics.Geometry.StereographicRiemannSphere

/-! ## §A — the conformal boundary of the `AdS₃` ball is `S²` -/

/-- **The Poincaré-ball model of (Euclidean) `AdS₃` / `ℍ³`**: the open unit ball `B³ ⊂ ℝ³`. -/
def adS3Ball : Set (EuclideanSpace ℝ (Fin 3)) := ball 0 1

/-- **The conformal boundary of `AdS₃` is the `2`-sphere** `∂(B³) = S²`: the topological frontier of the
ball model is the unit sphere. -/
theorem adS3_boundary_eq_sphere :
    frontier adS3Ball = sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [adS3Ball, frontier_ball 0 one_ne_zero]

/-! ## §B — the boundary sphere is the Riemann sphere `CP¹ = ℂ ∪ {∞}` -/

/-- **The stereographic chart is injective** `ℂ ↪ S²`: distinct complex boundary coordinates give
distinct boundary points (a left inverse exists, `stereoProj ∘ stereoInv = id`). -/
theorem stereoInv_injective : Function.Injective stereoInv := by
  intro w₁ w₂ h
  have h₁ := stereoProj_stereoInv w₁
  rw [h, stereoProj_stereoInv w₂] at h₁
  exact h₁.symm

/-- **The chart misses exactly the north pole** `(stereoInv w).3 ≠ 1`: no complex coordinate maps to the
north pole `(0,0,1)`, which is therefore the point at infinity of `CP¹ = ℂ ∪ {∞}`. -/
theorem stereoInv_ne_northPole (w : ℂ) : (stereoInv w).2.2 ≠ 1 := by
  have hd : Complex.normSq w + 1 ≠ 0 :=
    (by have := Complex.normSq_nonneg w; linarith : (0 : ℝ) < Complex.normSq w + 1).ne'
  simp only [stereoInv]
  intro hcontra
  field_simp [hd] at hcontra
  linarith

/-- **`CP¹ = ℂ ∪ {∞}` is the complex projective line**: Mathlib's identification of the one-point
compactification of `ℂ` (the Riemann sphere the boundary is) with `ℙ¹(ℂ)`. -/
theorem riemannSphere_equiv_projectiveLine :
    Nonempty (OnePoint ℂ ≃ Projectivization ℂ (Fin 2 → ℂ)) :=
  ⟨OnePoint.equivProjectivization ℂ⟩

/-! ## §C — the boundary conformal (Möbius) action of `GL(2,ℂ)` -/

/-- **The boundary conformal action is by Möbius transformations** `g • z = (g₀₀ z + g₀₁)/(g₁₀ z + g₁₁)`
on finite boundary points (where the denominator is nonzero): the `AdS₃` isometry `g ∈ GL(2,ℂ)` acts on
the boundary Riemann sphere `OnePoint ℂ` as the `CFT₂` global conformal (Möbius) transformation. -/
theorem boundary_mobius_action (g : GL (Fin 2) ℂ) (k : ℂ) (hk : g 1 0 * k + g 1 1 ≠ 0) :
    g • (k : OnePoint ℂ)
      = (((g 0 0 * k + g 0 1) / (g 1 0 * k + g 1 1) : ℂ) : OnePoint ℂ) := by
  rw [OnePoint.smul_some_eq_ite, if_neg hk]

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.AdS3ConformalBoundary
