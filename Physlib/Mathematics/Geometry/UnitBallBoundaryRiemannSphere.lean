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
# Unit-ball frontier and the Riemann sphere

This module proves elementary geometry used by later files: the frontier of the open unit ball in
`EuclideanSpace ℝ (Fin 3)` is the unit sphere; the inverse stereographic chart from `ℂ` into that sphere
is injective and misses the north pole; `OnePoint ℂ` is equivalent to the complex projective line supplied
by Mathlib; and the `GL(2,ℂ)` action on finite points of `OnePoint ℂ` has the fractional-linear formula.

It deliberately does not define anti-de Sitter geometry, a conformal compactification, a conformal field
theory, or an AdS/CFT correspondence. Those structures require additional metric and analytic data.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Mathematics.Geometry.UnitBallBoundaryRiemannSphere

open Metric
open Physlib.Mathematics.Geometry.StereographicRiemannSphere


/-- **The Poincaré-ball model of (Euclidean) the open unit ball / `ℍ³`**: the open unit ball `B³ ⊂ ℝ³`. -/
def unitBall3 : Set (EuclideanSpace ℝ (Fin 3)) := ball 0 1

/-- **The frontier of the open unit ball is the `2`-sphere** `∂(B³) = S²`: the topological frontier of the
ball model is the unit sphere. -/
lemma unitBall3_frontier_eq_sphere :
    frontier unitBall3 = sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [unitBall3, frontier_ball 0 one_ne_zero]


/-- **The stereographic chart is injective** `ℂ ↪ S²`: distinct complex complex coordinates give
distinct sphere points (a left inverse exists, `stereoProj ∘ stereoInv = id`). -/
lemma stereoInv_injective : Function.Injective stereoInv := by
  intro w₁ w₂ h
  have h₁ := stereoProj_stereoInv w₁
  rw [h, stereoProj_stereoInv w₂] at h₁
  exact h₁.symm

/-- **The chart misses exactly the north pole** `(stereoInv w).3 ≠ 1`: no complex coordinate maps to the
north pole `(0,0,1)`, which is therefore the point at infinity of `CP¹ = ℂ ∪ {∞}`. -/
lemma stereoInv_ne_northPole (w : ℂ) : (stereoInv w).2.2 ≠ 1 := by
  have hd : Complex.normSq w + 1 ≠ 0 :=
    (by have := Complex.normSq_nonneg w; linarith : (0 : ℝ) < Complex.normSq w + 1).ne'
  simp only [stereoInv]
  intro hcontra
  field_simp [hd] at hcontra
  linarith

/-- **`CP¹ = ℂ ∪ {∞}` is the complex projective line**: Mathlib's identification of the one-point
compactification of `ℂ` (the Riemann sphere the unit sphere is) with `ℙ¹(ℂ)`. -/
lemma riemannSphere_equiv_projectiveLine :
    Nonempty (OnePoint ℂ ≃ Projectivization ℂ (Fin 2 → ℂ)) :=
  ⟨OnePoint.equivProjectivization ℂ⟩


/-- **The fractional-linear action is by Möbius transformations** `g • z = (g₀₀ z + g₀₁)/(g₁₀ z + g₁₁)`
on finite sphere points (where the denominator is nonzero): the the open unit ball isometry `g ∈ GL(2,ℂ)` acts on
the one-point complex plane `OnePoint ℂ` as the the finite-point coordinate chart global conformal (Möbius) transformation. -/
lemma onePoint_complex_mobius_action (g : GL (Fin 2) ℂ) (k : ℂ) (hk : g 1 0 * k + g 1 1 ≠ 0) :
    g • (k : OnePoint ℂ)
      = (((g 0 0 * k + g 0 1) / (g 1 0 * k + g 1 1) : ℂ) : OnePoint ℂ) := by
  rw [OnePoint.smul_some_eq_ite, if_neg hk]

end Physlib.Mathematics.Geometry.UnitBallBoundaryRiemannSphere
