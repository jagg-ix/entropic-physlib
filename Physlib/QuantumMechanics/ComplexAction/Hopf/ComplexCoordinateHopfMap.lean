/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Complex.Basic

/-!
# The Hopf fibration `S³ → S²` in complex coordinates

`Hopf.QuaternionIsoclinicHopfFibration` builds the Hopf map from the **quaternion** side
(`hopf q = q·i·q̄`). This file gives the equivalent **complex-coordinate** map — the one the source
notes state as `(z₁, z₂) ↦ (2 z₁ z̄₂, |z₁|² − |z₂|²)` — over Mathlib's `ℂ`, where a pair `(z₁, z₂)` with
`|z₁|² + |z₂|² = 1` is a point of `S³ ⊂ ℂ²`.

Writing the image as a "plane" part `2 z₁ z̄₂ ∈ ℂ` and a "height" part `|z₁|² − |z₂|² ∈ ℝ` (so the
target is `ℂ × ℝ ≅ ℝ³`):

* **the map lands on `S²`.** `|2 z₁ z̄₂|² + (|z₁|² − |z₂|²)² = (|z₁|² + |z₂|²)²`
 (`hopf_normSq_identity`), hence `= 1` on `S³` (`hopf_onSphere`) — the exact Lagrange-type identity
 `4ab + (a−b)² = (a+b)²` with `a = |z₁|²`, `b = |z₂|²`.
* **the fibers are the `S¹` orbits.** For every unit `u` (`|u|² = 1`), `hopf(u z₁, u z₂) = hopf(z₁, z₂)`
 in both parts (`hopfPlane_fiber`, `hopfHeight_fiber`): the diagonal `U(1)` action `(z₁,z₂) ↦ (u z₁, u z₂)`
 leaves the image fixed. This is the circle fiber of the fibration `S³ → S²`.

Proven: the on-`S²` identity and the `S¹`-fiber invariance — the two defining
properties of the Hopf map, as exact algebra over `ℂ`. Interpretive: the identification of the unit
pairs with `S³` and of the image with `S² ⊂ ℝ³`, and the equivalence with the quaternion form
`q·i·q̄` of `Hopf.QuaternionIsoclinicHopfFibration`, is the standard geometric dictionary.

## References

* H. Hopf, "Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche" (1931); the complex
 presentation `(z₁,z₂) ↦ (2z₁z̄₂, |z₁|²−|z₂|²)`. Complements `Hopf.QuaternionIsoclinicHopfFibration`.

No additional assumptions.
-/

set_option autoImplicit false

open ComplexConjugate

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Hopf.ComplexCoordinateHopfMap

/-- **The "plane" part of the Hopf image** `2 z₁ z̄₂ ∈ ℂ`. -/
def hopfPlane (z₁ z₂ : ℂ) : ℂ := 2 * z₁ * conj z₂

/-- **The "height" part of the Hopf image** `|z₁|² − |z₂|² ∈ ℝ`. -/
noncomputable def hopfHeight (z₁ z₂ : ℂ) : ℝ := Complex.normSq z₁ - Complex.normSq z₂

/-- **The Hopf image lies on a sphere** `|2 z₁ z̄₂|² + (|z₁|² − |z₂|²)² = (|z₁|² + |z₂|²)²`: the exact
identity `4ab + (a−b)² = (a+b)²` with `a = |z₁|²`, `b = |z₂|²`. -/
theorem hopf_normSq_identity (z₁ z₂ : ℂ) :
    Complex.normSq (hopfPlane z₁ z₂) + hopfHeight z₁ z₂ ^ 2
      = (Complex.normSq z₁ + Complex.normSq z₂) ^ 2 := by
  simp only [hopfPlane, hopfHeight, Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_ofNat]
  ring

/-- **The Hopf map sends `S³` to `S²`** `|2 z₁ z̄₂|² + (|z₁|² − |z₂|²)² = 1` when `|z₁|² + |z₂|² = 1`. -/
theorem hopf_onSphere (z₁ z₂ : ℂ) (h : Complex.normSq z₁ + Complex.normSq z₂ = 1) :
    Complex.normSq (hopfPlane z₁ z₂) + hopfHeight z₁ z₂ ^ 2 = 1 := by
  rw [hopf_normSq_identity, h]; norm_num

/-- **The plane part is `S¹`-fiber invariant** `hopfPlane (u z₁, u z₂) = hopfPlane (z₁, z₂)` for any unit
`u` (`|u|² = 1`): the diagonal `U(1)` action leaves the plane part fixed. -/
theorem hopfPlane_fiber (u z₁ z₂ : ℂ) (hu : Complex.normSq u = 1) :
    hopfPlane (u * z₁) (u * z₂) = hopfPlane z₁ z₂ := by
  have huc : u * conj u = 1 := by rw [Complex.mul_conj, hu, Complex.ofReal_one]
  unfold hopfPlane
  have hstep : 2 * (u * z₁) * conj (u * z₂) = (u * conj u) * (2 * z₁ * conj z₂) := by
    rw [map_mul]; ring
  rw [hstep, huc, one_mul]

/-- **The height part is `S¹`-fiber invariant** `hopfHeight (u z₁, u z₂) = hopfHeight (z₁, z₂)` for any
unit `u`: `|u z|² = |u|²|z|² = |z|²`. -/
theorem hopfHeight_fiber (u z₁ z₂ : ℂ) (hu : Complex.normSq u = 1) :
    hopfHeight (u * z₁) (u * z₂) = hopfHeight z₁ z₂ := by
  unfold hopfHeight
  rw [Complex.normSq_mul, Complex.normSq_mul, hu]; ring

end Physlib.QuantumMechanics.ComplexAction.Hopf.ComplexCoordinateHopfMap
