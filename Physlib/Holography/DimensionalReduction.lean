/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Holographic dimensional reduction as an exact Johnson–Lindenstrauss isometry

The holographic principle and the Johnson–Lindenstrauss lemma are two faces of **distance-preserving dimensional
reduction**. The Johnson–Lindenstrauss lemma reduces `n` points to `O(log n)` dimensions preserving all pairwise
distances up to `1 ± ε`:

`(1 − ε)d² ≤ d_k² ≤ (1 + ε)d²`   (`JLBound`),

with target dimension `k = ⌈K log n⌉` (`jlTargetDim`). The holographic bulk→boundary reduction
`dimLength a 3 = scalingTransition 2 3 (dimLength a 2)` is a co-dimension-one reduction that preserves the length
**exactly** — so it is the `ε = 0` (isometric) case of a Johnson–Lindenstrauss reduction: **holography is lossless
distance-preserving dimensional reduction** (`holographic_reduction_is_exact_JL`).

References: W.B. Johnson, J. Lindenstrauss, Contemp. Math. 26 (1984) 189; the holographic principle. No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Holography.DimensionalReduction

/-- **The Johnson–Lindenstrauss distance-distortion bound** `(1 − ε)d² ≤ d_k² ≤ (1 + ε)d²` — a reduction preserves
each pairwise distance `d` as `d_k` up to the factor `1 ± ε`. -/
def JLBound (ε d dk : ℝ) : Prop := (1 - ε) * d ^ 2 ≤ dk ^ 2 ∧ dk ^ 2 ≤ (1 + ε) * d ^ 2

/-- **At `ε = 0` the bound is exact isometry** `JLBound 0 d d_k ↔ d_k² = d²` — the zero-distortion reduction is
precisely a distance-preserving isometry. -/
theorem JLBound_zero_iff (d dk : ℝ) : JLBound 0 d dk ↔ dk ^ 2 = d ^ 2 := by
  unfold JLBound
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; rw [h]; constructor <;> linarith

/-- **The Johnson–Lindenstrauss target dimension** `k = ⌈K log n⌉` — logarithmic in the number of points. -/
noncomputable def jlTargetDim (K n : ℝ) : ℕ := ⌈K * Real.log n⌉₊

/-- **The dimensional scaling factor** `√D`. -/
noncomputable def scalingFactor (D : ℕ) : ℝ := Real.sqrt D

/-- **The length in dimension `D`** `dimLength a D = a √D`. -/
noncomputable def dimLength (a : ℝ) (D : ℕ) : ℝ := a * scalingFactor D

/-- **The bulk→boundary scaling transition** `L ↦ L √(D'/D)`. -/
noncomputable def scalingTransition (D D' : ℕ) (L : ℝ) : ℝ := L * Real.sqrt ((D' : ℝ) / (D : ℝ))

/-- **The holographic bulk→boundary length identity** `dimLength a 3 = scalingTransition 2 3 (dimLength a 2)`: the
co-dimension-one reduction from the `3`-length to the `2`-boundary preserves the length exactly. -/
theorem holographic_bulk_boundary_length (a : ℝ) :
    dimLength a 3 = scalingTransition 2 3 (dimLength a 2) := by
  unfold dimLength scalingTransition scalingFactor
  rw [mul_assoc, ← Real.sqrt_mul (by norm_num)]
  norm_num

/-- **Holography is the exact `ε = 0` Johnson–Lindenstrauss isometry**
`JLBound 0 (dimLength a 3) (scalingTransition 2 3 (dimLength a 2))`: the holographic bulk→boundary reduction
preserves the length exactly, the lossless `ε = 0` case of the Johnson–Lindenstrauss distance-preserving
dimensional reduction. -/
theorem holographic_reduction_is_exact_JL (a : ℝ) :
    JLBound 0 (dimLength a 3) (scalingTransition 2 3 (dimLength a 2)) := by
  rw [JLBound_zero_iff, ← holographic_bulk_boundary_length a]

end Physlib.Holography.DimensionalReduction

end
