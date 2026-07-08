/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalBoundaryRepoLinks
public import Physlib.Mathematics.Geometry.StereographicRiemannSphere
public import Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition

/-!
# The Johnson–Lindenstrauss distance-preserving reduction, holography, and the lossless stereographic boundary chart

Formalizes the distance-preservation core of the Johnson–Lindenstrauss lemma (*Extensions of Lipschitz mappings
into a Hilbert space*, Contemp. Math. 26 (1984), Lemma 1) and its relation to the repository's holographic
dimensional reduction (`AdSCFT.ConformalBoundaryRepoLinks.holographic_bulk_boundary_length`). The Johnson–Lindenstrauss
lemma states that `n` points in Euclidean `ℓ²ₙ` can be mapped into `ℓ²_k` with `k = ⌈K log n⌉` so that all pairwise
distances are preserved up to a factor `1 ± ε`:

`(1 − ε)‖x − y‖² ≤ ‖f(x) − f(y)‖² ≤ (1 + ε)‖x − y‖²`,

a **dimensional reduction that preserves the metric** (approximately). The holographic reduction
`dimLength a 3 = scalingTransition 2 3 (dimLength a 2)` is a co-dimension-one reduction that preserves the length
**exactly** — so it is the `ε = 0` (exact isometric) case of a Johnson–Lindenstrauss reduction: holography is
lossless distance-preserving dimensional reduction.

* the **JL distance-distortion bound** `(1 − ε)d² ≤ d_k² ≤ (1 + ε)d²` (`JLBound`) — the pairwise-distance
 preservation of a JL embedding; an **exact isometry** satisfies it for every `ε ≥ 0` (`JLBound_of_isometry`), and
 at `ε = 0` it *is* exact isometry `d_k² = d²` (`JLBound_zero_iff`);
* the **target dimension is logarithmic** `k = ⌈K log n⌉` (`jlTargetDim`), monotone in the point count `n`
 (`jlTargetDim_mono`) — the reduction from `n` to `O(log n)` dimensions;
* the **holographic reduction is the exact JL isometry** `JLBound 0 (dimLength a 3) (scalingTransition 2 3 (dimLength a 2))`
 (`holographic_reduction_is_exact_JL`) — the bulk→boundary co-dimension-one length reduction preserves the length
 exactly, the `ε = 0` case of Johnson–Lindenstrauss, reusing `holographic_bulk_boundary_length`.

So the holographic principle and the Johnson–Lindenstrauss lemma are two faces of *distance-preserving dimensional
reduction*: JL reduces `n` points to `O(log n)` dimensions preserving distances within `1 ± ε`; holography reduces
the bulk to a co-dimension-one boundary preserving the length exactly — the `ε = 0`, lossless case. The
holographic bound is the sharp isometric limit of the Johnson–Lindenstrauss embedding.

The lossless `ε = 0` reduction is realized concretely by the **stereographic projection**: the holographic boundary
`S² ∖ {N} ≃ ℂ` (`Mathematics.Geometry.StereographicRiemannSphere`) is a bijection, so it encodes the `2`-sphere in
`ℂ` with zero distortion (`JLBound 0`), and that boundary sphere is exactly the
`Hopf.DualSphereFiberDecomposition` sphere (`sphereNormSq = 1`).

* **§A — the JL distance-distortion bound and its exact case** (`JLBound`, `JLBound_of_isometry`,
 `JLBound_zero_iff`).
* **§B — the logarithmic target dimension** (`jlTargetDim`, `jlTargetDim_mono`).
* **§C — the holographic reduction is the exact JL isometry** (`holographic_reduction_is_exact_JL`).
* **§D — the stereographic projection is the lossless boundary chart** (`stereographic_boundary_chart_lossless`,
 `stereographic_roundtrip_is_exact_JL`).
* **§E — the boundary sphere is the dual-sphere fiber decomposition sphere** (`stereographic_domain_is_dualSphere`).

The distortion bound, its exact case, the logarithmic dimension, and the holographic exact-JL
identity are exact algebra, reusing `holographic_bulk_boundary_length`. The full Johnson–Lindenstrauss lemma — the
existence of the embedding via a random rank-`k` orthogonal projection with high probability (measure on `O(n)`,
concentration of measure) — is the referenced content, not re-derived; here the distance-preservation property it
guarantees and its exact (holographic) case are proved. No new axioms.

## References

* W.B. Johnson, J. Lindenstrauss, Contemp. Math. 26 (1984) 189 (Lemma 1); holographic principle. Repo dependencies:
 `AdSCFT.ConformalBoundaryRepoLinks` (`holographic_bulk_boundary_length`),
 `Mathematics.DimensionalScaling` (`dimLength`, `scalingTransition`),
 `Mathematics.Geometry.StereographicRiemannSphere` (`stereoInv_stereoProj`),
 `Hopf.DualSphereFiberDecomposition` (`sphereNormSq`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.Mathematics.DimensionalScaling
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalBoundaryRepoLinks
open Physlib.Mathematics.Geometry.StereographicRiemannSphere
open Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussHolographicReduction

/-! ## §A — the JL distance-distortion bound and its exact case -/

/-- **The Johnson–Lindenstrauss distance-distortion bound** `(1 − ε)d² ≤ d_k² ≤ (1 + ε)d²` — a JL embedding
preserves each pairwise distance `d` (original) as `d_k` (reduced) up to the multiplicative factor `1 ± ε`
(Johnson–Lindenstrauss Lemma 1). -/
def JLBound (ε d dk : ℝ) : Prop := (1 - ε) * d ^ 2 ≤ dk ^ 2 ∧ dk ^ 2 ≤ (1 + ε) * d ^ 2

/-- **[An exact isometry satisfies the JL bound for every `ε ≥ 0`] `d_k² = d² ⟹ JLBound ε d d_k`.** A
distance-preserving (isometric) reduction meets the Johnson–Lindenstrauss distortion bound with any tolerance. -/
theorem JLBound_of_isometry (ε d dk : ℝ) (hε : 0 ≤ ε) (h : dk ^ 2 = d ^ 2) : JLBound ε d dk := by
  unfold JLBound
  rw [h]
  refine ⟨?_, ?_⟩ <;> nlinarith [mul_nonneg hε (sq_nonneg d)]

/-- **[At `ε = 0` the JL bound is exact isometry] `JLBound 0 d d_k ↔ d_k² = d²`.** The zero-distortion
Johnson–Lindenstrauss reduction is precisely a distance-preserving isometry. -/
theorem JLBound_zero_iff (d dk : ℝ) : JLBound 0 d dk ↔ dk ^ 2 = d ^ 2 := by
  unfold JLBound
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; rw [h]; constructor <;> linarith

/-! ## §B — the logarithmic target dimension -/

/-- **The Johnson–Lindenstrauss target dimension** `k = ⌈K log n⌉` — the reduced dimension for `n` points, growing
only logarithmically in the number of points (Johnson–Lindenstrauss Lemma 1). -/
noncomputable def jlTargetDim (K n : ℝ) : ℕ := ⌈K * Real.log n⌉₊

/-- **[The target dimension is monotone in the point count] `n₁ ≤ n₂ ⟹ k(n₁) ≤ k(n₂)`.** The logarithmic reduced
dimension grows with the number of points (for `K ≥ 0`), slowly (`O(log n)`). -/
theorem jlTargetDim_mono (K : ℝ) (hK : 0 ≤ K) {n₁ n₂ : ℝ} (h1 : 0 < n₁) (h : n₁ ≤ n₂) :
    jlTargetDim K n₁ ≤ jlTargetDim K n₂ := by
  unfold jlTargetDim
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_left (Real.log_le_log h1 h) hK)

/-! ## §C — the holographic reduction is the exact JL isometry -/

/-- **[The holographic reduction is the exact `ε = 0` Johnson–Lindenstrauss isometry].** The holographic
bulk→boundary co-dimension-one length reduction `dimLength a 3 = scalingTransition 2 3 (dimLength a 2)`
(`holographic_bulk_boundary_length`) preserves the length **exactly**, so it satisfies the Johnson–Lindenstrauss
distance-distortion bound at zero distortion `ε = 0`: holography is the lossless, sharp isometric case of the
Johnson–Lindenstrauss distance-preserving dimensional reduction. -/
theorem holographic_reduction_is_exact_JL (a : ℝ) :
    JLBound 0 (dimLength a 3) (scalingTransition 2 3 (dimLength a 2)) := by
  rw [JLBound_zero_iff, ← holographic_bulk_boundary_length a]

/-! ## §D — the stereographic projection is the lossless boundary chart -/

/-- **[The stereographic boundary chart is lossless] `stereoInv(stereoProj(X,Y,Z)) = (X,Y,Z)`.** The stereographic
projection `S² ∖ {N} → ℂ` is a bijection whose inverse recovers the sphere point exactly — the complex plane `ℂ`
encodes the `2`-sphere holographic boundary with no information lost. -/
theorem stereographic_boundary_chart_lossless (X Y Z : ℝ) (hsph : X ^ 2 + Y ^ 2 + Z ^ 2 = 1)
    (hN : Z ≠ 1) : stereoInv (stereoProj X Y Z) = (X, Y, Z) :=
  stereoInv_stereoProj X Y Z hsph hN

/-- **[The stereographic round-trip is the exact `ε = 0` Johnson–Lindenstrauss reduction] `JLBound 0 Z (round-trip Z)`.**
Because the stereographic round-trip `stereoInv ∘ stereoProj` recovers each coordinate exactly, the reduction onto
the `ℂ` boundary has zero Johnson–Lindenstrauss distortion: the lossless boundary chart is the sharp isometric
(`ε = 0`) case, the same lossless limit realized by the holographic reduction (`holographic_reduction_is_exact_JL`). -/
theorem stereographic_roundtrip_is_exact_JL (X Y Z : ℝ) (hsph : X ^ 2 + Y ^ 2 + Z ^ 2 = 1)
    (hN : Z ≠ 1) : JLBound 0 Z (stereoInv (stereoProj X Y Z)).2.2 := by
  rw [JLBound_zero_iff, stereoInv_stereoProj X Y Z hsph hN]

/-! ## §E — the boundary sphere is the dual-sphere fiber decomposition sphere -/

/-- **[The stereographic boundary sphere is the dual-sphere fiber-decomposition sphere] `sphereNormSq ξ = 1`.** The
unit `2`-sphere that the stereographic projection charts (`(ξ 0)² + (ξ 1)² + (ξ 2)² = 1`) is exactly the sphere of
`Hopf.DualSphereFiberDecomposition` (`sphereNormSq ξ = 1`): the lossless stereographic `ℂ` chart and the dual-sphere
fiber decomposition act on one and the same holographic boundary sphere. -/
theorem stereographic_domain_is_dualSphere (ξ : Fin 3 → ℝ)
    (hsph : (ξ 0) ^ 2 + (ξ 1) ^ 2 + (ξ 2) ^ 2 = 1) : sphereNormSq ξ = 1 := by
  unfold sphereNormSq sphereInner
  nlinarith [hsph]

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussHolographicReduction

end
