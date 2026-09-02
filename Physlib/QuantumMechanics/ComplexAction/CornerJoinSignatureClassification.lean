/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The causal classification of boundary corners (joins) in the gravitational action

Section 2 of I. Jubb, J. Samuel, R. Sorkin, S. Surya, *Boundary and Corner Terms in the Action for
General Relativity* (arXiv:1612.00149): where two boundary components `Σᵢ, Σⱼ` of a spacetime region
meet along a codimension-two **join** `𝒥ᵢⱼ`, that join is itself spacelike, timelike or null. The
paper classifies it by the causal character of the **plane of the two normals** `nᵢ, nⱼ`, read off the
range of the quadratic `f(α) = (nᵢ + α nⱼ)·(nᵢ + α nⱼ)` as `α` runs over `ℝ`.

Writing the Gram (inner-product) data `a = nᵢ·nᵢ`, `b = nᵢ·nⱼ`, `c = nⱼ·nⱼ`, that quadratic is
`f(α) = a + 2bα + cα²`, and its whole classification is governed by the single invariant — the **Gram
determinant** `Δ = a c − b²` (the discriminant of `f` is `−4Δ`):

  * `Δ < 0` : the plane is **Lorentzian**, `f` takes both signs — the join is **spacelike**;
  * `Δ > 0` : the plane is **Riemannian** (definite), `f` has one sign — the join is **timelike**;
  * `Δ = 0` : the plane is **null** (degenerate) — the join is **null**.

This complements the Lehner–Myers–Poisson–Sorkin arc, which formalizes the boundary/joint *terms*
(`GHYSurfaceTerm` the trace `K`, `HaywardJointRapidity` the boost `η`, `NullBoundaryGravitationalAction`
the inaffinity `κ`); here is the causal *classification* of the joins those terms live on.

* **§A — the join quadratic and Gram determinant.** `joinQuadratic a b c α = a + 2bα + cα²`
  (`= (nᵢ + α nⱼ)²`); `joinGram a b c = ac − b²`; the discriminant relation
  (`joinQuadratic_discriminant`, `= −4Δ`) and the completed square (`joinQuadratic_complete_square`).
* **§B — the signature trichotomy.** `spacelike_join_of_gram_neg` (`Δ < 0 ⟹ f < 0` somewhere),
  `timelike_join_of_gram_pos` (`Δ > 0 ⟹ f > 0` everywhere), `null_join_of_gram_zero` (`Δ = 0 ⟹ f = 0`
  at the double root) — all for the leading coefficient `c > 0`.
* **§C — the paper's cases.** The four page-4 cases as Gram-determinant values: both null
  (`gram_bothNull`), both unit spacelike (`gram_bothSpacelike`, `bothSpacelike_lorentzian_iff`), one
  spacelike one null (`gram_spacelikeNull`).

**Honest layering.** Proven: the algebra of `f(α)` and the Gram determinant, the signature trichotomy
via the completed square, and the specific Gram values reproducing the paper's join cases. Interpretive:
identifying `a, b, c` with the ambient-metric inner products of the two boundary normals, and the sign of
`Δ` with the causal character of the join, is the geometric content of §2 (the normals and the ambient
Lorentzian metric are not themselves formalized here — only the exact algebra that classifies the join).

## References

* I. Jubb, J. Samuel, R. Sorkin, S. Surya, arXiv:1612.00149 (§2, the join classification). Complements
  the Lehner–Myers–Poisson–Sorkin modules (`GHYSurfaceTerm`, `HaywardJointRapidity`,
  `NullBoundaryGravitationalAction`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CornerJoinSignatureClassification


/-- **The join quadratic** `f(α) = (nᵢ + α nⱼ)·(nᵢ + α nⱼ) = a + 2bα + cα²`, with `a = nᵢ·nᵢ`,
`b = nᵢ·nⱼ`, `c = nⱼ·nⱼ` the Gram data of the two boundary normals. -/
def joinQuadratic (a b c α : ℝ) : ℝ := a + 2 * b * α + c * α ^ 2

/-- **The Gram determinant of the two normals** `Δ = ac − b²`: its sign classifies the plane of normals,
hence the join. -/
def joinGram (a b c : ℝ) : ℝ := a * c - b ^ 2

/-- **`f(0) = a = nᵢ·nᵢ`**: the quadratic at `α = 0` recovers the first normal's squared norm. -/
lemma joinQuadratic_zero (a b c : ℝ) : joinQuadratic a b c 0 = a := by
  unfold joinQuadratic; ring

/-- **The discriminant of the join quadratic is `−4Δ`** `(2b)² − 4ca = −4(ac − b²)`: the join quadratic
`f` has real roots (the plane is Lorentzian) exactly when `Δ < 0`. -/
lemma joinQuadratic_discriminant (a b c : ℝ) :
    (2 * b) ^ 2 - 4 * c * a = -4 * joinGram a b c := by
  unfold joinGram; ring

/-- **Completed square** `f(α) = c(α + b/c)² + Δ/c` (for `c ≠ 0`). -/
lemma joinQuadratic_complete_square (a b c α : ℝ) (hc : c ≠ 0) :
    joinQuadratic a b c α = c * (α + b / c) ^ 2 + joinGram a b c / c := by
  unfold joinQuadratic joinGram; field_simp; ring

/-- **The join quadratic at its vertex** `f(−b/c) = Δ/c` (for `c ≠ 0`). -/
lemma joinQuadratic_vertex (a b c : ℝ) (hc : c ≠ 0) :
    joinQuadratic a b c (-b / c) = joinGram a b c / c := by
  unfold joinQuadratic joinGram; field_simp; ring


/-- **Lorentzian plane / spacelike join** `Δ < 0 ⟹ f < 0` somewhere (with `c > 0`): the plane of normals
contains a timelike direction, so the join is spacelike. -/
lemma spacelike_join_of_gram_neg (a b c : ℝ) (hc : 0 < c) (hG : joinGram a b c < 0) :
    ∃ α, joinQuadratic a b c α < 0 :=
  ⟨-b / c, by rw [joinQuadratic_vertex a b c hc.ne']; exact div_neg_of_neg_of_pos hG hc⟩

/-- **Riemannian plane / timelike join** `Δ > 0 ⟹ f > 0` everywhere (with `c > 0`): the plane of normals
is positive-definite, so the join is timelike. -/
lemma timelike_join_of_gram_pos (a b c : ℝ) (hc : 0 < c) (hG : 0 < joinGram a b c) :
    ∀ α, 0 < joinQuadratic a b c α := by
  intro α
  rw [joinQuadratic_complete_square a b c α hc.ne']
  have h1 : 0 ≤ c * (α + b / c) ^ 2 := by positivity
  have h2 : 0 < joinGram a b c / c := div_pos hG hc
  linarith

/-- **Null plane / null join** `Δ = 0 ⟹ f = 0` at the double root `α = −b/c` (with `c ≠ 0`): the plane of
normals is degenerate (has a null direction), so the join is null. -/
lemma null_join_of_gram_zero (a b c : ℝ) (hc : c ≠ 0) (hG : joinGram a b c = 0) :
    joinQuadratic a b c (-b / c) = 0 := by
  rw [joinQuadratic_vertex a b c hc, hG, zero_div]


/-- **Both normals null** `a = c = 0`: `Δ = −(nᵢ·nⱼ)²`, so the join is spacelike when `nᵢ·nⱼ ≠ 0`
(`Δ < 0`) and null when `nᵢ·nⱼ = 0`. -/
lemma gram_bothNull (b : ℝ) : joinGram 0 b 0 = -b ^ 2 := by unfold joinGram; ring

/-- **Both normals unit spacelike** `a = c = 1`: `Δ = 1 − (nᵢ·nⱼ)²` — spacelike join when `|nᵢ·nⱼ| > 1`,
timelike when `|nᵢ·nⱼ| < 1`, null when `|nᵢ·nⱼ| = 1`. -/
lemma gram_bothSpacelike (b : ℝ) : joinGram 1 b 1 = 1 - b ^ 2 := by unfold joinGram; ring

/-- **One spacelike, one null** `a = 1, c = 0`: `Δ = −(nᵢ·nⱼ)²` — spacelike join when `nᵢ·nⱼ ≠ 0`, and
the null join case `nᵢ·nⱼ = 0`. -/
lemma gram_spacelikeNull (b : ℝ) : joinGram 1 b 0 = -b ^ 2 := by unfold joinGram; ring

/-- **Two unit-spacelike normals give a spacelike join iff `|nᵢ·nⱼ| > 1`** (Lorentzian plane): case (iv)
of the paper's classification. -/
lemma bothSpacelike_lorentzian_iff (b : ℝ) : joinGram 1 b 1 < 0 ↔ 1 < b ^ 2 := by
  rw [gram_bothSpacelike]; constructor <;> intro h <;> linarith

/-- **Two unit-spacelike normals give a timelike join iff `|nᵢ·nⱼ| < 1`** (Riemannian plane): the
timelike-join case of the paper's classification. -/
lemma bothSpacelike_riemannian_iff (b : ℝ) : 0 < joinGram 1 b 1 ↔ b ^ 2 < 1 := by
  rw [gram_bothSpacelike]; constructor <;> intro h <;> linarith

end Physlib.QuantumMechanics.ComplexAction.CornerJoinSignatureClassification
