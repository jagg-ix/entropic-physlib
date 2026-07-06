/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Probability metrics as `Lᵖ` distances between cumulative distribution functions

The metric layer of the entropic-dynamics spine. Both the **1-Wasserstein** metric and the **Cramér** distance are
`Lᵖ` distances between the cumulative distribution functions `F_P, F_Q` of two probability laws:

`w₁(P,Q) = ∫ |F_P − F_Q|`   (the 1-Wasserstein / `l₁` distance),
`l₂²(P,Q) = ∫ (F_P − F_Q)²`   (the Cramér distance),

members of the family `lₚ(P,Q) = (∫ |F_P − F_Q|ᵖ)^{1/p}`, coinciding at `p = 1` and distinct otherwise (the Cramér
distance is `p = 2`). This is the metric that the entropic-dynamics Fokker–Planck flow descends.

* the **Cramér distance** `l₂² = ∫(F_P − F_Q)²` (`cramerDistance`) is a pseudometric: non-negative
  (`cramerDistance_nonneg`), symmetric (`cramerDistance_symm`), vanishing on the diagonal (`cramerDistance_self`);
* the **1-Wasserstein / `l₁` distance** `w₁ = ∫|F_P − F_Q|` (`wasserstein1Distance`) is likewise a pseudometric and
  satisfies the triangle inequality (`wasserstein1Distance_triangle`);
* the **`lₚ` family unifies them**: the Cramér integrand is the square of the `l₁` integrand
  (`cramer_integrand_eq_abs_sq`).

References: M.G. Bellemare et al., *The Cramér Distance as a Solution to Biased Wasserstein Gradients*
(arXiv:1705.10743, §2.1, §4.1). No new axioms.
-/

set_option autoImplicit false

open MeasureTheory

@[expose] public section

namespace Physlib.EntropicDynamics.ProbabilityMetric

/-! ## The Cramér distance -/

/-- **The Cramér distance** `l₂²(P,Q) = ∫ (F_P − F_Q)²` — the squared `L²` distance between the cumulative
distribution functions, the `p = 2` member of the `lₚ` family. -/
noncomputable def cramerDistance (F_P F_Q : ℝ → ℝ) : ℝ := ∫ x, (F_P x - F_Q x) ^ 2

/-- **The Cramér distance is non-negative** `l₂² ≥ 0`. -/
theorem cramerDistance_nonneg (F_P F_Q : ℝ → ℝ) : 0 ≤ cramerDistance F_P F_Q :=
  integral_nonneg fun x => sq_nonneg (F_P x - F_Q x)

/-- **The Cramér distance is symmetric** `l₂²(P,Q) = l₂²(Q,P)`. -/
theorem cramerDistance_symm (F_P F_Q : ℝ → ℝ) : cramerDistance F_P F_Q = cramerDistance F_Q F_P := by
  unfold cramerDistance
  congr 1
  funext x
  ring

/-- **The Cramér distance vanishes on the diagonal** `l₂²(P,P) = 0`. -/
theorem cramerDistance_self (F : ℝ → ℝ) : cramerDistance F F = 0 := by
  unfold cramerDistance
  simp

/-! ## The 1-Wasserstein / `l₁` distance -/

/-- **The 1-Wasserstein / `l₁` distance** `w₁(P,Q) = ∫ |F_P − F_Q|` — the `L¹` distance between the cumulative
distribution functions; the `lₚ` and Wasserstein metrics coincide at `p = 1`. -/
noncomputable def wasserstein1Distance (F_P F_Q : ℝ → ℝ) : ℝ := ∫ x, |F_P x - F_Q x|

/-- **The 1-Wasserstein distance is non-negative** `w₁ ≥ 0`. -/
theorem wasserstein1Distance_nonneg (F_P F_Q : ℝ → ℝ) : 0 ≤ wasserstein1Distance F_P F_Q :=
  integral_nonneg fun x => abs_nonneg (F_P x - F_Q x)

/-- **The 1-Wasserstein distance is symmetric** `w₁(P,Q) = w₁(Q,P)`. -/
theorem wasserstein1Distance_symm (F_P F_Q : ℝ → ℝ) :
    wasserstein1Distance F_P F_Q = wasserstein1Distance F_Q F_P := by
  unfold wasserstein1Distance
  congr 1
  funext x
  rw [abs_sub_comm]

/-- **The 1-Wasserstein distance vanishes on the diagonal** `w₁(P,P) = 0`. -/
theorem wasserstein1Distance_self (F : ℝ → ℝ) : wasserstein1Distance F F = 0 := by
  unfold wasserstein1Distance
  simp

/-- **The 1-Wasserstein distance satisfies the triangle inequality** `w₁(P,R) ≤ w₁(P,Q) + w₁(Q,R)`, from the
pointwise triangle inequality telescoping through `F_Q` and monotonicity of the integral (given integrability). -/
theorem wasserstein1Distance_triangle (F_P F_Q F_R : ℝ → ℝ)
    (hPR : Integrable fun x => |F_P x - F_R x|) (hPQ : Integrable fun x => |F_P x - F_Q x|)
    (hQR : Integrable fun x => |F_Q x - F_R x|) :
    wasserstein1Distance F_P F_R ≤ wasserstein1Distance F_P F_Q + wasserstein1Distance F_Q F_R := by
  unfold wasserstein1Distance
  rw [← integral_add hPQ hQR]
  refine integral_mono hPR (hPQ.add hQR) (fun x => ?_)
  calc |F_P x - F_R x| = |(F_P x - F_Q x) + (F_Q x - F_R x)| := by congr 1; ring
    _ ≤ |F_P x - F_Q x| + |F_Q x - F_R x| := abs_add_le _ _

/-! ## The `lₚ` family unification -/

/-- **The Cramér integrand is the square of the 1-Wasserstein integrand** `(F_P − F_Q)² = |F_P − F_Q|²`, so the
Cramér distance is the `L²` distance whose `p = 1` sibling is the 1-Wasserstein metric. -/
theorem cramer_integrand_eq_abs_sq (F_P F_Q : ℝ → ℝ) (x : ℝ) :
    (F_P x - F_Q x) ^ 2 = |F_P x - F_Q x| ^ 2 :=
  (sq_abs _).symm

end Physlib.EntropicDynamics.ProbabilityMetric

end
