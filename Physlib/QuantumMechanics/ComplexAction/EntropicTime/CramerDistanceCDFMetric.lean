/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow

/-!
# The Cramér distance and the 1-Wasserstein metric as `L^p` distances between CDFs (Bellemare et al.)

Extends the metric/distance side of the entropic-dynamics probability-flow arc (the Wasserstein gradient flow of
`EntropicDynamicsWassersteinGradientFlow`) with the **Cramér distance** and the `L^p` family of probability metrics
of Bellemare–Danihelka–Dabney–Mohamed–Lakshminarayanan–Hoyer–Munos (*The Cramér Distance as a Solution to Biased
Wasserstein Gradients*, arXiv:1705.10743). Both the 1-Wasserstein metric and the Cramér distance are `L^p` distances
between the cumulative distribution functions `F_P, F_Q`:

`w_1(P,Q) = l_1(P,Q) = ∫ |F_P − F_Q|` (the 1-Wasserstein = `l_1`),
`l_2²(P,Q) = ∫ (F_P − F_Q)²` (the Cramér distance),

members of the family `l_p(P,Q) = (∫ |F_P − F_Q|^p)^{1/p}`, identical to the Wasserstein metric at `p = 1` and
distinct otherwise (the Cramér is `p = 2`). This is the CDF representation of the metric that the entropic-dynamics
Fokker–Planck flow descends: the 1-Wasserstein is the `L¹` distance between CDFs, and the Cramér distance is its
`L²` analog with unbiased sample gradients.

* the **Cramér distance** `l_2² = ∫(F_P − F_Q)²` (`cramerDistance`) is a **pseudometric**: non-negative
 (`cramerDistance_nonneg`), symmetric (`cramerDistance_symm`), and zero on the diagonal
 (`cramerDistance_self`);
* the **1-Wasserstein / `l_1` distance** `w_1 = ∫|F_P − F_Q|` (`wasserstein1Distance`) is likewise non-negative
 (`wasserstein1Distance_nonneg`), symmetric (`wasserstein1Distance_symm`), and zero on the diagonal
 (`wasserstein1Distance_self`) — the `L¹` CDF distance that coincides with the 1-Wasserstein metric;
* the **`l_p` family unifies them** `(F_P − F_Q)² = |F_P − F_Q|²` (`cramer_integrand_eq_abs_sq`) — the Cramér
 integrand is the square of the 1-Wasserstein/`l_1` integrand, so the Cramér distance is the `L²` distance whose
 `p = 1` sibling is the Wasserstein metric.

So the probability metric behind the entropic-dynamics / Fokker–Planck flow has a CDF representation: the
1-Wasserstein is the `L¹` distance `∫|F_P − F_Q|` and the Cramér distance is the `L²` distance `∫(F_P − F_Q)²`,
both pseudometrics in one `l_p` family, the Cramér (`p = 2`) being the one with unbiased sample gradients.

* **§A — the Cramér distance is a pseudometric** (`cramerDistance`, `cramerDistance_nonneg`,
 `cramerDistance_symm`, `cramerDistance_self`).
* **§B — the 1-Wasserstein / `l_1` distance** (`wasserstein1Distance`, `wasserstein1Distance_nonneg`,
 `wasserstein1Distance_symm`, `wasserstein1Distance_self`).
* **§C — the `l_p` family unification** (`cramer_integrand_eq_abs_sq`).

The non-negativity, symmetry, diagonal-vanishing, and the `l_p` integrand identity are exact
integral/`abs` algebra, using `MeasureTheory.integral_nonneg`. The triangle inequality (Minkowski), the sum
invariance and scale sensitivity (Theorem 2), the unbiased-gradient property, and the energy-distance relation
`l_2² = ½ E` are the referenced content; here the CDF-distance definitions and their pseudometric core are proved.
No new axioms.

## References

* M.G. Bellemare et al., arXiv:1705.10743 (§2.1, §4.1; `l_p` metrics, Cramér distance). Repo companion:
 `EntropicTime.EntropicDynamicsWassersteinGradientFlow` (the Wasserstein gradient flow).

No new axioms.
-/

set_option autoImplicit false

open MeasureTheory

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric

/-! ## §A — the Cramér distance is a pseudometric -/

/-- **The Cramér distance** `l_2²(P,Q) = ∫ (F_P − F_Q)²` (Bellemare et al. §4.1) — the squared `L²` distance between
the cumulative distribution functions, the `p = 2` member of the `l_p` family. -/
noncomputable def cramerDistance (F_P F_Q : ℝ → ℝ) : ℝ := ∫ x, (F_P x - F_Q x) ^ 2

/-- **[The Cramér distance is non-negative] `l_2² ≥ 0`.** -/
theorem cramerDistance_nonneg (F_P F_Q : ℝ → ℝ) : 0 ≤ cramerDistance F_P F_Q :=
  integral_nonneg fun x => sq_nonneg (F_P x - F_Q x)

/-- **[The Cramér distance is symmetric] `l_2²(P,Q) = l_2²(Q,P)`.** -/
theorem cramerDistance_symm (F_P F_Q : ℝ → ℝ) :
    cramerDistance F_P F_Q = cramerDistance F_Q F_P := by
  unfold cramerDistance
  congr 1
  funext x
  ring

/-- **[The Cramér distance vanishes on the diagonal] `l_2²(P,P) = 0`.** -/
theorem cramerDistance_self (F : ℝ → ℝ) : cramerDistance F F = 0 := by
  unfold cramerDistance
  simp

/-! ## §B — the 1-Wasserstein / `l_1` distance -/

/-- **The 1-Wasserstein / `l_1` distance** `w_1(P,Q) = l_1(P,Q) = ∫ |F_P − F_Q|` (Bellemare et al. §2.1, §4.1) —
the `L¹` distance between the cumulative distribution functions; the `l_p` and Wasserstein metrics coincide at
`p = 1`. -/
noncomputable def wasserstein1Distance (F_P F_Q : ℝ → ℝ) : ℝ := ∫ x, |F_P x - F_Q x|

/-- **[The 1-Wasserstein distance is non-negative] `w_1 ≥ 0`.** -/
theorem wasserstein1Distance_nonneg (F_P F_Q : ℝ → ℝ) : 0 ≤ wasserstein1Distance F_P F_Q :=
  integral_nonneg fun x => abs_nonneg (F_P x - F_Q x)

/-- **[The 1-Wasserstein distance is symmetric] `w_1(P,Q) = w_1(Q,P)`.** -/
theorem wasserstein1Distance_symm (F_P F_Q : ℝ → ℝ) :
    wasserstein1Distance F_P F_Q = wasserstein1Distance F_Q F_P := by
  unfold wasserstein1Distance
  congr 1
  funext x
  rw [abs_sub_comm]

/-- **[The 1-Wasserstein distance vanishes on the diagonal] `w_1(P,P) = 0`.** -/
theorem wasserstein1Distance_self (F : ℝ → ℝ) : wasserstein1Distance F F = 0 := by
  unfold wasserstein1Distance
  simp

/-- **[The 1-Wasserstein distance satisfies the triangle inequality] `w_1(P,R) ≤ w_1(P,Q) + w_1(Q,R)`.** From the
pointwise triangle inequality `|F_P − F_R| ≤ |F_P − F_Q| + |F_Q − F_R|` (telescoping through `F_Q`) and monotonicity
of the integral, the 1-Wasserstein / `l_1` distance is a genuine metric — given integrability of the CDF
differences. -/
theorem wasserstein1Distance_triangle (F_P F_Q F_R : ℝ → ℝ)
    (hPR : Integrable fun x => |F_P x - F_R x|) (hPQ : Integrable fun x => |F_P x - F_Q x|)
    (hQR : Integrable fun x => |F_Q x - F_R x|) :
    wasserstein1Distance F_P F_R ≤ wasserstein1Distance F_P F_Q + wasserstein1Distance F_Q F_R := by
  unfold wasserstein1Distance
  rw [← integral_add hPQ hQR]
  refine integral_mono hPR (hPQ.add hQR) (fun x => ?_)
  calc |F_P x - F_R x| = |(F_P x - F_Q x) + (F_Q x - F_R x)| := by congr 1; ring
    _ ≤ |F_P x - F_Q x| + |F_Q x - F_R x| := abs_add_le _ _

/-! ## §C — the `l_p` family unification -/

/-- **[The Cramér integrand is the square of the 1-Wasserstein integrand] `(F_P − F_Q)² = |F_P − F_Q|²`.** The
Cramér distance is the `L²` distance whose `p = 1` sibling is the 1-Wasserstein metric: the two are the `p = 2` and
`p = 1` members of the single `l_p` family of CDF distances. -/
theorem cramer_integrand_eq_abs_sq (F_P F_Q : ℝ → ℝ) (x : ℝ) :
    (F_P x - F_Q x) ^ 2 = |F_P x - F_Q x| ^ 2 :=
  (sq_abs _).symm

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric

end
