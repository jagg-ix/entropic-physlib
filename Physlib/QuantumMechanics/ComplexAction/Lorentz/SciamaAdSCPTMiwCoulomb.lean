/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTManyInteractingWorlds

/-!
# MIW on a non-Gaussian model: the 1D Coulomb / hydrogen atom (Chen–Wang, arXiv:2212.09020)

The MIW modules so far treat the harmonic oscillator (Gaussian ground state, two-sided Maxwell first excited).
Chen–Wang extend the Many-Interacting-Worlds method to the **non-Gaussian** 1D Coulomb potential (the 1D hydrogen
atom), whose first excited state `Ψ_1(x) = √2 · x · e^{−|x|}` (dimensionless `me²/ℏ² = 1`) has density

`P(x) = |Ψ_1(x)|² = 2 x² e^{−2|x|}`  (the **weighted Laplace** distribution).

The central point this module formalizes: the first-excited **polynomial baseline is `x²` — the same as the
harmonic (Maxwell) case** (`SciamaAdSCPTManyInteractingWorlds.miwFirstBaseline`).  Only the *envelope* changes
(Gaussian `φ` → Laplace `e^{−2|x|}`); the node-at-origin / two-lobe structure `b_1(x) = x²` is **universal**
across the Gaussian and non-Gaussian first excited states.

* `firstExcited_baseline_universal` — `coulombFirstBaseline = miwFirstBaseline` (both `x²`): the MIW first-excited
  baseline is potential-independent.
* `coulombFirstBaseline_node` — node at the origin (the infinite Coulomb barrier's boundary condition) with a
  positive lobe on each side — the two-sided structure, as for Maxwell.
* `coulombPotential_even`, `coulombPotential_neg` — the `1D` Coulomb potential `V(x) = −e²/|x|` is even
  (parity-symmetric) and attractive (negative away from the origin), singular at `x = 0` (the source of the
  node).
* `weightedLaplacePoly_eq` — the density's polynomial factor `B_1² · x² = 2x²` (`B_1² = 2` from normalization).
* `interworldBound_two`, `interworldBound_three` — the Cauchy–Schwarz interworld bound `(Σ aₙ)² ≤ N·Σ aₙ²`
  (Eq. 15's `(Σ 1/xₙ)² ≤ N Σ(…)² xₙ⁴`) for `N = 2, 3`: the Coulomb interworld potential's lower bound, the
  non-Gaussian analog of the harmonic zero-point energy bound.

So the MIW method — and the `x²` first-excited baseline — carry over from the Gaussian harmonic oscillator to the
non-Gaussian hydrogen atom; the branch/world structure is potential-independent, only the envelope distinguishing
the Born densities.

Honest scope: the universal `x²` baseline, the Coulomb potential's symmetry/attractiveness, the weighted-Laplace
normalization, and the small-`N` Cauchy–Schwarz interworld bound.  The `e^{−2|x|}` envelope, the full Stein /
`b`-generalized-zero-bias convergence proof, and the general-`N` interworld potential are the paper's analytic
content (the exponential and general Cauchy–Schwarz kept out to stay import-light).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwCoulomb

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTManyInteractingWorlds

/-! ## A. The universal first-excited baseline -/

/-- The Coulomb (1D hydrogen) first-excited baseline `b_1(x) = |Ψ_1|²/e^{−2|x|} = 2x²`'s polynomial part `x²` —
identical to the harmonic Maxwell baseline. -/
def coulombFirstBaseline (x : ℝ) : ℝ := x ^ 2

/-- **[The MIW first-excited baseline is universal] `coulombFirstBaseline = miwFirstBaseline`.**  The harmonic
(Maxwell) and Coulomb (weighted Laplace) first excited states share the same `x²` baseline; only the envelope
(Gaussian vs Laplace) differs. -/
theorem firstExcited_baseline_universal : coulombFirstBaseline = miwFirstBaseline := by
  funext x
  rfl

/-- **[Node at the origin, two lobes]**  `b_1(0) = 0` (the Coulomb barrier's boundary condition) and `b_1(x) > 0`
for `x ≠ 0` — the two-sided weighted-Laplace structure, as for Maxwell. -/
theorem coulombFirstBaseline_node :
    coulombFirstBaseline 0 = 0 ∧ ∀ x : ℝ, x ≠ 0 → 0 < coulombFirstBaseline x := by
  refine ⟨by simp [coulombFirstBaseline], fun x hx => ?_⟩
  unfold coulombFirstBaseline
  exact lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hx))

/-! ## B. The 1D Coulomb potential -/

/-- The 1D Coulomb potential `V(x) = −e²/|x|` (Gaussian units, `V(x_n) = −e²/|x_n|`). -/
def coulombPotential (e x : ℝ) : ℝ := -e ^ 2 / |x|

/-- **[The Coulomb potential is even] `V(−x) = V(x)`.** -/
theorem coulombPotential_even (e x : ℝ) : coulombPotential e (-x) = coulombPotential e x := by
  unfold coulombPotential
  rw [abs_neg]

/-- **[The Coulomb potential is attractive] `V(x) < 0` for `x ≠ 0`, `e ≠ 0`.** -/
theorem coulombPotential_neg {e x : ℝ} (he : e ≠ 0) (hx : x ≠ 0) : coulombPotential e x < 0 := by
  unfold coulombPotential
  rw [neg_div]
  have hx' : 0 < |x| := abs_pos.mpr hx
  have he' : 0 < e ^ 2 := by positivity
  linarith [div_pos he' hx']

/-! ## C. The weighted-Laplace normalization -/

/-- The weighted-Laplace normalization `B_1² = 2` (from `∫ 2x²e^{−2|x|} dx = 1`). -/
def laplaceNormSq : ℝ := 2

/-- The weighted-Laplace density's polynomial factor `B_1² · x² = 2x²` (`P(x) = 2x² e^{−2|x|}`). -/
def weightedLaplacePoly (x : ℝ) : ℝ := laplaceNormSq * coulombFirstBaseline x

/-- **[The density polynomial is `2x²`] `weightedLaplacePoly x = 2x²`.** -/
theorem weightedLaplacePoly_eq (x : ℝ) : weightedLaplacePoly x = 2 * x ^ 2 := by
  unfold weightedLaplacePoly laplaceNormSq coulombFirstBaseline
  ring

/-! ## D. The Cauchy–Schwarz interworld bound -/

/-- **[Interworld bound, `N = 2`] `(a+b)² ≤ 2(a²+b²)`.**  The `N = 2` case of `(Σ aₙ)² ≤ N Σ aₙ²`, the Coulomb
interworld potential's lower bound (Eq. 15). -/
theorem interworldBound_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-- **[Interworld bound, `N = 3`] `(a+b+c)² ≤ 3(a²+b²+c²)`.** -/
theorem interworldBound_three (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwCoulomb

end
