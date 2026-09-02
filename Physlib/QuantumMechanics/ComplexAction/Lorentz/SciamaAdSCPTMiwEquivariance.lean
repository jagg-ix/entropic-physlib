/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The MIW equivariance method: cubic equal-area density (Wiseman et al., arXiv:1807.01568, App. A)

An alternative to the rational-smoothing interworld potential (`SciamaAdSCPTMiwGeneralisedPotential`), motivated
by the **equivariance** property of Bohmian mechanics (the configuration stays `|ψ|²`-distributed under
evolution).  Around each world one fits a smooth polynomial density `P_n(x)` and fixes its coefficients by
requiring equal probability `1/N` on each inter-world interval.  For the third-order (five-world) case,

`P_n(x) = a + b x + c x² + d x³`  (Eq. prob_eq),  `∫_{x_k}^{x_{k+1}} P_n(x) dx = 1/N`.

* `equivariance_cubic_integral` — the interval integral of the cubic density, computed with **actual interval
  integration** (FTC): `∫_p^q (a + bx + cx² + dx³) dx = F(q) − F(p)` with `F(x) = ax + bx²/2 + cx³/3 + dx⁴/4`.
* `equivariance_area_equation` — the resulting equal-area linear equation
  `a·Δx + (b/2)Δx² + (c/3)Δx³ + (d/4)Δx⁴ = 1/N`, one of the four equations (from five adjacent worlds) that fix
  `(a, b, c, d)` — the equivariance method's linear system.

This completes the paper's node-handling programme: the toy model cannot reproduce nodal (excited) states, and
both the generalised rational potential and this equivariance method fix that — the technical prerequisite for
simulating the Bell/Bohm/MIW nonlocality that the paper analyses (the MIW branch being an Everettian branch
`SciamaAdSCPTEverettBranches`, with signal-locality restored by averaging over the worlds of a branch).

Honest scope: the actual cubic interval integral (FTC) and the equal-area equation.  The four-equation solve for
`(a,b,c,d)`, the higher-degree polynomials, and the nonlocality simulations are the paper's content.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory intervalIntegral

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwEquivariance

/-- The cubic equivariance density `P_n(x) = a + bx + cx² + dx³` (Eq. prob_eq). -/
def equivDensity (a b c d x : ℝ) : ℝ := a + b * x + c * x ^ 2 + d * x ^ 3

/-- Its antiderivative `F(x) = ax + bx²/2 + cx³/3 + dx⁴/4`. -/
def equivAntideriv (a b c d x : ℝ) : ℝ := a * x + b * x ^ 2 / 2 + c * x ^ 3 / 3 + d * x ^ 4 / 4

/-- **[The cubic density's derivative]** `F′(x) = P_n(x)`. -/
theorem equivAntideriv_hasDerivAt (a b c d x : ℝ) :
    HasDerivAt (equivAntideriv a b c d) (equivDensity a b c d x) x := by
  unfold equivAntideriv equivDensity
  have e1 : HasDerivAt (fun y : ℝ => a * y) a x := by simpa using (hasDerivAt_id x).const_mul a
  have e2 : HasDerivAt (fun y : ℝ => b * y ^ 2 / 2) (b * x) x := by
    have h := ((hasDerivAt_pow 2 x).const_mul b).div_const 2
    have hv : b * ((2 : ℕ) * x ^ (2 - 1)) / 2 = b * x := by push_cast; ring
    rwa [hv] at h
  have e3 : HasDerivAt (fun y : ℝ => c * y ^ 3 / 3) (c * x ^ 2) x := by
    have h := ((hasDerivAt_pow 3 x).const_mul c).div_const 3
    have hv : c * ((3 : ℕ) * x ^ (3 - 1)) / 3 = c * x ^ 2 := by push_cast; ring
    rwa [hv] at h
  have e4 : HasDerivAt (fun y : ℝ => d * y ^ 4 / 4) (d * x ^ 3) x := by
    have h := ((hasDerivAt_pow 4 x).const_mul d).div_const 4
    have hv : d * ((4 : ℕ) * x ^ (4 - 1)) / 4 = d * x ^ 3 := by push_cast; ring
    rwa [hv] at h
  exact ((e1.add e2).add e3).add e4

/-- **[The equivariance cubic interval integral]** `∫_p^q (a + bx + cx² + dx³) dx = F(q) − F(p)`, by the
fundamental theorem of calculus. -/
theorem equivariance_cubic_integral (a b c d p q : ℝ) :
    ∫ x in p..q, equivDensity a b c d x = equivAntideriv a b c d q - equivAntideriv a b c d p := by
  apply integral_eq_sub_of_hasDerivAt (fun x _ => equivAntideriv_hasDerivAt a b c d x)
  exact (Continuous.intervalIntegrable (by unfold equivDensity; fun_prop) p q)

/-- **[The equal-area equation]** `∫_p^q P_n = a·Δx + (b/2)Δx² + (c/3)Δx³ + (d/4)Δx⁴`, set to `1/N` in the
equivariance method — one of the four linear equations fixing `(a,b,c,d)` from five adjacent worlds. -/
theorem equivariance_area_equation (a b c d p q : ℝ) :
    ∫ x in p..q, equivDensity a b c d x
      = a * (q - p) + b / 2 * (q ^ 2 - p ^ 2) + c / 3 * (q ^ 3 - p ^ 3) + d / 4 * (q ^ 4 - p ^ 4) := by
  rw [equivariance_cubic_integral]
  unfold equivAntideriv
  ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwEquivariance

end
