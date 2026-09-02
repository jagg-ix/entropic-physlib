/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The MIW Coulomb limiting ODE, with actual derivatives (Chen–Wang arXiv:2212.09020, Eq. 21)

`SciamaAdSCPTMiwCoulombAnalytic` captured the ODE `P′ − 2(1/x−1)P = 0` algebraically (the log-derivative
coefficient).  Here it is done with the *actual* derivative: the 1D-hydrogen first-excited density
`P(x) = C x² e^{−2x}` is shown, via `HasDerivAt`, to satisfy the first-order ODE that the `N → ∞` limit of the
MIW empirical density obeys.

* `coulombDensity_hasDerivAt` — `HasDerivAt (fun x => C x² e^{−2x}) (C(2x − 2x²)e^{−2x}) x`: the derivative of
  the weighted-Laplace density, by the product and chain rules (`hasDerivAt_pow`, `Real.hasDerivAt_exp`).
* **`coulombDensity_satisfies_ODE`** — for `x ≠ 0`, `P′(x) = 2(1/x − 1)·P(x)`: the density solves the limiting
  ODE (Eq. 21), verified as a genuine `HasDerivAt`, not merely algebraically.

So the MIW empirical density's `N → ∞` limit `C x² e^{−2x}` is confirmed — with real calculus — to be the exact
solution of the first-order ODE, completing the analytic ODE target left algebraic before.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwCoulombODE

/-- The coefficient `2(1/x − 1)` of the limiting ODE `P′ − 2(1/x − 1)P = 0`. -/
def odeCoefficient (x : ℝ) : ℝ := 2 * (1 / x - 1)

/-- The 1D-hydrogen first-excited density `P(x) = C x² e^{−2x}` (weighted Laplace, `x ≥ 0` branch). -/
def coulombDensity (C x : ℝ) : ℝ := C * x ^ 2 * Real.exp (-2 * x)

/-- **[The derivative of the density] `P′(x) = C(2x − 2x²)e^{−2x}`.**  By the product rule on `C x²` and
`e^{−2x}`, using `hasDerivAt_pow` and `Real.hasDerivAt_exp`. -/
theorem coulombDensity_hasDerivAt (C x : ℝ) :
    HasDerivAt (coulombDensity C) (C * (2 * x - 2 * x ^ 2) * Real.exp (-2 * x)) x := by
  have hpow : HasDerivAt (fun y : ℝ => C * y ^ 2) (C * (2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_mul C
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-2 * y)) (Real.exp (-2 * x) * (-2)) x := by
    have hlin : HasDerivAt (fun y : ℝ => -2 * y) (-2) x := by
      simpa using (hasDerivAt_id x).const_mul (-2 : ℝ)
    exact hlin.exp
  have hmul := hpow.mul hexp
  have hfun : coulombDensity C = fun y : ℝ => C * y ^ 2 * Real.exp (-2 * y) := rfl
  have hval : C * (2 * x) * Real.exp (-2 * x) + C * x ^ 2 * (Real.exp (-2 * x) * (-2))
      = C * (2 * x - 2 * x ^ 2) * Real.exp (-2 * x) := by ring
  rw [hfun, ← hval]
  exact hmul

/-- **[The density solves the limiting ODE] `P′(x) = 2(1/x − 1)·P(x)` for `x ≠ 0`.**  Verified as a genuine
derivative (Eq. 21): the `N → ∞` MIW empirical density `C x² e^{−2x}` is the exact solution. -/
theorem coulombDensity_satisfies_ODE {C x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (coulombDensity C) (odeCoefficient x * coulombDensity C x) x := by
  have h := coulombDensity_hasDerivAt C x
  have heq : odeCoefficient x * coulombDensity C x = C * (2 * x - 2 * x ^ 2) * Real.exp (-2 * x) := by
    unfold odeCoefficient coulombDensity
    field_simp
  rw [heq]
  exact h

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwCoulombODE

end
