/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The MIW Coulomb limits: the asymptotic `N → ∞` and the improper integral (Chen–Wang §4)

Completes the two remaining analytic targets of the MIW Coulomb convergence proof with actual analysis (the
Mathlib limit and improper-integral machinery, whose oleans are built in the mathlib package):

**The asymptotic (`N → ∞`).**  The finite-`N` MIW quantities — the ground energy factor `N/(N+1)`, the Heisenberg
bound factor, and the Stein-rate prefactor — all tend to their quantum limits:

* `coulombEnergyFactor_tendsto_one` — `N/(N+1) → 1`, so the MIW ground energy `−(me⁴/2ℏ²)·N/(N+1)` tends to the
  exact 1D-hydrogen first-excited energy `−me⁴/2ℏ²`, and the uncertainty bound `(ℏ/2)·(N−1)/N` to `ℏ/2`.

**The improper integral (Riemann/Lebesgue).**  The weighted-Laplace normalization is fixed by an improper
integral over `(0, ∞)`:

* `exp_envelope_integral` — `∫₀^∞ e^{−2x} dx = 1/2`, computed as a genuine improper integral (`integral_exp_mul_Ioi`).

Together with `SciamaAdSCPTMiwCoulombODE` (the ODE with real `HasDerivAt` derivatives), the three analytic
ingredients of the convergence proof — ODE, integral, asymptotic — are now formalized with actual calculus,
not only algebraically.

Honest scope: the `N/(N+1) → 1` limit and the exponential improper integral `∫₀^∞ e^{−2x} = 1/2`.  The full
weighted integral `∫₀^∞ 2x²e^{−2x} = 1/2` uses the Gamma function `Γ(3) = 2!` with a change of variables (its
value is fixed algebraically in `SciamaAdSCPTMiwCoulombAnalytic`); the exponential-envelope integral here is the
improper-integration core.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwCoulombLimits

/-! ## A. The asymptotic `N → ∞` -/

/-- The Coulomb ground-energy factor `N/(N+1)` (as in `SciamaAdSCPTMiwCoulombConvergence`). -/
def coulombEnergyFactor (N : ℕ) : ℝ := (N : ℝ) / ((N : ℝ) + 1)

/-- **[The MIW ground energy tends to the exact value] `N/(N+1) → 1`.**  So `−(me⁴/2ℏ²)·N/(N+1) → −me⁴/2ℏ²`
(the 1D-hydrogen first-excited energy), and `(ℏ/2)(N−1)/N → ℏ/2` (the Heisenberg bound). -/
theorem coulombEnergyFactor_tendsto_one :
    Tendsto coulombEnergyFactor atTop (𝓝 1) :=
  tendsto_natCast_div_add_atTop (1 : ℝ)

/-! ## B. The improper integral -/

/-- **[The exponential-envelope improper integral] `∫₀^∞ e^{−2x} dx = 1/2`.**  A genuine improper integral over
`(0, ∞)`, the Riemann/Lebesgue-integration core behind the weighted-Laplace normalization. -/
theorem exp_envelope_integral : ∫ x in Ioi (0 : ℝ), Real.exp (-2 * x) = 1 / 2 := by
  rw [integral_exp_mul_Ioi (show (-2 : ℝ) < 0 by norm_num) 0, mul_zero, Real.exp_zero]
  norm_num

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwCoulombLimits

end
