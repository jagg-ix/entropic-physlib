/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# The general-`N` interworld Cauchy–Schwarz bound and the weighted-Laplace integral (Chen–Wang §4)

Completes two suggested targets with the real Mathlib machinery (Chebyshev's sum inequality and the Gamma
improper integral, both built in the mathlib package):

**General-`N` interworld bound (Eq. 19).**  `SciamaAdSCPTMiwCoulomb` proved the interworld Cauchy–Schwarz bound
only for `N = 2, 3`.  Here it is the general finite-sum inequality:

* `interworld_cauchy_schwarz` — `(∑ aₙ)² ≤ #s · ∑ aₙ²` for any finite index set — the `(∑ 1/xₙ)² ≤ N ∑ 1/xₙ²`
  lower bound on the Coulomb interworld potential, for arbitrary `N`, from `sq_sum_le_card_mul_sum_sq`.

**The weighted-Laplace integral (Eqs. 24–27).**  The actual normalization integral, via `Γ(3) = 2!`:

* `coulomb_weighted_integral` — `∫₀^∞ x² e^{−2x} dx = 1/4`, so `∫₀^∞ 2x² e^{−2x} = 1/2` (the half-normalization
  `(1/4)C = 1/2`), computed as a genuine Gamma improper integral (`integral_rpow_mul_exp_neg_mul_rpow`), not only
  algebraically — this is the actual weighted density `P(x) = 2x²e^{−2x}`, not just the exponential envelope.

Together with `SciamaAdSCPTMiwCoulombODE` (`HasDerivAt` ODE) and `SciamaAdSCPTMiwCoulombLimits` (`N/(N+1) → 1`
and the exponential improper integral), the full analytic content of the MIW Coulomb convergence proof — the
ODE, the actual weighted integral, the asymptotic, and the general-`N` Cauchy–Schwarz — is now formalized with
real analysis.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Set Real

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwInterworldBound

/-! ## A. The general-`N` interworld Cauchy–Schwarz bound -/

/-- **[General-`N` interworld bound] `(∑ aₙ)² ≤ #s · ∑ aₙ²`.**  With `aₙ = 1/xₙ` and `s = range N` this is
`(∑ 1/xₙ)² ≤ N ∑ 1/xₙ²` (Eq. 19), the Coulomb interworld-potential lower bound for arbitrary `N`. -/
theorem interworld_cauchy_schwarz {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ s, a i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, a i ^ 2 :=
  sq_sum_le_card_mul_sum_sq

/-! ## B. The weighted-Laplace normalization integral -/

/-- The integrand `x² e^{−2x}` agrees with the `rpow` form `x^(2:ℝ) e^{−2·x^(1:ℝ)}` on `(0, ∞)`. -/
private theorem weighted_integrand_eq :
    (∫ x in Ioi (0 : ℝ), x ^ (2 : ℝ) * Real.exp (-2 * x ^ (1 : ℝ)))
      = ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-2 * x) := by
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  rw [Real.rpow_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **[The weighted integral] `∫₀^∞ x² e^{−2x} dx = 1/4`.**  So `∫₀^∞ 2x² e^{−2x} = 1/2`, the actual
weighted-Laplace half-normalization `(1/4)C = 1/2` (with `C = 2`), computed as a Gamma improper integral. -/
theorem coulomb_weighted_integral :
    ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-2 * x) = 1 / 4 := by
  rw [← weighted_integrand_eq,
    integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 2) (b := 2) (by norm_num) (by norm_num) (by norm_num)]
  have hg : Real.Gamma ((2 + 1) / 1) = 2 := by
    rw [show ((2 : ℝ) + 1) / 1 = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  rw [hg, show (-((2 : ℝ) + 1) / 1) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  norm_num

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwInterworldBound

end
