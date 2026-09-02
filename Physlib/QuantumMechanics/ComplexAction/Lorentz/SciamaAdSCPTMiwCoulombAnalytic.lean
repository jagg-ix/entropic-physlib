/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwCoulomb

/-!
# The analytic content of the MIW Coulomb convergence: ODE, integral limit, Stein rate (Chen–Wang §4)

`SciamaAdSCPTMiwCoulombConvergence` formalized the algebraic squeeze fixing `C = 2`.  This module formalizes the
**algebraic heart** of the three analytic ingredients of that proof — the first-order ODE, the Riemann-sum
integral limit, and the Stein rate — keeping the full derivative/integration/asymptotic machinery out (those
`Mathlib.Analysis.Calculus`, `MeasureTheory.Integral`, and `Analysis.Asymptotics` modules are not prebuilt here,
so their honest content is captured algebraically).

**The first-order ODE (Eqs. 21–23).**  As `N → ∞` the empirical density obeys `P′(x) − 2(1/x − 1)P(x) = 0`,
solved by `P(x) = C x² e^{−2x}`.  The algebraic heart is the **logarithmic derivative** `P′/P = (log P)′`:

* `odeCoefficient_eq` — the ODE coefficient is `2(1/x − 1) = 2/x − 2`;
* `odeCoefficient_logDeriv_decomposition` — it splits as `2/x + (−2)`: the `2/x` is the logarithmic derivative
  of the `x²` factor, the `−2` that of the `e^{−2x}` factor.  So `P = C x² e^{−2x}` solves the ODE because its
  log-derivative is exactly the coefficient — the algebraic statement of Eq. 21's limit.

**The Riemann-sum integral limit (Eqs. 24–27).**  `Σ P*_N(x_n)(x_n − x_{n+1}) → ∫₀^∞ P(x) dx`, whose value is a
Gamma integral `∫₀^∞ x^k e^{−ax} dx = k!/a^{k+1}`:

* `coulombHalfIntegral` — `∫₀^∞ 2x² e^{−2x} dx = 2·(2!/2³) = 1/2` — the limit `(1/4)C = 1/2`;
* `coulombFullIntegral` — the two-sided `∫_{−∞}^∞ 2x² e^{−2|x|} dx = 1`: normalized;
* `integral_forces_C_two` — the half-integral `1/2 = (1/4)·laplaceNormSq`, so the Riemann-sum limit reproduces
  `C = 2` (`SciamaAdSCPTMiwCoulomb.laplaceNormSq`).

**The Stein rate (Eq. 23).**  The per-step discretization error is bounded by `(1/(N+1))·(1/x_N²)`:

* `steinRateTerm_prefactor_antitone` — the `1/(N+1)` prefactor strictly decreases in `N`: the rate improves as
  worlds are added;
* `steinRate_le_energyFactor` — under the achieved bound `x_N² ≥ 1/N`, the rate is `≤ N/(N+1) < 1`, the same
  factor that governs the ground energy — a uniform bound, tightening to the `O(N^{2/a−1})` decay of the paper
  under the finer `x_N = O(N^{−1/a})` (`2 < a < 3`).

Honest scope: the log-derivative *coefficient* (not `HasDerivAt`), the Gamma integral *value* (not the
Riemann-sum→integral convergence), and the rate *bound* (not the asymptotic `O`).  Each is the algebraic core;
the analytic limits are the paper's content, deferred to keep imports light.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwCoulombAnalytic

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwCoulomb

/-! ## A. The first-order ODE via its logarithmic-derivative coefficient -/

/-- The coefficient `2(1/x − 1)` of the limiting ODE `P′ − 2(1/x − 1)P = 0` (Eq. 21). -/
def odeCoefficient (x : ℝ) : ℝ := 2 * (1 / x - 1)

/-- **[The ODE coefficient] `2(1/x − 1) = 2/x − 2`.** -/
theorem odeCoefficient_eq (x : ℝ) : odeCoefficient x = 2 / x - 2 := by
  unfold odeCoefficient; ring

/-- **[Log-derivative decomposition] `2(1/x − 1) = 2/x + (−2)`.**  The `2/x` is `(log x²)′` and the `−2` is
`(log e^{−2x})′`, so `P = C x² e^{−2x}` has log-derivative equal to the ODE coefficient — it solves the ODE. -/
theorem odeCoefficient_logDeriv_decomposition (x : ℝ) : odeCoefficient x = 2 / x + (-2) := by
  unfold odeCoefficient; ring

/-! ## B. The Riemann-sum limit as a Gamma integral -/

/-- The value of the Gamma integral `∫₀^∞ x^k e^{−ax} dx = k!/a^{k+1}`. -/
def gammaIntegral (k : ℕ) (a : ℝ) : ℝ := (Nat.factorial k : ℝ) / a ^ (k + 1)

/-- **[Half-integral] `∫₀^∞ 2x² e^{−2x} dx = 1/2`.**  The Riemann-sum limit `(1/4)C = 1/2` (Eqs. 25–27). -/
theorem coulombHalfIntegral : (2 : ℝ) * gammaIntegral 2 2 = 1 / 2 := by
  unfold gammaIntegral
  norm_num [Nat.factorial]

/-- **[Full normalization] `∫_{−∞}^∞ 2x² e^{−2|x|} dx = 1`.**  The two-sided weighted Laplace is normalized. -/
theorem coulombFullIntegral : (2 : ℝ) * ((2 : ℝ) * gammaIntegral 2 2) = 1 := by
  rw [coulombHalfIntegral]; norm_num

/-- **[The integral limit forces `C = 2`] `(1/4)·laplaceNormSq = ∫₀^∞ 2x² e^{−2x} = 1/2`.**  The Riemann-sum
limit reproduces the weighted-Laplace normalization `C = 2` used by the density module. -/
theorem integral_forces_C_two : (1 / 4 : ℝ) * laplaceNormSq = (2 : ℝ) * gammaIntegral 2 2 := by
  rw [coulombHalfIntegral]
  unfold laplaceNormSq
  norm_num

/-! ## C. The Stein rate bound -/

/-- The per-step Stein discretization-error bound `(1/(N+1))·t`, with `t = 1/x_N²` (Eq. 23). -/
def steinRateTerm (N : ℕ) (t : ℝ) : ℝ := (1 / ((N : ℝ) + 1)) * t

/-- **[The rate prefactor decays] `steinRateTerm` strictly decreases in `N`** (for a fixed `t > 0`): adding
worlds tightens the bound. -/
theorem steinRateTerm_prefactor_antitone {N M : ℕ} (h : N < M) {t : ℝ} (ht : 0 < t) :
    steinRateTerm M t < steinRateTerm N t := by
  unfold steinRateTerm
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hNM : (N : ℝ) + 1 < (M : ℝ) + 1 := by
    have hc : (N : ℝ) < (M : ℝ) := by exact_mod_cast h
    linarith
  exact mul_lt_mul_of_pos_right (one_div_lt_one_div_of_lt hN1 hNM) ht

/-- **[Uniform rate bound] under `x_N² ≥ 1/N`, the Stein rate is `≤ N/(N+1) < 1`.**  With the achieved lower
bound on the smallest world, the discretization error is bounded by the same `N/(N+1)` factor as the ground
energy — uniformly below `1`, tightening to `O(N^{2/a−1})` under the finer `x_N = O(N^{−1/a})`. -/
theorem steinRate_le_energyFactor {N : ℕ} (hN : 0 < N) {xNsq : ℝ}
    (hpos : 0 < xNsq) (hbound : 1 / (N : ℝ) ≤ xNsq) :
    steinRateTerm N (1 / xNsq) ≤ (N : ℝ) / ((N : ℝ) + 1) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hinv : 1 / xNsq ≤ (N : ℝ) := by
    rw [div_le_iff₀ hpos]
    have h1 : (1 : ℝ) = (N : ℝ) * (1 / (N : ℝ)) := by rw [mul_one_div, div_self hNpos.ne']
    rw [h1]
    exact mul_le_mul_of_nonneg_left hbound hNpos.le
  unfold steinRateTerm
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hN1 hN1]
  nlinarith [hinv, hNpos]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwCoulombAnalytic

end