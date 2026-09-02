/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondRelativisticEvaluation

/-!
# Rational Lorentz boosts are parametrized by Pythagorean triples

The general law behind the `(3,4,5)` evaluation (`DiamondRelativisticEvaluation`): the rationality there is
not a coincidence of `θ = log 2`, but an instance of a universal parametrization.  For **every** `k > 0`,

`cosh(log k) = (k²+1)/(2k)`,  `sinh(log k) = (k²−1)/(2k)`,  `tanh(log k) = (k²−1)/(k²+1)`,

so a boost of rapidity `θ = log k` has velocity `β = (k²−1)/(k²+1)` and Lorentz factor `γ = (k²+1)/(2k)`.
The three integers `(k²−1, 2k, k²+1)` are **Euclid's Pythagorean parametrization** — they satisfy
`(k²−1)² + (2k)² = (k²+1)²` for every `k`, and dividing by `(2k)²` is exactly the mass shell
`cosh²(log k) − sinh²(log k) = 1`.  So rational velocities and rational `γ` come in Pythagorean families;
rational boosts are the rational points of the unit hyperbola `x² − y² = 1`.

The `(3,4,5)` values of `DiamondRelativisticEvaluation` are the single instance `k = 2`:
`cosh(log 2)=5/4`, `sinh(log 2)=3/4`, `tanh(log 2)=3/5`, and `(3,4,5) = (2²−1, 2·2, 2²+1)`.

* `cosh_log`, `sinh_log`, `tanh_log` — the rational parametrization for every `k > 0`.
* `rationalBoost_pythagorean` — `(k²−1)² + (2k)² = (k²+1)²` (Euclid, every `k`).
* `rationalBoost_massShell` — `cosh²(log k) − sinh²(log k) = 1` from the Pythagorean identity.
* `pythagorean_345` — the `(3,4,5)` triple is the `k = 2` instance.

Honest scope: the algebraic parametrization of hyperbolic functions at logarithmic argument and its
Pythagorean structure; this is a statement about all `k > 0`, of which the earlier `(3,4,5)` evaluation is
one point.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.RationalBoostPythagorean

/-- **[Lorentz factor of a rational boost] `cosh(log k) = (k²+1)/(2k)`** for every `k > 0`. -/
theorem cosh_log (k : ℝ) (hk : 0 < k) : Real.cosh (Real.log k) = (k ^ 2 + 1) / (2 * k) := by
  rw [Real.cosh_eq, Real.exp_log hk, Real.exp_neg, Real.exp_log hk]; field_simp

/-- **[Momentum of a rational boost] `sinh(log k) = (k²−1)/(2k)`** for every `k > 0`. -/
theorem sinh_log (k : ℝ) (hk : 0 < k) : Real.sinh (Real.log k) = (k ^ 2 - 1) / (2 * k) := by
  rw [Real.sinh_eq, Real.exp_log hk, Real.exp_neg, Real.exp_log hk]; field_simp

/-- **[Velocity of a rational boost] `tanh(log k) = (k²−1)/(k²+1)`** for every `k > 0`. -/
theorem tanh_log (k : ℝ) (hk : 0 < k) : Real.tanh (Real.log k) = (k ^ 2 - 1) / (k ^ 2 + 1) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.cosh_eq, Real.sinh_eq, Real.exp_log hk, Real.exp_neg,
    Real.exp_log hk]
  have hk' : k ≠ 0 := hk.ne'
  have h2 : (k : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  field_simp

/-- **[Euclid's Pythagorean parametrization] `(k²−1)² + (2k)² = (k²+1)²`** for every `k`.  The
`(momentum, rest-mass, energy)` legs `(k²−1, 2k, k²+1)` of the rational boost form a Pythagorean triple. -/
theorem rationalBoost_pythagorean (k : ℝ) : (k ^ 2 - 1) ^ 2 + (2 * k) ^ 2 = (k ^ 2 + 1) ^ 2 := by ring

/-- **[Mass shell from the Pythagorean triple] `cosh²(log k) − sinh²(log k) = 1`.**  Dividing the Pythagorean
identity by `(2k)²` places the rational boost on the unit hyperbola `x² − y² = 1`. -/
theorem rationalBoost_massShell (k : ℝ) (hk : 0 < k) :
    Real.cosh (Real.log k) ^ 2 - Real.sinh (Real.log k) ^ 2 = 1 := by
  rw [cosh_log k hk, sinh_log k hk]
  have hk' : k ≠ 0 := hk.ne'
  field_simp
  ring

/-- **[The `(3,4,5)` triple is `k = 2`] `(2²−1)² + (2·2)² = (2²+1)²`**, i.e. `3² + 4² = 5²` — the earlier
evaluation is one instance of the universal parametrization. -/
theorem pythagorean_345 : ((2 : ℝ) ^ 2 - 1) ^ 2 + (2 * 2) ^ 2 = ((2 : ℝ) ^ 2 + 1) ^ 2 :=
  rationalBoost_pythagorean 2

end Physlib.QuantumMechanics.ComplexAction.Lorentz.RationalBoostPythagorean

end
