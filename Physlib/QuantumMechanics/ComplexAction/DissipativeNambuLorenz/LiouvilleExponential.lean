/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The Liouville operator exponential and its Taylor series (Axenides–Floratos §3, Eqs. 3.9–3.14)

The full Lorenz/Rössler trajectory is integrated formally through the Liouville operator `L = v·∇`:
`x(t) = e^{tL} x₀` (Axenides, Floratos, JHEP 04 (2010) 036, Eq. 3.11), with the convergent Taylor series
(Eqs. 3.12–3.14)

  `x(t) = Σ xₖ tᵏ/k!`,   `xₖ = Lᵏ x₀`.

`DissipativeNambuLorenz.LiouvilleComoving` handled the comoving-frame reparametrization concretely; this file
formalizes the operator exponential itself, realizing `L` as an element of a Banach algebra `𝔸` (e.g. the
matrix Liouvillian `Matrix.exp`) and `e^{tL}` as `NormedSpace.exp`:

* `liouville_exp_zero`: `e^{0·L} = 1` — the initial condition `x(0) = x₀` (Eq. 3.11 at `t = 0`).
* `liouville_evolution`: `d/dt e^{tL} = e^{tL}·L` — the Liouville evolution `ẋ = L x` (Eqs. 3.9–3.11).
* `liouville_taylor`: `e^{tL} = Σₙ (n!)⁻¹ (tL)ⁿ` — the convergent Taylor series (Eq. 3.12).
* `liouville_taylor_coeff`: `(tL)ⁿ = tⁿ Lⁿ`, so the `n`-th coefficient is `(tⁿ/n!)·Lⁿ` — the statement
  `xₖ = Lᵏ x₀` (Eqs. 3.13–3.14).

## References

* M. Axenides, E. Floratos, JHEP 04 (2010) 036, §3, Eqs. 3.9–3.14. `Mathlib` (`NormedSpace.exp`,
  `hasDerivAt_exp_smul_const`, `exp_eq_tsum`).

No additional assumptions.
-/

set_option autoImplicit false

open NormedSpace

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LiouvilleExponential

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- **[Initial condition]** `e^{0·L} = 1`: at `t = 0` the propagator is the identity, `x(0) = x₀`
(Eq. 3.11). -/
theorem liouville_exp_zero (L : 𝔸) : exp ((0 : ℝ) • L) = 1 := by
  rw [zero_smul, exp_zero]

/-- **[Liouville evolution]** `d/dt e^{tL} = e^{tL}·L` — the trajectory `x(t) = e^{tL}x₀` satisfies the
Liouville equation `ẋ = L x` (Eqs. 3.9–3.11). -/
theorem liouville_evolution [CompleteSpace 𝔸] (L : 𝔸) (t : ℝ) :
    HasDerivAt (fun u : ℝ => exp (u • L)) (exp (t • L) * L) t :=
  hasDerivAt_exp_smul_const L t

/-- **[Taylor series]** `e^{tL} = Σₙ (n!)⁻¹ (tL)ⁿ` — the convergent Taylor series of the propagator
(Eq. 3.12). -/
theorem liouville_taylor (L : 𝔸) (t : ℝ) :
    exp (t • L) = ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • (t • L) ^ n :=
  congrFun (exp_eq_tsum (𝕂 := ℝ)) (t • L)

/-- **[Taylor coefficient `xₖ = Lᵏ x₀`]** `(tL)ⁿ = tⁿ Lⁿ`: the `n`-th term of the series is
`(tⁿ/n!)·Lⁿ`, so the `n`-th Taylor coefficient of `x(t)` is `Lⁿ x₀ / n!` (Eqs. 3.13–3.14). -/
theorem liouville_taylor_coeff (L : 𝔸) (t : ℝ) (n : ℕ) :
    (t • L) ^ n = t ^ n • L ^ n := by
  rw [Algebra.smul_def, Algebra.smul_def, map_pow]
  exact (Algebra.commute_algebraMap_left t L).mul_pow n

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LiouvilleExponential

end
