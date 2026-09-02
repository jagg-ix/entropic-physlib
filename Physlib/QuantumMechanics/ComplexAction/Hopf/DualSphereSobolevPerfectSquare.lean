/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The Dual-Sphere-Fiber W-functional: the Sobolev `6/5` exponent and perfect-square monotonicity

Ports the genuine, **mathematical kernel** of the Navier–Stokes Dual-Sphere-Fiber bridges
(`DualSphereWFunctionalBridge`, `CameronSDGBridge`) into physlib. The source files themselves are *status
records* — `Bool`-valued structures with `:= rfl` theorems reading off which sectors are "controlled" — and
they rest on open conjectures proved by **axioms** (`sdg_implies_cameron_bkm`,
`clms_gives_nonneg_w_ns_integrand`). Neither the vacuous status theorems nor the axioms belong in physlib;
what *is* genuine and portable is the two pieces of real analysis the bridge is *about*:

* the **critical Sobolev exponent** `2n/(n−2)`, which at `n = 3` is `6`, whose Hölder dual is the `6/5` that
  appears intrinsically in the `W_NS` spatial integrand;
* the **perfect-square** structure (the NS analogue of Perelman's monotone entropy / the CLMS chain): a
  functional whose derivative is a perfect square is monotone — the H-theorem / second-law shape, the same
  monotonicity physlib's entropic-time arrow keys on.

* **§A — the 3D Sobolev critical exponent and its `6/5` dual** (`sobolevConjugate`,
  `sobolevConjugate_three`, `sixFifths_holder_dual`, `sixFifths_eq_conjugate`). `2·3/(3−2) = 6`; `6/5` is the
  Hölder conjugate `6/(6−1)` of the 3D Sobolev exponent.
* **§B — perfect square ⟹ monotonicity** (`wFunctional_monotone`). A differentiable functional whose
  derivative is `(g)²` is monotone (`monotone_of_deriv_nonneg` + `sq_nonneg`) — the Perelman/CLMS
  perfect-square ⟹ `W_NS` monotone.
* **§C — the H-theorem / equilibrium reading** (`entropyProduction_nonneg`, `equilibrium_iff_zero_flux`).
  The perfect-square production rate is nonnegative (the second law) and vanishes *iff* its flux does
  (equilibrium / stationarity) — the entropy-monotonicity structure underlying the entropic-time arrow.

## References

* The critical Sobolev embedding `H¹(ℝⁿ) ↪ L^{2n/(n−2)}`; Perelman's monotone `W`-entropy; the CLMS div–curl
  Hardy-space chain.
* Source (not directly portable — axioms + `Bool`-record status theorems):
  `NavierStokes/DualSphereWFunctionalBridge.lean`, `NavierStokes/CameronSDGBridge.lean`. Physical analogue:
  the H-theorem (`QuantumMechanics.Schrodinger.BadialiQuantitativeHTheorem`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereSobolevPerfectSquare


/-- **The critical Sobolev embedding exponent** `2n/(n−2)` of `H¹(ℝⁿ) ↪ L^{2n/(n−2)}`. -/
noncomputable def sobolevConjugate (n : ℝ) : ℝ := 2 * n / (n - 2)

/-- **In three dimensions the critical exponent is `6`** `2·3/(3−2) = 6`. -/
lemma sobolevConjugate_three : sobolevConjugate 3 = 6 := by
  unfold sobolevConjugate; norm_num

/-- **`6/5` is the Hölder conjugate of the 3D Sobolev exponent `6`** `1/6 + 1/(6/5) = 1` — the exponent
intrinsic to the `W_NS` spatial integrand. -/
lemma sixFifths_holder_dual : (1 : ℝ) / 6 + 1 / (6 / 5) = 1 := by norm_num

/-- **`6/5 = 6/(6−1)`** — the Hölder conjugate `p' = p/(p−1)` at `p = 6`. -/
lemma sixFifths_eq_conjugate : (6 : ℝ) / 5 = 6 / (6 - 1) := by norm_num


/-- **[Perfect-square ⟹ monotone] A functional with perfect-square derivative is monotone.** If
`dW/dτ = (g τ)²`, then `W` is monotone — the Perelman/CLMS perfect-square structure forcing `W_NS`
monotonicity (`monotone_of_deriv_nonneg` + `sq_nonneg`). -/
lemma wFunctional_monotone (W g : ℝ → ℝ) (hW : Differentiable ℝ W)
    (hderiv : ∀ τ, deriv W τ = (g τ) ^ 2) : Monotone W :=
  monotone_of_deriv_nonneg hW (fun τ => by rw [hderiv τ]; exact sq_nonneg _)


/-- **[Second law] The perfect-square production rate is nonnegative** `0 ≤ (g τ)²` — the entropy production
of the H-theorem. -/
lemma entropyProduction_nonneg (g : ℝ → ℝ) (τ : ℝ) : 0 ≤ (g τ) ^ 2 := sq_nonneg _

/-- **[Equilibrium] The production vanishes iff the flux does** `(g τ)² = 0 ↔ g τ = 0` — the functional is
stationary exactly at equilibrium (zero flux). -/
lemma equilibrium_iff_zero_flux (g : ℝ → ℝ) (τ : ℝ) : (g τ) ^ 2 = 0 ↔ g τ = 0 := by
  rw [sq_eq_zero_iff]

end Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereSobolevPerfectSquare

end
