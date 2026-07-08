/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Moulin §5.2 — the Schwarzschild solution of the vacuum field equation

Implements §5.2 of F. Moulin, *Generalization of Einstein's gravitational field equations*
(arXiv:2405.03698): in vacuum (`T^(M) = 0`), the centrally symmetric `n = 4` equation `B_{ijkl} = 0` is solved
by the **Schwarzschild metric** (Eqs. 65–66), `A(r) = 1/B(r) = 1 + r_g/r`.

Moulin's vacuum components `B_{0101} = B_{0202} = … = 0` (Eqs. 61–64) are second-order ODEs in `A(r), B(r)`;
their first integral (the radial vacuum equation) is `r·A'(r) + A(r) = 1`, i.e. `(r A)' = 1`. Here that
equation is verified directly for the Schwarzschild profile using Mathlib's real derivative:

* `hasDerivAt_schwarzschildA` — `A'(r) = −r_g/r²`;
* `schwarzschild_vacuum_ode` — `r·A'(r) + A(r) = 1` (Schwarzschild solves the vacuum equation);
* `schwarzschild_rA_eq` — `r·A(r) = r + r_g`, the integrated form `(rA) = r + r_g` whose derivative is `1`.

The full second-order component verification needs the 2-index Ricci/`B`-tensor in spherical coordinates
(a metric-to-curvature computation requiring Christoffel symbols, not in physlib); the first-integral radial
equation captures the solution exactly.

## References

* F. Moulin (2024), arXiv:2405.03698, §5.2, Eqs. 59–66; K. Schwarzschild (1916). structure: `Mathlib`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildVacuum

/-- **The Schwarzschild metric function** `A(r) = 1 + r_g/r` (with `r_g` the gravitational radius). -/
noncomputable def schwarzschildA (rg r : ℝ) : ℝ := 1 + rg / r

/-- **The Schwarzschild radial coefficient** `B(r) = 1/A(r) = (1 + r_g/r)⁻¹`. -/
noncomputable def schwarzschildB (rg r : ℝ) : ℝ := (1 + rg / r)⁻¹

/-- **[`B = 1/A`]** the Schwarzschild relation between the time and radial metric coefficients (Eq. 65). -/
theorem schwarzschildB_eq_inv_A (rg r : ℝ) : schwarzschildB rg r = (schwarzschildA rg r)⁻¹ := rfl

/-- **[The derivative of the Schwarzschild profile] `A'(r) = −r_g/r²`.** -/
theorem hasDerivAt_schwarzschildA (rg : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (schwarzschildA rg) (-rg / r ^ 2) r := by
  unfold schwarzschildA
  have h : HasDerivAt (fun x => 1 + rg * x⁻¹) (rg * -(r ^ 2)⁻¹) r :=
    ((hasDerivAt_inv hr).const_mul rg).const_add 1
  simpa [div_eq_mul_inv, neg_div] using h

/-- **[The integrated radial vacuum equation] `r·A(r) = r + r_g`.** The combination `r A` is the affine
function whose derivative is `1` — the first integral of the Schwarzschild vacuum equation. -/
theorem schwarzschild_rA_eq (rg : ℝ) {r : ℝ} (hr : r ≠ 0) :
    r * schwarzschildA rg r = r + rg := by
  unfold schwarzschildA
  field_simp

/-- **[Schwarzschild solves the vacuum field equation] `r·A'(r) + A(r) = 1`.** The centrally symmetric vacuum
solution of Moulin's `n = 4` equation `B_{ijkl} = 0`, in first-integral form. -/
theorem schwarzschild_vacuum_ode (rg : ℝ) {r : ℝ} (hr : r ≠ 0) :
    r * deriv (schwarzschildA rg) r + schwarzschildA rg r = 1 := by
  rw [(hasDerivAt_schwarzschildA rg hr).deriv, schwarzschildA]
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildVacuum

end
