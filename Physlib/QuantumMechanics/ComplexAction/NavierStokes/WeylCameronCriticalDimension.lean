/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Field.Basic

/-!
# The Weyl–Cameron exponent competition and its critical dimension four

Ports the verified exponent-algebra core of `NavierStokes/FiberDecomposedCameron.lean`
(reference tree, own authorship), *generalized*: the source proves the subcritical dominance
by a case split over `d ∈ {1,2,3}`; here the gap identity `α − β = (4−d)/d` is proven for
every positive dimension and yields the full two-sided criterion.

On a `d`-dimensional base manifold the Weyl law `λ_k ≳ k^{2/d}` (Métivier's general-dimension
form) sets the **Cameron suppression exponent** `α(d) = 2/d` — the rate at which mode sums
against the Cameron–Martin damping converge — while the partial inverse-trace sums grow as
`Σ_{k≤N} λ_k⁻¹ ∼ N^{(d−2)/d}`, the **trace growth exponent** `β(d) = (d−2)/d`.  The
competition between the two decides whether the suppression closes the trace:

* `exponent_gap` — `α(d) − β(d) = (4−d)/d` for all `0 < d`;
* `suppression_beats_growth_iff` — `β(d) < α(d) ↔ d < 4`: suppression wins exactly in
  subcritical dimension, with `d = 4` the borderline (`critical_dimension_eq`);
* `ns_exponents` — the Navier–Stokes case `d = 3`: `α = 2/3 > β = 1/3`, the `1/3` margin
  `(4−3)/3` of the trace–Cameron competition; bath modes enter at `d_eff = 1` (`α = 2`,
  `β = −1` — trivially convergent), which is how the fiber decomposition absorbs
  Ohmic/super-Ohmic couplings: the bath spectral exponent is a coupling parameter, not a
  base dimension.

**Honest layering.**  Exact exponent algebra over `ℚ`.  The Weyl law itself, the functional
trace bounds, and the Cameron–Martin damping are the analytic layer, not taken here; the
source's `FiberDecomposedCameronData` certificate registry (constraint-field structure) is
deliberately not reproduced.

## References

* G. Métivier, *Valeurs propres de problèmes aux limites elliptiques irréguliers*,
  Bull. Soc. Math. France (1977) — the general-dimension Weyl lower bound.
* Source: `NavierStokes/FiberDecomposedCameron.lean` (reference tree, own authorship).
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.WeylCameronCriticalDimension

/-- **The Cameron suppression exponent** `α(d) = 2/d` — from the Weyl law `λ_k ≳ k^{2/d}`
on a `d`-dimensional base. -/
def cameronSuppressionExponent (d : ℕ) : ℚ := 2 / d

/-- **The trace growth exponent** `β(d) = (d−2)/d` — the growth of the partial
inverse-trace sums `Σ_{k≤N} λ_k⁻¹ ∼ N^{(d−2)/d}`. -/
def traceGrowthExponent (d : ℕ) : ℚ := ((d : ℚ) - 2) / d

/-- **The gap identity** `α(d) − β(d) = (4−d)/d` — the entire competition in one fraction,
for every positive dimension (the source case-split `d ∈ {1,2,3}` is subsumed). -/
theorem exponent_gap (d : ℕ) (hd : 0 < d) :
    cameronSuppressionExponent d - traceGrowthExponent d = (4 - (d : ℚ)) / d := by
  unfold cameronSuppressionExponent traceGrowthExponent
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  ring

/-- **The critical dimension is four**: Cameron suppression beats trace growth exactly in
subcritical dimension, `β(d) < α(d) ↔ d < 4`. -/
theorem suppression_beats_growth_iff (d : ℕ) (hd : 0 < d) :
    traceGrowthExponent d < cameronSuppressionExponent d ↔ d < 4 := by
  have hd0 : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  constructor
  · intro h
    have hgap : (0 : ℚ) < (4 - (d : ℚ)) / d := by
      rw [← exponent_gap d hd]
      linarith
    rcases div_pos_iff.mp hgap with ⟨h4, -⟩ | ⟨-, hneg⟩
    · have : (d : ℚ) < 4 := by linarith
      exact_mod_cast this
    · linarith
  · intro h4
    have h4q : (d : ℚ) < 4 := by exact_mod_cast h4
    have hgap : (0 : ℚ) < (4 - (d : ℚ)) / d := div_pos (by linarith) hd0
    have hid := exponent_gap d hd
    linarith

/-- **At the critical dimension the exponents coincide**: `β(4) = α(4) = 1/2`. -/
theorem critical_dimension_eq :
    traceGrowthExponent 4 = cameronSuppressionExponent 4 := by
  unfold traceGrowthExponent cameronSuppressionExponent
  norm_num

/-- **The Navier–Stokes anchor** `d = 3`: `α = 2/3`, `β = 1/3` — suppression wins by the
subcritical margin `(4−3)/3 = 1/3`. -/
theorem ns_exponents :
    cameronSuppressionExponent 3 = 2/3 ∧ traceGrowthExponent 3 = 1/3 := by
  unfold cameronSuppressionExponent traceGrowthExponent
  constructor <;> norm_num

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.WeylCameronCriticalDimension

end
