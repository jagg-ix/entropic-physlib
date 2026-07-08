/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.MoulinSchwarzschildVacuum

/-!
# Moulin's explicit `B₀₁₀₁` vacuum component (Eqs. 61, 65–66)

`Curvature.SchwarzschildVacuum` proves the centrally-symmetric vacuum solution of Moulin's `n = 4` equation
`B_{ijkl} = 0` in its *first-integral* form `r·A'(r) + A(r) = 1` (arXiv:2405.03698, §5.2), but it deliberately
skips the explicit component expressions (Eqs. 61–64). This module supplies the first of those, `B₀₁₀₁`
(Eq. 61), for the metric `ds² = A(r)c²dt² − B(r)dr² − r²dΩ²`, and closes the loop: with the reciprocal relation
`B = 1/A` (Eq. 65) and the vacuum ODE, `B₀₁₀₁` vanishes identically.

* `bComponent0101` — Moulin Eq. 61, a function of `A, B, A', A'', B', r`.
* `bComponent0101_vacuum_zero` — for `B = 1/A` (`B' = −A'/A²`), the vacuum ODE `rA' + A = 1` together with its
 derivative `rA'' + 2A' = 0` makes `B₀₁₀₁ = 0`. The reciprocal substitution collapses Eq. 61 to
 `−⅙(A'' − 2A'/r + 4(1−A)/r²)`, which the ODE kills.
* `schwarzschild_bComponent0101_zero` — the explicit `A(r) = 1 + r_g/r` (`SchwarzschildVacuum.schwarzschildA`)
 makes `B₀₁₀₁ = 0`, the Eq.-61 form of `schwarzschild_vacuum_ode`.

All exact algebra. Only the `B₀₁₀₁` component of Eqs. 61–64 is performed; the other
three (`B₀₂₀₂`, `B₁₂₁₂`, `B₂₃₂₃`) reduce to the same radial vacuum equation by the same method.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.MoulinBComponentVacuum

open Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildVacuum

/-- **Moulin's `B₀₁₀₁` component** (Eq. 61) for `ds² = A(r)c²dt² − B(r)dr² − r²dΩ²`:
`B₀₁₀₁ = −⅙[A'' − A'²/(2A) − A'B'/(2B) + AB'/(rB) + 4AB/r² − A'/r − 4A/r²]`. -/
noncomputable def bComponent0101 (A B A' A'' B' r : ℝ) : ℝ :=
  -(1 / 6) * (A'' - A' ^ 2 / (2 * A) - A' * B' / (2 * B) + A * B' / (r * B)
    + 4 * A * B / r ^ 2 - A' / r - 4 * A / r ^ 2)

/-- **[The reciprocal relation collapses `B₀₁₀₁`]** with `B = 1/A` and `B' = −A'/A²` (Eq. 65), the `A'B'` and
`AB'` terms cancel the `A'²` term and one `A'/r`, leaving `B₀₁₀₁ = −⅙(A'' − 2A'/r + 4(1−A)/r²)`. -/
theorem bComponent0101_reciprocal (A A' A'' r : ℝ) (hA : A ≠ 0) (hr : r ≠ 0) :
    bComponent0101 A (1 / A) A' A'' (-(A') / A ^ 2) r
      = -(1 / 6) * (A'' - 2 * A' / r + 4 * (1 - A) / r ^ 2) := by
  unfold bComponent0101
  field_simp
  ring

/-- **[`B₀₁₀₁ = 0` on the vacuum solution]** given the reciprocal relation `B = 1/A` and the radial vacuum
equation `rA' + A = 1` with its derivative `rA'' + 2A' = 0`, Moulin's `B₀₁₀₁` component vanishes — the explicit
Eq.-61 form of `SchwarzschildVacuum.schwarzschild_vacuum_ode`. -/
theorem bComponent0101_vacuum_zero (A A' A'' r : ℝ) (hA : A ≠ 0) (hr : r ≠ 0)
    (hode : r * A' + A = 1) (hode2 : r * A'' + 2 * A' = 0) :
    bComponent0101 A (1 / A) A' A'' (-(A') / A ^ 2) r = 0 := by
  rw [bComponent0101_reciprocal A A' A'' r hA hr]
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  field_simp
  linear_combination (-r) * hode2 + 4 * hode

/-- **[Schwarzschild makes `B₀₁₀₁` vanish]** the profile `A(r) = 1 + r_g/r` (`schwarzschildA`), with
`A'(r) = −r_g/r²`, `A''(r) = 2r_g/r³` and `B = 1/A`, gives `B₀₁₀₁ = 0` — Moulin's centrally-symmetric vacuum
solution seen through the explicit Eq. 61, not only the first integral. -/
theorem schwarzschild_bComponent0101_zero (rg r : ℝ) (hr : r ≠ 0)
    (hA : schwarzschildA rg r ≠ 0) :
    bComponent0101 (schwarzschildA rg r) (1 / schwarzschildA rg r) (-rg / r ^ 2) (2 * rg / r ^ 3)
        (-(-rg / r ^ 2) / schwarzschildA rg r ^ 2) r = 0 := by
  apply bComponent0101_vacuum_zero _ _ _ _ hA hr
  · unfold schwarzschildA; field_simp; ring
  · field_simp; ring

end Physlib.QuantumMechanics.ComplexAction.Curvature.MoulinBComponentVacuum

end
