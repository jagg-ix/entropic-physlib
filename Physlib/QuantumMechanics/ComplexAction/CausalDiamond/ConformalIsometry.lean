/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.SmallDiamonds

/-!
# Conformal isometry and conformal Killing time of causal diamonds (Jacobson–Visser App. A, B)

This file formalizes the two geometric appendices of Jacobson & Visser (arXiv:1812.01596).

## §A — Conformal isometry of causal diamonds in (A)dS (Appendix A)

The conformal Killing vector preserving a causal diamond in de Sitter space is
`ζ = A(u)∂_u + B(v)∂_v` with `A = B` (Eq. A.1–A.5). The diamond-preserving, unit-surface-gravity
solution has coefficient

  `A(u) = cosh(R_*/L) − cosh(u/L)`   (`confKillingCoeff`, Eq. A.5),

which **vanishes at the horizons** `u = ±R_*` (so the flow maps the diamond onto itself,
`confKillingCoeff_future_horizon` / `_past_horizon`), with normalization `L/sinh(R_*/L)` giving **unit
surface gravity** `κ = 1` (`confKilling_unit_surface_gravity`). In the flat limit `L → ∞` it reduces to
`ζ^flat = (1/2R)[(R²−u²)∂_u + (R²−v²)∂_v]` (Eq. A.7, `confKillingFlatCoeffUV`), whose `(t,r)` form is the
`CausalDiamond.Construction` field (`confKillingFlatUV_sum_eq_time`).

## §B — Conformal Killing time and mean curvature (Appendix B)

In coordinates adapted to the conformal Killing flow, `C⁻¹(s,x) = (cosh s + cosh x · cosh(R_*/L))/(L
sinh(R_*/L))` (Eq. B.5), and the trace `K` of the extrinsic curvature of the constant-conformal-Killing-
time slices is

  `K = (1−d) ∂_s C⁻¹ = (1−d) sinh s/(L sinh(R_*/L))`   (`meanCurvature`, Eqs. B.3, B.6).

Because `∂_s C⁻¹` is **independent of `x`** (`deriv_confTimeCInv_x_independent`), `K` is **constant on
each constant-`s` slice** — the crucial fact for the geometric first law. At `s = 0` (the maximal slice
`Σ`) `K = 0` (`meanCurvature_maximal_slice`): `Σ` is a maximal-volume (extremal) slice.

## References

* T. Jacobson, M. Visser, arXiv:1812.01596, Appendices A, B. This development:
  `CausalDiamond.Construction`, `CausalDiamond.SmallDiamonds`.

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ConformalIsometry

open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.SmallDiamonds

/-! ## §A — the conformal Killing vector preserving the diamond (Appendix A) -/

/-- **The conformal Killing coefficient** `A(u) = cosh(R_*/L) − cosh(u/L)` (Jacobson–Visser Eq. A.5):
`ζ = A(u)∂_u + A(v)∂_v` is the conformal isometry preserving the de Sitter causal diamond. -/
def confKillingCoeff (L Rstar u : ℝ) : ℝ := Real.cosh (Rstar / L) - Real.cosh (u / L)

/-- **The flow preserves the future horizon** `A(R_*) = 0` (`u = R_*` is left invariant). -/
@[simp] theorem confKillingCoeff_future_horizon (L Rstar : ℝ) : confKillingCoeff L Rstar Rstar = 0 := by
  rw [confKillingCoeff]; ring

/-- **The flow preserves the past horizon** `A(−R_*) = 0` (`u = −R_*` is left invariant; `cosh` even). -/
@[simp] theorem confKillingCoeff_past_horizon (L Rstar : ℝ) :
    confKillingCoeff L Rstar (-Rstar) = 0 := by
  rw [confKillingCoeff, neg_div, Real.cosh_neg]; ring

/-- **The derivative** `A'(u) = −sinh(u/L)/L`. -/
theorem confKillingCoeff_hasDerivAt (L Rstar u : ℝ) :
    HasDerivAt (confKillingCoeff L Rstar) (-(Real.sinh (u / L) / L)) u := by
  have hinner : HasDerivAt (fun y : ℝ => y / L) (1 / L) u := by
    simpa using (hasDerivAt_id u).div_const L
  have h := hinner.cosh.const_sub (Real.cosh (Rstar / L))
  exact h.congr_deriv (by ring)

/-- **The normalization** `L/sinh(R_*/L)` of the conformal Killing vector (Eq. A.5). -/
def confKillingNorm (L Rstar : ℝ) : ℝ := L / Real.sinh (Rstar / L)

/-- **Unit surface gravity at the future horizon** `κ = 1` (Jacobson–Visser Eq. A.5): the normalization
`L/sinh(R_*/L)` times `−A'(R_*) = sinh(R_*/L)/L` is `1`. -/
theorem confKilling_unit_surface_gravity (L Rstar : ℝ) (hL : L ≠ 0)
    (hs : Real.sinh (Rstar / L) ≠ 0) :
    confKillingNorm L Rstar * (Real.sinh (Rstar / L) / L) = 1 := by
  rw [confKillingNorm]; field_simp

/-! ### Flat limit (Eq. A.7) -/

/-- **The flat conformal Killing coefficient** `A^flat(u) = (R² − u²)/(2R)` (Jacobson–Visser Eq. A.7,
the `L → ∞` limit): `ζ^flat = (1/2R)[(R²−u²)∂_u + (R²−v²)∂_v]`. -/
def confKillingFlatCoeffUV (R u : ℝ) : ℝ := (R ^ 2 - u ^ 2) / (2 * R)

/-- **The flat coefficient vanishes at the horizons** `u = ±R`. -/
theorem confKillingFlatCoeffUV_horizon (R : ℝ) :
    confKillingFlatCoeffUV R R = 0 ∧ confKillingFlatCoeffUV R (-R) = 0 := by
  constructor <;> · rw [confKillingFlatCoeffUV]; ring

/-- **The flat `(u,v)` coefficient gives the `(t,r)` field** `A^flat(t−r) + A^flat(t+r) = 2 ζ^flat,t`:
the Appendix-A flat conformal Killing vector (Eq. A.7) is the `CausalDiamond.Construction` /
`CausalDiamond.SmallDiamonds` field `ζ^flat,t = (R²−t²−r²)/(2R)`. -/
theorem confKillingFlatUV_sum_eq_time (R t r : ℝ) :
    confKillingFlatCoeffUV R (t - r) + confKillingFlatCoeffUV R (t + r)
      = 2 * confKillingFlatTime R t r := by
  rw [confKillingFlatCoeffUV, confKillingFlatCoeffUV, confKillingFlatTime, confKillingTime]
  ring

/-! ## §B — conformal Killing time and mean curvature (Appendix B) -/

/-- **The conformal factor inverse** `C⁻¹(s,x) = (cosh s + cosh x · cosh(R_*/L))/(L sinh(R_*/L))`
(Jacobson–Visser Eq. B.5), in coordinates adapted to the conformal Killing flow (`s = ` conformal
Killing time). -/
def confTimeCInv (L Rstar s x : ℝ) : ℝ :=
  (Real.cosh s + Real.cosh x * Real.cosh (Rstar / L)) / (L * Real.sinh (Rstar / L))

/-- **The `s`-derivative** `∂_s C⁻¹ = sinh s/(L sinh(R_*/L))` — note it is **independent of `x`**. -/
theorem confTimeCInv_hasDerivAt_s (L Rstar s x : ℝ) :
    HasDerivAt (fun s => confTimeCInv L Rstar s x)
      (Real.sinh s / (L * Real.sinh (Rstar / L))) s := by
  have h := (Real.hasDerivAt_cosh s).add_const (Real.cosh x * Real.cosh (Rstar / L))
  exact h.div_const (L * Real.sinh (Rstar / L))

/-- **`∂_s C⁻¹` is independent of `x`** — hence the mean curvature `K` is **constant on each
constant-`s` slice** (Jacobson–Visser Appendix B, the result `K` is constant on the CMC slices). -/
theorem deriv_confTimeCInv_x_independent (L Rstar s x x' : ℝ) :
    deriv (fun s => confTimeCInv L Rstar s x) s = deriv (fun s => confTimeCInv L Rstar s x') s := by
  rw [(confTimeCInv_hasDerivAt_s L Rstar s x).deriv, (confTimeCInv_hasDerivAt_s L Rstar s x').deriv]

/-- **The mean curvature** `K = (1−d) sinh s/(L sinh(R_*/L))` (Jacobson–Visser Eq. B.6). -/
def meanCurvature (d L Rstar s : ℝ) : ℝ := (1 - d) * Real.sinh s / (L * Real.sinh (Rstar / L))

/-- **`K = (1−d) ∂_s C⁻¹`** (Jacobson–Visser Eqs. B.3, B.6): the trace of the extrinsic curvature of the
constant-conformal-Killing-time slice is `(1−d)` times `∂_s C⁻¹` (independent of `x`). -/
theorem meanCurvature_eq_deriv (d L Rstar s x : ℝ) :
    meanCurvature d L Rstar s = (1 - d) * deriv (fun s => confTimeCInv L Rstar s x) s := by
  rw [(confTimeCInv_hasDerivAt_s L Rstar s x).deriv, meanCurvature]; ring

/-- **The maximal slice has zero mean curvature** `K|_{s=0} = 0` (Jacobson–Visser Appendix B): the
`s = 0` slice `Σ` is a maximal-volume (extremal) slice — the crucial property for the geometric form of
the first law (`sinh 0 = 0`). -/
@[simp] theorem meanCurvature_maximal_slice (d L Rstar : ℝ) : meanCurvature d L Rstar 0 = 0 := by
  rw [meanCurvature, Real.sinh_zero]; ring

/-- **`K` in terms of `α̇|_{s=0}`** (Jacobson–Visser Eq. B.6): `K = (d−1) α̇|_{s=0} sinh s` with
`α̇|_{s=0} = −1/(L sinh(R_*/L))` (matching Eq. 2.11). -/
theorem meanCurvature_eq_alphaDot (d L Rstar s : ℝ) (hL : L ≠ 0)
    (hs : Real.sinh (Rstar / L) ≠ 0) :
    meanCurvature d L Rstar s = (d - 1) * (-(1 / (L * Real.sinh (Rstar / L)))) * Real.sinh s := by
  rw [meanCurvature]; field_simp; ring

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ConformalIsometry

end
