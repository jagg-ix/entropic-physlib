/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ConformalIsometry

/-!
# Appendix B in full: conformal Killing time and mean curvature (Eqs. B.1–B.8)

This formalizes every numbered equation of Jacobson–Visser Appendix B (arXiv:1812.01596), building on
the `confTimeCInv` (`C⁻¹`, Eq. B.5) and `meanCurvature` (`K`, Eq. B.6) of
`CausalDiamond.ConformalIsometry`. The conformal factor is `C = (C⁻¹)⁻¹`.

* **B.1** `ds² = C²(−ds² + dx²) + r² dΩ²` — components `g_ss = −C²`, `g_xx = C²`, `g_ΩΩ = r²`
 (`metricSS`, `metricXX`, `metricAngular`).
* **B.2** `r = Cρ`, so `ds² = C²[−ds² + dx² + ρ²dΩ²]` (`areaRadiusB`, `metricAngular_B2`).
* **B.3** `K = (d−1)C⁻²∂_s C = (1−d)∂_s C⁻¹` (`meanCurvature_B3_cinv`, `meanCurvature_B3_conformalFactor`).
* **B.4** the null-coordinate relations `e^{ū} = sinh[(R_*+u)/2L]/sinh[(R_*−u)/2L]`,
 `e^{u/L} = cosh[(R_*/L+ū)/2]/cosh[(R_*/L−ū)/2]` (`expUBar`, `expUOverL`).
* **B.5** `C⁻¹ = (cosh s + cosh x cosh(R_*/L))/(L sinh(R_*/L))`, `ρ = sinh x` (`confTimeCInv_B5`, `rho_B5`).
* **B.6** `K = (1−d) sinh s/(L sinh(R_*/L)) = (d−1) α̇|_{s=0} sinh s` (`meanCurvature_B6`, `_B6_alphaDot`).
* **B.7** `𝓛_ζ h_ab = 2α h_ab`, `𝓛_ζ K_ab = (C⁻²∂_s²C) h_ab = (α̇ + α²/|ζ|) h_ab`
 (`lieMetricCoeff`, `lieExtrinsicCoeff`).
* **B.8** on `Σ` (`s = 0`, `α = 0`): `𝓛_ζ h_ab|_Σ = 0`, `𝓛_ζ K_ab|_Σ = α̇|_{s=0} h_ab`
 (`lieMetric_B8`, `lieExtrinsic_B8`).

## Scope

The scalar functions and the algebraic/calculus relations (B.2, B.3, B.5, B.6, B.7/B.8 coefficients) are
proved. The tensor equations B.1/B.7/B.8 are formalized through their scalar metric components and Lie
coefficients (the full `𝓛_ζ` of the tensors is not built); the coordinate relations B.4 and the
`C⁻²∂_s²C = α̇ + α²/|ζ|` identity of B.7 are the computed forms (stated as the defining maps).

No new axioms.
-/

set_option autoImplicit false

open Real

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixB

open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.ConformalIsometry

/-- **The conformal factor** `C = (C⁻¹)⁻¹` (the inverse of `confTimeCInv`, Eq. B.5). -/
def conformalFactor (L Rstar s x : ℝ) : ℝ := (confTimeCInv L Rstar s x)⁻¹

/-- **The radial coordinate function** `ρ(x) = sinh x` (Eq. B.5). -/
def rhoCoord (x : ℝ) : ℝ := Real.sinh x

/-! ## §B.1 — the line element `ds² = C²(−ds² + dx²) + r² dΩ²` -/

/-- **Eq. B.1: `g_ss = −C²`** (the conformal-to-flat `s`-component). -/
def metricSS (L Rstar s x : ℝ) : ℝ := -(conformalFactor L Rstar s x) ^ 2

/-- **Eq. B.1: `g_xx = C²`** (the conformal-to-flat `x`-component). -/
def metricXX (L Rstar s x : ℝ) : ℝ := (conformalFactor L Rstar s x) ^ 2

/-- **Eq. B.2: the area radius `r = Cρ`** (Eq. B.2). -/
def areaRadiusB (L Rstar s x : ℝ) : ℝ := conformalFactor L Rstar s x * rhoCoord x

/-- **Eq. B.1: `g_ΩΩ = r²`** (the angular component). -/
def metricAngular (L Rstar s x : ℝ) : ℝ := (areaRadiusB L Rstar s x) ^ 2

/-- **Eq. B.1 has a conformally-flat 2D block** `g_ss = −g_xx = −C²` (the `(s,x)` metric is `C²` times
the flat `diag(−1, 1)`). -/
theorem metricSS_eq_neg_metricXX (L Rstar s x : ℝ) :
    metricSS L Rstar s x = -metricXX L Rstar s x := by
  rw [metricSS, metricXX]

/-! ## §B.2 — `r = Cρ` factors the metric `ds² = C²[−ds² + dx² + ρ²dΩ²]` -/

/-- **Eq. B.2: `g_ΩΩ = C² ρ²`** — the angular metric factors the conformal factor `C²` out, leaving the
hyperbolic-space metric `ρ²(x) dΩ²` (`ρ = sinh x`): the slice is `ℝ × ℍ^{d-1}` up to the Weyl factor
`C²`. -/
theorem metricAngular_B2 (L Rstar s x : ℝ) :
    metricAngular L Rstar s x = (conformalFactor L Rstar s x) ^ 2 * (rhoCoord x) ^ 2 := by
  rw [metricAngular, areaRadiusB]; ring

/-! ## §B.3 — `K = (d−1)C⁻²∂_s C = (1−d)∂_s C⁻¹` -/

/-- **Eq. B.3 (form 1): `K = (1−d)∂_s C⁻¹`** — the mean curvature is `(1−d)` times the `s`-derivative of
`C⁻¹` (the divergence of the unit normal `u = C⁻¹∂_s`). -/
theorem meanCurvature_B3_cinv (d L Rstar s x : ℝ) :
    meanCurvature d L Rstar s = (1 - d) * deriv (fun s => confTimeCInv L Rstar s x) s :=
  meanCurvature_eq_deriv d L Rstar s x

/-- **`∂_s C`** — the `s`-derivative of the conformal factor `C = (C⁻¹)⁻¹` is `−(∂_s C⁻¹)/(C⁻¹)²`. -/
theorem conformalFactor_hasDerivAt_s (L Rstar s x : ℝ) (h : confTimeCInv L Rstar s x ≠ 0) :
    HasDerivAt (fun s => conformalFactor L Rstar s x)
      (-(Real.sinh s / (L * Real.sinh (Rstar / L))) / (confTimeCInv L Rstar s x) ^ 2) s :=
  (confTimeCInv_hasDerivAt_s L Rstar s x).inv h

/-- **Eq. B.3 (form 2): `K = (d−1)C⁻²∂_s C`** — the equal second form of the mean curvature, via
`∂_s C = −C²∂_s C⁻¹` (so `C⁻²∂_s C = −∂_s C⁻¹`). -/
theorem meanCurvature_B3_conformalFactor (d L Rstar s x : ℝ) (h : confTimeCInv L Rstar s x ≠ 0) :
    meanCurvature d L Rstar s
      = (d - 1) * (confTimeCInv L Rstar s x) ^ 2 * deriv (fun s => conformalFactor L Rstar s x) s := by
  rw [(conformalFactor_hasDerivAt_s L Rstar s x h).deriv, meanCurvature]
  field_simp
  ring

/-! ## §B.4 — the null-coordinate relations (`ū = s − x`, `v̄ = s + x`) -/

/-- **Eq. B.4 (first): `e^{ū} = sinh[(R_*+u)/2L]/sinh[(R_*−u)/2L]`** — the conformal-Killing null
coordinate `ū` in terms of the original null coordinate `u`. -/
def expUBar (L Rstar u : ℝ) : ℝ :=
  Real.sinh ((Rstar + u) / (2 * L)) / Real.sinh ((Rstar - u) / (2 * L))

/-- **Eq. B.4 (second): `e^{u/L} = cosh[(R_*/L+ū)/2]/cosh[(R_*/L−ū)/2]`** — the inverse relation. -/
def expUOverL (L Rstar uBar : ℝ) : ℝ :=
  Real.cosh ((Rstar / L + uBar) / 2) / Real.cosh ((Rstar / L - uBar) / 2)

/-- **At the vertex `u = 0`, `e^{ū} = 1`** (`ū = 0`): a consistency check of Eq. B.4. -/
theorem expUBar_at_zero (L Rstar : ℝ) (h : Real.sinh (Rstar / (2 * L)) ≠ 0) :
    expUBar L Rstar 0 = 1 := by
  rw [expUBar, add_zero, sub_zero, div_self h]

/-! ## §B.5 — `C⁻¹` and `ρ` explicitly -/

/-- **Eq. B.5: `C⁻¹ = (cosh s + cosh x cosh(R_*/L))/(L sinh(R_*/L))`**. -/
theorem confTimeCInv_B5 (L Rstar s x : ℝ) :
    confTimeCInv L Rstar s x
      = (Real.cosh s + Real.cosh x * Real.cosh (Rstar / L)) / (L * Real.sinh (Rstar / L)) := rfl

/-- **Eq. B.5: `ρ = sinh x`**. -/
theorem rho_B5 (x : ℝ) : rhoCoord x = Real.sinh x := rfl

/-! ## §B.6 — the mean curvature explicitly -/

/-- **Eq. B.6: `K = (1−d) sinh s/(L sinh(R_*/L))`**. -/
theorem meanCurvature_B6 (d L Rstar s : ℝ) :
    meanCurvature d L Rstar s = (1 - d) * Real.sinh s / (L * Real.sinh (Rstar / L)) := rfl

/-- **Eq. B.6: `K = (d−1) α̇|_{s=0} sinh s`** with `α̇|_{s=0} = −1/(L sinh(R_*/L))` (Eq. 2.11). -/
theorem meanCurvature_B6_alphaDot (d L Rstar s : ℝ) (hL : L ≠ 0)
    (hs : Real.sinh (Rstar / L) ≠ 0) :
    meanCurvature d L Rstar s = (d - 1) * (-(1 / (L * Real.sinh (Rstar / L)))) * Real.sinh s :=
  meanCurvature_eq_alphaDot d L Rstar s hL hs

/-! ## §B.7 — `𝓛_ζ h_ab = 2α h_ab`, `𝓛_ζ K_ab = (α̇ + α²/|ζ|) h_ab` -/

/-- **Eq. B.7 (metric): `𝓛_ζ h_ab = 2α h_ab`** — the coefficient of `h_ab` in the Lie derivative of the
induced metric is `2α` (from the conformal Killing equation `𝓛_ζ g = 2α g`, Eq. 2.7). -/
def lieMetricCoeff (α : ℝ) : ℝ := 2 * α

/-- **Eq. B.7 (extrinsic curvature): `𝓛_ζ K_ab = (α̇ + α²/|ζ|) h_ab`** — the coefficient of `h_ab` in the
Lie derivative of the extrinsic curvature is `α̇ + α²/|ζ|` (equal to `C⁻²∂_s²C`). -/
def lieExtrinsicCoeff (alphaDot α zetaNorm : ℝ) : ℝ := alphaDot + α ^ 2 / zetaNorm

/-- **Eq. B.7 (metric coefficient).** -/
theorem lieMetric_B7 (α : ℝ) : lieMetricCoeff α = 2 * α := rfl

/-- **Eq. B.7 (extrinsic coefficient).** -/
theorem lieExtrinsic_B7 (alphaDot α zetaNorm : ℝ) :
    lieExtrinsicCoeff alphaDot α zetaNorm = alphaDot + α ^ 2 / zetaNorm := rfl

/-! ## §B.8 — on the maximal slice `Σ` (`s = 0`, `α = 0`) -/

/-- **Eq. B.8 (metric): `𝓛_ζ h_ab|_Σ = 0`** — on the maximal slice the conformal factor `α = 0`
(`Σ` is everywhere orthogonal to `ζ`), so the Lie derivative of the induced metric vanishes: `Σ`
behaves *instantaneously* like a true Killing slice (cf. Eq. 2.8). -/
theorem lieMetric_B8 : lieMetricCoeff 0 = 0 := by rw [lieMetricCoeff, mul_zero]

/-- **Eq. B.8 (extrinsic curvature): `𝓛_ζ K_ab|_Σ = α̇|_{s=0} h_ab`** — at `α = 0` the extrinsic-curvature
Lie coefficient `α̇ + α²/|ζ|` reduces to `α̇|_{s=0}`: this is the *new York transformation* identified
on `Σ`. -/
theorem lieExtrinsic_B8 (alphaDot zetaNorm : ℝ) :
    lieExtrinsicCoeff alphaDot 0 zetaNorm = alphaDot := by
  rw [lieExtrinsicCoeff]; simp

/-- **`α̇|_{s=0} = −1/(L sinh(R_*/L))`** (Eq. 2.11), the value of the new-York coefficient on `Σ`. -/
def alphaDotZero (L Rstar : ℝ) : ℝ := -(1 / (L * Real.sinh (Rstar / L)))

/-- **The maximal-slice mean curvature vanishes** `K|_{s=0} = 0` (consistent with `α = 0` on `Σ`, Eq.
B.8): `Σ` is the extremal-volume slice. -/
theorem meanCurvature_B8_maximal (d L Rstar : ℝ) : meanCurvature d L Rstar 0 = 0 :=
  meanCurvature_maximal_slice d L Rstar

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixB

end
