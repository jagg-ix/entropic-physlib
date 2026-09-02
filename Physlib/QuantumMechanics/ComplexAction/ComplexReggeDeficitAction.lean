/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MinkowskianDihedralAngles

/-!
# Null-edge circling, the complexified deficit angles, and the complex Regge action

The remaining §II material of Asante–Dittrich–Padua-Argüelles: circling a configuration with a null
edge (§II.C), the complexified deficit angles (§II.D), and the complex Regge action (§II.E) — built on
the dihedral-angle machinery of `MinkowskianDihedralAngles` / `ComplexReggeActionCausality`.

* **§A — circling a null edge** (§II.C, Eqs. 2.26–2.27). For the path `s_a = r_a e^{iψ}, s_b = 1,
  s_c = 4`, the dihedral discriminant is `¼(s_a² − 10 s_a + 9)` (`nullEdge_discriminant`), factoring as
  `¼(s_a − 1)(s_a − 9)` (`nullEdge_discriminant_factor`) — the null configurations are `s_a = 1, 9`
  (`nullEdge_null_config_*`), and `s_a = 0` is the `log√z` branch point.
* **§B — the complexified deficit angles** (§II.D, Eqs. 2.29–2.33). Flat-cone angle `θ±(flat) = ∓2π`;
  `δ± = 2π ± Σθ±` (`complexDeficitPlus/Minus`), and since `θ⁺ = −θ⁻` the two versions agree
  `δ⁺ = δ⁻` (`deficit_versions_agree`); the Euclidean deficit `ε_E = 2π − Σψ_E` is recovered at
  `φ = 0` (`deficitPlus_euclidean`), and the Lorentzian deficit is `ε_L± = ∓2πi − Σψ_L±`.
* **§C — the complex Regge action** (§II.E, Eqs. 2.38–2.39). The Regge exponent per hinge
  `√V(2π ± Σθ)` (`reggeExponentPlus/Minus`); for Euclidean data (`θ⁺ = −ψ_E`, `θ⁻ = ψ_E`) the two
  versions agree `W⁺ = W⁻` (`regge_euclidean_versions_agree`) and reduce to the Euclidean action
  `√V·ε_E` (`reggeExponent_euclidean_eq_deficit`).

**Honest layering.** Proven: the null-edge discriminant and its factorization, the deficit-angle
`δ⁺ = δ⁻` identity and Euclidean value, the Regge-exponent Euclidean agreement. Interpretive: the
`log√z` branch-point structure at `s_a = 0` and the analytic continuations across it (Eq. 2.28) are
the branch content the factorization underlies; the full triangulation sum is per-hinge here.

## References

* S. K. Asante, B. Dittrich, J. Padua-Argüelles, "Complex actions and causality violations",
  arXiv:2112.15387 [`Asante:2021zzh`], §II.C–E, Eqs. (2.26)–(2.39). Reuses `MinkowskianDihedralAngles`
  (`dihedralDiscriminant`), `ComplexReggeActionCausality` (`lorentzianDeficitImaginary`).


-/

set_option autoImplicit false

open Complex

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexReggeDeficitAction

open Physlib.QuantumMechanics.ComplexAction.MinkowskianDihedralAngles


/-- **The null-edge path discriminant** (Eq. 2.26–2.27): for `s_a = r_a e^{iψ}`, `s_b = 1`, `s_c = 4`,
the dihedral discriminant is `¼(s_a² − 10 s_a + 9)`. -/
lemma nullEdge_discriminant (sa : ℂ) :
    dihedralDiscriminant sa 1 4 = (1 / 4) * (sa ^ 2 - 10 * sa + 9) := by
  unfold dihedralDiscriminant; ring

/-- **Factorization** `s_a² − 10 s_a + 9 = (s_a − 1)(s_a − 9)` — the null configurations of the path. -/
lemma nullEdge_discriminant_factor (sa : ℂ) :
    sa ^ 2 - 10 * sa + 9 = (sa - 1) * (sa - 9) := by ring

/-- The discriminant vanishes at the null configuration `s_a = 1`. -/
lemma nullEdge_null_config_one : ((1 : ℂ) ^ 2 - 10 * 1 + 9) = 0 := by ring

/-- The discriminant vanishes at the null configuration `s_a = 9`. -/
lemma nullEdge_null_config_nine : ((9 : ℂ) ^ 2 - 10 * 9 + 9) = 0 := by ring


/-- **The flat-cone angle** `θ⁺(flat) = −2π` (Eq. 2.29), four times the angle between `(0,1)` and
`(1,0)` — the reference value the deficit is measured against. -/
noncomputable def flatConeAnglePlus : ℝ := -(2 * Real.pi)

/-- **The flat-cone angle** `θ⁻(flat) = +2π` (Eq. 2.29). -/
noncomputable def flatConeAngleMinus : ℝ := 2 * Real.pi

/-- **The complex deficit angle** `δ⁺ = 2π + Σθ⁺` (Eq. 2.30). -/
noncomputable def complexDeficitPlus (sumTheta : ℂ) : ℂ := ((2 * Real.pi : ℝ) : ℂ) + sumTheta

/-- **The complex deficit angle** `δ⁻ = 2π − Σθ⁻` (Eq. 2.30). -/
noncomputable def complexDeficitMinus (sumTheta : ℂ) : ℂ := ((2 * Real.pi : ℝ) : ℂ) - sumTheta

/-- **The two deficit-angle versions agree** `δ⁺ = δ⁻` (Eq. 2.30), because `θ⁺ = −θ⁻` (Theorem II.1)
gives `Σθ⁺ = −Σθ⁻`. -/
lemma deficit_versions_agree (sumThetaPlus sumThetaMinus : ℂ) (h : sumThetaPlus = -sumThetaMinus) :
    complexDeficitPlus sumThetaPlus = complexDeficitMinus sumThetaMinus := by
  unfold complexDeficitPlus complexDeficitMinus; rw [h]; ring

/-- **The Euclidean deficit angle** `ε_E = 2π − Σψ_E` (Eq. 2.31). -/
noncomputable def euclideanDeficit (sumPsiE : ℝ) : ℝ := 2 * Real.pi - sumPsiE

/-- **The Euclidean deficit is recovered at `φ = 0`** (Eq. 2.33): with `θ⁺ = −ψ_E` (Eq. 2.24),
`δ⁺(0) = 2π − Σψ_E = ε_E`. -/
lemma deficitPlus_euclidean (sumPsiE : ℝ) :
    complexDeficitPlus (-(sumPsiE : ℂ)) = ((euclideanDeficit sumPsiE : ℝ) : ℂ) := by
  unfold complexDeficitPlus euclideanDeficit; push_cast; ring

/-- **The Lorentzian deficit angle** `ε_L⁺ = −2πi − Σψ_L⁺` (Eq. 2.32); its imaginary part is
`(N_c − 4)π/2` (`ComplexReggeActionCausality.lorentzianDeficitImaginary`), vanishing iff `N_c = 4`. -/
noncomputable def lorentzianDeficitPlus (sumPsiL : ℂ) : ℂ :=
  -((2 * Real.pi : ℝ) : ℂ) * Complex.I - sumPsiL


/-- **The complex Regge exponent per hinge** `√V(2π + Σθ⁺)` (Eq. 2.39, the `+` version). -/
noncomputable def reggeExponentPlus (sqrtV sumTheta : ℝ) : ℝ := sqrtV * (2 * Real.pi + sumTheta)

/-- **The complex Regge exponent per hinge** `√V(2π − Σθ⁻)` (Eq. 2.39, the `−` version). -/
noncomputable def reggeExponentMinus (sqrtV sumTheta : ℝ) : ℝ := sqrtV * (2 * Real.pi - sumTheta)

/-- **The two Regge-action versions agree on Euclidean data** `W⁺ = W⁻` (Eq. 2.38 note): with
`θ⁺ = −ψ_E` and `θ⁻ = +ψ_E`, both exponents equal `√V(2π − Σψ_E)`. -/
lemma regge_euclidean_versions_agree (sqrtV sumPsiE : ℝ) :
    reggeExponentPlus sqrtV (-sumPsiE) = reggeExponentMinus sqrtV sumPsiE := by
  unfold reggeExponentPlus reggeExponentMinus; ring

/-- **The Euclidean Regge exponent is the deficit-weighted volume** `√V·ε_E` (Eq. 2.38): the complex
Regge action reduces to the Euclidean Regge action on Euclidean data. -/
lemma reggeExponent_euclidean_eq_deficit (sqrtV sumPsiE : ℝ) :
    reggeExponentPlus sqrtV (-sumPsiE) = sqrtV * euclideanDeficit sumPsiE := by
  unfold reggeExponentPlus euclideanDeficit; ring

end Physlib.QuantumMechanics.ComplexAction.ComplexReggeDeficitAction
