/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Matrix.Basic
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixB

/-!
# The full `𝓛_ζ` of the tensors `h_ab` and `K_ab` (Eqs. B.7, B.8 at the tensor level)

`CausalDiamond.AppendixB` formalized Eqs. B.7–B.8 through their *scalar coefficients*. This file builds
the **full Lie derivatives** of the `(0,2)` tensors — the induced metric `h_ab = g_ab + u_a u_b` and the
extrinsic curvature `K_ab = κ_s h_ab` — represented as matrices (`Matrix (Fin n) (Fin n) ℝ`), with the
Lie derivative computed from additivity and the Leibniz rule for the tensor product `u ⊗ u`.

The geometric inputs are the conformal Killing equation `𝓛_ζ g_ab = 2α g_ab` (Eq. 2.7) and the unit
normal relation `𝓛_ζ u_a = α u_a`. From them:

  `𝓛_ζ h_ab = 𝓛_ζ g_ab + 𝓛_ζ(u_a u_b) = 2α g_ab + 2α u_a u_b = 2α h_ab`   (`lieDeriv_inducedMetric`, B.7),

using `𝓛_ζ(u_a u_b) = (𝓛_ζ u_a) u_b + u_a (𝓛_ζ u_b) = α u_a u_b + α u_a u_b = 2α u_a u_b`. And since
`K_ab = κ_s h_ab` is a scalar multiple of `h_ab`,

  `𝓛_ζ K_ab = (𝓛_ζ κ_s) h_ab + κ_s · 2α h_ab = (𝓛_ζ κ_s + 2α κ_s) h_ab`   (`lieDeriv_extrinsicCurvature`),

the coefficient `𝓛_ζκ_s + 2ακ_s = α̇ + α²/|ζ|` of `CausalDiamond.AppendixB.lieExtrinsicCoeff`. On the
maximal slice `Σ` (`α = 0`, `κ_s = 0`): `𝓛_ζ h_ab|_Σ = 0` (`lieDeriv_inducedMetric_sigma`, B.8) and
`𝓛_ζ K_ab|_Σ = (𝓛_ζκ_s) h_ab = α̇|_{s=0} h_ab` (`lieDeriv_extrinsicCurvature_sigma`, B.8).

## References

* T. Jacobson, M. Visser, arXiv:1812.01596, Eqs. 2.7, B.7, B.8. This development:
  `CausalDiamond.AppendixB`.

No new axioms.
-/

set_option autoImplicit false

open Matrix

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LieDerivative

open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.AppendixB

variable {n : ℕ}

/-! ## §A — tensors as matrices: the outer product and the induced metric -/

/-- **The tensor (outer) product** `(u ⊗ v)_ab = u_a v_b`. -/
def vecOuter (u v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j => u i * v j

@[simp] theorem vecOuter_apply (u v : Fin n → ℝ) (i j : Fin n) :
    vecOuter u v i j = u i * v j := rfl

/-- **The induced metric** `h_ab = g_ab + u_a u_b` (the metric on `Σ` with unit normal `u`). -/
def inducedMetric (g : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  g + vecOuter u u

/-! ## §B — the Lie derivative of the induced metric `𝓛_ζ h_ab = 2α h_ab` (Eq. B.7) -/

/-- **The Lie derivative of an outer product** `𝓛_ζ(u_a u_b) = (𝓛_ζ u_a) u_b + u_a (𝓛_ζ u_b)` (the
Leibniz/product rule), with `Lu = 𝓛_ζ u`. -/
def lieOfOuter (Lu u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  vecOuter Lu u + vecOuter u Lu

/-- **The Lie derivative of the induced metric** `𝓛_ζ h_ab = 𝓛_ζ g_ab + 𝓛_ζ(u_a u_b)` (additivity),
with `Lg = 𝓛_ζ g`, `Lu = 𝓛_ζ u`. -/
def lieOfInducedMetric (Lg : Matrix (Fin n) (Fin n) ℝ) (Lu u : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Lg + lieOfOuter Lu u

/-- **Eq. B.7 (full tensor): `𝓛_ζ h_ab = 2α h_ab`.** Given the conformal Killing equation
`𝓛_ζ g_ab = 2α g_ab` (Eq. 2.7) and `𝓛_ζ u_a = α u_a`, the Lie derivative of the induced metric
`h_ab = g_ab + u_a u_b` is the conformal scaling `2α h_ab`. -/
theorem lieDeriv_inducedMetric (g : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (α : ℝ) :
    lieOfInducedMetric ((2 * α) • g) (α • u) u = (2 * α) • inducedMetric g u := by
  ext i j
  simp only [lieOfInducedMetric, lieOfOuter, inducedMetric, vecOuter_apply, Matrix.add_apply,
    Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Eq. B.7 with the scalar coefficient**: `𝓛_ζ h_ab = (lieMetricCoeff α) h_ab` — the full tensor Lie
derivative records exactly the `CausalDiamond.AppendixB.lieMetricCoeff = 2α`. -/
theorem lieDeriv_inducedMetric_coeff (g : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (α : ℝ) :
    lieOfInducedMetric ((2 * α) • g) (α • u) u = lieMetricCoeff α • inducedMetric g u := by
  rw [lieMetricCoeff]; exact lieDeriv_inducedMetric g u α

/-! ## §C — the Lie derivative of the extrinsic curvature `K_ab = κ_s h_ab` (Eq. B.7) -/

/-- **The extrinsic curvature** `K_ab = κ_s h_ab` (a scalar multiple of the induced metric; `κ_s = α/|ζ|`
in the maximally symmetric diamond). -/
def extrinsicCurvature (κs : ℝ) (h : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := κs • h

/-- **The Lie derivative of `K_ab = κ_s h_ab`** `𝓛_ζ K_ab = (𝓛_ζ κ_s) h_ab + κ_s (𝓛_ζ h_ab)` (Leibniz),
with `Lκs = 𝓛_ζ κ_s` and `Lh = 𝓛_ζ h`. -/
def lieOfExtrinsic (Lκs κs : ℝ) (h Lh : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Lκs • h + κs • Lh

/-- **Eq. B.7 (full tensor): `𝓛_ζ K_ab = (𝓛_ζκ_s + 2α κ_s) h_ab`.** With `𝓛_ζ h = 2α h`, the Lie
derivative of `K_ab = κ_s h_ab` is `(𝓛_ζκ_s + 2α κ_s) h_ab` — the coefficient
`CausalDiamond.AppendixB.lieExtrinsicCoeff` (`= α̇ + α²/|ζ|`). -/
theorem lieDeriv_extrinsicCurvature (κs Lκs α : ℝ) (h : Matrix (Fin n) (Fin n) ℝ) :
    lieOfExtrinsic Lκs κs h ((2 * α) • h) = (Lκs + κs * (2 * α)) • h := by
  rw [lieOfExtrinsic, smul_smul, ← add_smul]

/-! ## §D — on the maximal slice `Σ` (`α = 0`, `κ_s = 0`): Eq. B.8 -/

/-- **Eq. B.8 (full tensor): `𝓛_ζ h_ab|_Σ = 0`.** On the maximal slice `α = 0`, so the Lie derivative of
the induced metric vanishes — `Σ` is instantaneously a true Killing slice. -/
theorem lieDeriv_inducedMetric_sigma (g : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    lieOfInducedMetric ((2 * (0 : ℝ)) • g) ((0 : ℝ) • u) u = 0 := by
  rw [lieDeriv_inducedMetric g u 0]; simp

/-- **Eq. B.8 (full tensor): `𝓛_ζ K_ab|_Σ = α̇|_{s=0} h_ab`.** On `Σ` (`κ_s = 0`, `𝓛_ζ h = 0`) the Lie
derivative of the extrinsic curvature reduces to `(𝓛_ζκ_s) h_ab = α̇|_{s=0} h_ab` — the new York
transformation, with `Lκs = α̇|_{s=0}`. -/
theorem lieDeriv_extrinsicCurvature_sigma (Lκs : ℝ) (h : Matrix (Fin n) (Fin n) ℝ) :
    lieOfExtrinsic Lκs 0 h 0 = Lκs • h := by
  rw [lieOfExtrinsic, smul_zero, add_zero]

/-- **The new-York coefficient on `Σ`** `𝓛_ζ K_ab|_Σ = α̇|_{s=0} h_ab` with
`α̇|_{s=0} = alphaDotZero L R_* = −1/(L sinh(R_*/L))`. -/
theorem lieDeriv_extrinsicCurvature_sigma_alphaDot (L Rstar : ℝ) (h : Matrix (Fin n) (Fin n) ℝ) :
    lieOfExtrinsic (alphaDotZero L Rstar) 0 h 0 = alphaDotZero L Rstar • h :=
  lieDeriv_extrinsicCurvature_sigma (alphaDotZero L Rstar) h

/-! ## §E — the algebraic rules backing the definitions: Leibniz/additivity and symmetry

The definitions `lieOfOuter`, `lieOfInducedMetric`, `lieOfExtrinsic` *name* the Leibniz/additivity
rules; the theorems below make those rules explicit (the entrywise product rule each definition realizes)
and prove that the `(0, 2)` tensors `h_ab`, `K_ab` and their Lie derivatives are **symmetric** — the
defining property of a `(0, 2)` metric/curvature tensor, which the rest of the file assumes but never
establishes. -/

/-- **The outer product realizes the Leibniz product rule.** `(𝓛(u_a u_b))_ij = (𝓛u_i) u_j + u_i (𝓛u_j)`
— the matrix `lieOfOuter Lu u` has exactly the entries given by the scalar product rule applied to
`u_i u_j`. This is the content the definition's docstring asserts. -/
@[simp] theorem lieOfOuter_apply (Lu u : Fin n → ℝ) (i j : Fin n) :
    lieOfOuter Lu u i j = Lu i * u j + u i * Lu j := by
  simp only [lieOfOuter, Matrix.add_apply, vecOuter_apply]

/-- **The induced-metric Lie derivative realizes additivity + Leibniz.**
`(𝓛h)_ij = (𝓛g)_ij + ((𝓛u_i) u_j + u_i (𝓛u_j))` — additivity over `h = g + u ⊗ u` together with the
Leibniz rule on `u ⊗ u`, entrywise. -/
@[simp] theorem lieOfInducedMetric_apply (Lg : Matrix (Fin n) (Fin n) ℝ) (Lu u : Fin n → ℝ)
    (i j : Fin n) :
    lieOfInducedMetric Lg Lu u i j = Lg i j + (Lu i * u j + u i * Lu j) := by
  simp only [lieOfInducedMetric, Matrix.add_apply, lieOfOuter_apply]

/-- **The extrinsic-curvature Lie derivative realizes the Leibniz rule for `K = κ_s h`.**
`(𝓛K)_ij = (𝓛κ_s) h_ij + κ_s (𝓛h)_ij` — the product rule for the scalar-times-tensor `κ_s h`,
entrywise. -/
@[simp] theorem lieOfExtrinsic_apply (Lκs κs : ℝ) (h Lh : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    lieOfExtrinsic Lκs κs h Lh i j = Lκs * h i j + κs * Lh i j := by
  simp only [lieOfExtrinsic, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- **The outer product transposes by swapping factors** `(u ⊗ v)ᵀ = v ⊗ u`. -/
theorem vecOuter_transpose (u v : Fin n → ℝ) : (vecOuter u v)ᵀ = vecOuter v u := by
  ext i j
  simp only [Matrix.transpose_apply, vecOuter_apply]
  ring

/-- **`u ⊗ u` is a symmetric tensor** `(u ⊗ u)ᵀ = u ⊗ u`. -/
theorem vecOuter_self_isSymm (u : Fin n → ℝ) : (vecOuter u u)ᵀ = vecOuter u u :=
  vecOuter_transpose u u

/-- **The induced metric is symmetric** `h_abᵀ = h_ab` when `g_ab` is — `h = g + u ⊗ u` is a genuine
`(0, 2)` symmetric tensor. -/
theorem inducedMetric_isSymm (g : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (hg : gᵀ = g) :
    (inducedMetric g u)ᵀ = inducedMetric g u := by
  unfold inducedMetric
  rw [Matrix.transpose_add, hg, vecOuter_self_isSymm]

/-- **The Leibniz term `𝓛(u ⊗ u)` is symmetric** `(lieOfOuter Lu u)ᵀ = lieOfOuter Lu u` — the product
rule `Lu ⊗ u + u ⊗ Lu` is symmetric under transpose (it swaps the two terms). -/
theorem lieOfOuter_isSymm (Lu u : Fin n → ℝ) : (lieOfOuter Lu u)ᵀ = lieOfOuter Lu u := by
  unfold lieOfOuter
  rw [Matrix.transpose_add, vecOuter_transpose, vecOuter_transpose, add_comm]

/-- **`𝓛_ζ h_ab` is symmetric** `(𝓛h)ᵀ = 𝓛h` when `𝓛g` is symmetric — the Lie derivative preserves the
`(0, 2)`-symmetric-tensor structure of the induced metric. -/
theorem lieOfInducedMetric_isSymm (Lg : Matrix (Fin n) (Fin n) ℝ) (Lu u : Fin n → ℝ)
    (hLg : Lgᵀ = Lg) : (lieOfInducedMetric Lg Lu u)ᵀ = lieOfInducedMetric Lg Lu u := by
  unfold lieOfInducedMetric
  rw [Matrix.transpose_add, hLg, lieOfOuter_isSymm]

/-- **The extrinsic curvature is symmetric** `K_abᵀ = K_ab` when `h_ab` is — `K = κ_s h` is a genuine
`(0, 2)` symmetric tensor. -/
theorem extrinsicCurvature_isSymm (κs : ℝ) (h : Matrix (Fin n) (Fin n) ℝ) (hh : hᵀ = h) :
    (extrinsicCurvature κs h)ᵀ = extrinsicCurvature κs h := by
  unfold extrinsicCurvature
  rw [Matrix.transpose_smul, hh]

/-- **`𝓛_ζ K_ab` is symmetric** `(𝓛K)ᵀ = 𝓛K` when `h_ab` and `𝓛h_ab` are — the Lie derivative preserves
the `(0, 2)`-symmetric-tensor structure of the extrinsic curvature. -/
theorem lieOfExtrinsic_isSymm (Lκs κs : ℝ) (h Lh : Matrix (Fin n) (Fin n) ℝ)
    (hh : hᵀ = h) (hLh : Lhᵀ = Lh) :
    (lieOfExtrinsic Lκs κs h Lh)ᵀ = lieOfExtrinsic Lκs κs h Lh := by
  unfold lieOfExtrinsic
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, hh, hLh]

/-- **The computed `𝓛_ζ h_ab = 2α h_ab` is symmetric** on the actual conformal-Killing data
(`𝓛g = 2α g`, `𝓛u = α u`) when `g` is symmetric — the flow keeps the induced metric a symmetric
`(0, 2)` tensor (consistent with `lieDeriv_inducedMetric` giving `2α h`). -/
theorem lieDeriv_inducedMetric_isSymm (g : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (α : ℝ)
    (hg : gᵀ = g) :
    (lieOfInducedMetric ((2 * α) • g) (α • u) u)ᵀ = lieOfInducedMetric ((2 * α) • g) (α • u) u := by
  apply lieOfInducedMetric_isSymm
  rw [Matrix.transpose_smul, hg]

end Physlib.QuantumMechanics.ComplexAction.CausalDiamond.LieDerivative

end
